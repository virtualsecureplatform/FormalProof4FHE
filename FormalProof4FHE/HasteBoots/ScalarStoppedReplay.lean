module
public import FormalProof4FHE.HasteBoots.ScalarAncestorExposure
@[expose] public section

/-! Causal native scalar replay stopped before the selected stream is read.
The guard inspects only the current native control and retained input. The
returned expected vector and point are actual machine state, not supplied
reconstructions from a receipt hash. -/
namespace FormalProof4FHE.HasteBoots.ScalarStoppedReplay
open InputIndexedOracle (Input World)
open NativeScalarBatchVerifier (Machine)
open NativeScalarBatchWire (Statement)
open NativeScalarBatchPreflight (Proof)
open NativeTranscript (Observation)
open OracleProgram (Program bind run)

/-- Reader starts are allowed. Sampling the selected input is not. -/
def blocked (target : Input) (machine : Machine) : Bool :=
  match machine.control with
  | .sampling _ field => decide (field.phase.pending.input = target)
  | _ => false

def program (target : Input) (statement : Statement) (proof : Proof) : ℕ → Machine → Program (Bool × Machine)
  | 0, machine => .pure (blocked target machine, machine)
  | fuel + 1, machine =>
      if blocked target machine then .pure (true, machine)
      else bind (NativeScalarBatchVerifier.tick statement proof machine) (program target statement proof fuel)

def execute (target : Input) (statement : Statement) (proof : Proof) : ℕ → Machine → World → (Bool × Machine) × List Observation
  | 0, machine, _ => ((blocked target machine, machine), [])
  | fuel + 1, machine, world =>
      if blocked target machine then ((true, machine), [])
      else
        let trial := NativeScalarBatchVerifier.tickExecute statement proof machine world
        let later := execute target statement proof fuel trial.1 world
        (later.1, trial.2 ++ later.2)

/-- Once the selected reader is reached, extra auxiliary budget is inert. -/
theorem stopped (target : Input) (statement : Statement) (proof : Proof) (fuel : ℕ)
    (machine : Machine) (world : World) (stop : blocked target machine = true) :
    execute target statement proof fuel machine world = ((true,machine),[]) := by
  cases fuel <;> simp [execute, stop]

theorem run_program (target : Input) (statement : Statement) (proof : Proof) (fuel : ℕ) (machine : Machine) (world : World) :
    (run (program target statement proof fuel machine) world).run = execute target statement proof fuel machine world := by
  induction fuel generalizing machine with
  | zero => rfl
  | succ fuel ih =>
    simp only [program, execute]
    split
    · rfl
    · simp only [OracleProgram.run_bind, ObservationReplay.run_bind, NativeScalarBatchVerifier.run_tick, ih]

theorem replayable (target : Input) (statement : Statement) (proof : Proof) (fuel : ℕ) (machine : Machine) :
    ObservationReplay.Replayable (run (program target statement proof fuel machine)) := OracleProgram.run_replay _

/-- An unblocked native tick cannot read the selected parsed stream, even
when a prior round finishes and emits its receipt during that tick. -/
theorem tick_unseen (target : Input) (view : ScalarChallengeInputView.View)
    (parsed : ScalarChallengeInputView.parse target = some view)
    (statement : Statement) (proof : Proof) (machine : Machine) (world : World)
    (allowed : blocked target machine = false) :
    CausalStreamExposure.seen (NativeScalarBatchVerifier.tickExecute statement proof machine world).2 target = false := by
  cases control : machine.control with
  | finished claims => simp [NativeScalarBatchVerifier.tickExecute, control, CausalStreamExposure.seen]
  | failed error => simp [NativeScalarBatchVerifier.tickExecute, control, CausalStreamExposure.seen]
  | ready =>
    simp only [NativeScalarBatchVerifier.tickExecute, control]
    split
    · rfl
    · simp [TypedFieldRequest.beginExecute,
        CausalStreamExposure.seen, CausalStreamExposure.touches]
  | sampling packet field =>
    have different : field.phase.pending.input ≠ target := by
      simpa only [blocked, control, decide_eq_false_iff_not] using allowed
    simp only [NativeScalarBatchVerifier.tickExecute, control]
    change CausalStreamExposure.seen (NativeFieldVector.driveExecute NativeFields.goldilocksModulus 1 field world).2 target = false
    exact ScalarAncestorExposure.drive_unseen _ _ field world target view parsed different

/-- Every finite stopped replay, including rejected and suspended runs,
leaves all selected SHAKE coordinates unobserved. -/
theorem unseen (target : Input) (view : ScalarChallengeInputView.View)
    (parsed : ScalarChallengeInputView.parse target = some view)
    (statement : Statement) (proof : Proof) (fuel : ℕ) (machine : Machine) (world : World) :
    CausalStreamExposure.seen (execute target statement proof fuel machine world).2 target = false := by
  induction fuel generalizing machine with
  | zero => rfl
  | succ fuel ih =>
    by_cases stop : blocked target machine = true
    · simp [execute, stop, CausalStreamExposure.seen]
    · have allowed : blocked target machine = false := Bool.eq_false_iff.mpr stop
      simp only [execute, allowed, Bool.false_eq_true, ite_false, ScalarAncestorExposure.seen_append,
        tick_unseen target view parsed statement proof machine world allowed, Bool.false_or]
      exact ih _

/-- Exact native prefix origin, including the entire ordered observation
log. Stopping never invents a prior expected vector or discards a read. -/
theorem origin (target : Input) (statement : Statement) (proof : Proof) (fuel : ℕ) (machine : Machine) (world : World) :
    ∃ used ≤ fuel,
      ((execute target statement proof fuel machine world).1.2,
        (execute target statement proof fuel machine world).2) =
          NativeScalarBatchVerifier.execute statement proof used machine world ∧
      (execute target statement proof fuel machine world).1.1 =
        blocked target (execute target statement proof fuel machine world).1.2 := by
  induction fuel generalizing machine with
  | zero => exact ⟨0, le_rfl, rfl, rfl⟩
  | succ fuel ih =>
    by_cases stop : blocked target machine = true
    · exact ⟨0, Nat.zero_le _, by simp [execute, stop, NativeScalarBatchVerifier.execute], by simp [execute, stop]⟩
    · have allowed : blocked target machine = false := Bool.eq_false_iff.mpr stop
      obtain ⟨used, bound, same, flag⟩ := ih (NativeScalarBatchVerifier.tickExecute statement proof machine world).1
      refine ⟨used + 1, by omega, ?_, ?_⟩
      · simp only [execute, allowed, Bool.false_eq_true, ite_false, NativeScalarBatchVerifier.execute]
        have first := congrArg Prod.fst same
        have log := congrArg Prod.snd same
        exact Prod.ext first (congrArg (fun tail => (NativeScalarBatchVerifier.tickExecute statement proof machine world).2 ++ tail) log)
      · simpa only [execute, allowed, Bool.false_eq_true, ite_false] using flag

/-- On a prefix with no earlier selected reader, stopped execution is exactly
native execution. In particular the first native occurrence is retained. -/
theorem before_first (target : Input) (statement : Statement) (proof : Proof) (fuel : ℕ)
    (machine : Machine) (world : World)
    (earlier : ∀ index < fuel, blocked target (NativeScalarBatchVerifier.execute statement proof index machine world).1 = false) :
    execute target statement proof fuel machine world =
      ((blocked target (NativeScalarBatchVerifier.execute statement proof fuel machine world).1,
        (NativeScalarBatchVerifier.execute statement proof fuel machine world).1),
        (NativeScalarBatchVerifier.execute statement proof fuel machine world).2) := by
  induction fuel generalizing machine with
  | zero => rfl
  | succ fuel ih =>
    have allowed := earlier 0 (Nat.zero_lt_succ fuel)
    change blocked target machine = false at allowed
    have tail : ∀ index < fuel, blocked target
        (NativeScalarBatchVerifier.execute statement proof index
          (NativeScalarBatchVerifier.tickExecute statement proof machine world).1 world).1 = false := by
      intro index bound
      simpa only [NativeScalarBatchVerifier.execute] using earlier (index + 1) (by omega)
    simp only [execute, allowed, Bool.false_eq_true, ite_false, ih _ tail,
      NativeScalarBatchVerifier.execute]

/-- The prior expected vector, completed records and common point returned
by initialized replay satisfy the existing actual native chain invariant. -/
theorem initialized_linked (target : Input) (transcript result : NativeTranscript.Transcript)
    (statement : Statement) (proof : Proof)
    (accepted : NativeScalarBatchPreflight.beginVerify transcript statement proof = .ok result)
    (fuel : ℕ) (world : World) :
    NativeScalarBatchHistory.Linked statement proof
      (execute target statement proof fuel (NativeScalarBatchVerifier.initial transcript statement proof) world).1.2 := by
  obtain ⟨used, _, same, _⟩ := origin target statement proof fuel
    (NativeScalarBatchVerifier.initial transcript statement proof) world
  have machineEq := congrArg Prod.fst same
  dsimp only at machineEq
  rw [machineEq]
  exact NativeScalarBatchHistory.initialized_linked transcript result statement proof accepted used world

/-- Extending an unseen retained past with auxiliary stopped replay preserves
freshness at every selected-stream offset. This includes the replay's receipt
queries, not only its field-candidate reads. -/
theorem retained_fresh (target : Input) (view : ScalarChallengeInputView.View)
    (parsed : ScalarChallengeInputView.parse target = some view)
    (statement : Statement) (proof : Proof) (fuel : ℕ) (machine : Machine) (world : World)
    (past : List Observation) (notSeen : CausalStreamExposure.seen past target = false) (offset : ℕ) :
    FreshShakeTail.Fresh (NativeShakeKernel.observed
      (past ++ (execute target statement proof fuel machine world).2) world) target offset := by
  apply FreshShakeTail.observed_fresh
  intro position beyond
  apply CausalStreamExposure.unseen_coordinates
  rw [ScalarAncestorExposure.seen_append, notSeen, unseen target view parsed statement proof fuel machine world]
  rfl

end FormalProof4FHE.HasteBoots.ScalarStoppedReplay
