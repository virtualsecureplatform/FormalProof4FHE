module

public import FormalProof4FHE.HasteBoots.NativeRootFamilyAudit
public import FormalProof4FHE.HasteBoots.OracleMachine
public import FormalProof4FHE.HasteBoots.ExpectedHazardMonotone
public import FormalProof4FHE.HasteBoots.NativeProgramComposition
@[expose] public section

/-! Persistent source/collision risk over an unbounded causal machine lifetime. The prelude is included in every complete prefix; suspension resumes the same ledger, byte cache, hash cache and monitor. The bound is an ideal-oracle charge supremum, not a physical-work or termination claim. -/
namespace FormalProof4FHE.HasteBoots.NativeRootFamilyLifetime
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (Input World)
open NativeGoldColumnAuthentication (encoding)
open NativeMerkleShapeFamily (shape)
open NativeGoldBatchFamilyAvailability (reconstructed)
open OracleProgram (Program run bind)
open OracleSpec OracleComp MeasureTheory
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

/-- The causal prelude is part of every actual complete prefix history. -/
def program {S A : Type} (prelude : Program S) (step : S → OracleMachine.Command S A) (fuel : ℕ) :=
  bind prelude (OracleMachine.take step fuel)

def prefixCharge {S A : Type} (dummy : Digest) (prelude : Program S) (step : S → OracleMachine.Command S A) (fuel : ℕ) :=
  ExpectedHazard.charge
    (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) encoding dummy shape)
    (CheckpointCollision.loss unifSpec shape)
    ((NativeRootFamilyFreeze.compile NativeParentLedger.empty (program prelude step fuel)).run NativeShakeCache.empty)
    (CheckpointExecution.empty shape)

def Bad (dummy : Digest) (history : List Observation) : Prop := CheckpointCollision.Bad shape (reconstructed dummy history)

theorem log_prefix {S A : Type} (prelude : Program S) (step : S → OracleMachine.Command S A)
    (first later : ℕ) (bounded : first ≤ later) (world : World) :
    (run (program prelude step first) world).run.2.IsPrefix (run (program prelude step later) world).run.2 := by
  obtain ⟨suffix,same⟩ := OracleMachine.log_prefix step first later bounded (run prelude world).run.1 world
  refine ⟨suffix,?_⟩
  simp only [program,OracleProgram.run_bind,ObservationReplay.run_bind]
  rw [List.append_assoc,same]

theorem charge_bind {A B : Type} (dummy : Digest) (ledger : NativeParentLedger.State)
    (cache : NativeShakeCache.Cache) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (first : Program A) (next : A → Program B) :
    ExpectedHazard.charge
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) encoding dummy shape)
      (CheckpointCollision.loss unifSpec shape) ((NativeRootFamilyFreeze.compile ledger first).run cache) state ≤
    ExpectedHazard.charge
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) encoding dummy shape)
      (CheckpointCollision.loss unifSpec shape) ((NativeRootFamilyFreeze.compile ledger (bind first next)).run cache) state := by
  rw [NativeRootFamilyFreeze.compile_bind]
  simp only [StateT.run_bind,StateT.run_pure]
  exact ExpectedHazardMonotone.charge_bind _ _ _ _ state

/-- The supremum is over increasing charges on the same causal run, including
its prelude; prefix extension never resets either cache or the root ledger. -/
theorem prefixCharge_monotone {S A : Type} (dummy : Digest) (prelude : Program S) (step : S → OracleMachine.Command S A) :
    Monotone (prefixCharge dummy prelude step) := by
  intro first later bounded
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le bounded
  have same : program prelude step (first+extra) =
      bind (program prelude step first) (OracleMachine.resume step extra) := by
    simp only [program,NativeProgramComposition.bind_assoc]
    apply congrArg (OracleProgram.bind prelude)
    funext initial
    exact OracleMachine.take_resume step first extra initial
  unfold prefixCharge
  rw [same]
  exact charge_bind dummy NativeParentLedger.empty NativeShakeCache.empty (CheckpointExecution.empty shape) _ _

theorem bad_monotone {S A : Type} (dummy : Digest) (prelude : Program S) (step : S → OracleMachine.Command S A) :
    Monotone (fun fuel : ℕ => {world | Bad dummy (run (program prelude step fuel) world).run.2}) := by
  intro first later bounded world failed
  exact NativeRootFamilyAudit.bad_persistent dummy world _ _ ((OracleProgram.run_replay _).truthful world)
    (log_prefix prelude step first later bounded world) failed

/-- No query/lifetime cutoff: the persistent bad-event probability is bounded
by the supremum of charges on the same actual full-state prefixes. -/
theorem lifetime_bad_le_charge {S A : Type} (dummy : Digest) (prelude : Program S) (step : S → OracleMachine.Command S A) :
    InputIndexedOracle.law {world | ∃ fuel, Bad dummy (run (program prelude step fuel) world).run.2} ≤
      ⨆ fuel : ℕ, prefixCharge dummy prelude step fuel := by
  have union : {world | ∃ fuel, Bad dummy (run (program prelude step fuel) world).run.2} =
      ⋃ fuel : ℕ, {world | Bad dummy (run (program prelude step fuel) world).run.2} := by
    ext world
    simp
  rw [union,(bad_monotone dummy prelude step).measure_iUnion]
  exact iSup_mono (fun fuel => NativeRootFamilyAudit.bad_le_charge dummy (program prelude step fuel))

/-- Prefix suspension carries the actual ledger, owned SHAKE cache, shared
SHA512 cache, checkpoints, flag, and residual local machine state. -/
theorem execute_resume {S A : Type} (dummy : Digest) (step : S → OracleMachine.Command S A)
    (first later : ℕ) (initial : S) (ledger : NativeParentLedger.State) (cache : NativeShakeCache.Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    NativeRootFamilyFreeze.execute encoding dummy ledger (OracleMachine.take step (first+later) initial) cache state = (do
      let before ← NativeRootFamilyFreeze.execute encoding dummy ledger (OracleMachine.take step first initial) cache state
      let after ← NativeRootFamilyFreeze.execute encoding dummy before.1.1.2
        (OracleMachine.resume step later before.1.1.1.1) before.1.2 before.2
      pure ((((after.1.1.1.1,before.1.1.1.2++after.1.1.1.2),after.1.1.2),after.1.2),after.2)) := by
  rw [OracleMachine.take_resume]
  exact NativeRootFamilyState.execute_bind encoding dummy _ _ ledger cache state
end
end FormalProof4FHE.HasteBoots.NativeRootFamilyLifetime
