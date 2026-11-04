module

public import FormalProof4FHE.HasteBoots.NativeRootMessage
public import FormalProof4FHE.HasteBoots.TypedFieldVector
public import FormalProof4FHE.HasteBoots.NativeLookupBatch
import all Init.Data.String.Defs

@[expose] public section

/-!
# Helper-root binding followed by native shared lookup equality points

This is the next phase of the canonical shared lookup child after all
compression/reciprocal challenges. Roots are supplied by the proof (or the
prover's commitment phase), not invented by this compiler. Native dimension
checks must have already identified their number with the challenge count.
Each point uses one typed vector request, retaining the full reader and
receipt across analysis pauses. Sumcheck, commitment/leaf generation,
source refinement and expected-work bounds remain separate obligations.
-/

namespace FormalProof4FHE.HasteBoots.NativeLookupEquality

open InputIndexedOracle (Input World)
open NativeTranscript (Transcript Observation utf8)
open OracleProgram (Program bind run)

def rootsLabel : Input := utf8 "shared lookup helper roots"
def pointLabel : Input := utf8 "shared lookup equality point"

def bindRoots (transcript : Transcript) (roots : List NativeRootMessage.Digest)
    (fits : roots.length < 2 ^ 64) : Transcript :=
  NativeTranscript.appendBytes transcript rootsLabel (NativeRootMessage.encode roots fits)

theorem bindRoots_input (transcript : Transcript) (roots : List NativeRootMessage.Digest)
    (fits : roots.length < 2 ^ 64) :
    (bindRoots transcript roots fits).input = transcript.input ++
      TranscriptFrame.encode ⟨1, rootsLabel, NativeRootMessage.encode roots fits⟩ := rfl

/-- A complete, well-sized helper-root message is bound injectively in
the child input. This does not assert collision freedom of oracle outputs. -/
theorem bindRoots_injective (transcript : Transcript) (left right : List NativeRootMessage.Digest)
    (leftFits : left.length < 2 ^ 64) (rightFits : right.length < 2 ^ 64)
    (leftFrame : (NativeRootMessage.encode left leftFits).length < TranscriptFrame.lengthLimit)
    (rightFrame : (NativeRootMessage.encode right rightFits).length < TranscriptFrame.lengthLimit)
    (same : (bindRoots transcript left leftFits).input = (bindRoots transcript right rightFits).input) : left = right := by
  rw [bindRoots_input, bindRoots_input] at same
  have bytes := List.append_cancel_left same
  have labelFits : rootsLabel.length < TranscriptFrame.lengthLimit := by decide +kernel
  have frames := TranscriptFrame.encodeMany_injective
    [⟨1, rootsLabel, NativeRootMessage.encode left leftFits⟩]
    [⟨1, rootsLabel, NativeRootMessage.encode right rightFits⟩]
    (by intro frame member; obtain rfl := List.mem_singleton.mp member; exact ⟨labelFits, leftFrame⟩)
    (by intro frame member; obtain rfl := List.mem_singleton.mp member; exact ⟨labelFits, rightFrame⟩)
    (by simpa only [TranscriptFrame.encodeMany, List.append_nil] using bytes)
  have frame := List.cons.inj frames
  exact NativeRootMessage.encode_injective left right leftFits rightFits (congrArg TranscriptFrame.Frame.message frame.1)

theorem first_input_injective (p degree w count : ℕ) (transcript : Transcript)
    (left right : List NativeRootMessage.Digest) (leftFits : left.length < 2 ^ 64) (rightFits : right.length < 2 ^ 64)
    (leftFrame : (NativeRootMessage.encode left leftFits).length < TranscriptFrame.lengthLimit)
    (rightFrame : (NativeRootMessage.encode right rightFits).length < TranscriptFrame.lengthLimit)
    (same : (TypedFieldVector.phase p degree w count (bindRoots transcript left leftFits) pointLabel).pending.input =
      (TypedFieldVector.phase p degree w count (bindRoots transcript right rightFits) pointLabel).pending.input) : left = right :=
  bindRoots_injective transcript left right leftFits rightFits leftFrame rightFrame
    (TypedFieldVector.phase_input_injective p degree w count _ _ pointLabel same)

structure Draw (count : ℕ) (K : Type) where
  point : Fin count → K
  coefficients : NativeFieldVector.State

structure Machine (count : ℕ) (K : Type) where
  remaining : ℕ
  active : Option NativeFieldVector.State
  draws : List (Draw count K)
  transcript : Transcript

def initial {K : Type} (count : ℕ) (transcript : Transcript) (roots : List NativeRootMessage.Digest)
    (fits : roots.length < 2 ^ 64) : Machine count K :=
  ⟨roots.length, none, [], bindRoots transcript roots fits⟩

noncomputable section

variable {p degree count : ℕ} {K : Type} [Field K] [Algebra (ZMod p) K]

def tick (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ) (machine : Machine count K) :
    Program (Machine count K) :=
  if machine.remaining = 0 then .pure machine
  else match machine.active with
  | none => bind (TypedFieldVector.begin p degree w count machine.transcript pointLabel)
      (fun field => .pure { machine with active := some field })
  | some field => bind (NativeFieldVector.drive p 1 field) (fun result => match result with
      | .suspended field => .pure { machine with active := some field }
      | .finished field transcript => .pure
          ⟨machine.remaining - 1, none,
            machine.draws ++ [⟨TypedFieldVector.value basis count field.values, field⟩], transcript⟩)

def tickExecute (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ)
    (machine : Machine count K) (world : World) : Machine count K × List Observation :=
  if machine.remaining = 0 then (machine, [])
  else match machine.active with
  | none =>
      let started := TypedFieldVector.beginExecute p degree w count machine.transcript pointLabel
      ({ machine with active := some started.1 }, started.2)
  | some field =>
      let trial := NativeFieldVector.driveExecute p 1 field world
      match trial.1 with
      | .suspended field => ({ machine with active := some field }, trial.2)
      | .finished field transcript =>
          (⟨machine.remaining - 1, none,
            machine.draws ++ [⟨TypedFieldVector.value basis count field.values, field⟩], transcript⟩, trial.2)

theorem run_tick (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ)
    (machine : Machine count K) (world : World) :
    (run (tick basis w machine) world).run = tickExecute basis w machine world := by
  simp only [tick, tickExecute]
  split
  · rfl
  · split
    · simp only [OracleProgram.run_bind, ObservationReplay.run_bind, TypedFieldVector.run_begin,
        OracleProgram.run, CanonicalTranscriptSampler.run_pure, List.append_nil]
    · simp only [OracleProgram.run_bind, ObservationReplay.run_bind, NativeFieldVector.run_drive]
      split <;> simp only [OracleProgram.run, CanonicalTranscriptSampler.run_pure, List.append_nil]

def steps (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ) : ℕ → Machine count K → Program (Machine count K)
  | 0, machine => .pure machine
  | fuel + 1, machine => bind (tick basis w machine) (steps basis w fuel)

def execute (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ) :
    ℕ → Machine count K → World → Machine count K × List Observation
  | 0, machine, _ => (machine, [])
  | fuel + 1, machine, world =>
      let trial := tickExecute basis w machine world
      let later := execute basis w fuel trial.1 world
      (later.1, trial.2 ++ later.2)

theorem run_steps (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (machine : Machine count K) (world : World) :
    (run (steps basis w fuel machine) world).run = execute basis w fuel machine world := by
  induction fuel generalizing machine with
  | zero => rfl
  | succ fuel ih => simp only [steps, execute, OracleProgram.run_bind, ObservationReplay.run_bind, run_tick, ih]

theorem execute_add (basis : Module.Basis (Fin degree) (ZMod p) K) (w first extra : ℕ)
    (machine : Machine count K) (world : World) :
    execute basis w (first + extra) machine world =
      let earlier := execute basis w first machine world
      let later := execute basis w extra earlier.1 world
      (later.1, earlier.2 ++ later.2) := by
  induction first generalizing machine with
  | zero => simp [execute]
  | succ first ih => simp only [Nat.succ_add, execute, ih, List.append_assoc]

def request (basis : Module.Basis (Fin degree) (ZMod p) K) (w count fuel : ℕ)
    (transcript : Transcript) (roots : List NativeRootMessage.Digest) (fits : roots.length < 2 ^ 64) :
    Program (Machine count K) := steps basis w fuel (initial count transcript roots fits)

/-- Completed points and remaining points retain exactly the number of
roots supplied before the first equality challenge. -/
theorem tick_count (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ)
    (machine : Machine count K) (world : World) :
    (tickExecute basis w machine world).1.remaining + (tickExecute basis w machine world).1.draws.length =
      machine.remaining + machine.draws.length := by
  simp only [tickExecute]
  split
  · rfl
  · rename_i pending
    split
    · rfl
    · split
      · rfl
      · simp only [List.length_append, List.length_singleton]
        omega

theorem execute_count (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (machine : Machine count K) (world : World) :
    (execute basis w fuel machine world).1.remaining + (execute basis w fuel machine world).1.draws.length =
      machine.remaining + machine.draws.length := by
  induction fuel generalizing machine with
  | zero => rfl
  | succ fuel ih => exact (ih _).trans (tick_count basis w machine world)

/-- No more reads or receipts are emitted after all points complete. -/
theorem execute_complete (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (machine : Machine count K) (world : World) (complete : machine.remaining = 0) :
    execute basis w fuel machine world = (machine, []) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [execute, tickExecute, complete, ite_true, ih, List.nil_append]

def Valid (basis : Module.Basis (Fin degree) (ZMod p) K) (machine : Machine count K) : Prop :=
  (match machine.active with
    | none => True
    | some field => TypedFieldRequest.FieldValid p (count * degree) field) ∧
  ∀ draw ∈ machine.draws, draw.coefficients.values.length = count * degree ∧
    NativeFieldVector.ValuesValid p draw.coefficients ∧
    draw.point = TypedFieldVector.value basis count draw.coefficients.values

theorem initial_valid (basis : Module.Basis (Fin degree) (ZMod p) K) (count : ℕ)
    (transcript : Transcript) (roots : List NativeRootMessage.Digest) (fits : roots.length < 2 ^ 64) :
    Valid basis (initial count transcript roots fits) := ⟨True.intro, by simp [initial]⟩

theorem tick_valid (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ)
    (machine : Machine count K) (world : World) (valid : Valid basis machine) :
    Valid basis (tickExecute basis w machine world).1 := by
  simp only [tickExecute]
  split
  · exact valid
  · split
    · exact ⟨TypedFieldVector.begin_valid p degree w count machine.transcript pointLabel, valid.2⟩
    next field active =>
      cases trial : (NativeFieldVector.driveExecute p 1 field world).1 with
      | suspended next =>
        have updated := TypedFieldRequest.drive_valid p (count * degree) 1 world field (by simpa only [active] using valid.1)
        rw [trial] at updated
        exact ⟨updated, valid.2⟩
      | finished completed transcript =>
        have finished := TypedFieldRequest.drive_finished_length p (count * degree) 1 world field completed transcript
          (by simpa only [active] using valid.1) trial
        refine ⟨True.intro, ?_⟩
        intro draw member
        rcases List.mem_append.mp member with prior | added
        · exact valid.2 draw prior
        · have same := List.mem_singleton.mp added
          subst draw
          exact ⟨finished.1, finished.2, rfl⟩

theorem execute_valid (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (machine : Machine count K) (world : World) (valid : Valid basis machine) :
    Valid basis (execute basis w fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact valid
  | succ fuel ih => exact ih _ (tick_valid basis w machine world valid)

theorem draw_coordinate (basis : Module.Basis (Fin degree) (ZMod p) K) (machine : Machine count K)
    (valid : Valid basis machine) (draw : Draw count K) (member : draw ∈ machine.draws)
    (element : Fin count) (coordinate : Fin degree) :
    (basis.equivFun (draw.point element) coordinate).val =
      draw.coefficients.values[coordinate.val + degree * element.val]'(by
        have length := (valid.2 draw member).1
        have bound := (finProdFinEquiv (element, coordinate)).isLt
        change coordinate.val + degree * element.val < count * degree at bound
        omega) := by
  have information := valid.2 draw member
  rw [information.2.2]
  exact TypedFieldVector.value_coordinate basis count draw.coefficients.values information.1 information.2.1 element coordinate

theorem request_valid (basis : Module.Basis (Fin degree) (ZMod p) K) (w count fuel : ℕ)
    (transcript : Transcript) (roots : List NativeRootMessage.Digest) (fits : roots.length < 2 ^ 64) (world : World) :
    Valid basis (run (request basis w count fuel transcript roots fits) world).run.1 := by
  rw [request, run_steps]
  exact execute_valid basis w fuel _ world (initial_valid basis count transcript roots fits)

theorem request_count (basis : Module.Basis (Fin degree) (ZMod p) K) (w count fuel : ℕ)
    (transcript : Transcript) (roots : List NativeRootMessage.Digest) (fits : roots.length < 2 ^ 64) (world : World) :
    let result := (run (request basis w count fuel transcript roots fits) world).run.1
    result.remaining + result.draws.length = roots.length := by
  rw [request, run_steps]
  dsimp only
  rw [execute_count]
  simp only [initial, List.length_nil, add_zero]

theorem request_replay (basis : Module.Basis (Fin degree) (ZMod p) K) (w count fuel : ℕ)
    (transcript : Transcript) (roots : List NativeRootMessage.Digest) (fits : roots.length < 2 ^ 64) :
    ObservationReplay.Replayable (run (request basis w count fuel transcript roots fits)) := OracleProgram.run_replay _

/-- The very first observation is the vector reader start under the
already absorbed full root packet; no candidate or receipt precedes it. -/
theorem request_first_start (basis : Module.Basis (Fin degree) (ZMod p) K) (w count : ℕ)
    (transcript : Transcript) (roots : List NativeRootMessage.Digest) (fits : roots.length < 2 ^ 64)
    (nonempty : roots.length ≠ 0) (world : World) :
    (run (request basis w count 1 transcript roots fits) world).run.2 =
      [.start (TypedFieldVector.phase p degree w count (bindRoots transcript roots fits) pointLabel).pending.input] := by
  simp only [request, steps, tick, initial, nonempty, ite_false, OracleProgram.run_bind,
    ObservationReplay.run_bind, TypedFieldVector.run_begin, OracleProgram.run,
    CanonicalTranscriptSampler.run_pure, List.append_nil, TypedFieldVector.beginExecute]

/-- Completion clears the active reader. Zero-dimensional points still
need their single final receipt before this condition can be reached. -/
def Settled (machine : Machine count K) : Prop := machine.remaining = 0 → machine.active = none

theorem tick_settled (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ)
    (machine : Machine count K) (world : World) (settled : Settled machine) :
    Settled (tickExecute basis w machine world).1 := by
  simp only [tickExecute]
  split
  · exact settled
  · rename_i pending
    split
    · exact fun complete => (pending complete).elim
    · split
      · exact fun complete => (pending complete).elim
      · exact fun _ => rfl

theorem execute_settled (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (machine : Machine count K) (world : World) (settled : Settled machine) :
    Settled (execute basis w fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact settled
  | succ fuel ih => exact ih _ (tick_settled basis w machine world settled)

theorem request_complete (basis : Module.Basis (Fin degree) (ZMod p) K) (w count fuel : ℕ)
    (transcript : Transcript) (roots : List NativeRootMessage.Digest) (fits : roots.length < 2 ^ 64) (world : World)
    (complete : (run (request basis w count fuel transcript roots fits) world).run.1.remaining = 0) :
    (run (request basis w count fuel transcript roots fits) world).run.1.draws.length = roots.length ∧
      (run (request basis w count fuel transcript roots fits) world).run.1.active = none := by
  have total := request_count basis w count fuel transcript roots fits world
  dsimp only at total
  rw [complete, zero_add] at total
  refine ⟨total, ?_⟩
  have settled := execute_settled basis w fuel (initial count transcript roots fits) world (fun _ => rfl)
  rw [← run_steps, ← request] at settled
  exact settled complete

theorem request_add (basis : Module.Basis (Fin degree) (ZMod p) K) (w count first extra : ℕ)
    (transcript : Transcript) (roots : List NativeRootMessage.Digest) (fits : roots.length < 2 ^ 64) (world : World) :
    (run (request basis w count (first + extra) transcript roots fits) world).run =
      let earlier := (run (request basis w count first transcript roots fits) world).run
      let later := (run (steps basis w extra earlier.1) world).run
      (later.1, earlier.2 ++ later.2) := by
  simp only [request, run_steps, execute_add]

/-- Concrete native challenge fields. Root generation and matching this
phase's count to native preflight remain caller/refinement obligations. -/
def goldilocks (count fuel : ℕ) (transcript : Transcript) (roots : List NativeRootMessage.Digest)
    (fits : roots.length < 2 ^ 64) : Program (Machine count NativeExtensionFields.Goldilocks3) :=
  request NativeExtensionFields.goldilocksBasis 7 count fuel transcript roots fits

def babyBear (count fuel : ℕ) (transcript : Transcript) (roots : List NativeRootMessage.Digest)
    (fits : roots.length < 2 ^ 64) : Program (Machine count NativeExtensionFields.BabyBear6) :=
  request NativeExtensionFields.babyBearBasis 31 count fuel transcript roots fits

/-- Analysis-level phase composition refuses an unfinished lookup batch.
Native proof dimensions are checked earlier in Rust; this gate does not
replace those checks or silently complete an unfinished reciprocal loop. -/
def afterBatch (basis : Module.Basis (Fin degree) (ZMod p) K) (w count fuel : ℕ)
    (batch : NativeLookupBatch.Machine p K) (roots : List NativeRootMessage.Digest) (fits : roots.length < 2 ^ 64) :
    Option (Program (Machine count K)) :=
  match batch.control with
  | .finished transcript =>
      if roots.length = batch.completed.length then some (request basis w count fuel transcript roots fits) else none
  | _ => none

theorem afterBatch_finished (basis : Module.Basis (Fin degree) (ZMod p) K) (w count fuel : ℕ)
    (batch : NativeLookupBatch.Machine p K) (roots : List NativeRootMessage.Digest) (fits : roots.length < 2 ^ 64)
    (transcript : Transcript) (finished : batch.control = .finished transcript)
    (dimensions : roots.length = batch.completed.length) :
    afterBatch basis w count fuel batch roots fits = some (request basis w count fuel transcript roots fits) := by
  simp only [afterBatch, finished, dimensions, ite_true]

end

end FormalProof4FHE.HasteBoots.NativeLookupEquality
