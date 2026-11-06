module
public import FormalProof4FHE.HasteBoots.CausalSeedExposure
public import FormalProof4FHE.HasteBoots.NativeFieldMatrixLaw
@[expose] public section

/-! First positive reads of complete SHAKE inputs, at arbitrary offsets.
Starts, empty reads and hashes do not expose SHAKE bytes. Any earlier partial
read of the same input prevents eligibility. This supplies fresh-tail facts
from the actual mixed history; native phase/parent lineage remains separate. -/
namespace FormalProof4FHE.HasteBoots.CausalStreamExposure
open InputIndexedOracle (Input World law)
open NativeTranscript (Observation)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
open scoped Classical
noncomputable section

def touches (input : Input) : Observation → Bool
  | .output other _ values => decide (other = input ∧ 0 < values.length)
  | _ => false

def seen (log : List Observation) (input : Input) : Bool := log.any (touches input)

theorem unseen_coordinates (log : List Observation) (input : Input) (unseen : seen log input = false) :
    ∀ position, (.inl (input,position) : InputIndexedOracle.Coordinate) ∉ ObservationReplay.footprint log := by
  intro position member
  obtain ⟨entry,inLog,coordinate⟩ := Finset.mem_biUnion.mp member
  cases entry with
  | start other => simp [ObservationReplay.coordinates] at coordinate
  | hash other digest => simp [ObservationReplay.coordinates] at coordinate
  | output other offset values =>
    have info := (NativeShakeProjection.output_coordinate other offset values (input,position)).mp coordinate
    have yes : seen log input = true := by
      apply List.any_eq_true.mpr
      refine ⟨.output other offset values,List.mem_toFinset.mp inLog,?_⟩
      simp only [touches,decide_eq_true_eq]
      exact ⟨info.1.symm,by omega⟩
    rw [unseen] at yes
    contradiction

def firstRead {S A : Type} (step : S → OracleMachine.Command S A) (history : (S ⊕ A) × List Observation) : Option Input :=
  match CausalSeedExposure.request step history.1 with
  | some (.read input _ count) => if 0 < count ∧ seen history.2 input = false then some input else none
  | _ => none

/-- No coordinate of the input has been exposed, even if the first read is
far beyond the canonical collector's initial byte cursor. -/
theorem firstRead_fresh {S A : Type} (step : S → OracleMachine.Command S A)
    (history : (S ⊕ A) × List Observation) (input : Input) (selected : firstRead step history = some input)
    (world : World) (offset : ℕ) : FreshShakeTail.Fresh (NativeShakeKernel.observed history.2 world) input offset := by
  unfold firstRead at selected
  split at selected <;> simp at selected
  obtain ⟨eligible,rfl⟩ := selected
  apply FreshShakeTail.observed_fresh
  intro position beyond
  exact unseen_coordinates _ _ eligible.2 position

/-- At the actual next first positive read, field-matrix uniformity is
derived from the complete history instead of a caller-provided cache claim. -/
theorem conditional_uniform_at_first_read {Cfg Payload S A : Type}
    (step : S → OracleMachine.Command S A)
    {past : World → NativeTranscript.Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) (world : World)
    (enc : MerkleOracle.Encoding Input NativeRootMessage.Digest Payload) (dummy : NativeRootMessage.Digest)
    (shape : Cfg → BinaryTree.Skeleton) (state : CheckpointExecution.State (Input := Input) (Digest := NativeRootMessage.Digest) shape)
    (hashStart : state.hash = JointHashCache.project (past world).run.2)
    (p : ℕ) (valid : 1 < p) [NeZero p] (fuel width rows : ℕ) (phase : NativeTranscript.FieldPhase)
    (selected : firstRead step (past world).run = some phase.pending.input)
    (event : (Fin width → Fin rows → ZMod p) → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | (NativeFieldMatrixLaw.values p fuel width rows phase other).elim False event} =
      BudgetedUniformSequence.completion (CanonicalCoefficientVector.scalar p 1) fuel (rows*width) *
        Pr{let matrix ← $ᵗ (Fin width → Fin rows → ZMod p)}[event matrix] :=
  NativeFieldMatrixLaw.conditional_uniform replay world enc dummy shape state hashStart p valid fuel width rows phase
    (firstRead_fresh step (past world).run phase.pending.input selected world phase.consumed.length) event

/-- The same first-read eligibility bounds any eventual completed matrix
event over all analysis prefixes, with no attempt cap or success floor. -/
theorem eventual_le_uniform_at_first_read {Cfg Payload S A : Type}
    (step : S → OracleMachine.Command S A)
    {past : World → NativeTranscript.Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) (world : World)
    (enc : MerkleOracle.Encoding Input NativeRootMessage.Digest Payload) (dummy : NativeRootMessage.Digest)
    (shape : Cfg → BinaryTree.Skeleton) (state : CheckpointExecution.State (Input := Input) (Digest := NativeRootMessage.Digest) shape)
    (hashStart : state.hash = JointHashCache.project (past world).run.2)
    (p : ℕ) (valid : 1 < p) [NeZero p] (width rows : ℕ) (phase : NativeTranscript.FieldPhase)
    (selected : firstRead step (past world).run = some phase.pending.input)
    (event : (Fin width → Fin rows → ZMod p) → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | ∃ fuel, (NativeFieldMatrixLaw.values p fuel width rows phase other).elim False event} ≤
        Pr{let matrix ← $ᵗ (Fin width → Fin rows → ZMod p)}[event matrix] :=
  NativeFieldMatrixLaw.eventual_le_uniform replay world enc dummy shape state hashStart p valid width rows phase
    (firstRead_fresh step (past world).run phase.pending.input selected world phase.consumed.length) event
end
end FormalProof4FHE.HasteBoots.CausalStreamExposure
