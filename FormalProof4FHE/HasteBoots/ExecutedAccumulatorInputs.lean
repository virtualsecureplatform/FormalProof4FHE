module
public import FormalProof4FHE.HasteBoots.DecodedAccumulatorConstraints
public import FormalProof4FHE.HasteBoots.OwnedAmbientAccumulator
public import FormalProof4FHE.HasteBoots.AmbientSourceDescriptor
public import FormalProof4FHE.HasteBoots.RecordedPaddedSourceFamily
public import FormalProof4FHE.HasteBoots.PackedPBSAccumulatorReferences
public import FormalProof4FHE.HasteBoots.PackedHadamardRows
public import FormalProof4FHE.HasteBoots.DecompositionBlindRotation
public import FormalProof4FHE.HasteBoots.CheckpointHistoryChain
@[expose] public section

/-! Associate recorded reconstruction inputs with the original duplicated
sources of an actual accumulator run, then enforce difference-row semantics. -/
namespace FormalProof4FHE.HasteBoots.ExecutedAccumulatorInputs
open OracleSpec OracleComp
noncomputable section
attribute [local irreducible] MonadAttach.support
variable {q cells lanes rows front suffix m queries height d : ℕ} [Fact q.Prime]
  {Input Digest Cfg Response Memory CommitMemory : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [SampleableType (Fin (2^lanes) → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) (2^lanes))]
  [SampleableType (Fin queries → Fin (2^height))]
  (heights : Cfg → ℕ)
  (s : AmbientAccumulator.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2^lanes) cells rows front suffix m queries height)
  (dummy : Digest)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
  (outcome : AmbientAccumulator.Prefix heights (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) ×
    AmbientAccumulator.RunResult heights (F := ZMod q) (Input := Input) (Digest := Digest) (Response := Response)
      (Memory := Memory) (b := 2^lanes) (c := cells) (r := rows) (front := front) (queries := queries) (height := height))
  (supported : outcome ∈ support (AmbientAccumulator.witness heights s dummy initial))

/-- Literal fresh owners retained by this executed accumulator. -/
def owners := AmbientDependentBatchOpening.snapshots heights s.tag outcome.1

/-- The original accumulator sources use those actual owners. -/
def sources (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ) :=
  OwnedAmbientAccumulator.originalSources heights s dummy capacity radius (owners heights s outcome)

include supported in
/-- Actual accepted arithmetic/opening gates enforce the original full source
constraints, or the existing accumulator original-risk event occurs. -/
theorem full_holds_or_risk (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (arithmetic : outcome.2.1.1.accepted = true) (opened : outcome.2.1.2.accepted = true) :
    AccumulatorEndpointSoundness.FullHolds (sources heights s dummy outcome capacity radius) ∨
      OwnedAmbientAccumulator.OriginalRisk heights s dummy capacity radius outcome := by
  classical
  by_cases holds : AccumulatorEndpointSoundness.FullHolds (sources heights s dummy outcome capacity radius)
  · exact Or.inl holds
  · exact Or.inr ⟨owners heights s outcome,fun factor => ⟨rfl,
      AmbientAccumulator.fresh_recorded heights s dummy initial outcome supported factor⟩,holds,arithmetic,opened⟩

/-- Public decoder metadata for each original accumulator source. -/
def parameters (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (geometry : ∀ factor, heights (s.tag factor) = height) (factor : Fin 7) :=
  AmbientSourceDescriptor.parameters (front := front) heights (s.tag factor) (geometry factor)
    s.domain capacity radius

/-- Physical coefficient addresses used to read the reconstruction polynomial. -/
def address (position : Fin (2^rows)) (half : Bool) (index : Fin (2^(cells+lanes))) :
    MatrixFold.Cube (front+suffix) × Fin (2^lanes) :=
  let coefficient := (PackedAccumulatorTrace.polynomial cells lanes).symm index
  (s.layout.symm ▸ AccumulatorPackedQueries.coordinate coefficient.1
    ((FlatMatrixFold.index rows).symm position) half,coefficient.2)

omit [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [SampleableType (Fin (2^lanes) → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) (2^lanes))]
  [SampleableType (Fin queries → Fin (2^height))] in
/-- These are exactly the original NTT coefficient-row addresses, with
round low and output half high; no row-local permutation is assumed. -/
theorem address_ntt (position : Fin (2^rows)) (half : Bool) :
    address s position half = PackedHadamardRows.address (Nat.pow_add 2 cells lanes).symm
      (show (rows+1)+cells = front+suffix by have := s.layout; omega)
      (PackedMonomialRotation.rowIndex position half) := by
  funext index
  apply Prod.ext
  · apply (FlatMatrixFold.index (front+suffix)).injective
    apply Fin.ext
    simp only [address,PackedHadamardRows.address,PackedNTTBinding.address,
      PaddedSourceAddress.index_transport,AccumulatorPackedQueries.coordinate_index,
      NTTSourceQuery.join_index,PackedMonomialRotation.rowIndex_val,Equiv.apply_symm_apply]
    rfl
  · rfl

include supported in
/-- A recorded reconstruction input and the actual duplicated source agree
outside the same final Bad. Only complete public metadata and root identity
are associated; decoded source values are not premises. -/
theorem input_table_eq_or_bad
    (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (geometry : ∀ factor, heights (s.tag factor) = height)
    (family : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest (Fin (2*d+2)) heights (2^lanes))
    (selected : Bool)
    (associated : parameters heights s capacity radius geometry (PackedPBSAccumulatorReferences.inputSlot selected) =
      family.parameters DecompositionLinear.input)
    (sameRoot : outcome.1.1.1 (PackedPBSAccumulatorReferences.inputSlot selected) = family.roots DecompositionLinear.input)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state)
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) state)
    (recorded : RecordedPaddedSourceFamily.Recorded family state) :
    DecodedAccumulatorConstraints.duplicate (sources heights s dummy outcome capacity radius) selected =
      QueryReindex.source s.layout.symm
        (RecordedPaddedSourceFamily.logical family s.encoding dummy (front+suffix) DecompositionLinear.input) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  have original := AmbientAccumulator.fresh_recorded heights s dummy initial outcome supported
    (PackedPBSAccumulatorReferences.inputSlot selected)
  have same := RecordedPaddedSourceFamily.associated_owner_agrees_or_bad family s.encoding dummy
    (front+suffix) DecompositionLinear.input
    (parameters heights s capacity radius geometry (PackedPBSAccumulatorReferences.inputSlot selected))
    associated state audited recorded
    (owners heights s outcome (PackedPBSAccumulatorReferences.inputSlot selected)) (retained _ _ original) sameRoot
  rcases same with equal | bad
  · left
    have normalized := AmbientSourceDescriptor.original (front := front) s.encoding dummy heights
      (s.tag (PackedPBSAccumulatorReferences.inputSlot selected))
      (geometry (PackedPBSAccumulatorReferences.inputSlot selected)) s.domain capacity radius rfl
      (owners heights s outcome (PackedPBSAccumulatorReferences.inputSlot selected))
    have actual : DecodedAccumulatorConstraints.duplicate (sources heights s dummy outcome capacity radius) selected =
        QueryReindex.source s.layout.symm
          (RecordedPaddedSource.logical (parameters heights s capacity radius geometry
            (PackedPBSAccumulatorReferences.inputSlot selected)) s.encoding dummy (front+suffix)
              (owners heights s outcome (PackedPBSAccumulatorReferences.inputSlot selected))) := by
      dsimp only [parameters]
      rw [← normalized]
      cases selected <;> rfl
    exact actual.trans (congrArg (QueryReindex.source s.layout.symm) equal)
  · exact Or.inr bad

include supported in
/-- Actual reconstruction input rows are the selected difference polynomial,
including both repeated output halves, or existing accumulator risk/final Bad. -/
theorem input_row_or_risks
    (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (geometry : ∀ factor, heights (s.tag factor) = height)
    (family : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest (Fin (2*d+2)) heights (2^lanes))
    (selected : Bool)
    (associated : parameters heights s capacity radius geometry (PackedPBSAccumulatorReferences.inputSlot selected) =
      family.parameters DecompositionLinear.input)
    (sameRoot : outcome.1.1.1 (PackedPBSAccumulatorReferences.inputSlot selected) = family.roots DecompositionLinear.input)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state)
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) state)
    (recorded : RecordedPaddedSourceFamily.Recorded family state)
    (arithmetic : outcome.2.1.1.accepted = true) (opened : outcome.2.1.2.accepted = true) :
    (∀ position outputHalf, DecompositionBlindRotation.project
      (RecordedPaddedSourceFamily.logical family s.encoding dummy (front+suffix))
      (address s position outputHalf) DecompositionLinear.input =
        DecodedAccumulatorRows.decode (sources heights s dummy outcome capacity radius).difference position selected) ∨
      OwnedAmbientAccumulator.OriginalRisk heights s dummy capacity radius outcome ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  rcases input_table_eq_or_bad heights s dummy initial outcome supported capacity radius geometry family selected
    associated sameRoot state retained audited recorded with equal | bad
  · rcases full_holds_or_risk heights s dummy initial outcome supported capacity radius arithmetic opened with holds | risk
    · left
      intro position outputHalf
      have same := DecodedAccumulatorConstraints.duplicate_rows_of_holds
        (sources heights s dummy outcome capacity radius) holds.1 position selected outputHalf
      rw [equal] at same
      exact same
    · exact Or.inr (Or.inl risk)
  · exact Or.inr (Or.inr bad)

include supported in
/-- The same executed-input conclusion at the literal original NTT row
addresses, for every stored round and physical output half. -/
theorem input_ntt_rows_or_risks
    (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (geometry : ∀ factor, heights (s.tag factor) = height)
    (family : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest (Fin (2*d+2)) heights (2^lanes))
    (selected : Bool)
    (associated : parameters heights s capacity radius geometry (PackedPBSAccumulatorReferences.inputSlot selected) =
      family.parameters DecompositionLinear.input)
    (sameRoot : outcome.1.1.1 (PackedPBSAccumulatorReferences.inputSlot selected) = family.roots DecompositionLinear.input)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state)
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) state)
    (recorded : RecordedPaddedSourceFamily.Recorded family state)
    (arithmetic : outcome.2.1.1.accepted = true) (opened : outcome.2.1.2.accepted = true) :
    (∀ position outputHalf, DecompositionBlindRotation.project
      (RecordedPaddedSourceFamily.logical family s.encoding dummy (front+suffix))
      (PackedHadamardRows.address (Nat.pow_add 2 cells lanes).symm
        (show (rows+1)+cells = front+suffix by have := s.layout; omega)
        (PackedMonomialRotation.rowIndex position outputHalf)) DecompositionLinear.input =
        DecodedAccumulatorRows.decode (sources heights s dummy outcome capacity radius).difference position selected) ∨
      OwnedAmbientAccumulator.OriginalRisk heights s dummy capacity radius outcome ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  have result := input_row_or_risks heights s dummy initial outcome supported capacity radius geometry
    family selected associated sameRoot state retained audited recorded arithmetic opened
  simpa only [address_ntt] using result

end
end FormalProof4FHE.HasteBoots.ExecutedAccumulatorInputs
