module
public import FormalProof4FHE.HasteBoots.PaddedMixedWidthOwnedRequestSources
public import FormalProof4FHE.HasteBoots.PaddedLookupSourceInterpretation
public import FormalProof4FHE.HasteBoots.RecordedPaddedSourceFamily
@[expose] public section

/-! Full active comparison requests constrain every entry of their original
packed columns. The same constraints transfer to a recorded source family
using public decoder associations and a single global collision exclusion. -/
namespace FormalProof4FHE.HasteBoots.DecodedPaddedLookup
open OracleSpec OracleComp BinaryTree Matrix
open scoped BigOperators
open InteractiveAuthenticatedOpening PaddedMixedWidthLookupOpeningFamily MixedWidthSharedLookupPCSAlgebra
open PaddedMixedWidthOwnedLookupSources (Owners Outcome)
noncomputable section
variable {F K Message Memory Cfg Input Digest SourceMemory HelperMemory RetainedMemory Result : Type}
  [Field F] [Field K] [Algebra F K] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {d padding helperPadding c row count requests : ℕ} {widths sizes repetitions : Fin requests → ℕ} {mode : Mode}
  {heights : Cfg → ℕ} {tag : Root count (∑ i, repetitions i) → Cfg}
  {g : Geometry c row count (∑ i, repetitions i)}

abbrev Config := PaddedMixedWidthRequestSharedLookup.Parameters F K Message Memory Cfg Input Digest SourceMemory HelperMemory
  d padding c row count requests widths sizes repetitions mode


variable (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (config : Config (F := F) (K := K) (Message := Message) (Memory := Memory) (Cfg := Cfg) (Input := Input) (Digest := Digest)
      (SourceMemory := SourceMemory) (HelperMemory := HelperMemory) (d := d) (padding := padding) (c := c) (row := row)
      (count := count) (requests := requests) (widths := widths) (sizes := sizes) (repetitions := repetitions) (mode := mode))
    (domain : ∀ root, Fin (2^heights (tag root)) ↪ F)
    (capacity : ∀ root, 2^g.suffix root ≤ g.m root * packedWidth (d+padding) (d+helperPadding) root)
    (radius : Root count (∑ i, repetitions i) → ℕ)

omit [DecidableEq Input] in
/-- Excluding the actual original-owner failure gives membership at every
queried active scalar position, including for owners chosen after execution. -/
theorem membership_of_not_false
    (outcome : Outcome count (∑ i, repetitions i) Cfg Input Digest SourceMemory RetainedMemory Result heights)
    (owner : Owners Input Digest heights tag)
    (recorded : ∀ source, (owner source).root = outcome.1.1.1 source ∧
      ⟨tag (.inl source),owner source⟩ ∈ outcome.2.2.2.checkpoints.checkpoints)
    (clear : ¬PaddedMixedWidthOwnedRequestSources.OriginalFalse enc dummy config domain capacity radius outcome)
    (index : Fin requests) (position : Fin (config.active index)) :
    ∃ j, PaddedMixedWidthOwnedRequestSources.tuples enc dummy config domain capacity radius owner index position = config.tables index j := by
  classical
  by_contra outside
  push Not at outside
  exact clear ⟨owner,recorded,index,position,outside⟩

omit [DecidableEq Input] in
/-- Full activity covers every original packed row/lane. No constraint on
inactive scalar padding is inferred for a partially active request. -/
theorem columns_membership_of_not_false
    (outcome : Outcome count (∑ i, repetitions i) Cfg Input Digest SourceMemory RetainedMemory Result heights)
    (owner : Owners Input Digest heights tag)
    (recorded : ∀ source, (owner source).root = outcome.1.1.1 source ∧
      ⟨tag (.inl source),owner source⟩ ∈ outcome.2.2.2.checkpoints.checkpoints)
    (clear : ¬PaddedMixedWidthOwnedRequestSources.OriginalFalse enc dummy config domain capacity radius outcome)
    (index : Fin requests) (full : config.active index = 2^(c+row))
    (cell : MatrixFold.Cube row) (lane : Fin (d+padding)) :
    ∃ j, (fun column => PaddedMixedWidthOwnedLookupSources.columns enc dummy domain capacity radius owner
      (config.slots index column) cell lane) = config.tables index j := by
  let scalar := LookupSourceFlattening.split.symm (ExtensionQuery.nativeLanes config.shape lane,cell)
  let position : Fin (config.active index) := ⟨(FlatMatrixFold.index (c+row) scalar).val,by
    rw [full]
    exact (FlatMatrixFold.index (c+row) scalar).isLt⟩
  have addressed : LookupReciprocalEnforcement.cells (config.logicalShape index)
      (position.castAdd (config.inactive index)) = scalar := by
    apply (FlatMatrixFold.index (c+row)).injective
    apply Fin.ext
    exact LookupReciprocalEnforcement.cells_address (config.logicalShape index) _
  obtain ⟨j,equal⟩ := membership_of_not_false enc dummy config domain capacity radius outcome owner recorded clear index position
  refine ⟨j,?_⟩
  change (fun column => LookupSourceFlattening.flatten config.shape
    (PaddedMixedWidthOwnedLookupSources.columns enc dummy domain capacity radius owner (config.slots index column))
      (LookupReciprocalEnforcement.cells (config.logicalShape index) (position.castAdd (config.inactive index)))) = _ at equal
  rw [addressed] at equal
  simpa only [scalar,LookupSourceFlattening.flatten_recover] using equal

variable {Index : Type}
/-- A complete comparison column is the same canonical logical view as its
associated original root in the common audited family. -/
theorem columns_family_eq_or_bad
    (world : RecordedPaddedSourceFamily.Family F Cfg Input Digest Index heights (d+padding))
    (slots : Fin count → Index)
    (associated : ∀ source, PaddedLookupSourceInterpretation.parameters domain capacity radius source = world.parameters (slots source))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (worldRecorded : RecordedPaddedSourceFamily.Recorded world state)
    (owner : Owners Input Digest heights tag)
    (retained : ∀ source, ⟨tag (.inl source),owner source⟩ ∈ state.checkpoints.checkpoints)
    (roots : ∀ source, (owner source).root = world.roots (slots source)) :
    PaddedMixedWidthOwnedLookupSources.columns enc dummy domain capacity radius owner =
      (fun source => RecordedPaddedSourceFamily.logical world enc dummy row (slots source)) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  classical
  by_cases bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state
  · exact Or.inr bad
  left
  funext source
  rw [PaddedLookupSourceInterpretation.columns]
  exact (RecordedPaddedSourceFamily.associated_owner_agrees_or_bad world enc dummy row (slots source)
    (PaddedLookupSourceInterpretation.parameters domain capacity radius source) (associated source)
    state audited worldRecorded (owner source) (retained source) (roots source)).resolve_right bad

/-- The executed full request enforces its public table on the same family
used by reconstruction, with no supplied source-value interpretation. -/
theorem family_membership_of_not_false
    (outcome : Outcome count (∑ i, repetitions i) Cfg Input Digest SourceMemory RetainedMemory Result heights)
    (owner : Owners Input Digest heights tag)
    (recorded : ∀ source, (owner source).root = outcome.1.1.1 source ∧
      ⟨tag (.inl source),owner source⟩ ∈ outcome.2.2.2.checkpoints.checkpoints)
    (clear : ¬PaddedMixedWidthOwnedRequestSources.OriginalFalse enc dummy config domain capacity radius outcome)
    (world : RecordedPaddedSourceFamily.Family F Cfg Input Digest Index heights (d+padding))
    (slots : Fin count → Index)
    (associated : ∀ source, PaddedLookupSourceInterpretation.parameters domain capacity radius source = world.parameters (slots source))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (worldRecorded : RecordedPaddedSourceFamily.Recorded world state)
    (retained : ∀ source, ⟨tag (.inl source),owner source⟩ ∈ state.checkpoints.checkpoints)
    (roots : ∀ source, (owner source).root = world.roots (slots source))
    (noBad : ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state)
    (index : Fin requests) (full : config.active index = 2^(c+row))
    (cell : MatrixFold.Cube row) (lane : Fin (d+padding)) :
    ∃ j, (fun column => RecordedPaddedSourceFamily.logical world enc dummy row
      (slots (config.slots index column)) cell lane) = config.tables index j := by
  have same := (columns_family_eq_or_bad enc dummy domain capacity radius world slots associated
    state audited worldRecorded owner retained roots).resolve_right noBad
  have member := columns_membership_of_not_false enc dummy config domain capacity radius outcome owner recorded clear index full cell lane
  rw [same] at member
  exact member

end
end FormalProof4FHE.HasteBoots.DecodedPaddedLookup
