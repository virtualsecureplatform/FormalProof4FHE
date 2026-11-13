module
public import FormalProof4FHE.HasteBoots.RectangularOwnedLookupSources
public import FormalProof4FHE.HasteBoots.RectangularRequestLookup
@[expose] public section

/-! Request-specific tuples from matching original owner checkpoints, including
owner families selected after execution. Slot order and aliases are preserved;
coherence is over complete columns with fixed source parameters. -/
namespace FormalProof4FHE.HasteBoots.RectangularOwnedRequestSources
open OracleSpec OracleComp BinaryTree Matrix
open scoped BigOperators
open InteractiveAuthenticatedOpening PaddedMixedWidthLookupOpeningFamily MixedWidthSharedLookupPCSAlgebra
open RectangularOwnedLookupSources (Owners Outcome)
noncomputable section
variable {F K Message Memory Cfg Input Digest SourceMemory HelperMemory RetainedMemory Result : Type}
  [Field F] [Field K] [Algebra F K] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {d padding helperPadding c row count requests : ℕ} {widths sizes repetitions : Fin requests → ℕ} {mode : Mode}
  {heights : Cfg → ℕ} {tag : Root count (∑ i, repetitions i) → Cfg}
  {g : Geometry c row count (∑ i, repetitions i)} {symbolWidth : Root count (∑ i, repetitions i) → ℕ}

abbrev Config := RectangularRequestLookup.Parameters F K Message Memory Cfg Input Digest SourceMemory HelperMemory
  d padding c row count requests widths sizes repetitions mode

def tuples (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (config : Config (F := F) (K := K) (Message := Message) (Memory := Memory) (Cfg := Cfg) (Input := Input) (Digest := Digest)
      (SourceMemory := SourceMemory) (HelperMemory := HelperMemory) (d := d) (padding := padding) (c := c) (row := row)
      (count := count) (requests := requests) (widths := widths) (sizes := sizes) (repetitions := repetitions) (mode := mode))
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * symbolWidth root)
    (radius : Root count (∑ i, repetitions i) → ℕ) (owner : Owners Input Digest heights tag) :
    (index : Fin requests) → Fin (config.active index) → Fin (widths index) → F :=
  fun index => LookupPairArithmetic.activeTuples (config.logicalShape index)
    (fun column => LookupSourceFlattening.flatten config.shape
      (RectangularOwnedLookupSources.columns (d := d) (padding := padding) enc dummy domain capacity radius owner (config.slots index column)))

/-- Owner identity includes the original context, matching root, and membership
in the actual final history. It is not a source-truth or safety certificate. -/
def OriginalFalse (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (config : Config (F := F) (K := K) (Message := Message) (Memory := Memory) (Cfg := Cfg) (Input := Input) (Digest := Digest)
      (SourceMemory := SourceMemory) (HelperMemory := HelperMemory) (d := d) (padding := padding) (c := c) (row := row)
      (count := count) (requests := requests) (widths := widths) (sizes := sizes) (repetitions := repetitions) (mode := mode))
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * symbolWidth root)
    (radius : Root count (∑ i, repetitions i) → ℕ)
    (outcome : Outcome count (∑ i, repetitions i) Cfg Input Digest SourceMemory RetainedMemory Result heights) : Prop :=
  ∃ owner : Owners Input Digest heights tag,
    (∀ source, (owner source).root = outcome.1.1.1 source ∧
      ⟨tag (.inl source),owner source⟩ ∈ outcome.2.2.2.checkpoints.checkpoints) ∧
    ∃ index position, ∀ j, tuples enc dummy config domain capacity radius owner index position ≠ config.tables index j

variable [SampleableType Digest]

theorem fresh_false_implies_original
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (config : Config (F := F) (K := K) (Message := Message) (Memory := Memory) (Cfg := Cfg) (Input := Input) (Digest := Digest)
      (SourceMemory := SourceMemory) (HelperMemory := HelperMemory) (d := d) (padding := padding) (c := c) (row := row)
      (count := count) (requests := requests) (widths := widths) (sizes := sizes) (repetitions := repetitions) (mode := mode))
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * symbolWidth root)
    (radius : Root count (∑ i, repetitions i) → ℕ)
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest)
      (RectangularStagedSharedLookup.SourceEmission count Digest SourceMemory))
    (helperCommit : RectangularStagedSharedLookup.SourceEmission count Digest SourceMemory →
      OracleComp (SharedSequence.Shared Cfg Input Digest)
        (RectangularStagedSharedLookup.HelperEmission (∑ i, repetitions i) Digest RetainedMemory))
    (next : RectangularStagedSharedLookup.SourceEmission count Digest SourceMemory →
      RectangularStagedSharedLookup.HelperEmission (∑ i, repetitions i) Digest RetainedMemory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (outcome : Outcome count (∑ i, repetitions i) Cfg Input Digest SourceMemory RetainedMemory Result heights)
    (supported : outcome ∈ support (StagedCommitmentPrefix.witness enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (RectangularStagedOpening.sourceRequests tag (List.finRange count))
      (RectangularStagedOpening.helperRequests tag (List.finRange (∑ i, repetitions i))) sourceCommit helperCommit next
      (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg)))))
    (bad : ∃ index position, ∀ j,
      RectangularRequestLookup.tuples enc dummy config domain capacity radius outcome.1 index position ≠ config.tables index j) :
    OriginalFalse enc dummy config domain capacity radius outcome := by
  refine ⟨(fun source => RectangularStagedOpening.snapshots heights tag outcome.1 outcome.2.1 (.inl source)),?_,?_⟩
  · intro source
    exact ⟨rfl,RectangularOwnedLookupSources.fresh_recorded enc dummy sourceCommit helperCommit next outcome supported (.inl source)⟩
  · exact bad

theorem original_false_reduction
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (config : Config (F := F) (K := K) (Message := Message) (Memory := Memory) (Cfg := Cfg) (Input := Input) (Digest := Digest)
      (SourceMemory := SourceMemory) (HelperMemory := HelperMemory) (d := d) (padding := padding) (c := c) (row := row)
      (count := count) (requests := requests) (widths := widths) (sizes := sizes) (repetitions := repetitions) (mode := mode))
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * symbolWidth root)
    (radius : Root count (∑ i, repetitions i) → ℕ)
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest)
      (RectangularStagedSharedLookup.SourceEmission count Digest SourceMemory))
    (helperCommit : RectangularStagedSharedLookup.SourceEmission count Digest SourceMemory →
      OracleComp (SharedSequence.Shared Cfg Input Digest)
        (RectangularStagedSharedLookup.HelperEmission (∑ i, repetitions i) Digest RetainedMemory))
    (next : RectangularStagedSharedLookup.SourceEmission count Digest SourceMemory →
      RectangularStagedSharedLookup.HelperEmission (∑ i, repetitions i) Digest RetainedMemory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (outcome : Outcome count (∑ i, repetitions i) Cfg Input Digest SourceMemory RetainedMemory Result heights)
    (supported : outcome ∈ support (StagedCommitmentPrefix.witness enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (RectangularStagedOpening.sourceRequests tag (List.finRange count))
      (RectangularStagedOpening.helperRequests tag (List.finRange (∑ i, repetitions i))) sourceCommit helperCommit next
      (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg)))))
    (bad : OriginalFalse enc dummy config domain capacity radius outcome) :
    (∃ index position, ∀ j,
      RectangularRequestLookup.tuples enc dummy config domain capacity radius outcome.1 index position ≠ config.tables index j) ∨
      CheckpointCollision.Bad (fun cfg => Skeleton.perfect (heights cfg)) outcome.2.2.2 := by
  obtain ⟨owner,recorded,index,position,outside⟩ := bad
  rcases RectangularOwnedLookupSources.columns_eq_or_bad enc dummy domain capacity radius
    sourceCommit helperCommit next outcome supported owner recorded with same | failed
  · left
    have tuplesEq : tuples enc dummy config domain capacity radius owner =
        RectangularRequestLookup.tuples enc dummy config domain capacity radius outcome.1 :=
      congrArg (fun values : Fin count → MatrixFold.Cube row → Fin (d + padding) → F =>
        fun index => LookupPairArithmetic.activeTuples (config.logicalShape index)
          (fun column => LookupSourceFlattening.flatten config.shape (values (config.slots index column)))) same
    refine ⟨index,position,?_⟩
    intro j equal
    exact outside j ((congrFun (congrFun tuplesEq index) position).trans equal)
  · exact Or.inr failed

end
end FormalProof4FHE.HasteBoots.RectangularOwnedRequestSources
