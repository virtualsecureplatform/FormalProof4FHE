module
public import FormalProof4FHE.HasteBoots.RectangularLookupOwnerConditional
public import FormalProof4FHE.HasteBoots.RectangularOwnedRequestSources
public import FormalProof4FHE.HasteBoots.RectangularRequestLookup
@[expose] public section

/-! Request-specific original tuple reuse from an arbitrary audited incoming
history, with one shared final collision alternative. -/
namespace FormalProof4FHE.HasteBoots.RectangularOwnedRequestConditional
open OracleSpec OracleComp BinaryTree Matrix
open scoped BigOperators
open InteractiveAuthenticatedOpening PaddedMixedWidthLookupOpeningFamily MixedWidthSharedLookupPCSAlgebra
open RectangularOwnedLookupSources (Owners Outcome)
open RectangularOwnedRequestSources (Config tuples OriginalFalse)
noncomputable section
variable {F K Message Memory Cfg Input Digest SourceMemory HelperMemory RetainedMemory Result : Type}
  [Field F] [Field K] [Algebra F K] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {d padding helperPadding c row count requests : ℕ} {widths sizes repetitions : Fin requests → ℕ} {mode : Mode}
  {heights : Cfg → ℕ} {tag : Root count (∑ i, repetitions i) → Cfg}
  {g : Geometry c row count (∑ i, repetitions i)} {symbolWidth : Root count (∑ i, repetitions i) → ℕ}

variable [SampleableType Digest]

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
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (audited : CheckpointExecution.Audited enc dummy (fun cfg => Skeleton.perfect (heights cfg)) initial)
    (outcome : Outcome count (∑ i, repetitions i) Cfg Input Digest SourceMemory RetainedMemory Result heights)
    (supported : outcome ∈ support (StagedCommitmentPrefix.witness enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (RectangularStagedOpening.sourceRequests tag (List.finRange count))
      (RectangularStagedOpening.helperRequests tag (List.finRange (∑ i, repetitions i))) sourceCommit helperCommit next
      initial))
    (bad : OriginalFalse enc dummy config domain capacity radius outcome) :
    (∃ index position, ∀ j,
      RectangularRequestLookup.tuples enc dummy config domain capacity radius outcome.1 index position ≠ config.tables index j) ∨
      CheckpointCollision.Bad (fun cfg => Skeleton.perfect (heights cfg)) outcome.2.2.2 := by
  obtain ⟨owner,recorded,index,position,outside⟩ := bad
  rcases RectangularLookupOwnerConditional.columns_eq_or_bad enc dummy domain capacity radius
    sourceCommit helperCommit next initial audited outcome supported owner recorded with same | failed
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
end FormalProof4FHE.HasteBoots.RectangularOwnedRequestConditional
