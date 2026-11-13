module
public import FormalProof4FHE.HasteBoots.RectangularStagedOpening
public import FormalProof4FHE.HasteBoots.StagedVariableWidthBatchOpening
public import FormalProof4FHE.HasteBoots.RectangularBatchSquareCompatibility
@[expose] public section

/-! Square specialization preserves the complete staged continuation, including
helper-first checking, short-circuiting, provider work and worker scheduling. -/
open OracleSpec OracleComp
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
namespace FormalProof4FHE.HasteBoots.RectangularStagedSquareCompatibility
noncomputable section
variable {F Source Helper Input Digest Cfg Response Memory SourceMemory HelperMemory QueryData : Type}
  [Field F] [DecidableEq F] [DecidableEq Digest]
  {width : (Source ⊕ Helper) → ℕ} {heights : Cfg → ℕ} {tag : (Source ⊕ Helper) → Cfg}
  {layout : (Source ⊕ Helper) → VariableWidthBatchOpening.Layout}
  [∀ root, SampleableType (TestMatrix F (2^(layout root).front) (width root))]
  [∀ root, SampleableType (Fin (layout root).queries → Fin (2^heights (tag root)))]

theorem continuation_eq (enc : MerkleOracle.Encoding Input Digest (List F))
    (domain : ∀ root, Fin (2^heights (tag root)) ↪ F)
    (build : (((Source ⊕ Helper) → Digest) × StagedVariableWidthBatchOpening.CommitMemory Source Helper Digest SourceMemory HelperMemory) →
      QueryData → (root : Source ⊕ Helper) → VariableWidthBatchOpening.Protocol F Input Digest Cfg Response Memory width heights tag layout root)
    (selectQuery : (((Source ⊕ Helper) → Digest) × StagedVariableWidthBatchOpening.CommitMemory Source Helper Digest SourceMemory HelperMemory) →
      OracleComp (SharedSequence.Shared Cfg Input Digest) QueryData)
    (enabled : (((Source ⊕ Helper) → Digest) × StagedVariableWidthBatchOpening.CommitMemory Source Helper Digest SourceMemory HelperMemory) → QueryData → Bool)
    (start : (((Source ⊕ Helper) → Digest) × StagedVariableWidthBatchOpening.CommitMemory Source Helper Digest SourceMemory HelperMemory) → QueryData → Memory)
    (sources : List Source) (helpers : List Helper)
    (first : StagedVariableWidthBatchOpening.SourceEmission Source Digest SourceMemory)
    (second : StagedVariableWidthBatchOpening.HelperEmission Helper Digest HelperMemory) :
    RectangularStagedOpening.continuation enc domain
      (fun emission query root => RectangularBatchSquareCompatibility.ofSquare (build emission query root))
      selectQuery enabled start sources helpers first second =
    StagedVariableWidthBatchOpening.continuation enc domain build selectQuery enabled start sources helpers first second := rfl

end
end FormalProof4FHE.HasteBoots.RectangularStagedSquareCompatibility
