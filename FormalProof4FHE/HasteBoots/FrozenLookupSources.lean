module

public import FormalProof4FHE.HasteBoots.LookupPairVectorMiddle

@[expose] public section

/-!
# Lookup tuples fixed at the original source checkpoint

The definition takes only the saved source state. It has no helper emission,
helper state, pair vector, algebra coins or query-selection argument. The staged
lookup pass predicate reduces to these exact tuples, without moving a snapshot.
-/

open OracleSpec OracleComp BinaryTree Matrix
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.LookupOpeningFamily

namespace FormalProof4FHE.HasteBoots.FrozenLookupSources

noncomputable section

variable {F K Cfg Input Digest SourceMemory HelperMemory : Type}
  [Field F] [Field K] [Algebra F K] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {d padding c row count repetitions active inactive size : ℕ}
  {heights : Cfg → ℕ} {tag : Root count repetitions → Cfg} {g : Geometry c row count repetitions}

def tuples (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (shape : d + padding = 2 ^ c) (logicalShape : active + inactive = 2 ^ (c + row))
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * (d + padding)) (radius : Root count repetitions → ℕ)
    (first : StagedRepeatedLookup.SourceEmission count Digest SourceMemory ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg))) :
    Fin active → Fin count → F :=
  LookupPairArithmetic.activeTuples logicalShape (fun source => LookupSourceFlattening.flatten shape
    (PackedQueryArity.table (g.sourceArity source).symm
      (SubclaimSourceLayout.decodedSource (domain (.inl source)) (capacity (.inl source)) (radius (.inl source))
        (word enc dummy heights (tag (.inl source)) ⟨first.1.1 source, first.2.hash.log⟩))))

omit [DecidableEq Input] in
/-- Definitional equality establishes that no helper-time decoding or later
query-dependent source replacement enters the pair probability theorem. -/
theorem allPass_iff (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c) (logicalShape : active + inactive = 2 ^ (c + row))
    (table : Fin size → Fin count → F)
    (multiplicities : StagedRepeatedLookup.SourceEmission count Digest SourceMemory → Fin size → F)
    (pairs : StagedRepeatedLookup.HelperEmission repetitions Digest HelperMemory → Fin repetitions → StagedRepeatedLookup.Pair K)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * (d + padding)) (radius : Root count repetitions → ℕ)
    (first : StagedRepeatedLookup.SourceEmission count Digest SourceMemory ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (second : StagedRepeatedLookup.HelperEmission repetitions Digest HelperMemory ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg))) :
    StagedRepeatedLookup.AllPass enc dummy basis shape logicalShape table multiplicities pairs domain capacity radius first second ↔
      LookupPairVector.AllPass (tuples enc dummy shape logicalShape domain capacity radius first) table
        (fun i => algebraMap F K (multiplicities first.1 i)) (pairs second.1) := by
  rfl

end

end FormalProof4FHE.HasteBoots.FrozenLookupSources
