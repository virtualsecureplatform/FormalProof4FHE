module
public import FormalProof4FHE.HasteBoots.OwnedRadixCoverage
@[expose] public section
open FormalProof4FHE.HasteBoots
open OracleSpec OracleComp BinaryTree
open scoped Matrix
namespace HasteBootsRadixLookupSourcesSmoke
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩

-- Input four, digits [4,0,0], and zero borrows: both field and integer
-- reconstruction pass, but the first digit is not a radix-four digit.
def registry : Fin 8 → MatrixFold.Cube 0 → Fin 1 → ZMod 17 :=
  fun factor _ _ => if factor.val ≤ 1 then 4 else 0
theorem linear : DecompositionLinear.Relation (d := 3) (n := 0) (b := 1) (4 : ZMod 17) registry := by
  unfold DecompositionLinear.Relation
  decide +kernel
example : RadixCanonicity.CanonicalAt (d := 3) (n := 0) (b := 1) 17 4 registry () 0 := by
  unfold RadixCanonicity.CanonicalAt
  decide +kernel
example : (registry (DecompositionLinear.digit (0 : Fin 3)) () 0).val ≠
    (registry (DecompositionLinear.input (d := 3)) () 0).val / 4^(0 : Fin 3).val % 4 := by decide +kernel
example : ¬RadixCanonicity.LookupAt (d := 3) (n := 0) (b := 1) 17 4 registry () 0 := by
  unfold RadixCanonicity.LookupAt
  decide +kernel

def address (_ : Fin 1) : MatrixFold.Cube 0 × Fin 1 := ((),0)
theorem outside : ∃ position, ∀ index, RadixLookupSources.sources registry address (0 : Fin 3) position ≠
    RadixLookupSources.publicTable 17 4 (RadixCanonicity.modulusDigit 17 4 0) index := by
  refine ⟨0,?_⟩
  decide +kernel

example : ∃ limb, ∀ index, RadixLookupSources.tuple (d := 3) (n := 0) (b := 1) registry limb () 0 ≠
    RadixLookupSources.publicTable 17 4 (RadixCanonicity.modulusDigit 17 4 limb.val) index := by
  rcases RadixLookupSources.digit_failure_coverage (d := 3) (n := 0) (b := 1) (by decide +kernel : 1 < 4)
    (by decide +kernel : 4 < 17) (by decide +kernel : 17-1 < 4^3) registry () 0 (0 : Fin 3)
    (by decide +kernel) with failed | comparison
  · exact (failed linear).elim
  · exact comparison

-- Public table order and the incoming/outgoing borrow roles are distinct.
example : RadixLookupSources.publicTable 17 4 1 (1 : Fin 8) = ![0,1,0] := by decide +kernel
example : ∀ index, (![0,0,1] : Fin 3 → ZMod 17) ≠ RadixLookupSources.publicTable 17 4 1 index := by
  decide +kernel

-- Native comparisons omit the input and keep all remaining columns.
example : RadixLookupSources.comparisonSlots (0 : Fin 3) = ![0,3,4] ∧
    RadixLookupSources.comparisonSlots (2 : Fin 3) = ![2,5,6] := by decide +kernel
example : RadixLookupSources.comparisonRegistry (d := 3) (id : Fin 8 → Fin 8) (0 : Fin 7) = 1 ∧
    RadixLookupSources.comparisonRegistry (d := 3) (id : Fin 8 → Fin 8) (6 : Fin 7) = 7 := by decide +kernel

-- A mathematical degree-two extension checks the full hash/reciprocal term.
-- This is a sampler-model regression, not a native extension implementation.
abbrev K := PCSAnalysisField.Alphabet 17 2
example : TupleLookupPair.error 289 3 1 8 = (8 : ENNReal)*(2/289)+8/280 := by
  norm_num [TupleLookupPair.error]
example {Cfg Input Digest Later Payload : Type} [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (multiplicities : Fin 8 → K)
    (next : Option (List (K × K)) → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Later)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (SharedContinuation.program (PrivateSampling.embed Cfg Input Digest (TupleLookupPair.repeats (K := K)
        (RadixLookupSources.publicTable 17 4 (RadixCanonicity.modulusDigit 17 4 0)) 2).run) next)).run state}[
      outcome.1.1.elim False (TupleLookupPair.AllPass (RadixLookupSources.sources registry address (0 : Fin 3))
        (RadixLookupSources.publicTable 17 4 (RadixCanonicity.modulusDigit 17 4 0)) multiplicities)] ≤
      ((8 : ENNReal)*(2/289)+8/280)^2 := by
  have bound := RadixLookupSources.comparison_bound registry address (0 : Fin 3) multiplicities outside
    (by decide +kernel : 1 < 17) 2 enc dummy shape next state
  simpa [PCSAnalysisField.cardinality,TupleLookupPair.error] using bound

end
end HasteBootsRadixLookupSourcesSmoke
