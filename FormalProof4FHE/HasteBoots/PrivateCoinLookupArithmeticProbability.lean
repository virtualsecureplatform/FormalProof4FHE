module
public import FormalProof4FHE.HasteBoots.PrivateCoinPairedScalarProbability
public import FormalProof4FHE.HasteBoots.PrivateCoinEqualityProbability
@[expose] public section

/-! Paired scalar events and attained equality events share one excluded
global reference ledger. All three work charges are retained explicitly. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinLookupArithmeticProbability
open MeasureTheory
open InputIndexedOracle (Input World law)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction)
open NativeRootMessage (Digest)
noncomputable section

def scalarRate : ENNReal := PrivateCoinPairedScalarProbability.scalarRate + EqualityPositionKernel.rate

def Event (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (dummy : Digest) (fuel : ℕ) (execution : Tape × World) : Prop :=
  PrivateCoinPairedScalarProbability.Event code publicData privateData dummy fuel execution ∨
    PrivateCoinEqualityProbability.Event code publicData privateData dummy fuel execution

abbrev Bad := PrivateCoinPairedScalarProbability.Bad

theorem safe_bound (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) :
    (coins.prod law) {execution | (∃ fuel, Event code publicData privateData dummy fuel execution) ∧
      ¬∃ fuel, Bad code publicData privateData dummy fuel execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData * scalarRate := by
  have included : {execution | (∃ fuel, Event code publicData privateData dummy fuel execution) ∧
      ¬∃ fuel, Bad code publicData privateData dummy fuel execution} ⊆
      {execution | (∃ fuel, PrivateCoinPairedScalarProbability.Event code publicData privateData dummy fuel execution) ∧
        ¬∃ fuel, PrivateCoinPairedScalarProbability.Bad code publicData privateData dummy fuel execution} ∪
      {execution | (∃ fuel, PrivateCoinEqualityProbability.Event code publicData privateData dummy fuel execution) ∧
        ¬∃ fuel, PrivateCoinEqualityProbability.Bad code publicData privateData dummy fuel execution} := by
    rintro execution ⟨⟨fuel,identity | sum⟩,safe⟩
    · exact Or.inl ⟨⟨fuel,identity⟩,safe⟩
    · exact Or.inr ⟨⟨fuel,sum⟩,safe⟩
  exact (measure_mono included).trans ((measure_union_le _ _).trans ((add_le_add
    (PrivateCoinPairedScalarProbability.safe_bound coins code publicData privateData dummy)
    (PrivateCoinEqualityProbability.safe_bound coins code publicData privateData dummy)).trans (le_of_eq (mul_add _ _ _).symm)))

end
end FormalProof4FHE.HasteBoots.PrivateCoinLookupArithmeticProbability
