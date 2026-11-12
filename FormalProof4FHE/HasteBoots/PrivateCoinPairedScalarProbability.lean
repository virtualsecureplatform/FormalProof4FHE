module
public import FormalProof4FHE.HasteBoots.PrivateCoinCanonicalSumProbability
public import FormalProof4FHE.HasteBoots.PrivateCoinCanonicalScalarProbability
@[expose] public section

/-! Original sum and identity events share one excluded global reference bad
ledger. Their conservative scalar work charges are added explicitly. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinPairedScalarProbability
open MeasureTheory
open InputIndexedOracle (Input World law)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction)
open NativeRootMessage (Digest)
noncomputable section

def scalarRate : ENNReal := ScalarEquationWork.rate + ScalarEquationWork.rate

def Event (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (dummy : Digest) (fuel : ℕ) (execution : Tape × World) : Prop :=
  PrivateCoinCanonicalScalarProbability.Event code publicData privateData dummy fuel execution ∨
    PrivateCoinCanonicalSumProbability.Event code publicData privateData dummy fuel execution

abbrev Bad := PrivateCoinCanonicalScalarProbability.Bad

theorem safe_bound (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) :
    (coins.prod law) {execution | (∃ fuel, Event code publicData privateData dummy fuel execution) ∧
      ¬∃ fuel, Bad code publicData privateData dummy fuel execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData * scalarRate := by
  have included : {execution | (∃ fuel, Event code publicData privateData dummy fuel execution) ∧
      ¬∃ fuel, Bad code publicData privateData dummy fuel execution} ⊆
      {execution | (∃ fuel, PrivateCoinCanonicalScalarProbability.Event code publicData privateData dummy fuel execution) ∧
        ¬∃ fuel, PrivateCoinCanonicalScalarProbability.Bad code publicData privateData dummy fuel execution} ∪
      {execution | (∃ fuel, PrivateCoinCanonicalSumProbability.Event code publicData privateData dummy fuel execution) ∧
        ¬∃ fuel, PrivateCoinCanonicalSumProbability.Bad code publicData privateData dummy fuel execution} := by
    rintro execution ⟨⟨fuel,identity | sum⟩,safe⟩
    · exact Or.inl ⟨⟨fuel,identity⟩,safe⟩
    · exact Or.inr ⟨⟨fuel,sum⟩,safe⟩
  exact (measure_mono included).trans ((measure_union_le _ _).trans ((add_le_add
    (PrivateCoinCanonicalScalarProbability.safe_bound coins code publicData privateData dummy)
    (PrivateCoinCanonicalSumProbability.safe_bound coins code publicData privateData dummy)).trans (le_of_eq (mul_add _ _ _).symm)))

end
end FormalProof4FHE.HasteBoots.PrivateCoinPairedScalarProbability
