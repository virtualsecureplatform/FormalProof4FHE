module
public import FormalProof4FHE.HasteBoots.PrivateCoinOffsetWorkProbability
public import FormalProof4FHE.HasteBoots.PrivateCoinLookupArithmeticProbability
@[expose] public section

/-! Arithmetic scalar/equality and reciprocal lookup events share one
excluded reference ledger while their specified-work rates are combined. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinLookupChallengeProbability
open MeasureTheory
open InputIndexedOracle (Input World law)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction)
open NativeRootMessage (Digest)
noncomputable section

def rate : ENNReal := PrivateCoinLookupArithmeticProbability.scalarRate + LookupStreamWorkRate.rate

def Event (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (dummy : Digest) (fuel : ℕ) (execution : Tape × World) : Prop :=
  PrivateCoinLookupArithmeticProbability.Event code publicData privateData dummy fuel execution ∨
    PrivateCoinOffsetWorkProbability.Event code publicData privateData dummy fuel execution

abbrev Bad := PrivateCoinOffsetWorkProbability.Bad

theorem safe_bound (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) :
    (coins.prod law) {execution | (∃ fuel, Event code publicData privateData dummy fuel execution) ∧
      ¬∃ fuel, Bad code publicData privateData dummy fuel execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData * rate := by
  have included : {execution | (∃ fuel, Event code publicData privateData dummy fuel execution) ∧
      ¬∃ fuel, Bad code publicData privateData dummy fuel execution} ⊆
      {execution | (∃ fuel, PrivateCoinLookupArithmeticProbability.Event code publicData privateData dummy fuel execution) ∧
        ¬∃ fuel, PrivateCoinLookupArithmeticProbability.Bad code publicData privateData dummy fuel execution} ∪
      {execution | (∃ fuel, PrivateCoinOffsetWorkProbability.Event code publicData privateData dummy fuel execution) ∧
        ¬∃ fuel, PrivateCoinOffsetWorkProbability.Bad code publicData privateData dummy fuel execution} := by
    rintro execution ⟨⟨fuel,arithmetic | reciprocal⟩,safe⟩
    · exact Or.inl ⟨⟨fuel,arithmetic⟩,safe⟩
    · exact Or.inr ⟨⟨fuel,reciprocal⟩,safe⟩
  exact (measure_mono included).trans ((measure_union_le _ _).trans ((add_le_add
    (PrivateCoinLookupArithmeticProbability.safe_bound coins code publicData privateData dummy)
    (PrivateCoinOffsetWorkProbability.safe_bound coins code publicData privateData dummy)).trans (le_of_eq (mul_add _ _ _).symm)))

end
end FormalProof4FHE.HasteBoots.PrivateCoinLookupChallengeProbability
