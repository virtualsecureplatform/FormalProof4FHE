module
public import FormalProof4FHE.HasteBoots.PrivateCoinFirstCompressionWorkProbability
public import FormalProof4FHE.HasteBoots.PrivateCoinLookupChallengeProbability
@[expose] public section

/-! Arithmetic scalar/equality, reciprocal and compression lookup events share one
excluded reference ledger while their specified-work rates are combined. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinAllLookupChallengeProbability
open MeasureTheory
open InputIndexedOracle (Input World law)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction)
open NativeRootMessage (Digest)
noncomputable section

def rate : ENNReal := PrivateCoinLookupChallengeProbability.rate + LookupStreamWorkRate.rate

def Event (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (dummy : Digest) (fuel : ℕ) (execution : Tape × World) : Prop :=
  PrivateCoinLookupChallengeProbability.Event code publicData privateData dummy fuel execution ∨
    PrivateCoinFirstCompressionWorkProbability.Event code publicData privateData dummy fuel execution

abbrev Bad := PrivateCoinFirstCompressionWorkProbability.Bad

theorem safe_bound (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) :
    (coins.prod law) {execution | (∃ fuel, Event code publicData privateData dummy fuel execution) ∧
      ¬∃ fuel, Bad code publicData privateData dummy fuel execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData * rate := by
  have included : {execution | (∃ fuel, Event code publicData privateData dummy fuel execution) ∧
      ¬∃ fuel, Bad code publicData privateData dummy fuel execution} ⊆
      {execution | (∃ fuel, PrivateCoinLookupChallengeProbability.Event code publicData privateData dummy fuel execution) ∧
        ¬∃ fuel, PrivateCoinLookupChallengeProbability.Bad code publicData privateData dummy fuel execution} ∪
      {execution | (∃ fuel, PrivateCoinFirstCompressionWorkProbability.Event code publicData privateData dummy fuel execution) ∧
        ¬∃ fuel, PrivateCoinFirstCompressionWorkProbability.Bad code publicData privateData dummy fuel execution} := by
    rintro execution ⟨⟨fuel,arithmetic | reciprocal⟩,safe⟩
    · exact Or.inl ⟨⟨fuel,arithmetic⟩,safe⟩
    · exact Or.inr ⟨⟨fuel,reciprocal⟩,safe⟩
  exact (measure_mono included).trans ((measure_union_le _ _).trans ((add_le_add
    (PrivateCoinLookupChallengeProbability.safe_bound coins code publicData privateData dummy)
    (PrivateCoinFirstCompressionWorkProbability.safe_bound coins code publicData privateData dummy)).trans (le_of_eq (mul_add _ _ _).symm)))

def finiteRate : NNReal := ((4/(NativeFields.goldilocksModulus^3 : NNReal)+4/(NativeFields.goldilocksModulus^3 : NNReal))+
  63/(NativeFields.goldilocksModulus^3 : NNReal))+1/2^132+1/2^132

theorem finite_rate_coe : (finiteRate : ENNReal) = rate := by
  simp only [finiteRate,rate,PrivateCoinLookupChallengeProbability.rate,PrivateCoinLookupArithmeticProbability.scalarRate,
    PrivateCoinPairedScalarProbability.scalarRate,ScalarEquationWork.rate,EqualityPositionKernel.rate,LookupStreamWorkRate.rate,
    ENNReal.coe_add,ENNReal.coe_div (by norm_num [NativeFields.goldilocksModulus] : (NativeFields.goldilocksModulus^3 : NNReal) ≠ 0),
    ENNReal.coe_div (by positivity : (2 : NNReal)^132 ≠ 0),ENNReal.coe_pow,ENNReal.coe_ofNat,ENNReal.coe_natCast,ENNReal.coe_one,Nat.cast_pow]

theorem rate_le_130 : rate ≤ 1/(2 : ENNReal)^130 := by
  have finite : finiteRate ≤ 1/(2 : NNReal)^130 := by
    rw [← NNReal.coe_le_coe]
    norm_num [finiteRate,NativeFields.goldilocksModulus]
  have cast := ENNReal.coe_le_coe.mpr finite
  rw [finite_rate_coe] at cast
  simpa only [ENNReal.coe_div (by positivity : (2 : NNReal)^130 ≠ 0),ENNReal.coe_pow,ENNReal.coe_ofNat,ENNReal.coe_one] using cast

/-- All native scalar, equality, compression and reciprocal safe events
retain 130 bits of specified-work security, before PCS/bad-event composition. -/
theorem safe_work_130 (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) :
    (2 : ENNReal)^130 * (coins.prod law)
      {execution | (∃ fuel, Event code publicData privateData dummy fuel execution) ∧
        ¬∃ fuel, Bad code publicData privateData dummy fuel execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  calc
    _ ≤ (2 : ENNReal)^130 * (PrivateCoinByteWork.expectedWork coins code publicData privateData * rate) :=
      mul_le_mul' le_rfl (safe_bound coins code publicData privateData dummy)
    _ ≤ (2 : ENNReal)^130 * (PrivateCoinByteWork.expectedWork coins code publicData privateData * (1/(2 : ENNReal)^130)) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl rate_le_130)
    _ = PrivateCoinByteWork.expectedWork coins code publicData privateData * ((2 : ENNReal)^130*(1/(2 : ENNReal)^130)) := by ac_rfl
    _ = _ := by rw [one_div,ENNReal.mul_inv_cancel (by norm_num) (by norm_num),mul_one]

end
end FormalProof4FHE.HasteBoots.PrivateCoinAllLookupChallengeProbability
