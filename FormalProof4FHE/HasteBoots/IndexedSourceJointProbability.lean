module
public import FormalProof4FHE.HasteBoots.PrivateCoinEarlyReceiptProbability
@[expose] public section

/-! Eliminate the original indexed source-failure probability. One shared
receipt charge and two adaptive native exposure charges cover every index. -/
namespace FormalProof4FHE.HasteBoots.IndexedSourceJointProbability
open InputIndexedOracle (Input World law)
open NativeGoldBatchPcsProgram (Context)
open NativeRootMessage (Digest)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction)
open MeasureTheory
noncomputable section

def rate : ENNReal := AdaptiveBatchFieldKernel.rate+AdaptiveBatchColumnKernel.rate+1/(2 : ENNReal)^255

variable {I : Type} (Memory : Type) (code : List Instruction) (publicData : Input)
  (privateData : ClosedByteMachine.Tape → Input) (dummy profile : Digest)
  (source : I → Context) (origin : (i : I) → CacheBackedCodeOrigin.Origin (source i))
  (role : I → NativeBrakedownCalibration.Role)

theorem covered (admitted : ∀ i, NativeGoldBatchCalibration.Matches (source i) (role i))
    (profiles : ∀ i, (source i).parent.profile = profile) (execution : Tape × World)
    (failed : IndexedSourceFieldReduction.Failure Memory code publicData privateData dummy source origin role execution)
    (safe : ¬∃ fuel, AdaptiveBatchFieldLifetime.Bad code publicData privateData dummy fuel execution) :
    (∃ fuel, PrivateCoinEarlyReceiptProbability.Occurs code publicData privateData profile fuel execution) ∨
    (∃ fuel, AdaptiveBatchFieldLifetime.Occurs code publicData privateData profile dummy fuel execution) ∨
    ∃ fuel, AdaptiveBatchColumnLifetime.Occurs code publicData privateData profile dummy fuel execution := by
  obtain ⟨fuel,i,failed⟩ := failed
  obtain ⟨index,_,hazard⟩ := OriginalSourceJointCoverage.original_covered Memory code publicData privateData execution.1 fuel execution.2 dummy
    (source i) (origin i) (role i) (admitted i) failed
  rw [profiles i] at hazard
  rcases hazard with root | early | field | column
  · exact False.elim (safe ⟨index,Or.inl root⟩)
  · exact Or.inl ⟨index,early⟩
  · exact Or.inr (Or.inl ⟨index,field⟩)
  · exact Or.inr (Or.inr ⟨index,column⟩)

theorem safe_bound (coins : Measure Tape) (admitted : ∀ i, NativeGoldBatchCalibration.Matches (source i) (role i))
    (profiles : ∀ i, (source i).parent.profile = profile) :
    (coins.prod law) {execution | IndexedSourceFieldReduction.Failure Memory code publicData privateData dummy source origin role execution ∧
      ¬∃ fuel, AdaptiveBatchFieldLifetime.Bad code publicData privateData dummy fuel execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData * rate := by
  have included : {execution | IndexedSourceFieldReduction.Failure Memory code publicData privateData dummy source origin role execution ∧
      ¬∃ fuel, AdaptiveBatchFieldLifetime.Bad code publicData privateData dummy fuel execution} ⊆
      {execution | ∃ fuel, PrivateCoinEarlyReceiptProbability.Occurs code publicData privateData profile fuel execution} ∪
      ({execution | (∃ fuel, AdaptiveBatchFieldLifetime.Occurs code publicData privateData profile dummy fuel execution) ∧
        ¬∃ fuel, AdaptiveBatchFieldLifetime.Bad code publicData privateData dummy fuel execution} ∪
       {execution | (∃ fuel, AdaptiveBatchColumnLifetime.Occurs code publicData privateData profile dummy fuel execution) ∧
        ¬∃ fuel, AdaptiveBatchColumnLifetime.Bad code publicData privateData dummy fuel execution}) := by
    rintro execution ⟨failed,safe⟩
    rcases covered Memory code publicData privateData dummy profile source origin role admitted profiles execution failed safe with receipt | field | column
    · exact Or.inl receipt
    · exact Or.inr (Or.inl ⟨field,safe⟩)
    · exact Or.inr (Or.inr ⟨column,safe⟩)
  apply (measure_mono included).trans ((measure_union_le _ _).trans ?_)
  apply (add_le_add (PrivateCoinEarlyReceiptProbability.lifetime_le_255 coins code publicData privateData profile)
    ((measure_union_le _ _).trans (add_le_add
      (AdaptiveBatchFieldLifetime.safe_bound coins code publicData privateData profile dummy)
      (AdaptiveBatchColumnLifetime.safe_bound coins code publicData privateData profile dummy)))).trans
  exact le_of_eq (by simp only [rate,mul_add]; ac_rfl)

theorem root_safe_bound (coins : Measure Tape) (admitted : ∀ i, NativeGoldBatchCalibration.Matches (source i) (role i))
    (profiles : ∀ i, (source i).parent.profile = profile) :
    (coins.prod law) {execution | IndexedSourceFieldReduction.Failure Memory code publicData privateData dummy source origin role execution ∧
      ¬∃ fuel, PrivateCoinSharedHash.Root code publicData privateData dummy fuel execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData * (rate+1/(2 : ENNReal)^159) := by
  have included : {execution | IndexedSourceFieldReduction.Failure Memory code publicData privateData dummy source origin role execution ∧
      ¬∃ fuel, PrivateCoinSharedHash.Root code publicData privateData dummy fuel execution} ⊆
      {execution | IndexedSourceFieldReduction.Failure Memory code publicData privateData dummy source origin role execution ∧
        ¬∃ fuel, AdaptiveBatchFieldLifetime.Bad code publicData privateData dummy fuel execution} ∪
      {execution | PrivateCoinSharedHash.Other code publicData privateData execution} := by
    rintro execution ⟨failed,safe⟩
    by_cases other : PrivateCoinSharedHash.Other code publicData privateData execution
    · exact Or.inr other
    · left
      refine ⟨failed,?_⟩
      rintro ⟨fuel,root | bad⟩
      · exact safe ⟨fuel,root⟩
      · exact other ⟨fuel,bad⟩
  apply (measure_mono included).trans ((measure_union_le _ _).trans ?_)
  apply (add_le_add (safe_bound Memory code publicData privateData dummy profile source origin role coins admitted profiles)
    (PrivateCoinReferenceProbability.lifetime_le_159 coins code publicData privateData)).trans
  exact le_of_eq (mul_add _ _ _).symm

end
end FormalProof4FHE.HasteBoots.IndexedSourceJointProbability
