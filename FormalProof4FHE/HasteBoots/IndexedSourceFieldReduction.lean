module
public import FormalProof4FHE.HasteBoots.OriginalSourceAdaptiveCoverage
@[expose] public section

/-! An arbitrary indexed original source union pays one adaptive field bound.
The common-profile early receipt and indexed column branches remain explicit. -/
namespace FormalProof4FHE.HasteBoots.IndexedSourceFieldReduction
open InputIndexedOracle (Input World law)
open NativeGoldBatchPcsProgram (Context)
open NativeRootMessage (Digest)
open OracleProgram (runPrefix)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction)
open InterpreterScalarLifetime (privateProgram)
open MeasureTheory
noncomputable section

theorem registry_profiles (ctx : NativeGoldHelperVerification.Context (NativePrefixCodec.Vector NativeGoldBatchOpening.Opening)) :
    ∀ slot, (RegistryPublicSource.context ctx slot).parent.profile = ctx.parent.profile := fun _ => rfl

variable {I : Type} (Memory : Type) (code : List Instruction) (publicData : Input)
  (privateData : ClosedByteMachine.Tape → Input) (dummy profile : Digest)
  (source : I → Context) (origin : (i : I) → CacheBackedCodeOrigin.Origin (source i))
  (role : I → NativeBrakedownCalibration.Role)

def Failure (execution : Tape × World) : Prop :=
  ∃ fuel i, CacheBackedBatchLifetimeSoundness.Failure Memory dummy (source i) (origin i)
    (NativeBrakedownCalibration.radius .goldilocks (role i))
    (SingleOpeningLifetimeSoundness.clean (privateProgram code publicData execution.1 privateData fuel)) id OracleProgramMachine.step execution.2

def Remaining (execution : Tape × World) : Prop :=
  (∃ fuel position, NativeEarlyReceiptBound.event profile OracleProgramMachine.step
    (runPrefix position (privateProgram code publicData execution.1 privateData fuel) execution.2).run execution.2) ∨
  ∃ fuel i position, NativeGoldBatchProfileColumnExposure.event dummy (source i) ((origin i).primitiveAt _ rfl) profile OracleProgramMachine.step
    (runPrefix position (privateProgram code publicData execution.1 privateData fuel) execution.2).run
      (NativeBrakedownCalibration.radius .goldilocks (role i)) execution.2

theorem covered (admitted : ∀ i, NativeGoldBatchCalibration.Matches (source i) (role i))
    (profiles : ∀ i, (source i).parent.profile = profile) (execution : Tape × World)
    (failed : Failure Memory code publicData privateData dummy source origin role execution)
    (safe : ¬∃ fuel, AdaptiveBatchFieldLifetime.Bad code publicData privateData dummy fuel execution) :
    Remaining code publicData privateData dummy profile source origin role execution ∨
      ∃ fuel, AdaptiveBatchFieldLifetime.Occurs code publicData privateData profile dummy fuel execution := by
  obtain ⟨fuel,i,failed⟩ := failed
  obtain ⟨index,_,hazard⟩ := OriginalSourceAdaptiveCoverage.original_covered Memory code publicData privateData execution.1 fuel execution.2 dummy
    (source i) (origin i) (role i) (admitted i) failed
  rcases hazard with root | ⟨position,early⟩ | ⟨position,field⟩ | ⟨position,column⟩
  · exact False.elim (safe ⟨index,Or.inl root⟩)
  · left; left
    rw [profiles i] at early
    exact ⟨index,position,early⟩
  · right
    rw [profiles i] at field
    exact ⟨index,position,field⟩
  · left; right
    rw [profiles i] at column
    exact ⟨index,i,position,column⟩

theorem safe_bound (coins : Measure Tape) (admitted : ∀ i, NativeGoldBatchCalibration.Matches (source i) (role i))
    (profiles : ∀ i, (source i).parent.profile = profile) :
    (coins.prod law) {execution | Failure Memory code publicData privateData dummy source origin role execution ∧
      ¬∃ fuel, AdaptiveBatchFieldLifetime.Bad code publicData privateData dummy fuel execution} ≤
      (coins.prod law) {execution | Remaining code publicData privateData dummy profile source origin role execution} +
        PrivateCoinByteWork.expectedWork coins code publicData privateData * AdaptiveBatchFieldKernel.rate := by
  have included : {execution | Failure Memory code publicData privateData dummy source origin role execution ∧
      ¬∃ fuel, AdaptiveBatchFieldLifetime.Bad code publicData privateData dummy fuel execution} ⊆
      {execution | Remaining code publicData privateData dummy profile source origin role execution} ∪
      {execution | (∃ fuel, AdaptiveBatchFieldLifetime.Occurs code publicData privateData profile dummy fuel execution) ∧
        ¬∃ fuel, AdaptiveBatchFieldLifetime.Bad code publicData privateData dummy fuel execution} := by
    rintro execution ⟨failed,safe⟩
    rcases covered Memory code publicData privateData dummy profile source origin role admitted profiles execution failed safe with remaining | field
    · exact Or.inl remaining
    · exact Or.inr ⟨field,safe⟩
  exact (measure_mono included).trans ((measure_union_le _ _).trans (add_le_add le_rfl
    (AdaptiveBatchFieldLifetime.safe_bound coins code publicData privateData profile dummy)))

/-- Match the original ledger's shared-hash mask. Reference failures are
charged once for this source reduction, independent of the index type. -/
theorem root_safe_bound (coins : Measure Tape) (admitted : ∀ i, NativeGoldBatchCalibration.Matches (source i) (role i))
    (profiles : ∀ i, (source i).parent.profile = profile) :
    (coins.prod law) {execution | Failure Memory code publicData privateData dummy source origin role execution ∧
      ¬∃ fuel, PrivateCoinSharedHash.Root code publicData privateData dummy fuel execution} ≤
      (coins.prod law) {execution | Remaining code publicData privateData dummy profile source origin role execution} +
        PrivateCoinByteWork.expectedWork coins code publicData privateData *
          (AdaptiveBatchFieldKernel.rate+1/(2 : ENNReal)^159) := by
  have included : {execution | Failure Memory code publicData privateData dummy source origin role execution ∧
      ¬∃ fuel, PrivateCoinSharedHash.Root code publicData privateData dummy fuel execution} ⊆
      {execution | Failure Memory code publicData privateData dummy source origin role execution ∧
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
  exact le_of_eq (by rw [mul_add,add_assoc])

end
end FormalProof4FHE.HasteBoots.IndexedSourceFieldReduction
