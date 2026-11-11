module
public import FormalProof4FHE.HasteBoots.ProgramOpeningLifetime
@[expose] public section

/-! Original source parameter families and a helper share one lifetime hash
bad event. Distinct complete parameters retain their own exposure charges;
no geometry equality is promoted to full parameter equality. -/
namespace FormalProof4FHE.HasteBoots.OpeningLifetimeFamily
open InputIndexedOracle (World law)
open NativeRootMessage (Digest)
open SingleOpeningLifetimeSoundness (clean SourceBad)
open SharedNativeOpeningLifetime (HelperEvents SourceEvents)
open MeasureTheory
noncomputable section

variable {I S A : Type}

def Failure (HelperMemory SourceMemory : Type) (dummy : Digest)
    (helper : NativeGoldPcsExecution.Context) (source : I → NativeGoldBatchPcsProgram.Context)
    (sourceOrigin : (i : I) → CacheBackedCodeOrigin.Origin (source i)) (helperRadius : ℕ) (sourceRadius : I → ℕ)
    (state : S) (step : S → OracleMachine.Command S A) (world : World) : Prop :=
  SingleOpeningLifetimeSoundness.Failure HelperMemory dummy helper helperRadius (clean state) id step world ∨
    ∃ i, CacheBackedBatchLifetimeSoundness.Failure SourceMemory dummy (source i) (sourceOrigin i) (sourceRadius i) (clean state) id step world

theorem coverage (HelperMemory SourceMemory : Type) (dummy : Digest)
    (helper : NativeGoldPcsExecution.Context) (helperOrigin : CacheBackedSingleOpening.Origin helper)
    (source : I → NativeGoldBatchPcsProgram.Context) (sourceOrigin : (i : I) → CacheBackedCodeOrigin.Origin (source i))
    (helperRadius : ℕ) (sourceRadius : I → ℕ) (helperWidth : 3 ≤ helper.parameters.width.val)
    (sourceWidth : ∀ i, 3 ≤ (source i).parameters.width.val)
    (state : S) (step : S → OracleMachine.Command S A) (world : World)
    (failed : SourceBad dummy (clean state) id step world ∨
      Failure HelperMemory SourceMemory dummy helper source sourceOrigin helperRadius sourceRadius state step world) :
    SourceBad dummy (clean state) id step world ∨
      HelperEvents (clean state) id dummy helper helperOrigin helperRadius step world ∨
      ∃ i, SourceEvents (clean state) id dummy (source i) (sourceOrigin i) (sourceRadius i) step world := by
  rcases failed with bad | single | ⟨i,batch⟩
  · exact Or.inl bad
  · rcases SingleOpeningLifetimeSoundness.failure_covered HelperMemory dummy helper helperOrigin helperRadius helperWidth
      (ObservationReplay.pure_replay state) id step world single with old | bad | receipt | field | column
    · have member : world ∈ {world | SingleOpeningLifetimeSoundness.Inherited HelperMemory dummy helper helperRadius (clean state) id step world} := old
      rw [SingleOpeningLifetimeSoundness.inherited_clean] at member
      cases member
    · exact Or.inl bad
    · exact Or.inr (Or.inl (Or.inl receipt))
    · exact Or.inr (Or.inl (Or.inr (Or.inl field)))
    · exact Or.inr (Or.inl (Or.inr (Or.inr column)))
  · have native := (CacheBackedBatchLifetimeSoundness.failure_iff SourceMemory dummy (source i) (sourceOrigin i) (sourceRadius i) _ id step world).mp batch
    rcases NativeGoldBatchLifetimeSoundness.failure_covered SourceMemory dummy (source i) ((sourceOrigin i).primitiveAt _ rfl)
      (sourceOrigin i).tables (sourceOrigin i).request.message (sourceOrigin i).request.block (sourceOrigin i).request.blowup
      ((sourceOrigin i).constructedAt _ rfl) (sourceRadius i) (sourceWidth i) (ObservationReplay.pure_replay state) id step world native with
      old | bad | receipt | field | column
    · have member : world ∈ {world | NativeGoldBatchLifetimeSoundness.Inherited SourceMemory dummy (source i) (sourceRadius i) (NativeGoldBatchLifetimeSoundness.clean state) id step world} := old
      rw [NativeGoldBatchLifetimeSoundness.inherited_clean] at member
      cases member
    · exact Or.inl bad
    · exact Or.inr (Or.inr ⟨i,Or.inl receipt⟩)
    · exact Or.inr (Or.inr ⟨i,Or.inr (Or.inl field)⟩)
    · exact Or.inr (Or.inr ⟨i,Or.inr (Or.inr column)⟩)

theorem bound [Countable I] (HelperMemory SourceMemory : Type) (dummy : Digest)
    (helper : NativeGoldPcsExecution.Context) (helperOrigin : CacheBackedSingleOpening.Origin helper)
    (source : I → NativeGoldBatchPcsProgram.Context) (sourceOrigin : (i : I) → CacheBackedCodeOrigin.Origin (source i))
    (helperRadius : ℕ) (sourceRadius : I → ℕ) (helperWidth : 3 ≤ helper.parameters.width.val)
    (sourceWidth : ∀ i, 3 ≤ (source i).parameters.width.val)
    (state : S) (step : S → OracleMachine.Command S A)
    (helperSmall : 3*helperRadius < helper.parameters.code.blocks.val-helper.parameters.code.messageBlocks.val+1)
    (sourceSmall : ∀ i, 3*sourceRadius i < (source i).parameters.code.blocks.val-(source i).parameters.code.messageBlocks.val+1) :
    law {world | SourceBad dummy (clean state) id step world ∨
      Failure HelperMemory SourceMemory dummy helper source sourceOrigin helperRadius sourceRadius state step world} ≤
      (⨆ fuel : ℕ, NativeRootFamilyLifetime.prefixCharge dummy (.pure state) step fuel) +
      (SingleOpeningLifetimeSoundness.exposureCharge (clean state) id dummy helper helperOrigin helperRadius step +
        ∑' i, NativeGoldBatchLifetimeSoundness.exposureCharge (clean state) id dummy (source i) ((sourceOrigin i).primitiveAt _ rfl) (sourceRadius i) step) := by
  have included : {world | SourceBad dummy (clean state) id step world ∨
        Failure HelperMemory SourceMemory dummy helper source sourceOrigin helperRadius sourceRadius state step world} ⊆
      {world | SourceBad dummy (clean state) id step world} ∪
        ({world | HelperEvents (clean state) id dummy helper helperOrigin helperRadius step world} ∪
          {world | ∃ i, SourceEvents (clean state) id dummy (source i) (sourceOrigin i) (sourceRadius i) step world}) := by
    intro world failed
    exact coverage HelperMemory SourceMemory dummy helper helperOrigin source sourceOrigin helperRadius sourceRadius helperWidth sourceWidth state step world failed
  have hash : law {world | SourceBad dummy (clean state) id step world} ≤
      ⨆ fuel : ℕ, NativeRootFamilyLifetime.prefixCharge dummy (.pure state) step fuel := by
    change law {world | ∃ fuel, NativeRootFamilyLifetime.Bad dummy
      (OracleProgram.run (NativeRootFamilyLifetime.program (.pure state) step fuel) world).run.2} ≤ _
    exact NativeRootFamilyLifetime.lifetime_bad_le_charge dummy (.pure state) step
  have union : {world | ∃ i, SourceEvents (clean state) id dummy (source i) (sourceOrigin i) (sourceRadius i) step world} =
      ⋃ i, {world | SourceEvents (clean state) id dummy (source i) (sourceOrigin i) (sourceRadius i) step world} := by
    ext world
    simp
  have sources : law {world | ∃ i, SourceEvents (clean state) id dummy (source i) (sourceOrigin i) (sourceRadius i) step world} ≤
      ∑' i, NativeGoldBatchLifetimeSoundness.exposureCharge (clean state) id dummy (source i) ((sourceOrigin i).primitiveAt _ rfl) (sourceRadius i) step := by
    rw [union]
    exact (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum (fun i => SharedNativeOpeningLifetime.source_events_bound
      (ObservationReplay.pure_replay state) id dummy (source i) (sourceOrigin i) (sourceRadius i) step (sourceSmall i)))
  exact (measure_mono included).trans ((measure_union_le _ _).trans (add_le_add hash
    ((measure_union_le _ _).trans (add_le_add
      (SharedNativeOpeningLifetime.helper_events_bound (ObservationReplay.pure_replay state) id dummy helper helperOrigin helperRadius step helperSmall) sources))))

end
end FormalProof4FHE.HasteBoots.OpeningLifetimeFamily
