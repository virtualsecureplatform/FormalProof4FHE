module
public import FormalProof4FHE.HasteBoots.SingleOpeningConstructorBounds
public import FormalProof4FHE.HasteBoots.CacheBackedBatchLifetimeSoundness
public import FormalProof4FHE.HasteBoots.NativeGoldBatchLifetimeMeasurable
@[expose] public section

/-! Single helper and source-batch failure events share one complete-history
hash bad event. Their fixed parameters, packing widths and profiles may differ;
all queries still use the same oracle world and machine history. This is a
joint analysis-extractor lifetime bound, not the outer lookup/PBS reduction
or a physical attacker-work theorem. -/
namespace FormalProof4FHE.HasteBoots.SharedNativeOpeningLifetime
open NativeRootMessage (Digest)
open NativeTranscript (Execution)
open InputIndexedOracle (World law)
open CausalExposureLifetime (history)
open OracleProgram (Program run)
open MeasureTheory
noncomputable section

abbrev HelperContext := NativeGoldPcsExecution.Context
abbrev SourceContext := NativeGoldBatchPcsProgram.Context

def Failure {P S A : Type} (HelperMemory SourceMemory : Type) (dummy : Digest)
    (helper : HelperContext) (source : SourceContext) (sourceOrigin : CacheBackedCodeOrigin.Origin source)
    (helperRadius sourceRadius : ℕ) (past : World → Execution P) (initial : P → S)
    (step : S → OracleMachine.Command S A) (world : World) : Prop :=
  SingleOpeningLifetimeSoundness.Failure HelperMemory dummy helper helperRadius past initial step world ∨
    CacheBackedBatchLifetimeSoundness.Failure SourceMemory dummy source sourceOrigin sourceRadius past initial step world

def HelperEvents {P S A : Type} (past : World → Execution P) (initial : P → S) (dummy : Digest)
    (ctx : HelperContext) (origin : CacheBackedSingleOpening.Origin ctx) (radius : ℕ)
    (step : S → OracleMachine.Command S A) (world : World) : Prop :=
  (∃ index, SingleOpeningEarlyReceiptBound.event ctx.transcript.profile step (history past initial step index world).run world) ∨
  (∃ index, SingleOpeningFieldProximity.event dummy ctx origin.primitive radius ctx.transcript.profile step (history past initial step index world).run world) ∨
  (∃ index, SingleOpeningProfileColumnExposure.event dummy ctx origin.primitive ctx.transcript.profile step (history past initial step index world).run radius world)

def SourceEvents {P S A : Type} (past : World → Execution P) (initial : P → S) (dummy : Digest)
    (ctx : SourceContext) (origin : CacheBackedCodeOrigin.Origin ctx) (radius : ℕ)
    (step : S → OracleMachine.Command S A) (world : World) : Prop :=
  (∃ index, NativeEarlyReceiptBound.event ctx.parent.profile step (history past initial step index world).run world) ∨
  (∃ index, NativeGoldBatchFieldProximity.event dummy ctx (origin.primitiveAt ctx rfl) radius ctx.parent.profile step (history past initial step index world).run world) ∨
  (∃ index, NativeGoldBatchProfileColumnExposure.event dummy ctx (origin.primitiveAt ctx rfl) ctx.parent.profile step (history past initial step index world).run radius world)

theorem helper_events_bound {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (dummy : Digest) (ctx : HelperContext) (origin : CacheBackedSingleOpening.Origin ctx)
    (radius : ℕ) (step : S → OracleMachine.Command S A)
    (small : 3*radius < ctx.parameters.code.blocks.val-ctx.parameters.code.messageBlocks.val+1) :
    law {world | HelperEvents past initial dummy ctx origin radius step world} ≤
      SingleOpeningLifetimeSoundness.exposureCharge past initial dummy ctx origin radius step := by
  have receipt := SingleOpeningEarlyReceiptBound.lifetime_le replay initial ctx.transcript.profile step ∅
  have matrixSmall : 3*radius < Code.minDist (BlockCode.code (SingleOpeningConcreteColumnFamily.Domain ctx origin.primitive)
      ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
      Set (SingleOpeningConcreteColumnFamily.Position ctx → SingleOpeningConcreteColumnFamily.Symbol ctx)) := by
    rw [SingleOpeningConstructorBounds.distance origin]
    exact small
  have field := SingleOpeningFieldProximity.lifetime_le replay initial dummy ctx origin.primitive radius ctx.transcript.profile step ∅
    (SingleOpeningConstructorBounds.radius_fits origin radius small) matrixSmall
  have column := SingleOpeningProfileColumnExposure.lifetime_le replay initial dummy ctx origin.primitive ctx.transcript.profile step radius ∅
  simp only [Set.empty_union,measure_empty,zero_add] at receipt field column
  exact (measure_union_le _ _).trans (add_le_add receipt ((measure_union_le _ _).trans (add_le_add field column)))

theorem source_events_bound {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (dummy : Digest) (ctx : SourceContext) (origin : CacheBackedCodeOrigin.Origin ctx)
    (radius : ℕ) (step : S → OracleMachine.Command S A)
    (small : 3*radius < ctx.parameters.code.blocks.val-ctx.parameters.code.messageBlocks.val+1) :
    law {world | SourceEvents past initial dummy ctx origin radius step world} ≤
      NativeGoldBatchLifetimeSoundness.exposureCharge past initial dummy ctx (origin.primitiveAt ctx rfl) radius step := by
  have receipt := NativeEarlyReceiptBound.lifetime_le replay initial ctx.parent.profile step ∅
  have matrixSmall : 3*radius < Code.minDist (BlockCode.code (NativeGoldBatchResponseMeaning.Domain ctx (origin.primitiveAt ctx rfl))
      ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
      Set (NativeGoldBatchConcreteColumnFamily.Position ctx → NativeGoldBatchConcreteColumnFamily.Symbol ctx)) := by
    rw [origin.distanceAt ctx rfl]
    exact small
  have field := NativeGoldBatchFieldProximity.lifetime_le replay initial dummy ctx (origin.primitiveAt ctx rfl) radius ctx.parent.profile step ∅
    (origin.radius_fits radius small) matrixSmall
  have column := NativeGoldBatchProfileColumnExposure.lifetime_le replay initial dummy ctx (origin.primitiveAt ctx rfl) ctx.parent.profile step radius ∅
  simp only [Set.empty_union,measure_empty,zero_add] at receipt field column
  exact (measure_union_le _ _).trans (add_le_add receipt ((measure_union_le _ _).trans (add_le_add field column)))

theorem failure_measurable {P S A : Type} (HelperMemory SourceMemory : Type) (dummy : Digest)
    (helper : HelperContext) (source : SourceContext) (sourceOrigin : CacheBackedCodeOrigin.Origin source)
    (helperRadius sourceRadius : ℕ) {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (step : S → OracleMachine.Command S A) :
    MeasurableSet {world | Failure HelperMemory SourceMemory dummy helper source sourceOrigin helperRadius sourceRadius past initial step world} := by
  have single := SingleOpeningLifetimeMeasurable.failure_measurable HelperMemory dummy helper helperRadius replay initial step
  have batch : MeasurableSet {world | CacheBackedBatchLifetimeSoundness.Failure SourceMemory dummy source sourceOrigin sourceRadius past initial step world} := by
    simpa only [CacheBackedBatchLifetimeSoundness.failure_iff] using
      NativeGoldBatchLifetimeMeasurable.failure_measurable SourceMemory dummy source sourceRadius replay initial step
  exact single.union batch

theorem clean_coverage {S A : Type} (HelperMemory SourceMemory : Type) (dummy : Digest)
    (helper : HelperContext) (helperOrigin : CacheBackedSingleOpening.Origin helper)
    (source : SourceContext) (sourceOrigin : CacheBackedCodeOrigin.Origin source) (helperRadius sourceRadius : ℕ)
    (helperWidth : 3 ≤ helper.parameters.width.val) (sourceWidth : 3 ≤ source.parameters.width.val)
    (state : S) (step : S → OracleMachine.Command S A) (world : World)
    (failed : Failure HelperMemory SourceMemory dummy helper source sourceOrigin helperRadius sourceRadius
      (SingleOpeningLifetimeSoundness.clean state) id step world) :
    SingleOpeningLifetimeSoundness.SourceBad dummy (SingleOpeningLifetimeSoundness.clean state) id step world ∨
      HelperEvents (SingleOpeningLifetimeSoundness.clean state) id dummy helper helperOrigin helperRadius step world ∨
      SourceEvents (SingleOpeningLifetimeSoundness.clean state) id dummy source sourceOrigin sourceRadius step world := by
  rcases failed with single | batch
  · rcases SingleOpeningLifetimeSoundness.failure_covered HelperMemory dummy helper helperOrigin helperRadius helperWidth
      (ObservationReplay.pure_replay state) id step world single with old | bad | receipt | field | column
    · have member : world ∈ {world | SingleOpeningLifetimeSoundness.Inherited HelperMemory dummy helper helperRadius
          (SingleOpeningLifetimeSoundness.clean state) id step world} := old
      rw [SingleOpeningLifetimeSoundness.inherited_clean] at member
      cases member
    · exact Or.inl bad
    · exact Or.inr (Or.inl (Or.inl receipt))
    · exact Or.inr (Or.inl (Or.inr (Or.inl field)))
    · exact Or.inr (Or.inl (Or.inr (Or.inr column)))
  · have native := (CacheBackedBatchLifetimeSoundness.failure_iff SourceMemory dummy source sourceOrigin sourceRadius _ id step world).mp batch
    rcases NativeGoldBatchLifetimeSoundness.failure_covered SourceMemory dummy source (sourceOrigin.primitiveAt source rfl)
      sourceOrigin.tables sourceOrigin.request.message sourceOrigin.request.block sourceOrigin.request.blowup (sourceOrigin.constructedAt source rfl)
      sourceRadius sourceWidth (ObservationReplay.pure_replay state) id step world native with old | bad | receipt | field | column
    · have member : world ∈ {world | NativeGoldBatchLifetimeSoundness.Inherited SourceMemory dummy source sourceRadius
          (NativeGoldBatchLifetimeSoundness.clean state) id step world} := old
      rw [NativeGoldBatchLifetimeSoundness.inherited_clean] at member
      cases member
    · exact Or.inl bad
    · exact Or.inr (Or.inr (Or.inl receipt))
    · exact Or.inr (Or.inr (Or.inr (Or.inl field)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr column)))

theorem initialised_bound {S A : Type} (HelperMemory SourceMemory : Type) (dummy : Digest)
    (helper : HelperContext) (helperOrigin : CacheBackedSingleOpening.Origin helper)
    (source : SourceContext) (sourceOrigin : CacheBackedCodeOrigin.Origin source) (helperRadius sourceRadius : ℕ)
    (helperWidth : 3 ≤ helper.parameters.width.val) (sourceWidth : 3 ≤ source.parameters.width.val)
    (state : S) (step : S → OracleMachine.Command S A)
    (helperSmall : 3*helperRadius < helper.parameters.code.blocks.val-helper.parameters.code.messageBlocks.val+1)
    (sourceSmall : 3*sourceRadius < source.parameters.code.blocks.val-source.parameters.code.messageBlocks.val+1) :
    law {world | Failure HelperMemory SourceMemory dummy helper source sourceOrigin helperRadius sourceRadius
      (SingleOpeningLifetimeSoundness.clean state) id step world} ≤
      (⨆ fuel : ℕ, NativeRootFamilyLifetime.prefixCharge dummy (.pure state) step fuel) +
      (SingleOpeningLifetimeSoundness.exposureCharge (SingleOpeningLifetimeSoundness.clean state) id dummy helper helperOrigin helperRadius step +
        NativeGoldBatchLifetimeSoundness.exposureCharge (SingleOpeningLifetimeSoundness.clean state) id dummy source (sourceOrigin.primitiveAt source rfl) sourceRadius step) := by
  have included : {world | Failure HelperMemory SourceMemory dummy helper source sourceOrigin helperRadius sourceRadius
        (SingleOpeningLifetimeSoundness.clean state) id step world} ⊆
      {world | SingleOpeningLifetimeSoundness.SourceBad dummy (SingleOpeningLifetimeSoundness.clean state) id step world} ∪
      ({world | HelperEvents (SingleOpeningLifetimeSoundness.clean state) id dummy helper helperOrigin helperRadius step world} ∪
       {world | SourceEvents (SingleOpeningLifetimeSoundness.clean state) id dummy source sourceOrigin sourceRadius step world}) := by
    intro world failed
    exact clean_coverage HelperMemory SourceMemory dummy helper helperOrigin source sourceOrigin helperRadius sourceRadius helperWidth sourceWidth state step world failed
  have hash : law {world | SingleOpeningLifetimeSoundness.SourceBad dummy (SingleOpeningLifetimeSoundness.clean state) id step world} ≤
      ⨆ fuel : ℕ, NativeRootFamilyLifetime.prefixCharge dummy (.pure state) step fuel := by
    change law {world | ∃ fuel, NativeRootFamilyLifetime.Bad dummy
      (run (NativeRootFamilyLifetime.program (.pure state) step fuel) world).run.2} ≤ _
    exact NativeRootFamilyLifetime.lifetime_bad_le_charge dummy (.pure state) step
  exact (measure_mono included).trans ((measure_union_le _ _).trans (add_le_add hash
    ((measure_union_le _ _).trans (add_le_add
      (helper_events_bound (ObservationReplay.pure_replay state) id dummy helper helperOrigin helperRadius step helperSmall)
      (source_events_bound (ObservationReplay.pure_replay state) id dummy source sourceOrigin sourceRadius step sourceSmall)))))

theorem failure_rebase {S A : Type} (HelperMemory SourceMemory : Type) (dummy : Digest)
    (helper : HelperContext) (source : SourceContext) (sourceOrigin : CacheBackedCodeOrigin.Origin source)
    (helperRadius sourceRadius : ℕ) (prelude : Program S) (step : S → OracleMachine.Command S A) (world : World)
    (failed : Failure HelperMemory SourceMemory dummy helper source sourceOrigin helperRadius sourceRadius (run prelude) id step world) :
    Failure HelperMemory SourceMemory dummy helper source sourceOrigin helperRadius sourceRadius
      (SingleOpeningLifetimeSoundness.clean prelude) id (OracleMachinePrelude.prepend step) world := by
  rcases failed with single | batch
  · exact Or.inl (SingleOpeningLifetimeSoundness.failure_rebase HelperMemory dummy helper helperRadius prelude step world single)
  · have native := (CacheBackedBatchLifetimeSoundness.failure_iff SourceMemory dummy source sourceOrigin sourceRadius _ id step world).mp batch
    have rebased := NativeGoldBatchLifetimeSoundness.failure_rebase SourceMemory dummy source sourceRadius prelude step world native
    exact Or.inr ((CacheBackedBatchLifetimeSoundness.failure_iff SourceMemory dummy source sourceOrigin sourceRadius _ id _ world).mpr rebased)

theorem prelude_bound {S A : Type} (HelperMemory SourceMemory : Type) (dummy : Digest)
    (helper : HelperContext) (helperOrigin : CacheBackedSingleOpening.Origin helper)
    (source : SourceContext) (sourceOrigin : CacheBackedCodeOrigin.Origin source) (helperRadius sourceRadius : ℕ)
    (helperWidth : 3 ≤ helper.parameters.width.val) (sourceWidth : 3 ≤ source.parameters.width.val)
    (prelude : Program S) (step : S → OracleMachine.Command S A)
    (helperSmall : 3*helperRadius < helper.parameters.code.blocks.val-helper.parameters.code.messageBlocks.val+1)
    (sourceSmall : 3*sourceRadius < source.parameters.code.blocks.val-source.parameters.code.messageBlocks.val+1) :
    law {world | Failure HelperMemory SourceMemory dummy helper source sourceOrigin helperRadius sourceRadius (run prelude) id step world} ≤
      (⨆ fuel : ℕ, NativeRootFamilyLifetime.prefixCharge dummy (.pure prelude) (OracleMachinePrelude.prepend step) fuel) +
      (SingleOpeningLifetimeSoundness.exposureCharge (SingleOpeningLifetimeSoundness.clean prelude) id dummy helper helperOrigin helperRadius (OracleMachinePrelude.prepend step) +
        NativeGoldBatchLifetimeSoundness.exposureCharge (SingleOpeningLifetimeSoundness.clean prelude) id dummy source (sourceOrigin.primitiveAt source rfl) sourceRadius (OracleMachinePrelude.prepend step)) := by
  have included : {world | Failure HelperMemory SourceMemory dummy helper source sourceOrigin helperRadius sourceRadius (run prelude) id step world} ⊆
      {world | Failure HelperMemory SourceMemory dummy helper source sourceOrigin helperRadius sourceRadius
        (SingleOpeningLifetimeSoundness.clean prelude) id (OracleMachinePrelude.prepend step) world} :=
    fun world failed => failure_rebase HelperMemory SourceMemory dummy helper source sourceOrigin helperRadius sourceRadius prelude step world failed
  exact (measure_mono included).trans (initialised_bound HelperMemory SourceMemory dummy helper helperOrigin source sourceOrigin helperRadius sourceRadius
    helperWidth sourceWidth prelude (OracleMachinePrelude.prepend step) helperSmall sourceSmall)

end
end FormalProof4FHE.HasteBoots.SharedNativeOpeningLifetime
