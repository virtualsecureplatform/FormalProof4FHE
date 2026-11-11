module
public import FormalProof4FHE.HasteBoots.RegistryPublicSource
public import FormalProof4FHE.HasteBoots.LookupSourceParameterAssociation
public import FormalProof4FHE.HasteBoots.SourceOpeningObligationLifetime
@[expose] public section

/-! Every used original source in an accepted native lookup reaches an
accepted original batch pair whose analysis table equals the public cube of
that source's actual allocated registry object, outside the same hash bad
event. Aliases and both constructor provenances remain original data. -/
namespace FormalProof4FHE.HasteBoots.LookupSourcePublicOwnership
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldParameterStore (Entry Reference)
open NativeDeferredBatchVerification (Receipt Progress)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

variable {Memory : Type} (ctx : Context (Vector Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (lookup : NativeGoldLookupVerification.Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (after : Progress Memory)
    (executed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase =
      .batches lookup progress (.verification (.done after)))
    (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (references : Vector Reference) (collected : NativeGoldParameterStore.registry entries references = some ctx.registry)
    (dummy : Digest) (history : List Observation)

/-- The first-original receipt owner retains its own allocation history. The
reference cube retains the original used slot's allocation history instead;
the statement never equates their requests or configurations. -/
def Owned (slot : Fin ctx.registry.val.length) : Prop :=
  ∃ (receipt : Receipt Memory) (member : receipt ∈ after.receipts),
    LookupSourceParameterAssociation.Associated ctx lookup after slot receipt ∧
    let candidate := receipt.call.context ctx.tables ctx.fieldFuel receipt.before
    let original := RegistryPublicSource.context ctx slot
    let candidateOrigin := RegistryBatchCodeOrigin.ofReceipt ctx chooseHelper chooseBatch memory world lookup progress (.done after)
      executed receipt member entries reachable references collected
    let prepared := SourceOpeningObligationLifetime.preparation ctx chooseHelper chooseBatch memory world lookup progress (.done after)
      executed receipt member
    ∃ sizes : GoldHistorySourceTable.Geometry original.parameters,
      RegistryPublicSource.Compatible candidate original candidateOrigin
        (RegistryPublicSource.origin ctx entries reachable references collected slot) world receipt.work prepared dummy history sizes

variable (truthful : ObservationReplay.Agrees world history)
    (observed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.2.Sublist history)
include truthful observed

theorem source_no_bad (slot : Fin ctx.registry.val.length) (used : NativeSharedSourceClaims.used ctx.requests slot = true)
    (noBad : ¬NativeRootFamilyLifetime.Bad dummy history) :
    Owned ctx chooseHelper chooseBatch memory world lookup progress after executed entries reachable references collected dummy history slot := by
  obtain ⟨receipt,associated⟩ := LookupSourceParameterAssociation.associated_no_bad ctx chooseHelper chooseBatch memory world lookup progress after
    executed slot used dummy history truthful observed noBad
  refine ⟨receipt,associated.1,associated,?_⟩
  let candidate := receipt.call.context ctx.tables ctx.fieldFuel receipt.before
  let original := RegistryPublicSource.context ctx slot
  have parameters : candidate.parameters = original.parameters := associated.2.1
  have root : candidate.root = original.root := associated.2.2.1
  let prepared := SourceOpeningObligationLifetime.preparation ctx chooseHelper chooseBatch memory world lookup progress (.done after)
    executed receipt associated.1
  exact ⟨RegistryPublicSource.geometry candidate original parameters world receipt.work prepared,
    RegistryPublicSource.compatible candidate original _ _ parameters root world receipt.work prepared dummy history⟩

theorem source_or_bad (slot : Fin ctx.registry.val.length) (used : NativeSharedSourceClaims.used ctx.requests slot = true) :
    Owned ctx chooseHelper chooseBatch memory world lookup progress after executed entries reachable references collected dummy history slot ∨
      NativeRootFamilyLifetime.Bad dummy history := by
  by_cases bad : NativeRootFamilyLifetime.Bad dummy history
  · exact Or.inr bad
  · exact Or.inl (source_no_bad ctx chooseHelper chooseBatch memory world lookup progress after executed entries reachable references collected
      dummy history truthful observed slot used bad)

/-- All original used slots, including later aliases, share one bad event.
There is no per-slot or per-alias collision union in this coverage theorem. -/
theorem all_sources_or_bad :
    (∀ slot : Fin ctx.registry.val.length, NativeSharedSourceClaims.used ctx.requests slot = true →
      Owned ctx chooseHelper chooseBatch memory world lookup progress after executed entries reachable references collected dummy history slot) ∨
      NativeRootFamilyLifetime.Bad dummy history := by
  by_cases bad : NativeRootFamilyLifetime.Bad dummy history
  · exact Or.inr bad
  · exact Or.inl (fun slot used => source_no_bad ctx chooseHelper chooseBatch memory world lookup progress after executed entries reachable references collected
      dummy history truthful observed slot used bad)

end
end FormalProof4FHE.HasteBoots.LookupSourcePublicOwnership
