module

public import FormalProof4FHE.HasteBoots.NativeGoldLookupSourceInvariant
@[expose] public section

/-! Whole typed lookup execution excludes the source and dispatch auxiliary
domains in every phase, including rejected source prefixes. PCS internal
domains, strict decoding and native/work refinement remain separate. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldLookupProgramDomain
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open NativeGoldLookupVerification (Prepared sourceProgram)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

def PhaseAvailable {Memory : Type} : NativeGoldLookupVerification.Phase Memory → Prop
  | .prior => True
  | .sourceClaims _ result => NativeSourceClaimDomain.Available result
  | .batches _ _ result => NativeDeferredBatchDomain.OutcomeAvailable result

theorem program_available {Memory : Type} (ctx : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory) (world : World) :
    PhaseAvailable (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase := by
  simp only [NativeGoldLookupVerification.program,OracleProgram.run_bind,ObservationReplay.run_bind]
  unfold NativeGoldLookupVerification.continuation
  cases selected : NativeGoldLookupVerification.prepare (run (NativeRegisteredLookup.helpers ctx chooseHelper memory) world).run.1 with
  | none => trivial
  | some prepared =>
    simp only [OracleProgram.run_bind,ObservationReplay.run_bind]
    have available := NativeGoldLookupSourceInvariant.source_available ctx chooseHelper memory world prepared selected
    cases collected : (run (sourceProgram ctx prepared) world).run.1 with
    | stopped progress reason =>
      simp only [NativeGoldLookupVerification.continueSources,
        OracleProgram.run,CanonicalTranscriptSampler.run_pure,PhaseAvailable]
      simpa only [collected] using available
    | done progress =>
      simp only [NativeGoldLookupVerification.continueSources,OracleProgram.run_bind,ObservationReplay.run_bind,
        OracleProgram.run,CanonicalTranscriptSampler.run_pure,PhaseAvailable]
      have keys := NativeGoldLookupVerification.source_registry ctx prepared world
      rw [collected] at keys
      change progress.state.sources = prepared.metadata.sources at keys
      have corresponding := NativeGoldLookupSourceInvariant.prepared_registry ctx chooseHelper memory world prepared selected
      have sources : progress.state.sources.val.length = ctx.registry.val.length := by
        rw [keys]
        exact corresponding.length_eq.symm
      exact NativeDeferredBatchDomain.program_available (NativeGoldLookupVerification.batchContext ctx progress) chooseBatch prepared.helpers.memory world sources
end
end FormalProof4FHE.HasteBoots.NativeGoldLookupProgramDomain
