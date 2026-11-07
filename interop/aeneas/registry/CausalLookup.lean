/-! Causal source decoding and actual modeled dispatcher execution share one
history. No caller registry-correspondence or trace-inclusion certificate is
required. Native dispatcher/heap/physical-work refinement remains open. -/
namespace HasteBootsExtractedRegistryCausalLookup
open Aeneas Aeneas.Std Result
open FormalProof4FHE.HasteBoots
open HasteBootsExtractedRegistryDecode (Source)
open HasteBootsExtractedRegistry (registry)
open InputIndexedOracle (World)
open OracleProgram (Program bind run)
noncomputable section

abbrev Context := NativeGoldHelperVerification.Context (NativePrefixCodec.Vector NativeGoldBatchOpening.Opening)
abbrev Ready (Memory : Type) := Context × NativeGoldLookupVerification.Outcome Memory

structure Setup (Memory : Type) where
  source : Slice Source
  context : Context
  memory : Memory

abbrev State (Memory : Type) := Setup Memory × Option (Ready Memory)

def dispatch {Memory : Type} (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (setup : Setup Memory) : Program (Option (Ready Memory)) :=
  match registry setup.source with
  | none => .pure none
  | some models =>
    let ctx := {setup.context with registry := models}
    bind (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch setup.memory)
      (fun outcome => .pure (some (ctx,outcome)))

def prelude {Memory : Type} (prior : Program (Setup Memory))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) : Program (State Memory) :=
  bind prior (fun setup => bind (dispatch chooseHelper chooseBatch setup) (fun result => .pure (setup,result)))

theorem dispatch_run {Memory : Type} (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (setup : Setup Memory) (world : World) :
    (run (dispatch chooseHelper chooseBatch setup) world).run =
      match registry setup.source with
      | none => (none,[])
      | some models =>
        let ctx := {setup.context with registry := models}
        let result := (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch setup.memory) world).run
        (some (ctx,result.1),result.2) := by
  cases decoded : registry setup.source <;>
    simp only [dispatch,decoded,OracleProgram.run_bind,ObservationReplay.run_bind,
      OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]

theorem dispatch_origin {Memory : Type} (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (setup : Setup Memory) (world : World)
    (ctx : Context) (outcome : NativeGoldLookupVerification.Outcome Memory)
    (executed : (run (dispatch chooseHelper chooseBatch setup) world).run.1 = some (ctx,outcome)) :
    registry setup.source = some ctx.registry ∧
      (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch setup.memory) world).run.1 = outcome ∧
      (run (dispatch chooseHelper chooseBatch setup) world).run.2 =
        (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch setup.memory) world).run.2 := by
  rw [dispatch_run] at executed
  cases decoded : registry setup.source with
  | none => simp only [decoded] at executed; cases executed
  | some models =>
    simp only [decoded] at executed
    have same := Prod.mk.inj (Option.some.inj executed)
    cases same.1
    exact ⟨rfl,same.2,by rw [dispatch_run,decoded]⟩

theorem prelude_run {Memory : Type} (prior : Program (Setup Memory))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (world : World) :
    (run (prelude prior chooseHelper chooseBatch) world).run =
      let setup := (run prior world).run.1
      let result := (run (dispatch chooseHelper chooseBatch setup) world).run
      ((setup,result.1),(run prior world).run.2 ++ result.2) := by
  simp only [prelude,OracleProgram.run_bind,ObservationReplay.run_bind,
    OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]

theorem prelude_origin {Memory : Type} (prior : Program (Setup Memory))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (world : World) (setup : Setup Memory) (ctx : Context) (outcome : NativeGoldLookupVerification.Outcome Memory)
    (executed : (run (prelude prior chooseHelper chooseBatch) world).run.1 = (setup,some (ctx,outcome))) :
    registry setup.source = some ctx.registry ∧
      (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch setup.memory) world).run.1 = outcome ∧
      (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch setup.memory) world).run.2.Sublist
        (run (prelude prior chooseHelper chooseBatch) world).run.2 := by
  rw [prelude_run] at executed
  have setupEq := congrArg Prod.fst executed
  have resultEq := congrArg Prod.snd executed
  dsimp only at setupEq resultEq
  rw [setupEq] at resultEq
  obtain ⟨decoded,dispatched,trace⟩ := dispatch_origin chooseHelper chooseBatch setup world ctx outcome resultEq
  refine ⟨decoded,dispatched,?_⟩
  rw [prelude_run]
  change (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch setup.memory) world).run.2.Sublist
    ((run prior world).run.2 ++ (run (dispatch chooseHelper chooseBatch ((run prior world).run.1)) world).run.2)
  rw [setupEq,trace]
  exact List.sublist_append_right _ _

theorem lookup_included {Memory A : Type} (prior : Program (Setup Memory))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (step : State Memory → OracleMachine.Command (State Memory) A) (fuel : ℕ)
    (world : World) (setup : Setup Memory) (ctx : Context) (outcome : NativeGoldLookupVerification.Outcome Memory)
    (executed : (run (prelude prior chooseHelper chooseBatch) world).run.1 = (setup,some (ctx,outcome))) :
    registry setup.source = some ctx.registry ∧
      (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch setup.memory) world).run.1 = outcome ∧
      (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch setup.memory) world).run.2.Sublist
        (run (NativeRootFamilyLifetime.program (prelude prior chooseHelper chooseBatch) step fuel) world).run.2 := by
  obtain ⟨decoded,dispatched,trace⟩ := prelude_origin prior chooseHelper chooseBatch world setup ctx outcome executed
  refine ⟨decoded,dispatched,trace.trans ?_⟩
  unfold NativeRootFamilyLifetime.program
  rw [OracleProgram.run_bind,ObservationReplay.run_bind]
  exact List.sublist_append_left _ _

theorem receipt_bad_or_original_read {Memory A : Type} (prior : Program (Setup Memory))
    (step : State Memory → OracleMachine.Command (State Memory) A) (fuel : ℕ)
    (setup : Setup Memory) (ctx : NativeGoldHelperVerification.Context (NativePrefixCodec.Vector NativeGoldBatchOpening.Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (world : World) (prepared : NativeGoldLookupVerification.Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (result : NativeDeferredBatchVerification.Result Memory)
    (outcome : NativeGoldLookupVerification.Outcome Memory)
    (started : (run (prelude prior chooseHelper chooseBatch) world).run.1 = (setup,some (ctx,outcome)))
    (phase : outcome.phase = .batches prepared progress (.verification result))
    (receipt : NativeDeferredBatchVerification.Receipt Memory) (member : receipt ∈ result.progress.receipts)
    (parentFramed : NativeTranscriptFraming.Framed ctx.parent)
    (bodyDomain : NativeLookupBodyFraming.Domain ctx.registry ctx.requests ctx.proof)
    (helperDomain : NativeGoldHelperFraming.Domain prepared.plan.calls)
    (sourceDomain : NativeSourceClaimFraming.Domain ctx.registry ctx.requests prepared.query ctx.proof.sources)
    (batchDomain : NativeDeferredBatchFraming.Domain (NativeGoldLookupVerification.batchContext ctx progress))
    (dummy : _root_.Vector InputIndexedOracle.Byte 64)
    (extractCtx : NativeGoldBatchPcsProgram.Context) (radius : ℕ) (output)
    (accepted : (ObservedGoldFieldExtraction.run (run (NativeRootFamilyLifetime.program (prelude prior chooseHelper chooseBatch) step fuel) world).run.2
      (NativeGoldBatchReadExposure.phase (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) receipt.work).pending.input
      dummy extractCtx radius).value = some output)
    : NativeRootFamilyLifetime.Bad dummy.get (run (NativeRootFamilyLifetime.program (prelude prior chooseHelper chooseBatch) step fuel) world).run.2 ∨
      (∃ (original : Fin ctx.registry.val.length) (word : Usize) (entry : Source),
      original.val = receipt.call.slot ∧ word.val = receipt.call.slot ∧
      formalproof4fhe_native_registry_fixture.registry_get setup.source word = .ok (some (entry.parameters,entry.commitment.root)) ∧
      HasteBootsExtractedRegistryDecode.decode entry = some receipt.call.oracle ∧
      HasteBootsExtractedParametersDecode.decodeParameters entry.parameters = some extractCtx.parameters ∧
      HasteBootsExtractedRegistryDecode.root entry.commitment.root = output.1.data.source.2.get) := by
  obtain ⟨decoded,dispatched,included⟩ := lookup_included prior chooseHelper chooseBatch step fuel world setup ctx outcome started
  have executed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch setup.memory) world).run.1.phase =
      .batches prepared progress (.verification result) := by rw [dispatched]; exact phase
  exact HasteBootsExtractedRegistryLookup.receipt_from_original_parent
    (NativeRootFamilyLifetime.program (prelude prior chooseHelper chooseBatch) step fuel) ctx chooseHelper chooseBatch setup.memory world
    prepared progress result executed receipt member parentFramed bodyDomain helperDomain sourceDomain batchDomain included dummy
    extractCtx radius output accepted setup.source decoded


def OriginalRead {Memory : Type} (source : Slice Source) (ctx : Context)
    (receipt : NativeDeferredBatchVerification.Receipt Memory) (extractCtx : NativeGoldBatchPcsProgram.Context)
    (expectedRoot : NativeRootMessage.Digest) : Prop :=
  ∃ (original : Fin ctx.registry.val.length) (word : Usize) (entry : Source),
    original.val = receipt.call.slot ∧ word.val = receipt.call.slot ∧
    formalproof4fhe_native_registry_fixture.registry_get source word = .ok (some (entry.parameters,entry.commitment.root)) ∧
    HasteBootsExtractedRegistryDecode.decode entry = some receipt.call.oracle ∧
    HasteBootsExtractedParametersDecode.decodeParameters entry.parameters = some extractCtx.parameters ∧
    HasteBootsExtractedRegistryDecode.root entry.commitment.root = expectedRoot

def Misassociation {Memory A : Type} (prior : Program (Setup Memory))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (step : State Memory → OracleMachine.Command (State Memory) A) (fuel : ℕ)
    (dummy : _root_.Vector InputIndexedOracle.Byte 64) (world : World) : Prop :=
  ∃ (setup : Setup Memory) (ctx : Context) (prepared : NativeGoldLookupVerification.Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (result : NativeDeferredBatchVerification.Result Memory)
    (receipt : NativeDeferredBatchVerification.Receipt Memory) (outcome : NativeGoldLookupVerification.Outcome Memory)
    (extractCtx : NativeGoldBatchPcsProgram.Context) (radius : ℕ), ∃ output,
    (run (prelude prior chooseHelper chooseBatch) world).run.1 = (setup,some (ctx,outcome)) ∧
    outcome.phase = .batches prepared progress (.verification result) ∧
    receipt ∈ result.progress.receipts ∧
    NativeTranscriptFraming.Framed ctx.parent ∧
    NativeLookupBodyFraming.Domain ctx.registry ctx.requests ctx.proof ∧
    NativeGoldHelperFraming.Domain prepared.plan.calls ∧
    NativeSourceClaimFraming.Domain ctx.registry ctx.requests prepared.query ctx.proof.sources ∧
    NativeDeferredBatchFraming.Domain (NativeGoldLookupVerification.batchContext ctx progress) ∧
    (ObservedGoldFieldExtraction.run
      (run (NativeRootFamilyLifetime.program (prelude prior chooseHelper chooseBatch) step fuel) world).run.2
      (NativeGoldBatchReadExposure.phase (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) receipt.work).pending.input
      dummy extractCtx radius).value = some output ∧
    ¬OriginalRead setup.source ctx receipt extractCtx output.1.data.source.2.get

theorem misassociation_bad {Memory A : Type} (prior : Program (Setup Memory))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (step : State Memory → OracleMachine.Command (State Memory) A) (fuel : ℕ)
    (dummy : _root_.Vector InputIndexedOracle.Byte 64) (world : World)
    (failed : Misassociation prior chooseHelper chooseBatch step fuel dummy world) :
    NativeRootFamilyLifetime.Bad dummy.get
      (run (NativeRootFamilyLifetime.program (prelude prior chooseHelper chooseBatch) step fuel) world).run.2 := by
  obtain ⟨setup,ctx,prepared,progress,result,receipt,outcome,extractCtx,radius,output,
    started,phase,member,parentFramed,bodyDomain,helperDomain,sourceDomain,batchDomain,accepted,missing⟩ := failed
  rcases receipt_bad_or_original_read prior step fuel setup ctx chooseHelper chooseBatch world prepared progress result
    outcome started phase receipt member parentFramed bodyDomain helperDomain sourceDomain batchDomain dummy extractCtx radius output accepted
    with bad | original
  · exact bad
  · exact False.elim (missing original)

theorem lifetime_misassociation_le_charge {Memory A : Type} (prior : Program (Setup Memory))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (step : State Memory → OracleMachine.Command (State Memory) A) (dummy : _root_.Vector InputIndexedOracle.Byte 64) :
    InputIndexedOracle.law {world | ∃ fuel, Misassociation prior chooseHelper chooseBatch step fuel dummy world} ≤
      ⨆ fuel : ℕ, NativeRootFamilyLifetime.prefixCharge dummy.get (prelude prior chooseHelper chooseBatch) step fuel := by
  apply le_trans (MeasureTheory.measure_mono ?_)
    (NativeRootFamilyLifetime.lifetime_bad_le_charge dummy.get (prelude prior chooseHelper chooseBatch) step)
  rintro world ⟨fuel,failed⟩
  exact ⟨fuel,misassociation_bad prior chooseHelper chooseBatch step fuel dummy world failed⟩

end
end HasteBootsExtractedRegistryCausalLookup
