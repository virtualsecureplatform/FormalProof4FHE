module

public import FormalProof4FHE.HasteBoots.NativeRegisteredLookup
public import FormalProof4FHE.HasteBoots.NativeSharedSourceClaims
public import FormalProof4FHE.HasteBoots.NativeDeferredBatchVerification
@[expose] public section

/-! Typed Goldilocks lookup execution through deferred source batches.
Original registry metadata and post-helper memory/transcript are retained.
This is operational composition; application soundness, reachable allocation
domains, decoding and native/work refinement remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldLookupVerification
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open InputIndexedOracle (World)
open OracleProgram (Program bind run)
noncomputable section
structure Prepared (Memory : Type) where
  body : NativeSharedLookupBody.Bound
  plan : NativeSharedLookupHelpers.Plan NativeGoldPcsOpening.Opening
  helpers : NativeGoldHelperVerification.Progress Memory
  metadata : NativeSourceRegistry.Initialized
  query : NativeGoldPcsWire.Query

def prepare {Memory : Type} :
    NativeGoldHelperVerification.Outcome Memory × Option NativeSourceRegistry.Initialized → Option (Prepared Memory)
  | (.helpers body plan (.done progress),some metadata) =>
    (NativeGoldPcsWire.fromPairs body.terminal.pulled.pairs).map (fun query => ⟨body,plan,progress,metadata,query⟩)
  | _ => none

def initial {Memory : Type} (prepared : Prepared Memory) : NativeDeferredOpeningBatch.State :=
  {NativeDeferredOpeningBatch.initial prepared.metadata with parent := prepared.helpers.lastAccepted}

def sourceProgram {Memory : Type} (ctx : Context (Vector Opening)) (prepared : Prepared Memory) : Program NativeSharedSourceClaims.Result :=
  NativeSharedSourceClaims.program NativeGoldBlockCode.description.row ctx.registry ctx.requests prepared.query ctx.proof.sources (initial prepared)

def batchContext (ctx : Context (Vector Opening)) (progress : NativeSharedSourceClaims.Progress) : NativeDeferredBatchVerification.Context :=
  ⟨ctx.tables,ctx.registry,progress.state,ctx.proof.sourceOpening,ctx.fieldFuel,ctx.workerFuel⟩
inductive Phase (Memory : Type) where
  | prior
  | sourceClaims (prepared : Prepared Memory) (result : NativeSharedSourceClaims.Result)
  | batches (prepared : Prepared Memory) (progress : NativeSharedSourceClaims.Progress) (result : NativeDeferredBatchVerification.Outcome Memory)
structure Outcome (Memory : Type) where
  helpers : NativeGoldHelperVerification.Outcome Memory × Option NativeSourceRegistry.Initialized
  phase : Phase Memory

def continueSources {Memory : Type} (ctx : Context (Vector Opening)) (choose : NativeGoldBatchPcsProgram.Scheduler Memory)
    (prepared : Prepared Memory) : NativeSharedSourceClaims.Result → Program (Phase Memory)
  | .stopped progress reason => .pure (.sourceClaims prepared (.stopped progress reason))
  | .done progress => bind (NativeDeferredBatchVerification.program (batchContext ctx progress) choose prepared.helpers.memory)
      (fun outcome => .pure (.batches prepared progress outcome))

def continuation {Memory : Type} (ctx : Context (Vector Opening)) (choose : NativeGoldBatchPcsProgram.Scheduler Memory)
    (helpers : NativeGoldHelperVerification.Outcome Memory × Option NativeSourceRegistry.Initialized) : Program (Outcome Memory) :=
  match prepare helpers with
  | none => .pure ⟨helpers,.prior⟩
  | some prepared => bind (sourceProgram ctx prepared) (fun result =>
      bind (continueSources ctx choose prepared result) (fun phase => .pure ⟨helpers,phase⟩))

/-- One causal program: registered body and helpers, actual scalar source claims,
then sealed batches. Local representability failures remain explicit outcomes. -/
def program {Memory : Type} (ctx : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory) : Program (Outcome Memory) :=
  bind (NativeRegisteredLookup.helpers ctx chooseHelper memory) (continuation ctx chooseBatch)

theorem prepare_spec {Memory : Type}
    (helpers : NativeGoldHelperVerification.Outcome Memory × Option NativeSourceRegistry.Initialized)
    (prepared : Prepared Memory) (success : prepare helpers = some prepared) :
    helpers = (.helpers prepared.body prepared.plan (.done prepared.helpers),some prepared.metadata) ∧
      NativeGoldPcsWire.fromPairs prepared.body.terminal.pulled.pairs = some prepared.query := by
  rcases helpers with ⟨helpers,metadata⟩
  cases helpers with
  | prior packet => contradiction
  | helpers body plan status =>
    cases status with
    | stopped progress call outcome => contradiction
    | done progress =>
      cases metadata with
      | none => contradiction
      | some metadata =>
        obtain ⟨query,computed,same⟩ := Option.map_eq_some_iff.mp success
        subst prepared
        exact ⟨rfl,computed⟩

theorem prepared_metadata {Memory : Type} (ctx : Context (Vector Opening)) (choose : NativeGoldPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (prepared : Prepared Memory)
    (success : prepare (run (NativeRegisteredLookup.helpers ctx choose memory) world).run.1 = some prepared) :
    ∃ geometry, (run (NativeRegisteredLookup.prepare NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests) world).run.1.2 =
      some (geometry,prepared.metadata) := by
  have spec := (prepare_spec _ prepared success).1
  have upstream := congrArg Prod.fst spec
  have retained := congrArg Prod.snd spec
  obtain ⟨metadata,geometry,recorded,origin⟩ := NativeRegisteredLookup.helpers_metadata ctx choose memory world prepared.body prepared.plan (.done prepared.helpers) upstream
  rw [retained] at recorded
  cases Option.some.inj recorded
  exact ⟨geometry,origin⟩

theorem prepared_query {Memory : Type}
    (helpers : NativeGoldHelperVerification.Outcome Memory × Option NativeSourceRegistry.Initialized)
    (prepared : Prepared Memory) (success : prepare helpers = some prepared) :
    prepared.query.models = prepared.body.terminal.pulled.pairs :=
  NativeGoldPcsWire.fromPairs_spec _ _ (prepare_spec helpers prepared success).2

theorem program_helpers {Memory : Type} (ctx : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory) (world : World) :
    (run (NativeGoldHelperVerification.program ctx chooseHelper memory) world).run.2.Sublist
      (run (program ctx chooseHelper chooseBatch memory) world).run.2 := by
  have erased := congrArg Prod.snd (NativeRegisteredLookup.helpers_erasure ctx chooseHelper memory world)
  rw [← erased]
  simp only [program,OracleProgram.run_bind,ObservationReplay.run_bind]
  exact List.sublist_append_left _ _

theorem continuation_helpers {Memory : Type} (ctx : Context (Vector Opening)) (choose : NativeGoldBatchPcsProgram.Scheduler Memory)
    (helpers : NativeGoldHelperVerification.Outcome Memory × Option NativeSourceRegistry.Initialized) (world : World) :
    (run (continuation ctx choose helpers) world).run.1.helpers = helpers := by
  unfold continuation
  split
  · rfl
  · simp only [OracleProgram.run_bind,ObservationReplay.run_bind]
    cases (run (sourceProgram ctx _) world).run.1 with
    | stopped progress reason => rfl
    | done progress => rfl

theorem batches_origin {Memory : Type} (ctx : Context (Vector Opening)) (choose : NativeGoldBatchPcsProgram.Scheduler Memory)
    (helpers : NativeGoldHelperVerification.Outcome Memory × Option NativeSourceRegistry.Initialized) (world : World)
    (prepared : Prepared Memory) (progress : NativeSharedSourceClaims.Progress) (result : NativeDeferredBatchVerification.Outcome Memory)
    (executed : (run (continuation ctx choose helpers) world).run.1.phase = .batches prepared progress result) :
    prepare helpers = some prepared ∧ (run (sourceProgram ctx prepared) world).run.1 = .done progress ∧
      (run (NativeDeferredBatchVerification.program (batchContext ctx progress) choose prepared.helpers.memory) world).run.1 = result ∧
      (run (continuation ctx choose helpers) world).run.2 = (run (sourceProgram ctx prepared) world).run.2 ++
        (run (NativeDeferredBatchVerification.program (batchContext ctx progress) choose prepared.helpers.memory) world).run.2 := by
  simp only [continuation] at executed ⊢
  cases selected : prepare helpers with
  | none => simp only [selected,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed; contradiction
  | some original =>
    simp only [selected,OracleProgram.run_bind,ObservationReplay.run_bind] at executed ⊢
    cases collected : (run (sourceProgram ctx original) world).run.1 with
    | stopped previous reason =>
      simp only [collected,continueSources,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed
      contradiction
    | done previous =>
      simp only [collected,continueSources,OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed ⊢
      cases executed
      exact ⟨rfl,collected,rfl,by simp only [List.append_nil]⟩

theorem program_helpers_value {Memory : Type} (ctx : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory) (world : World) :
    (run (program ctx chooseHelper chooseBatch memory) world).run.1.helpers.1 =
      (run (NativeGoldHelperVerification.program ctx chooseHelper memory) world).run.1 := by
  simp only [program,OracleProgram.run_bind,ObservationReplay.run_bind]
  rw [continuation_helpers]
  exact congrArg Prod.fst (NativeRegisteredLookup.helpers_erasure ctx chooseHelper memory world)

theorem source_registry {Memory : Type} (ctx : Context (Vector Opening)) (prepared : Prepared Memory) (world : World) :
    (run (sourceProgram ctx prepared) world).run.1.progress.state.sources = prepared.metadata.sources :=
  NativeSharedSourceClaims.loop_sources NativeGoldBlockCode.description.row ctx.registry ctx.requests prepared.query ctx.proof.sources
    (List.finRange ctx.registry.val.length) ⟨initial prepared,[]⟩ world

theorem program_batches_origin {Memory : Type} (ctx : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory) (world : World)
    (prepared : Prepared Memory) (progress : NativeSharedSourceClaims.Progress) (result : NativeDeferredBatchVerification.Outcome Memory)
    (executed : (run (program ctx chooseHelper chooseBatch memory) world).run.1.phase = .batches prepared progress result) :
    prepare (run (NativeRegisteredLookup.helpers ctx chooseHelper memory) world).run.1 = some prepared ∧
      (run (sourceProgram ctx prepared) world).run.1 = .done progress ∧
      (run (NativeDeferredBatchVerification.program (batchContext ctx progress) chooseBatch prepared.helpers.memory) world).run.1 = result ∧
      (run (program ctx chooseHelper chooseBatch memory) world).run.2 =
        (run (NativeGoldHelperVerification.program ctx chooseHelper memory) world).run.2 ++
          ((run (sourceProgram ctx prepared) world).run.2 ++
            (run (NativeDeferredBatchVerification.program (batchContext ctx progress) chooseBatch prepared.helpers.memory) world).run.2) := by
  simp only [program,OracleProgram.run_bind,ObservationReplay.run_bind] at executed ⊢
  have origin := batches_origin ctx chooseBatch _ world prepared progress result executed
  refine ⟨origin.1,origin.2.1,origin.2.2.1,?_⟩
  rw [origin.2.2.2]
  rw [congrArg Prod.snd (NativeRegisteredLookup.helpers_erasure ctx chooseHelper memory world)]
end
end FormalProof4FHE.HasteBoots.NativeGoldLookupVerification
