module
public import FormalProof4FHE.HasteBoots.SingleOpeningFinishing
public import FormalProof4FHE.HasteBoots.SingleHelperNativeValue
public import FormalProof4FHE.HasteBoots.NativeGoldParameterInitialization
public import FormalProof4FHE.HasteBoots.NativeGoldHelperVerification
@[expose] public section

/-! Original allocated code provenance and deterministic finishing for the
native single-opening helper verifier. Constructor, primitive-root and capacity
facts follow from completed reachable allocation. Authentication, extraction and
production lifetime probability still need composition. -/
namespace FormalProof4FHE.HasteBoots.CacheBackedSingleOpening
open NativeGoldPcsExecution (Context)
open NativeGoldBlockCodeProgram (Request Config Completed)
open NativeGoldPcsWorkers (Prepared)
open NativeGoldBlockCode (logSize)
open NativeFieldRepresentation (goldValue)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

structure Origin (ctx : Context) where
  request : Request
  config : Config
  reachable : NativeGoldBlockCodeProgram.Reachable request config
  result : Completed
  finished : config.phase = .done result
  retained : result.code = ctx.parameters.code

namespace Origin
variable {ctx : Context} (origin : Origin ctx)
include origin

def tables : NativeGoldBlockCode.Tables :=
  NativeGoldBlockCodeBackend.observations origin.config.cache
    (NativeGoldBlockCodeProgram.reachable_good origin.request origin.config origin.reachable).1

theorem constructed : NativeGoldBlockCode.build origin.tables origin.request.message origin.request.block origin.request.blowup =
    .ok ctx.parameters.code := by
  have built := NativeGoldBlockCodeBackend.completed_build origin.request origin.config origin.reachable origin.result origin.finished
  rw [origin.retained] at built
  exact built

theorem primitive : IsPrimitiveRoot (goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)) := by
  rw [← origin.retained]
  exact NativeGoldBlockCodeBackend.completed_primitive origin.request origin.config origin.reachable origin.result origin.finished

theorem capacity : ctx.parameters.code.messageLength.val ≤
    ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val :=
  (NativeGoldBlockCodeMeaning.constructor_dimensions origin.tables origin.request.message origin.request.block origin.request.blowup
    ctx.parameters.code origin.constructed).2.2.1

theorem accepted_finishes {Memory : Type} (choose : NativeGoldPcsProgram.Scheduler Memory)
    (fuel : ℕ) (memory : Memory) (world : World) (work : Prepared)
    (completion : NativeGoldPcsAcceptance.Completion Memory work.jobs.length)
    (executed : (run (NativeGoldPcsProgram.program ctx choose fuel memory) world).run.1 = .completed work completion)
    (parent : NativeTranscript.Transcript) (accepted : completion.status = .accepted parent) :
    SingleOpeningFinishing.Finishes ctx work origin.primitive origin.capacity :=
  SingleOpeningFinishing.accepted_finishes ctx choose fuel memory world work completion executed parent accepted
    origin.tables origin.request.message origin.request.block origin.request.blowup origin.constructed origin.primitive

/-- A single accepted original helper packet also enforces the matched sum
value, at the level of fields. Raw duplicate encodings are preserved. -/
theorem matched_sum_finishes {Memory : Type} (choose : NativeGoldPcsProgram.Scheduler Memory)
    (fuel : ℕ) (memory : Memory) (world : World) (work : Prepared)
    (completion : NativeGoldPcsAcceptance.Completion Memory work.jobs.length)
    (executed : (run (NativeGoldPcsProgram.program ctx choose fuel memory) world).run.1 = .completed work completion)
    (parent : NativeTranscript.Transcript) (accepted : completion.status = .accepted parent)
    (sum helper : NativeFieldWire.GoldExtension)
    (received : ctx.claimed = NativeSharedLookupHelpers.vector ctx.parameters.width helper)
    (matched : NativeGoldInterpolation.equal sum helper = true) :
    SingleOpeningFinishing.FinishesAs ctx work origin.primitive origin.capacity
      ((NativeGoldHelper.vector ctx.parameters.width.val sum).map goldValue) := by
  apply SingleOpeningFinishing.finishes_as ctx work origin.primitive origin.capacity
    (origin.accepted_finishes choose fuel memory world work completion executed parent accepted)
  rw [received,NativeSharedLookupHelpers.vector_raw]
  exact SingleHelperNativeValue.matched_vector ctx.parameters.width.val sum helper matched

/-- A successful native terminal guard supplies the matched sum. Source guard
width and physical helper packing width remain independent. -/
theorem guarded_sum_finishes {Memory : Type} (choose : NativeGoldPcsProgram.Scheduler Memory)
    (fuel : ℕ) (memory : Memory) (world : World) (work : Prepared)
    (completion : NativeGoldPcsAcceptance.Completion Memory work.jobs.length)
    (executed : (run (NativeGoldPcsProgram.program ctx choose fuel memory) world).run.1 = .completed work completion)
    (parent : NativeTranscript.Transcript) (accepted : completion.status = .accepted parent)
    (inputs : NativeSharedLookupGuard.Inputs) (claims : List NativeScalarBatchVerifier.SubClaim)
    (sourceVars guardWidth : ℕ) (result : NativeSharedLookupGuard.Result)
    (guarded : NativeSharedLookupGuard.guard inputs claims sourceVars guardWidth = some result)
    (checked : NativeSharedLookupGuard.Checked) (member : checked ∈ result.checked)
    (received : ctx.claimed = NativeSharedLookupHelpers.vector ctx.parameters.width checked.helper) :
    SingleOpeningFinishing.FinishesAs ctx work origin.primitive origin.capacity
      ((NativeGoldHelper.vector ctx.parameters.width.val checked.sumClaim.expected).map goldValue) :=
  origin.matched_sum_finishes choose fuel memory world work completion executed parent accepted
    checked.sumClaim.expected checked.helper received
    ((NativeSharedLookupGuard.guard_spec inputs claims sourceVars guardWidth result guarded).checked checked member).matched

end Origin

/-- Keep the constructor request/configuration of the actual successful
initializer. Its retained code identity is a derived conclusion. -/
def ofInitialization (header : NativeGoldEncodedParameters.Header) (request : Request) (config : Config)
    (reachable : NativeGoldBlockCodeProgram.Reachable request config) (initialized : NativeGoldEncodedParameters.Initialized)
    (executed : NativeGoldParameterInitialization.finish header config = some (.ok initialized))
    (ctx : Context) (same : ctx.parameters = initialized.parameters) : Origin ctx :=
  let produced := NativeGoldParameterInitialization.code_origin header request config reachable initialized executed
  { request := request
    config := config
    reachable := reachable
    result := Classical.choose produced
    finished := (Classical.choose_spec produced).1
    retained := (Classical.choose_spec produced).2.1.symm.trans (congrArg (fun parameters => parameters.code) same.symm) }

theorem initialization_data (header : NativeGoldEncodedParameters.Header) (request : Request) (config : Config)
    (reachable : NativeGoldBlockCodeProgram.Reachable request config) (initialized : NativeGoldEncodedParameters.Initialized)
    (executed : NativeGoldParameterInitialization.finish header config = some (.ok initialized))
    (ctx : Context) (same : ctx.parameters = initialized.parameters) :
    (ofInitialization header request config reachable initialized executed ctx same).request = request ∧
      (ofInitialization header request config reachable initialized executed ctx same).config = config := ⟨rfl,rfl⟩

/-- Every accepted receipt, including those before a later helper stops, finishes
in the retained allocated code's domain. No per-receipt acceptance or encoding
certificate is assumed; the original ordered verifier supplies it. -/
theorem helper_receipt_finishes {B Memory : Type} (ctx : NativeGoldHelperVerification.Context B)
    (choose : NativeGoldPcsProgram.Scheduler Memory) (memory : Memory) (world : World)
    (bound : NativeSharedLookupBody.Bound) (plan : NativeSharedLookupHelpers.Plan NativeGoldPcsOpening.Opening)
    (status : NativeGoldHelperVerification.Result Memory)
    (executed : (run (NativeGoldHelperVerification.program ctx choose memory) world).run.1 = .helpers bound plan status)
    (header : NativeGoldEncodedParameters.Header) (request : Request) (config : Config)
    (reachable : NativeGoldBlockCodeProgram.Reachable request config) (initialized : NativeGoldEncodedParameters.Initialized)
    (allocated : NativeGoldParameterInitialization.finish header config = some (.ok initialized))
    (same : ctx.helper = initialized.parameters)
    (receipt : NativeGoldHelperVerification.Receipt Memory) (member : receipt ∈ status.progress.receipts) :
    ∃ origin : Origin (NativeGoldHelperVerification.context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call),
      origin.request = request ∧ origin.config = config ∧
      SingleOpeningFinishing.Finishes _ receipt.work origin.primitive origin.capacity := by
  let origin := ofInitialization header request config reachable initialized allocated
    (NativeGoldHelperVerification.context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call) same
  have checked := (NativeGoldHelperVerification.helpers_receipts ctx choose memory world bound plan status executed receipt member).1
  exact ⟨origin,rfl,rfl,origin.accepted_finishes choose ctx.workerFuel receipt.memory world receipt.work receipt.completion
    checked.1 receipt.after checked.2⟩

end
end FormalProof4FHE.HasteBoots.CacheBackedSingleOpening
