module
public import FormalProof4FHE.HasteBoots.SingleOpeningRectangularAcceptance
public import FormalProof4FHE.HasteBoots.NativeFieldReceipt
@[expose] public section

/-! Exact native single-opening sampler lineage. The field binding, collector
state, completed receipt and atomic column result are recovered from the same
checked column prefix. These are analysis outputs, never verifier certificates. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningSamplingReceipt
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open NativeGoldBlockCode (description)
open NativeTranscript (Transcript Observation)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

structure Receipt (ctx : Context) (world : World) (work : Prepared) (sample : NativeIndexRequest.Result) where
  bound : Transcript
  state : NativeFieldVector.State
  next : Transcript
  columns : (run (NativeGoldPcsColumns.protocol description ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed ctx.opening ctx.fieldFuel) world).run.1 =
    .columns work.geometry state work.structured sample
  prelude : (run (NativeGoldPcsPrelude.protocol description ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed ctx.opening ctx.fieldFuel) world).run.1 =
    .sampling work.geometry (.finished state next)
  binding : (run (NativeGoldPcsBinding.protocol description.row ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed) world).run.1 = some bound
  field : (run (NativePrimeRequest.request NativeFields.goldilocksModulus ctx.fieldFuel bound .vector NativeGoldPcsPrelude.randomLabel work.geometry.randomCount) world).run.1 =
    .finished state next
  drawn : (run (NativeIndexRequest.request (NativeGoldPcsWire.bindResponses next ctx.opening.test ctx.opening.evaluation)
    NativeGoldPcsColumns.label ctx.parameters.code.blocks ctx.parameters.queries) world).run.1 = some sample
  random : work.random = NativeGoldPcsColumns.random state
  transcript : work.transcript = sample.transcript

/-- The exact sample already retained by a native rectangular view gets its
actual collector and receipt, rather than an arbitrary equal draw list. -/
theorem ofSampled (ctx : Context) (world : World) (work : Prepared) (sample : NativeIndexRequest.Result)
    (sampled : SingleOpeningRectangularChecks.Sampled ctx world work sample) : Nonempty (Receipt ctx world work sample) := by
  obtain ⟨state,columns,random,transcript⟩ := sampled
  obtain ⟨next,prelude,_,drawn,_⟩ := NativeGoldPcsColumns.columns_origin description ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed
    ctx.opening ctx.fieldFuel world work.geometry state work.structured sample columns
  obtain ⟨_,_,bound,binding,field⟩ := NativeGoldPcsPrelude.sampling_origin description ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed
    ctx.opening ctx.fieldFuel world work.geometry (.finished state next) prelude
  exact ⟨⟨bound,state,next,columns,prelude,binding,field,drawn,random,transcript⟩⟩

theorem ofPreparation (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) : ∃ sample, Nonempty (Receipt ctx world work sample) := by
  obtain ⟨geometry,state,weights,sample,planRoot,test,evaluation,jobs,encoded,_,workEq⟩ :=
    NativeGoldPcsWorkers.prepared_origin ctx.tables ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed ctx.opening ctx.fieldFuel world work prepared
  have original := (NativeGoldPcsEncoding.encoded_origin ctx.tables ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed
    ctx.opening ctx.fieldFuel world geometry state weights sample planRoot test evaluation encoded).1
  refine ⟨sample,ofSampled ctx world work sample ⟨state,?_,?_,?_⟩⟩
  · rw [workEq]; exact original
  · rw [workEq]
  · rw [workEq]

namespace Receipt
variable {ctx : Context} {world : World} {work : Prepared} {sample : NativeIndexRequest.Result}

def parent (receipt : Receipt ctx world work sample) (other : World) : Transcript :=
  (NativeTranscript.finishField other receipt.state.phase).run.1

theorem finished_parent (receipt : Receipt ctx world work sample) : receipt.next = receipt.parent world := by
  obtain ⟨_,_,actual,_⟩ := NativeFieldReceipt.finished_origin NativeFields.goldilocksModulus ctx.fieldFuel work.geometry.randomCount.val
    (NativePrimeRequest.prepare receipt.bound .vector) NativeGoldPcsPrelude.randomLabel world receipt.state receipt.next receipt.field
  exact actual

/-- The request immediately following this same completed collector binds the
original test and evaluation rows, with the original single-opening label. -/
theorem column_request (receipt : Receipt ctx world work sample) :
    (run (NativeIndexRequest.request (NativeGoldPcsWire.bindResponses (receipt.parent world) ctx.opening.test ctx.opening.evaluation)
      NativeGoldPcsColumns.label ctx.parameters.code.blocks ctx.parameters.queries) world).run.1 = some sample := by
  rw [← receipt.finished_parent]
  exact receipt.drawn

/-- Recorded receipt bytes assembled by any prior split reads fix the parent
on the entire replay fiber. No unknown receipt coordinate is refreshed. -/
theorem parent_on_fiber {P : Type} {past : World → NativeTranscript.Execution P}
    (replay : ObservationReplay.Replayable past) (receipt : Receipt ctx world work sample) (other : World)
    (known : NativeFieldReceipt.Known (past world).run.2 receipt.state.phase)
    (fiber : (past other).run = (past world).run) : receipt.parent other = receipt.parent world :=
  NativeFieldReceipt.transcript_on_fiber_of_known replay world other receipt.state.phase known fiber

end Receipt
end
end FormalProof4FHE.HasteBoots.SingleOpeningSamplingReceipt
