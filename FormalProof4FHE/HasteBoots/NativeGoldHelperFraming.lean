module

public import FormalProof4FHE.HasteBoots.NativeGoldPcsTranscriptExtension
public import FormalProof4FHE.HasteBoots.NativeGoldHelperVerification
public import FormalProof4FHE.HasteBoots.NativeGoldLookupVerification
@[expose] public section

/-! Ordered helper verification retains framed ancestry of the last accepted
transcript, including a later stopped helper. The initial lookup-body parent
and original helper message bounds remain explicit upstream obligations. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldHelperFraming
open NativeGoldHelperVerification (Progress Result Trace)
open NativeSharedLookupHelpers (Call)
open NativeGoldPcsOpening (Opening)
open NativeGoldBlockCode (Tables Stored)
open NativeBrakedownContext (Parameters)
open NativeGoldPcsProgram (Scheduler)
open NativeTranscript (Transcript)
open NativeTranscriptExtension (Extends)
open NativeTranscriptFraming (Framed)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

def CallFits (call : Call Opening) : Prop :=
  (NativeGoldPcsWire.opening call.root call.query call.values).length < TranscriptFrame.lengthLimit ∧
  (NativeGoldPcsWire.responses call.opening.test call.opening.evaluation).length < TranscriptFrame.lengthLimit

def Domain (calls : List (Call Opening)) : Prop := ∀ call ∈ calls, CallFits call

theorem trace_extension {Memory : Type} {tables : Tables} {parameters : Parameters Stored} {fieldFuel : ℕ}
    {choose : Scheduler Memory} {workerFuel : ℕ} {world : World} {calls : List (Call Opening)}
    {before : Progress Memory} {result : Result Memory} {log : List NativeTranscript.Observation}
    (trace : Trace tables parameters fieldFuel choose workerFuel world calls before result log)
    (domain : Domain calls) : Extends before.lastAccepted result.progress.lastAccepted := by
  revert domain
  induction trace with
  | done before => intro _; exact Extends.refl _
  | stopped before call rest outcome log executed stopped => intro _; exact Extends.refl _
  | passed before after call rest outcome log result later executed advanced tail ih =>
    intro domain
    obtain ⟨work,completion,next,sameOutcome,accepted,sameAfter⟩ :=
      NativeGoldHelperVerification.advance_spec before call outcome after advanced
    have completed : (run (NativeGoldPcsProgram.program (NativeGoldHelperVerification.context tables parameters fieldFuel before.lastAccepted call)
        choose workerFuel before.memory) world).run.1 = .completed work completion :=
      (congrArg Prod.fst executed).trans sameOutcome
    have extension := NativeGoldPcsTranscriptExtension.accepted
      (NativeGoldHelperVerification.context tables parameters fieldFuel before.lastAccepted call) choose workerFuel before.memory world
      work completion completed next accepted (domain call (by simp))
    have afterExtension : Extends before.lastAccepted after.lastAccepted := by
      rw [sameAfter]
      exact extension
    exact afterExtension.trans (ih (fun selected member => domain selected (List.mem_cons_of_mem call member)))

theorem loop_extension {Memory : Type} (tables : Tables) (parameters : Parameters Stored) (fieldFuel : ℕ)
    (choose : Scheduler Memory) (workerFuel : ℕ) (calls : List (Call Opening)) (before : Progress Memory) (world : World)
    (domain : Domain calls) : Extends before.lastAccepted
      (run (NativeGoldHelperVerification.loop tables parameters fieldFuel choose workerFuel calls before) world).run.1.progress.lastAccepted :=
  trace_extension (NativeGoldHelperVerification.loop_trace tables parameters fieldFuel choose workerFuel calls before world) domain

theorem loop_framed {Memory : Type} (tables : Tables) (parameters : Parameters Stored) (fieldFuel : ℕ)
    (choose : Scheduler Memory) (workerFuel : ℕ) (calls : List (Call Opening)) (before : Progress Memory) (world : World)
    (framed : Framed before.lastAccepted) (domain : Domain calls) : Framed
      (run (NativeGoldHelperVerification.loop tables parameters fieldFuel choose workerFuel calls before) world).run.1.progress.lastAccepted :=
  NativeTranscriptFraming.of_extension framed (loop_extension tables parameters fieldFuel choose workerFuel calls before world domain)

theorem program_framed {B Memory : Type} (ctx : NativeGoldHelperVerification.Context B) (choose : Scheduler Memory)
    (memory : Memory) (world : World) (body : NativeSharedLookupBody.Bound) (plan : NativeSharedLookupHelpers.Plan Opening)
    (status : Result Memory)
    (executed : (run (NativeGoldHelperVerification.program ctx choose memory) world).run.1 = .helpers body plan status)
    (framed : Framed body.parent) (domain : Domain plan.calls) : Framed status.progress.lastAccepted := by
  have origin := NativeGoldHelperVerification.helpers_origin ctx choose memory world body plan status executed
  rw [← origin.helpers]
  exact loop_framed ctx.tables ctx.helper ctx.fieldFuel choose ctx.workerFuel plan.calls ⟨body.parent,memory,[]⟩ world framed domain

theorem prepared_framed {Memory : Type}
    (ctx : NativeGoldHelperVerification.Context (NativePrefixCodec.Vector NativeGoldBatchOpening.Opening))
    (choose : Scheduler Memory) (memory : Memory) (world : World) (prepared : NativeGoldLookupVerification.Prepared Memory)
    (executed : NativeGoldLookupVerification.prepare (run (NativeRegisteredLookup.helpers ctx choose memory) world).run.1 = some prepared)
    (framed : Framed prepared.body.parent) (domain : Domain prepared.plan.calls) : Framed prepared.helpers.lastAccepted := by
  have same := (NativeGoldLookupVerification.prepare_spec _ prepared executed).1
  have erased := congrArg Prod.fst (NativeRegisteredLookup.helpers_erasure ctx choose memory world)
  have native : (run (NativeGoldHelperVerification.program ctx choose memory) world).run.1 =
      .helpers prepared.body prepared.plan (.done prepared.helpers) := by
    rw [← erased, same]
  exact program_framed ctx choose memory world prepared.body prepared.plan (.done prepared.helpers) native framed domain
end
end FormalProof4FHE.HasteBoots.NativeGoldHelperFraming
