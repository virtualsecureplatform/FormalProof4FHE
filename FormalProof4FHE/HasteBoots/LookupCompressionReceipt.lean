module
public import FormalProof4FHE.HasteBoots.LookupDrawReceiptBatch
public import FormalProof4FHE.HasteBoots.LookupDrawSeedQuote
public import FormalProof4FHE.HasteBoots.LookupProducedEndpoints
import all FormalProof4FHE.HasteBoots.NativeLookupChallenge
import all Init.Data.String.Defs
@[expose] public section

/-! The last compression-labeled receipt in any original reciprocal draw's
pending input belongs to that same job's first draw. Earlier job receipts and
arbitrarily many rejected offsets cannot replace it. -/
namespace FormalProof4FHE.HasteBoots.LookupCompressionReceipt
open InputIndexedOracle (Input World)
open ReceiptFrameView (frames frame)
open NativeLookupChallenge (hashLabel reciprocalLabel)
noncomputable section

def latest (input : Input) : Option TranscriptFrame.Frame :=
  ((frames input).filter (fun entry => entry.label = hashLabel)).getLast?

theorem member (input : Input) (entry : TranscriptFrame.Frame) (found : latest input = some entry) :
    entry ∈ frames input := by
  have present : entry ∈ ((frames input).filter (fun item => item.label = hashLabel)).getLast? := by
    change entry ∈ latest input
    rw [found]
    rfl
  exact List.mem_of_mem_filter (List.mem_of_mem_getLast? present)

theorem labels_distinct : reciprocalLabel ≠ hashLabel := by
  unfold reciprocalLabel hashLabel NativeTranscript.utf8
  decide +kernel

theorem tail_filter {K : Type} (world : World) (rest : List (NativeLookupChallenge.Draw K))
    (labels : ∀ draw ∈ rest, draw.coefficients.phase.label = reciprocalLabel) :
    (rest.map (fun draw => frame world draw.coefficients.phase)).filter (fun entry => entry.label = hashLabel) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro entry member
  obtain ⟨draw,present,rfl⟩ := List.mem_map.mp member
  simp [frame,labels draw present,labels_distinct]

theorem at_offset {K : Type} (world : World) (earlier : List TranscriptFrame.Frame)
    (first : NativeLookupChallenge.Draw K) (rest : List (NativeLookupChallenge.Draw K))
    (ordered : LookupDrawReceiptOrder.Before world earlier (first :: rest))
    (headLabel : first.coefficients.phase.label = hashLabel)
    (tailLabels : ∀ draw ∈ rest, draw.coefficients.phase.label = reciprocalLabel)
    (index : ℕ) (draw : NativeLookupChallenge.Draw K) (found : (first :: rest)[index]? = some draw)
    (positive : 0 < index) : latest draw.coefficients.phase.pending.input = some (frame world first.coefficients.phase) := by
  obtain ⟨index,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  have before := ordered (index+1) draw found
  simp only [List.take_succ_cons,List.map_cons] at before
  have filtered := tail_filter world (rest.take index) (fun draw present => tailLabels draw (List.mem_of_mem_take present))
  unfold latest
  rw [before,List.filter_append,List.filter_cons]
  have headCheck : (frame world first.coefficients.phase).label = hashLabel := headLabel
  simp only [headCheck,decide_true,ite_true,filtered]
  simp

open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
open OracleProgram (run)

theorem original {ctx : Context (Vector Opening)} {world : World} {body : NativeSharedLookupBody.Bound}
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world body) {index : Fin origin.ready.jobs.length}
    (job : LookupExecutionJob.Job origin index) :
    ∃ earlier, LookupDrawReceiptOrder.Traced world earlier job.view.producer.selection ∧
      LookupReceiptLabels.Labels job.view.producer.selection := by
  let transcript := LookupExecutionOrigin.childStart NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof world
  obtain ⟨suffix,valid,bytes⟩ := NativeForkAncestry.start_header world
    (run (NativeSharedLookupParent.prepare NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests) world).run.1.1
    ctx.proof.multiplicities
  have decoded := TranscriptFrame.decodeAll_encodeMany _ valid
  rw [← bytes] at decoded
  exact (LookupDrawReceiptBatch.initialized goldilocksBasis 7 ctx.lookupFuel
    (NativeLookupBatch.schedule ctx.requests.property.le (fun i => (NativeSharedLookupParent.models ctx.requests i).sampling))
    transcript world ⟨_,decoded⟩ (by decide +kernel)).2 _ job.producerMember

/-- The literal original last draw supplies its own first compression
receipt even after an arbitrary number of rejected offset trials. -/
theorem last {ctx : Context (Vector Opening)} {world : World} {body : NativeSharedLookupBody.Bound}
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world body) {index : Fin origin.ready.jobs.length}
    (job : LookupExecutionJob.Job origin index) :
    ∃ first last : NativeLookupChallenge.Draw Goldilocks3,
      job.view.producer.selection.draws.head? = some first ∧
      job.view.producer.selection.draws.getLast? = some last ∧
      NativeGoldLookupProducer.decode first.coefficients.values = some (origin.ready.jobs.get index).output.y ∧
      latest last.coefficients.phase.pending.input = some (frame world first.coefficients.phase) := by
  let transcript := LookupExecutionOrigin.childStart NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof world
  let actions := NativeLookupBatch.schedule ctx.requests.property.le (fun i => (NativeSharedLookupParent.models ctx.requests i).sampling)
  have terminal := ((NativeLookupBatch.execute_valid goldilocksBasis 7 ctx.lookupFuel _ world
    (NativeLookupBatch.initial_valid goldilocksBasis actions transcript)).2 _ job.producerMember).2
  have roles := NativeLookupDrawHistory.completed_roles goldilocksBasis 7 ctx.lookupFuel actions transcript world _ job.producerMember
  obtain ⟨earlier,ordered,labels⟩ := original origin job
  cases control : job.view.producer.selection.control with
  | compression field | reciprocal y weights table field => simp only [NativeLookupBatch.Terminal,control] at terminal
  | finished y r weights table state =>
    simp only [NativeLookupDrawHistory.Roles,control] at roles
    obtain ⟨first,middle,last,history,_,_,_,_,_⟩ := roles
    have firstAt : job.view.producer.selection.draws.head? = some first := by simp [history]
    have lastAt : job.view.producer.selection.draws.getLast? = some last := by
      rw [history,← List.cons_append,List.getLast?_append_of_ne_nil _ (by simp)]
      rfl
    obtain ⟨decodedFirst,_,decodedAt,_,decoded,_⟩ := LookupProducedEndpoints.draws _ _ _ _ job.view.produced
    have firstEq : decodedFirst = first := Option.some.inj (decodedAt.symm.trans firstAt)
    subst decodedFirst
    have group : LookupReceiptLabels.Group job.view.producer.selection.draws := by simpa only [LookupReceiptLabels.Labels,control] using labels
    obtain ⟨labelFirst,rest,groupAt,headLabel,tailLabels⟩ := group
    have heads : labelFirst = first := by
      have equal := congrArg List.head? groupAt
      rw [firstAt] at equal
      exact (Option.some.inj equal).symm
    subst labelFirst
    have restEq : rest = middle ++ [last] := List.cons.inj (groupAt.symm.trans history) |>.2
    subst rest
    have found : (first :: (middle ++ [last]))[middle.length+1]? = some last := by simp
    refine ⟨first,last,firstAt,lastAt,decoded,?_⟩
    exact at_offset world earlier first (middle ++ [last]) (by rw [← history]; exact ordered.2)
      headLabel tailLabels (middle.length+1) last found (by omega)

end
end FormalProof4FHE.HasteBoots.LookupCompressionReceipt
