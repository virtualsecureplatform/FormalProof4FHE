module
public import FormalProof4FHE.HasteBoots.LookupCompressionCount
public import FormalProof4FHE.HasteBoots.LookupOffsetCompressionFixation
@[expose] public section

/-! An original accepted-offset input identifies its prepared-job ordinal by
compression-marker count, without a supplied ordinal match or retry count. -/
namespace FormalProof4FHE.HasteBoots.LookupOffsetOrdinal
open InputIndexedOracle (Input World)
open ReceiptFrameView (frames frame)
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
open LookupCompressionCount (count fromInput)
open OracleProgram (Program run)
noncomputable section

theorem at_last {K : Type} (world : World) (earlier : List TranscriptFrame.Frame)
    (first last : NativeLookupChallenge.Draw K) (middle : List (NativeLookupChallenge.Draw K))
    (ordered : LookupDrawReceiptOrder.Before world earlier (first :: (middle ++ [last])))
    (head : first.coefficients.phase.label = NativeLookupChallenge.hashLabel)
    (tail : ∀ draw ∈ middle, draw.coefficients.phase.label = NativeLookupChallenge.reciprocalLabel) :
    fromInput last.coefficients.phase.pending.input = count earlier + 1 := by
  have found : (first :: (middle ++ [last]))[middle.length+1]? = some last := by simp
  have before := ordered (middle.length+1) last found
  have taken : (first :: (middle ++ [last])).take (middle.length+1) = first :: middle := by simp
  rw [taken] at before
  unfold fromInput
  rw [before,LookupCompressionCount.append,LookupCompressionCount.group world _ ⟨first,middle,rfl,head,tail⟩]

theorem original {ctx : Context (Vector Opening)} {world : World} {body : NativeSharedLookupBody.Bound}
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world body) {index : Fin origin.ready.jobs.length}
    (job : LookupExecutionJob.Job origin index) (last : NativeLookupChallenge.Draw Goldilocks3)
    (lastAt : job.view.producer.selection.draws.getLast? = some last) :
    fromInput last.coefficients.phase.pending.input = index.val+1 := by
  let transcript := LookupExecutionOrigin.childStart NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof world
  let actions := NativeLookupBatch.schedule ctx.requests.property.le (fun i => (NativeSharedLookupParent.models ctx.requests i).sampling)
  let batch := NativeLookupBatch.execute goldilocksBasis 7 ctx.lookupFuel (NativeLookupBatch.initial actions transcript) world
  have initial := LookupInitialReceipt.start world
    (run (NativeSharedLookupParent.prepare NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests) world).run.1.1 ctx.proof.multiplicities
  have indexed := (LookupJobReceiptPrefix.initialized goldilocksBasis 7 ctx.lookupFuel actions transcript world initial.1 (by decide +kernel)).2
  have producerAt := LookupProducerOrdinal.producer_at origin job
  have before := indexed index.val _ producerAt
  have labels := (LookupBatchReceiptLabels.execute goldilocksBasis 7 ctx.lookupFuel _ world (LookupBatchReceiptLabels.initial actions transcript)).2
  have group := labels _ job.producerMember
  have priorCount : count (LookupJobReceiptPrefix.emitted world (batch.1.completed.take index.val)) = index.val := by
    rw [LookupCompressionCount.emitted world _ (fun entry present => labels entry (List.mem_of_mem_take present))]
    rw [List.length_take,Nat.min_eq_left (Nat.le_of_lt (List.getElem?_eq_some_iff.mp producerAt).1)]
  have initialCount : fromInput transcript.input = 0 := LookupCompressionCount.start world _ ctx.proof.multiplicities
  have earlierCount : count (frames transcript.input ++ LookupJobReceiptPrefix.emitted world (batch.1.completed.take index.val)) = index.val := by
    rw [LookupCompressionCount.append,priorCount]
    change fromInput transcript.input + index.val = index.val
    rw [initialCount,Nat.zero_add]
  have terminal := ((NativeLookupBatch.execute_valid goldilocksBasis 7 ctx.lookupFuel _ world
    (NativeLookupBatch.initial_valid goldilocksBasis actions transcript)).2 _ job.producerMember).2
  have roles := NativeLookupDrawHistory.completed_roles goldilocksBasis 7 ctx.lookupFuel actions transcript world _ job.producerMember
  cases control : job.view.producer.selection.control with
  | compression field | reciprocal y weights table field => simp only [NativeLookupBatch.Terminal,control] at terminal
  | finished y r weights table state =>
    simp only [NativeLookupDrawHistory.Roles,control] at roles
    obtain ⟨first,middle,actual,history,_,_,_,_,_⟩ := roles
    have actualAt : job.view.producer.selection.draws.getLast? = some actual := by
      rw [history,← List.cons_append,List.getLast?_append_of_ne_nil _ (by simp)]
      rfl
    have equal : actual = last := Option.some.inj (actualAt.symm.trans lastAt)
    subst actual
    obtain ⟨labelFirst,rest,groupAt,head,tail⟩ := group
    have same : first :: (middle ++ [last]) = labelFirst :: rest := history.symm.trans groupAt
    obtain ⟨rfl,restEq⟩ := List.cons.inj same
    subst rest
    have result := at_last world _ first last middle (by rw [← history]; exact before.2) head
      (fun draw present => tail draw (List.mem_append_left _ present))
    rw [earlierCount] at result
    exact result

theorem candidate {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : LookupOffsetCompressionFixation.Candidate program position world) :
    fromInput candidate.source.draw.coefficients.phase.pending.input = candidate.source.index.val+1 :=
  original candidate.source.origin candidate.source.job candidate.source.draw candidate.last

/-- Equal original offset inputs already imply equal original job ordinals;
no reference bad exclusion or counterfactual ordinal certificate is needed. -/
theorem unique {A B : Type} {leftProgram : Program A} {rightProgram : Program B} {leftPosition rightPosition : ℕ}
    {world other : World} (left : LookupOffsetCompressionFixation.Candidate leftProgram leftPosition world)
    (right : LookupOffsetCompressionFixation.Candidate rightProgram rightPosition other)
    (input : left.source.draw.coefficients.phase.pending.input = right.source.draw.coefficients.phase.pending.input) :
    left.source.index.val = right.source.index.val := by
  have equal := congrArg fromInput input
  rw [candidate left,candidate right] at equal
  omega

end
end FormalProof4FHE.HasteBoots.LookupOffsetOrdinal
