module
public import FormalProof4FHE.HasteBoots.EqualityInputSeparation
public import FormalProof4FHE.HasteBoots.LookupSourceCandidate
import all Init.Data.String.Defs
@[expose] public section

/-! Original lookup field inputs cannot be auxiliary parent-seed inputs.
The last native request frame remains kind 4 across suspensions and every
rejected offset. Separation is derived through the original batch execution. -/
namespace FormalProof4FHE.HasteBoots.LookupInputSeparation
open InputIndexedOracle (Input World)
open NativeTranscript (Transcript)
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
open NativeFields (goldilocksModulus)
open NativeLookupChallenge (Machine)
open ReceiptSequence (Framed)
noncomputable section

theorem begin_rejected (state : Transcript) (label : Input) (old : Framed state)
    (labelFits : label.length < TranscriptFrame.lengthLimit) :
    NativeParentInputView.parseParent (TypedFieldRequest.beginExecute goldilocksModulus 3 7 state label).1.phase.pending.input = none := by
  have prepared := ReceiptSequence.prepare state .scalar 3 7 old (by decide +kernel)
  exact EqualityInputSeparation.field_rejected _ _ goldilocksModulus 3 prepared.1 labelFits

theorem drive_input (fuel : ℕ) (field : NativeFieldVector.State) (world : World) :
    (NativeFieldVector.stateOf (NativeFieldVector.driveExecute goldilocksModulus fuel field world).1).phase.pending.input = field.phase.pending.input := by
  simp only [NativeFieldVector.driveExecute,NativeFieldVector.finish_state]
  exact congrArg NativeTranscript.Transcript.input (NativeFieldVector.header_preserved goldilocksModulus fuel field world).1

theorem finished_framed (field next : NativeFieldVector.State) (world : World) (transcript : Transcript)
    (result : (NativeFieldVector.driveExecute goldilocksModulus 1 field world).1 = .finished next transcript)
    (old : Framed field.phase.pending) (labelFits : field.phase.label.length < TranscriptFrame.lengthLimit) : Framed transcript := by
  have fields := NativeTranscriptExtension.execute_fields goldilocksModulus 1 field world
  have state := congrArg NativeFieldVector.stateOf result
  rw [NativeFieldVector.driveExecute,NativeFieldVector.finish_state] at state
  change (NativeFieldVector.execute goldilocksModulus 1 field world).1 = next at state
  rw [state] at fields
  have framed := (ReceiptSequence.finish next.phase world (by rw [fields.1]; exact old) (by rw [fields.2]; exact labelFits)).1
  rwa [← LookupReceiptLineage.drive_finished goldilocksModulus 1 field next world transcript result] at framed

def Separated (machine : Machine Goldilocks3) : Prop :=
  (match machine.control with
    | .compression field | .reciprocal _ _ _ field => NativeParentInputView.parseParent field.phase.pending.input = none
    | .finished _ _ _ _ _ => True) ∧
  ∀ draw ∈ machine.draws, NativeParentInputView.parseParent draw.coefficients.phase.pending.input = none

theorem initial (transcript : Transcript) (old : Framed transcript) :
    Separated (NativeLookupChallenge.initialExecute (K := Goldilocks3) goldilocksModulus 3 7 transcript).1 :=
  ⟨begin_rejected transcript _ old (by decide +kernel),by simp [NativeLookupChallenge.initialExecute]⟩

theorem tick (width : ℕ) (rows : List (List NativeFields.Goldilocks)) (machine : Machine Goldilocks3)
    (world : World) (earlier : List TranscriptFrame.Frame) (ordered : LookupReceiptOrder.Ordered world earlier machine)
    (separated : Separated machine) : Separated (NativeLookupChallenge.tickExecute goldilocksBasis 7 width rows machine world).1 := by
  cases control : machine.control with
  | finished y r weights table transcript => simpa only [NativeLookupChallenge.tickExecute,control] using separated
  | compression field =>
    have rejected : NativeParentInputView.parseParent field.phase.pending.input = none := by simpa only [control] using separated.1
    have old : Framed field.phase.pending := by simpa only [LookupReceiptLineage.current,control] using ordered.1
    have labelFits : field.phase.label.length < TranscriptFrame.lengthLimit := by simpa only [control] using ordered.2.1.1
    have input := drive_input 1 field world
    cases result : (NativeFieldVector.driveExecute goldilocksModulus 1 field world).1 with
    | suspended next =>
      rw [result] at input
      simpa only [Separated,NativeLookupChallenge.tickExecute,control,result,NativeFieldVector.stateOf] using
        And.intro ((congrArg NativeParentInputView.parseParent input).trans rejected) separated.2
    | finished next transcript =>
      rw [result] at input
      have framed := finished_framed field next world transcript result old labelFits
      simp only [Separated,NativeLookupChallenge.tickExecute,control,result]
      refine ⟨begin_rejected transcript _ framed (by decide +kernel),?_⟩
      intro draw member
      rcases List.mem_append.mp member with previous | added
      · exact separated.2 draw previous
      · cases List.mem_singleton.mp added
        exact (congrArg NativeParentInputView.parseParent input).trans rejected
  | reciprocal y weights table field =>
    have rejected : NativeParentInputView.parseParent field.phase.pending.input = none := by simpa only [control] using separated.1
    have old : Framed field.phase.pending := by simpa only [LookupReceiptLineage.current,control] using ordered.1
    have labelFits : field.phase.label.length < TranscriptFrame.lengthLimit := by simpa only [control] using ordered.2.1.1
    have input := drive_input 1 field world
    cases result : (NativeFieldVector.driveExecute goldilocksModulus 1 field world).1 with
    | suspended next =>
      rw [result] at input
      simpa only [Separated,NativeLookupChallenge.tickExecute,control,result,NativeFieldVector.stateOf] using
        And.intro ((congrArg NativeParentInputView.parseParent input).trans rejected) separated.2
    | finished next transcript =>
      rw [result] at input
      have draws : ∀ draw ∈ machine.draws ++ [(⟨TypedFieldRequest.scalarValue goldilocksBasis next.values,next⟩ : NativeLookupChallenge.Draw Goldilocks3)],
          NativeParentInputView.parseParent draw.coefficients.phase.pending.input = none := by
        intro draw member
        rcases List.mem_append.mp member with previous | added
        · exact separated.2 draw previous
        · cases List.mem_singleton.mp added
          exact (congrArg NativeParentInputView.parseParent input).trans rejected
      cases allowed : NativeLookupChallenge.allowed table (TypedFieldRequest.scalarValue goldilocksBasis next.values) with
      | true =>
        simpa only [Separated,NativeLookupChallenge.tickExecute,control,result,allowed,ite_true] using And.intro True.intro draws
      | false =>
        have framed := finished_framed field next world transcript result old labelFits
        simpa only [Separated,NativeLookupChallenge.tickExecute,control,result,allowed,Bool.false_eq_true,ite_false] using
          And.intro (begin_rejected transcript _ framed (by decide +kernel)) draws

def BatchSeparated (machine : NativeLookupBatch.Machine goldilocksModulus Goldilocks3) : Prop :=
  (match machine.control with | .sampling _ _ selection => Separated selection | _ => True) ∧
    ∀ completed ∈ machine.completed, Separated completed.selection

theorem after_sample (machine : NativeLookupBatch.Machine goldilocksModulus Goldilocks3)
    (job : NativeLookupBatch.Job goldilocksModulus) (todo : List (NativeLookupBatch.Action goldilocksModulus))
    (selection : Machine Goldilocks3) (selected : Separated selection)
    (completed : ∀ entry ∈ machine.completed, Separated entry.selection) :
    BatchSeparated (NativeLookupBatch.afterSample machine job todo selection) := by
  cases control : selection.control <;> simp only [NativeLookupBatch.afterSample,control,BatchSeparated]
  · exact ⟨selected,completed⟩
  · exact ⟨selected,completed⟩
  · refine ⟨True.intro,?_⟩
    intro entry member
    rcases List.mem_append.mp member with previous | added
    · exact completed entry previous
    · cases List.mem_singleton.mp added
      exact selected

theorem batch_tick (machine : NativeLookupBatch.Machine goldilocksModulus Goldilocks3) (world : World)
    (earlier : List TranscriptFrame.Frame) (ordered : LookupBatchReceiptOrder.Ordered world earlier machine)
    (separated : BatchSeparated machine) : BatchSeparated (NativeLookupBatch.tickExecute goldilocksBasis 7 machine world).1 := by
  cases control : machine.control with
  | finished transcript => simpa only [NativeLookupBatch.tickExecute,control] using separated
  | ready todo transcript =>
    have old : Framed transcript := by simpa only [LookupReceiptBatchLineage.current,control] using ordered.1
    cases todo with
    | nil => simpa only [NativeLookupBatch.tickExecute,control,BatchSeparated] using And.intro True.intro separated.2
    | cons action todo =>
      cases action with
      | request ordinal => simpa only [NativeLookupBatch.tickExecute,control,BatchSeparated] using And.intro True.intro separated.2
      | sample job => simpa only [NativeLookupBatch.tickExecute,control,BatchSeparated] using And.intro (initial transcript old) separated.2
  | sampling job todo selection =>
    have selected := tick job.request.width job.request.rows selection world _ (by simpa only [control] using ordered.2.1)
      (by simpa only [control] using separated.1)
    simpa only [NativeLookupBatch.tickExecute,control] using after_sample machine job todo _ selected separated.2

theorem batch_execute (fuel : ℕ) (machine : NativeLookupBatch.Machine goldilocksModulus Goldilocks3) (world : World)
    (earlier : List TranscriptFrame.Frame) (ordered : LookupBatchReceiptOrder.Ordered world earlier machine)
    (separated : BatchSeparated machine) : BatchSeparated (NativeLookupBatch.execute goldilocksBasis 7 fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact separated
  | succ fuel ih =>
    exact ih _ (LookupBatchReceiptOrder.tick goldilocksBasis 7 machine world earlier (by decide +kernel) ordered)
      (batch_tick machine world earlier ordered separated)

theorem original {A : Type} {program : OracleProgram.Program A} {position : ℕ} {world : World}
    (candidate : LookupSourceCandidate.Candidate program position world) :
    NativeParentInputView.parseParent candidate.draw.coefficients.phase.pending.input = none := by
  have header := NativeForkAncestry.start_header world
    (OracleProgram.run (NativeSharedLookupParent.prepare NativeGoldBlockCode.description.row candidate.ctx.registry candidate.ctx.helper
      candidate.ctx.parent candidate.ctx.requests) world).run.1.1 candidate.ctx.proof.multiplicities
  obtain ⟨suffix,valid,bytes⟩ := header
  have decoded := TranscriptFrame.decodeAll_encodeMany _ valid
  rw [← bytes] at decoded
  have old : Framed (LookupExecutionOrigin.childStart NativeGoldBlockCode.description.row candidate.ctx.registry candidate.ctx.helper
      candidate.ctx.parent candidate.ctx.requests candidate.ctx.proof world) := ⟨_,decoded⟩
  let actions := NativeLookupBatch.schedule candidate.ctx.requests.property.le
    (fun i => (NativeSharedLookupParent.models candidate.ctx.requests i).sampling)
  let child := LookupExecutionOrigin.childStart NativeGoldBlockCode.description.row candidate.ctx.registry candidate.ctx.helper
    candidate.ctx.parent candidate.ctx.requests candidate.ctx.proof world
  have separated := batch_execute candidate.ctx.lookupFuel (NativeLookupBatch.initial actions child) world _
    (LookupBatchReceiptOrder.initial actions child world old)
    (show BatchSeparated (NativeLookupBatch.initial actions child) from ⟨True.intro,by simp [NativeLookupBatch.initial]⟩)
  exact (separated.2 candidate.job.view.producer candidate.job.producerMember).2 candidate.draw candidate.member

end
end FormalProof4FHE.HasteBoots.LookupInputSeparation
