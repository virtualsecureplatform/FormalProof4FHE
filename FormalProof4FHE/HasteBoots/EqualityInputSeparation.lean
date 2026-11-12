module
public import FormalProof4FHE.HasteBoots.EqualityCandidateKernel
import all Init.Data.String.Defs
@[expose] public section

/-! Original equality inputs end in native field-request frames. They cannot
be parent-seed request keys, including after collector suspension and before
receipt finalization. No later scalar parser is used for this separation. -/
namespace FormalProof4FHE.HasteBoots.EqualityInputSeparation
open InputIndexedOracle (Input World)
open NativeTranscript (Transcript)
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
open NativeFields (goldilocksModulus)
open NativeLookupEquality (Machine Draw)
open ReceiptSequence (Framed)
open OracleProgram (run)
noncomputable section

theorem field_rejected (state : Transcript) (label : Input) (p count : ℕ) (old : Framed state)
    (labelFits : label.length < TranscriptFrame.lengthLimit) :
    NativeParentInputView.parseParent (NativeTranscript.beginField state label p count).run.1.pending.input = none := by
  obtain ⟨frames,decoded⟩ := old
  obtain ⟨valid,bytes⟩ := TranscriptFrame.decodeAll_sound _ _ decoded
  let field : TranscriptFrame.Frame := ⟨4,label,TranscriptFrame.littleEndian 16 p ++ TranscriptFrame.littleEndian 8 count⟩
  have fieldValid : TranscriptFrame.Valid field := ⟨labelFits,by
    simp only [field,List.length_append,TranscriptFrame.littleEndian_length]; decide +kernel⟩
  have allValid : ∀ frame ∈ frames++[field], TranscriptFrame.Valid frame := by
    intro frame member
    rcases List.mem_append.mp member with old | added
    · exact valid frame old
    · obtain rfl := List.mem_singleton.mp added
      exact fieldValid
  have input : (NativeTranscript.beginField state label p count).run.1.pending.input = TranscriptFrame.encodeMany (frames++[field]) := by
    change state.input ++ TranscriptFrame.encode field = _
    rw [bytes,SingleOpeningExposure.encodeMany_append]
    simp only [TranscriptFrame.encodeMany,List.append_nil]
  have rejected : ¬NativeParentInputView.isSeedFrames (frames++[field]) := by
    simp only [NativeParentInputView.isSeedFrames,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append]
    cases frames.reverse <;> simp [field]
  simp only [NativeParentInputView.parseParent,input,TranscriptFrame.decodeAll_encodeMany _ allValid,Option.bind_some,ite_eq_right rejected]

theorem begin_rejected (n : ℕ) (state : Transcript) (old : Framed state) :
    NativeParentInputView.parseParent (TypedFieldVector.beginExecute goldilocksModulus 3 7 n state NativeLookupEquality.pointLabel).1.phase.pending.input = none := by
  have prepared := ReceiptSequence.prepare state .vector 3 7 old (by decide +kernel)
  exact field_rejected _ _ goldilocksModulus (n*3) prepared.1 (by decide +kernel)

def Separated {n : ℕ} (machine : Machine n Goldilocks3) : Prop :=
  (∀ field, machine.active = some field → NativeParentInputView.parseParent field.phase.pending.input = none) ∧
    ∀ draw ∈ machine.draws, NativeParentInputView.parseParent draw.coefficients.phase.pending.input = none

theorem initial (n : ℕ) (transcript : Transcript) (roots : List NativeRootMessage.Digest) (fits : roots.length < 2^64) :
    Separated (NativeLookupEquality.initial n transcript roots fits) := by
  constructor <;> simp [NativeLookupEquality.initial]

theorem tick {n : ℕ} (machine : Machine n Goldilocks3) (world : World) (earlier : List TranscriptFrame.Frame)
    (ordered : EqualityReceiptOrder.Ordered world earlier machine) (separated : Separated machine) :
    Separated (NativeLookupEquality.tickExecute goldilocksBasis 7 machine world).1 := by
  by_cases done : machine.remaining = 0
  · simpa only [NativeLookupEquality.tickExecute,done,ite_true] using separated
  · cases active : machine.active with
    | none =>
      simp only [NativeLookupEquality.tickExecute,done,ite_false,active,Separated]
      refine ⟨?_,separated.2⟩
      intro field same
      cases Option.some.inj same
      exact begin_rejected n machine.transcript ordered.1
    | some field =>
      have rejected := separated.1 field active
      have header := NativeTranscriptExtension.execute_fields goldilocksModulus 1 field world
      cases result : (NativeFieldVector.driveExecute goldilocksModulus 1 field world).1 with
      | suspended next =>
        have state := congrArg NativeFieldVector.stateOf result
        rw [NativeFieldVector.driveExecute,NativeFieldVector.finish_state] at state
        change (NativeFieldVector.execute goldilocksModulus 1 field world).1 = next at state
        rw [state] at header
        have nextRejected : NativeParentInputView.parseParent next.phase.pending.input = none := by rw [header.1]; exact rejected
        simp only [NativeLookupEquality.tickExecute,done,ite_false,active,result,Separated]
        exact ⟨by intro field same; cases Option.some.inj same; exact nextRejected,separated.2⟩
      | finished next transcript =>
        have state := congrArg NativeFieldVector.stateOf result
        rw [NativeFieldVector.driveExecute,NativeFieldVector.finish_state] at state
        change (NativeFieldVector.execute goldilocksModulus 1 field world).1 = next at state
        rw [state] at header
        simp only [NativeLookupEquality.tickExecute,done,ite_false,active,result,Separated]
        refine ⟨by simp,?_⟩
        intro draw member
        rcases List.mem_append.mp member with old | added
        · exact separated.2 draw old
        · cases List.mem_singleton.mp added
          rw [header.1]
          exact rejected

theorem execute {n : ℕ} (fuel : ℕ) (machine : Machine n Goldilocks3) (world : World) (earlier : List TranscriptFrame.Frame)
    (ordered : EqualityReceiptOrder.Ordered world earlier machine) (separated : Separated machine) :
    Separated (NativeLookupEquality.execute goldilocksBasis 7 fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact separated
  | succ fuel ih =>
    exact ih _ (EqualityReceiptOrder.tick goldilocksBasis 7 machine world earlier (by decide +kernel) ordered)
      (tick machine world earlier ordered separated)

theorem request (n fuel : ℕ) (transcript : Transcript) (roots : List NativeRootMessage.Digest) (fits : roots.length < 2^64)
    (world : World) (old : Framed (NativeLookupEquality.bindRoots transcript roots fits)) :
    Separated (run (NativeLookupEquality.request goldilocksBasis 7 n fuel transcript roots fits) world).run.1 := by
  rw [NativeLookupEquality.request,NativeLookupEquality.run_steps]
  exact execute fuel _ world _ (EqualityReceiptOrder.initial n transcript roots fits world old) (initial n transcript roots fits)

open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)

/-- Successful original preparation derives separation for every retained
native equality draw, without a supplied request-suffix certificate. -/
theorem original {ctx : Context (Vector Opening)} {world : World} {body : NativeSharedLookupBody.Bound}
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world body)
    (rootsFit : (NativeRootMessage.encode ctx.proof.roots.val ctx.proof.roots.property).length < TranscriptFrame.lengthLimit)
    (draw : Draw origin.geometry.geometry.1.val Goldilocks3) (member : draw ∈ origin.ready.machine.draws) :
    NativeParentInputView.parseParent draw.coefficients.phase.pending.input = none := by
  have header := NativeForkAncestry.start_header world
    (run (NativeSharedLookupParent.prepare NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests) world).run.1.1
    ctx.proof.multiplicities
  obtain ⟨suffix,valid,bytes⟩ := header
  have decoded := TranscriptFrame.decodeAll_encodeMany _ valid
  rw [← bytes] at decoded
  have old : ReceiptSequence.Framed
      (LookupExecutionOrigin.childStart NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof world) := ⟨_,decoded⟩
  have batch := LookupBatchReceiptOrder.execute goldilocksBasis 7 ctx.lookupFuel _ world _ (by decide +kernel)
    (LookupBatchReceiptOrder.initial (NativeLookupBatch.schedule ctx.requests.property.le
      (fun i => (NativeSharedLookupParent.models ctx.requests i).sampling)) _ world old)
  have contract := NativeSharedLookupPrelude.protocol_contract ctx.requests.property.le (NativeSharedLookupParent.models ctx.requests)
    origin.geometry.geometry.1 ctx.proof.values.multiplicities ctx.proof.values.roots ctx.proof.roots.property
    7 ctx.lookupFuel ctx.equalityFuel _ world origin.ready origin.prepared
  obtain ⟨child,finished,machine,_⟩ := contract.lookup
  have childFramed := batch.1
  simp only [LookupReceiptBatchLineage.current,finished] at childFramed
  have bound := ReceiptSequence.absorb child 1 NativeLookupEquality.rootsLabel
    (NativeRootMessage.encode ctx.proof.values.roots ctx.proof.roots.property) childFramed
    ⟨by change NativeLookupEquality.rootsLabel.length < _; decide +kernel,rootsFit⟩ (by decide)
  have separated := request origin.geometry.geometry.1.val ctx.equalityFuel child ctx.proof.values.roots ctx.proof.roots.property world bound.1
  rw [← machine] at separated
  exact separated.2 draw member

end
end FormalProof4FHE.HasteBoots.EqualityInputSeparation
