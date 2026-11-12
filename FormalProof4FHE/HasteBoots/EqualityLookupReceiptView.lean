module
public import FormalProof4FHE.HasteBoots.HelperRootsBoundary
@[expose] public section

/-! The latest roots binder identifies the completed lookup transcript before
any equality receipt. Its original job groups are fixed by equal equality
inputs, retaining every rejected offset and original request repetition. -/
namespace FormalProof4FHE.HasteBoots.EqualityLookupReceiptView
open InputIndexedOracle (Input World)
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeExtensionFields (goldilocksBasis Goldilocks3)
open NativeRootMessage (Digest)
open OracleProgram (run)
noncomputable section

structure View where
  input : Input
  roots : Vector Digest
  before : List TranscriptFrame.Frame
  parsed : HelperRootsBoundary.parse input = some (roots,before)
  prelude : OriginalReceiptSegmentation.View
  bytes : prelude.transcript.input = TranscriptFrame.encodeMany before
  noEquality : prelude.equality = []

theorem compare (left right : View) (same : left.input = right.input) : left.prelude.groups = right.prelude.groups := by
  have parsed := left.parsed
  rw [same,right.parsed] at parsed
  have before : left.before = right.before := (Prod.mk.inj (Option.some.inj parsed)).2.symm
  exact (OriginalReceiptSegmentation.compare left.prelude right.prelude
    (left.bytes.trans ((congrArg TranscriptFrame.encodeMany before).trans right.bytes.symm))).1

theorem recover {ctx : Context (Vector Opening)} {world : World} {body : NativeSharedLookupBody.Bound}
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world body)
    (rootsFit : (NativeRootMessage.encode ctx.proof.roots.val ctx.proof.roots.property).length < TranscriptFrame.lengthLimit)
    (draw : NativeLookupEquality.Draw origin.geometry.geometry.1.val Goldilocks3)
    (member : draw ∈ origin.ready.machine.draws) :
    ∃ view : View, view.input = draw.coefficients.phase.pending.input ∧
      view.prelude.groups = (OriginalReceiptSegmentation.original origin rootsFit).groups := by
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
  have sequence := batch.2.2
  simp only [LookupReceiptBatchLineage.current,finished] at childFramed
  simp only [LookupReceiptBatchLineage.current,LookupBatchReceiptOrder.activeFrames,finished,List.append_nil] at sequence
  obtain ⟨frames,framed⟩ := childFramed
  obtain ⟨frameValid,frameBytes⟩ := TranscriptFrame.decodeAll_sound _ _ framed
  have boundParsed := HelperRootsBoundary.bound child frames frameBytes frameValid ctx.proof.roots rootsFit
  obtain ⟨boundFrames,boundDecoded,_⟩ := Option.bind_eq_some_iff.mp boundParsed
  have equality := RootSafeEquality.equality_request goldilocksBasis 7 origin.geometry.geometry.1.val ctx.equalityFuel
    child ctx.proof.values.roots ctx.proof.roots.property world (by decide +kernel)
  rw [← machine] at equality
  have parsed : HelperRootsBoundary.parse draw.coefficients.phase.pending.input = some (ctx.proof.roots,frames) := by
    rw [HelperRootsBoundary.preserved (equality.2.2 draw member).1 boundFrames boundDecoded]
    exact boundParsed
  let base := OriginalReceiptSegmentation.original origin rootsFit
  let prelude : OriginalReceiptSegmentation.View :=
    ⟨child,base.earlier,base.groups,[],by
      simpa only [base,OriginalReceiptSegmentation.original,LookupBatchReceiptOrder.completedFrames,
        List.append_nil,List.flatten_eq_flatMap,List.flatMap_map,Function.comp_def,id_eq] using sequence,
      base.initialCount,base.groupLabels,by simp⟩
  exact ⟨⟨draw.coefficients.phase.pending.input,ctx.proof.roots,frames,parsed,prelude,frameBytes,rfl⟩,rfl,rfl⟩

end
end FormalProof4FHE.HasteBoots.EqualityLookupReceiptView
