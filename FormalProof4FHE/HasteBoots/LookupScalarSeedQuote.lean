module
public import FormalProof4FHE.HasteBoots.AllocatedLookupFrontier
public import FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension
import all FormalProof4FHE.HasteBoots.NativeLookupEquality
@[expose] public section

/-! A completed original scalar reader quotes the actual caller fork seed.
The header follows from the executed lookup/equality prelude and native
scalar transcript extension, without a supplied sampled-seed equality. -/
namespace FormalProof4FHE.HasteBoots.LookupScalarSeedQuote
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open InputIndexedOracle (Input World)
open OracleProgram (run)
noncomputable section

def forkInput (ctx : Context (Vector Opening)) (world : World) : Input :=
  NativeForkAncestry.seedInput (NativeSharedLookupChild.prepare
    (run (NativeSharedLookupParent.prepare NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests) world).run.1.1
      ctx.proof.multiplicities) NativeSharedLookupChild.childLabel NativeSharedLookupChild.childContext

theorem completed_quote {ctx : Context (Vector Opening)} {world : World} {body : NativeSharedLookupBody.Bound}
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world body)
    (rootsFit : (NativeRootMessage.encode ctx.proof.roots.val ctx.proof.roots.property).length < TranscriptFrame.lengthLimit)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode origin.ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain ctx.proof.algebra)
    (entry : NativeScalarBatchVerifier.CompletedRound)
    (member : entry ∈ (NativeScalarBatchVerifier.execute origin.ready.statement ctx.proof.algebra ctx.scalarFuel
      (NativeScalarBatchVerifier.initial origin.ready.equality.transcript origin.ready.statement ctx.proof.algebra) world).1.completed) :
    NativeChildSeedView.quote entry.coefficients.phase.pending.input = some (InputIndexedOracle.block world (forkInput ctx world) 0 64) := by
  have earlier := NativeLookupTranscriptExtension.ready_extends ctx.requests.property.le (NativeSharedLookupParent.models ctx.requests)
    origin.geometry.geometry.1 ctx.proof.values.multiplicities ctx.proof.values.roots ctx.proof.roots.property 7 ctx.lookupFuel ctx.equalityFuel
    (LookupExecutionOrigin.childStart NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof world)
    world origin.ready origin.prepared (by decide +kernel) rootsFit
  have header := NativeForkAncestry.start_header world
    (run (NativeSharedLookupParent.prepare NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests) world).run.1.1 ctx.proof.multiplicities
  have readyHeader := earlier.header header
  have scalar := NativeScalarTranscriptExtension.execute origin.ready.equality.transcript origin.ready.statement ctx.proof.algebra ctx.scalarFuel _ world domain
    (NativeScalarTranscriptExtension.initial origin.ready.equality.transcript origin.ready.statement ctx.proof.algebra statementFits)
  exact ((scalar.2.2 entry member).1.header readyHeader).quote

/-- The actual helper-roots frame remains recognizable after binding. -/
theorem bound_root {child : NativeTranscript.Transcript} {profile : NativeRootMessage.Digest} {label context : Input}
    {seed : NativeRootMessage.Digest} (header : NativeChildSeedView.HasHeader child profile label context seed)
    (roots : List NativeRootMessage.Digest) (fits : roots.length < 2^64)
    (payloadFits : (NativeRootMessage.encode roots fits).length < TranscriptFrame.lengthLimit)
    (root : NativeRootMessage.Digest) (member : root ∈ roots) :
    root ∈ NativeParentLedger.roots (NativeLookupEquality.bindRoots child roots fits).input := by
  obtain ⟨suffix,valid,bytes⟩ := header
  let frames := NativeChildSeedView.seededFrames profile label context seed ++ suffix
  let frame : TranscriptFrame.Frame := ⟨1,NativeLookupEquality.rootsLabel,NativeRootMessage.encode roots fits⟩
  have afterBytes : (NativeLookupEquality.bindRoots child roots fits).input = TranscriptFrame.encodeMany (frames++[frame]) := by
    simp only [NativeLookupEquality.bindRoots,NativeTranscript.appendBytes,NativeTranscript.absorb,bytes,SingleOpeningExposure.encodeMany_append,
      TranscriptFrame.encodeMany,List.append_nil,frames,frame]
  have decoded : TranscriptFrame.decodeAll (NativeLookupEquality.bindRoots child roots fits).input = some (frames++[frame]) := by
    rw [afterBytes]
    apply TranscriptFrame.decodeAll_encodeMany
    intro entry present
    rcases List.mem_append.mp present with old | added
    · exact valid entry old
    · obtain rfl := List.mem_singleton.mp added
      exact ⟨by change NativeLookupEquality.rootsLabel.length < _; decide +kernel,payloadFits⟩
  simp only [NativeParentLedger.roots,NativeParentLedger.frames,decoded,Option.getD_some]
  apply List.mem_flatMap.mpr
  refine ⟨frame,List.mem_append_right _ List.mem_cons_self,?_⟩
  rw [NativeParentInputView.helperRoots_complete]
  exact member

/-- Every original helper root, including the selected job root, occurs in
the literal pending input of every completed scalar reader. -/
theorem completed_root {ctx : Context (Vector Opening)} {world : World} {body : NativeSharedLookupBody.Bound}
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world body)
    (rootsFit : (NativeRootMessage.encode ctx.proof.roots.val ctx.proof.roots.property).length < TranscriptFrame.lengthLimit)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode origin.ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain ctx.proof.algebra)
    (entry : NativeScalarBatchVerifier.CompletedRound)
    (member : entry ∈ (NativeScalarBatchVerifier.execute origin.ready.statement ctx.proof.algebra ctx.scalarFuel
      (NativeScalarBatchVerifier.initial origin.ready.equality.transcript origin.ready.statement ctx.proof.algebra) world).1.completed)
    (root : NativeRootMessage.Digest) (rootMember : root ∈ ctx.proof.roots.val) :
    root ∈ NativeParentLedger.roots entry.coefficients.phase.pending.input := by
  obtain ⟨child,earlier,later⟩ := NativeLookupTranscriptExtension.ready_origins ctx.requests.property.le (NativeSharedLookupParent.models ctx.requests)
    origin.geometry.geometry.1 ctx.proof.values.multiplicities ctx.proof.values.roots ctx.proof.roots.property 7 ctx.lookupFuel ctx.equalityFuel
    (LookupExecutionOrigin.childStart NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof world)
    world origin.ready origin.prepared (by decide +kernel)
  have header := earlier.header (NativeForkAncestry.start_header world
    (run (NativeSharedLookupParent.prepare NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests) world).run.1.1 ctx.proof.multiplicities)
  have present := bound_root header ctx.proof.roots.val ctx.proof.roots.property rootsFit root rootMember
  have boundHeader := header.absorb 1 NativeLookupEquality.rootsLabel _
    ⟨by change NativeLookupEquality.rootsLabel.length < _; decide +kernel,rootsFit⟩
  obtain ⟨suffix,valid,bytes⟩ := boundHeader
  have decoded := TranscriptFrame.decodeAll_encodeMany _ valid
  rw [← bytes] at decoded
  have scalar := NativeScalarTranscriptExtension.execute origin.ready.equality.transcript origin.ready.statement ctx.proof.algebra ctx.scalarFuel _ world domain
    (NativeScalarTranscriptExtension.initial origin.ready.equality.transcript origin.ready.statement ctx.proof.algebra statementFits)
  exact ((later.1.trans (scalar.2.2 entry member).1).roots _ decoded).subset present

end
end FormalProof4FHE.HasteBoots.LookupScalarSeedQuote
