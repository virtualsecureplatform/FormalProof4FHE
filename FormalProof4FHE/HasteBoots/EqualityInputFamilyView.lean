module
public import FormalProof4FHE.HasteBoots.LookupEqualityResidual
@[expose] public section

/-! Recover the entire helper-root vector and original caller seed quote at
an equality reader input, before that reader's own receipt is appended. -/
namespace FormalProof4FHE.HasteBoots.EqualityInputFamilyView
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeExtensionFields (Goldilocks3)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

theorem forget {before after : NativeTranscript.Transcript} (extension : RootSafeExtension.Extends before after) :
    NativeTranscriptExtension.Extends before after := by
  obtain ⟨suffix,valid,_,bytes,profile⟩ := extension
  exact ⟨suffix,valid,bytes,profile⟩

theorem recover {ctx : Context (Vector Opening)} {world : World} {body : NativeSharedLookupBody.Bound}
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world body)
    (rootsFit : (NativeRootMessage.encode ctx.proof.roots.val ctx.proof.roots.property).length < TranscriptFrame.lengthLimit)
    (draw : NativeLookupEquality.Draw origin.geometry.geometry.1.val Goldilocks3)
    (member : draw ∈ origin.ready.machine.draws) :
    HelperRootsView.parse draw.coefficients.phase.pending.input = some ctx.proof.roots ∧
      NativeChildSeedView.quote draw.coefficients.phase.pending.input =
        some (InputIndexedOracle.block world (LookupScalarSeedQuote.forkInput ctx world) 0 64) := by
  have header := NativeForkAncestry.start_header world
    (run (NativeSharedLookupParent.prepare NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests) world).run.1.1
    ctx.proof.multiplicities
  obtain ⟨child,earlier,_,later⟩ := RootSafeEquality.ready_origins ctx.requests.property.le
    (NativeSharedLookupParent.models ctx.requests) origin.geometry.geometry.1 ctx.proof.values.multiplicities
    ctx.proof.values.roots ctx.proof.roots.property 7 ctx.lookupFuel ctx.equalityFuel _ world origin.ready origin.prepared
    (by decide +kernel)
  have childHeader := earlier.header header
  have retainedHeader := childHeader
  obtain ⟨suffix,valid,bytes⟩ := childHeader
  have parsed := HelperRootsView.parse_bound child _ bytes valid ctx.proof.roots rootsFit
  obtain ⟨frames,decoded,_⟩ := Option.bind_eq_some_iff.mp parsed
  have drawExtends := (later.2.2 draw member).1
  constructor
  · rw [drawExtends.parse frames decoded]
    exact parsed
  · have bound := NativeLookupTranscriptExtension.bind_roots child ctx.proof.values.roots ctx.proof.roots.property rootsFit
    exact ((bound.trans (forget drawExtends)).header retainedHeader).quote

/-- Parsing the complete ordered vector also names every original root in
the native ancestry ledger; equal roots do not change original ordinals. -/
theorem parsed_root (input : InputIndexedOracle.Input) (roots : Vector NativeRootMessage.Digest)
    (parsed : HelperRootsView.parse input = some roots) (root : NativeRootMessage.Digest) (member : root ∈ roots.val) :
    root ∈ NativeParentLedger.roots input := by
  obtain ⟨before,after,bytes,valid,_⟩ := HelperRootsView.parse_sound input roots parsed
  have decoded := TranscriptFrame.decodeAll_encodeMany _ valid
  simp only [NativeParentLedger.roots,NativeParentLedger.frames,bytes,decoded,Option.getD_some]
  apply List.mem_flatMap.mpr
  refine ⟨HelperRootsView.rootFrame roots,?_,?_⟩
  · exact List.mem_append_right _ List.mem_cons_self
  · change root ∈ (NativeParentInputView.helperRoots ⟨1,NativeLookupEquality.rootsLabel,NativeRootMessage.encode roots.val roots.property⟩).getD []
    rw [NativeParentInputView.helperRoots_complete]
    exact member

end
end FormalProof4FHE.HasteBoots.EqualityInputFamilyView
