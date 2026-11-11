module
public import FormalProof4FHE.HasteBoots.OriginalPackedFamily
public import FormalProof4FHE.HasteBoots.RootSafeEquality
public import FormalProof4FHE.HasteBoots.RootSafeScalar
public import FormalProof4FHE.HasteBoots.AllocatedFirstParentFamily
@[expose] public section

/-! A completed original scalar reader recovers the entire actual proof-root
vector, in original order. This strengthens root membership to vector and
ordinal identity and tolerates earlier roots-frame decoys. -/
namespace FormalProof4FHE.HasteBoots.OriginalHelperRoots
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeTranscript (Transcript)
open NativePrefixCodec (Vector)
open OracleProgram (run)
noncomputable section

theorem ready_roots {count : ℕ} (fits : count ≤ 2^64)
    (requests : Fin count → NativeSharedLookupStatement.Request) (n : NativeUsizeMessage.Usize)
    (multiplicities : List (List NativeFieldRepresentation.GoldWord)) (roots : Vector Digest)
    (w lookupFuel equalityFuel : ℕ) (state : Transcript) (world : World)
    (ready : NativeSharedLookupPrelude.Ready n.val)
    (success : (run (NativeSharedLookupPrelude.protocol fits requests n multiplicities roots.val roots.property w lookupFuel equalityFuel state) world).run.1 = some ready)
    (frames : List TranscriptFrame.Frame) (decoded : TranscriptFrame.decodeAll state.input = some frames)
    (descriptorFits : (NativeExtensionDescriptor.descriptor 3 w).length < TranscriptFrame.lengthLimit)
    (rootsFit : (NativeRootMessage.encode roots.val roots.property).length < TranscriptFrame.lengthLimit) :
    HelperRootsView.parse ready.equality.transcript.input = some roots := by
  obtain ⟨child,earlier,later,_⟩ := RootSafeEquality.ready_origins fits requests n multiplicities roots.val roots.property w lookupFuel equalityFuel
    state world ready success descriptorFits
  obtain ⟨suffix,childDecoded⟩ := earlier.frames frames decoded
  obtain ⟨valid,bytes⟩ := TranscriptFrame.decodeAll_sound _ _ childDecoded
  have parsed := HelperRootsView.parse_bound child (frames++suffix) bytes valid roots rootsFit
  obtain ⟨boundFrames,boundDecoded,_⟩ := Option.bind_eq_some_iff.mp parsed
  rw [later.parse boundFrames boundDecoded]
  exact parsed

theorem completed_roots {ctx : NativeGoldHelperVerification.Context (Vector NativeGoldBatchOpening.Opening)}
    {world : World} {body : NativeSharedLookupBody.Bound} (origin : AllocatedLookupIdentity.NativeOrigin ctx world body)
    (rootsFit : (NativeRootMessage.encode ctx.proof.roots.val ctx.proof.roots.property).length < TranscriptFrame.lengthLimit)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode origin.ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain ctx.proof.algebra)
    (entry : NativeScalarBatchVerifier.CompletedRound)
    (member : entry ∈ (NativeScalarBatchVerifier.execute origin.ready.statement ctx.proof.algebra ctx.scalarFuel
      (NativeScalarBatchVerifier.initial origin.ready.equality.transcript origin.ready.statement ctx.proof.algebra) world).1.completed) :
    HelperRootsView.parse entry.coefficients.phase.pending.input = some ctx.proof.roots := by
  have header := NativeForkAncestry.start_header world
    (run (NativeSharedLookupParent.prepare NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests) world).run.1.1 ctx.proof.multiplicities
  obtain ⟨suffix,valid,bytes⟩ := header
  have initialDecoded : ∃ frames, TranscriptFrame.decodeAll
      (LookupExecutionOrigin.childStart NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof world).input = some frames := by
    unfold LookupExecutionOrigin.childStart
    rw [bytes]
    exact ⟨_,TranscriptFrame.decodeAll_encodeMany _ valid⟩
  obtain ⟨frames,decoded⟩ := initialDecoded
  have readyParsed := ready_roots ctx.requests.property.le (NativeSharedLookupParent.models ctx.requests) origin.geometry.geometry.1
    ctx.proof.values.multiplicities ctx.proof.roots 7 ctx.lookupFuel ctx.equalityFuel _ world origin.ready origin.prepared frames decoded (by decide +kernel) rootsFit
  obtain ⟨readyFrames,readyDecoded,_⟩ := Option.bind_eq_some_iff.mp readyParsed
  have scalar := RootSafeScalar.execute origin.ready.equality.transcript origin.ready.statement ctx.proof.algebra ctx.scalarFuel _ world domain
    (RootSafeScalar.initial origin.ready.equality.transcript origin.ready.statement ctx.proof.algebra statementFits)
  rw [((scalar.2.2 entry member).1).parse readyFrames readyDecoded]
  exact readyParsed

/-- Exact parsing of one literal scalar input fixes the full root vector,
not merely a set of mentioned or equal-looking roots. -/
theorem compare (leftInput rightInput : Input) (left right : Vector Digest)
    (leftParsed : HelperRootsView.parse leftInput = some left) (rightParsed : HelperRootsView.parse rightInput = some right)
    (same : leftInput = rightInput) : left = right := by
  rw [same] at leftParsed
  exact Option.some.inj (leftParsed.symm.trans rightParsed)

theorem ordinal (leftInput rightInput : Input) (left right : Vector Digest)
    (leftParsed : HelperRootsView.parse leftInput = some left) (rightParsed : HelperRootsView.parse rightInput = some right)
    (same : leftInput = rightInput) (leftIndex : Fin left.val.length) (rightIndex : Fin right.val.length)
    (position : leftIndex.val = rightIndex.val) : left.val.get leftIndex = right.val.get rightIndex :=
  OriginalPackedFamily.entry_eq left right (compare leftInput rightInput left right leftParsed rightParsed same) leftIndex rightIndex position

end
end FormalProof4FHE.HasteBoots.OriginalHelperRoots
