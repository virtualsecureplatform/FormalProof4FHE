module
public import FormalProof4FHE.HasteBoots.SafeEqualityClassKernel
@[expose] public section

/-! Original job ordinals are bounded by the ordered helper-root vector
inside the actual equality input. Its literal encoded size pays this finite
cover without a supplied job-count or unique-root premise. -/
namespace FormalProof4FHE.HasteBoots.EqualityInputJobCount
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativePrefixCodec (Vector)
open OracleProgram (Program)
open EqualityFactorCandidate (Candidate)
noncomputable section

theorem parsed_length (input : Input) (roots : Vector Digest) (parsed : HelperRootsView.parse input = some roots) :
    roots.val.length ≤ input.length := by
  obtain ⟨before,after,bytes,_,_⟩ := HelperRootsView.parse_sound input roots parsed
  have inputLength := congrArg List.length bytes
  rw [SingleOpeningExposure.encodeMany_append,TranscriptFrame.encodeMany,List.length_append,List.length_append] at inputLength
  have message : 64*roots.val.length ≤ (HelperRootsView.rootFrame roots).message.length := by
    change _ ≤ (NativeRootMessage.encode roots.val roots.property).length
    rw [NativeRootMessage.encode_length]
    omega
  have frame : (HelperRootsView.rootFrame roots).message.length ≤ (TranscriptFrame.encode (HelperRootsView.rootFrame roots)).length := by
    simp only [TranscriptFrame.encode,TranscriptFrame.sized,List.length_cons,List.length_append,TranscriptFrame.littleEndian_length]
    omega
  omega

theorem ordinal_lt {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) :
    candidate.family.selection.index.val < candidate.family.selection.family.input.length := by
  have contract := NativeSharedLookupPrelude.protocol_contract candidate.family.selection.ctx.requests.property.le
    (NativeSharedLookupParent.models candidate.family.selection.ctx.requests) candidate.family.selection.origin.geometry.geometry.1
    candidate.family.selection.ctx.proof.values.multiplicities candidate.family.selection.ctx.proof.values.roots
    candidate.family.selection.ctx.proof.roots.property 7 candidate.family.selection.ctx.lookupFuel candidate.family.selection.ctx.equalityFuel
    _ world candidate.family.selection.origin.ready candidate.family.selection.origin.prepared
  have roots := contract.rootCount
  change candidate.family.selection.ctx.proof.roots.val.length = candidate.family.selection.origin.ready.jobs.length at roots
  have size := parsed_length candidate.family.selection.family.input candidate.family.selection.family.roots candidate.family.selection.family.parsed
  rw [candidate.family.selection.roots] at size
  have inside := candidate.family.selection.index.isLt
  omega

end
end FormalProof4FHE.HasteBoots.EqualityInputJobCount
