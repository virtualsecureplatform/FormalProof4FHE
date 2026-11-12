module
public import FormalProof4FHE.HasteBoots.EqualityInputSeparation
@[expose] public section

/-! Parent-seed and named-receipt auxiliary completion leave the original
native equality stream unseen. The fixed residual kernel is therefore bounded
on the same refined fiber that fixes its decoded families and r/y factors. -/
namespace FormalProof4FHE.HasteBoots.RefinedEqualityKernel
open InputIndexedOracle (World law)
open OracleProgram (Program runPrefix)
open NativeRootMessage (Digest)
open EqualityFactorCandidate (Candidate)
open RefinedScalarSourceKernel (retained retained_replay retained_packet pending)
open MeasureTheory ProbabilityTheory
noncomputable section

theorem rejected {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) :
    NativeParentInputView.parseParent candidate.family.selection.family.input = none := by
  have original := EqualityInputSeparation.original candidate.family.selection.origin candidate.family.rootsFit candidate.family.draw
    (List.mem_of_getElem? candidate.family.drawAt)
  exact (congrArg NativeParentInputView.parseParent candidate.family.input).trans original

theorem input_frames {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) :
    ∃ frames, candidate.family.selection.family.input = TranscriptFrame.encodeMany frames := by
  obtain ⟨after,bytes,_⟩ := HelperRootsBoundary.sound candidate.compression.value.view.input candidate.compression.value.view.roots
    candidate.compression.value.view.before candidate.compression.value.view.parsed
  exact ⟨_,candidate.compression.input_eq.symm.trans bytes⟩

theorem unseen {A : Type} (program : Program A) (position : ℕ) (world : World) (candidate : Candidate program position world) :
    CausalStreamExposure.seen (ParentFactorFiber.extend (runPrefix position program) world).run.2
      candidate.family.selection.family.input = false := by
  have oldFresh : CausalStreamExposure.seen (runPrefix position program world).run.2 candidate.family.selection.family.input = false := by
    have fresh := candidate.family.first.fresh
    rwa [candidate.family.first_position] at fresh
  have parentFresh := ParentSeedCompletion.unseen (runPrefix position program) world _ oldFresh (rejected candidate)
  obtain ⟨frames,encoded⟩ := input_frames candidate
  apply ReceiptCandidateCompletion.unseen_extended (ParentSeedCompletion.extend (runPrefix position program)) world _ parentFresh
  intro raw _
  rw [encoded]
  exact NativeTranscript.receipt_not_frame_stream raw frames

theorem selected {A : Type} (program : Program A) (position : ℕ) (world : World) (candidate : Candidate program position world) :
    CausalStreamExposure.firstRead (pending candidate.family.selection.family.input)
      (retained (ParentFactorFiber.extend (runPrefix position program)) world).run = some candidate.family.selection.family.input := by
  simp only [CausalStreamExposure.firstRead,CausalSeedExposure.request,retained,WriterT.run_mk,pending,unseen program position world candidate,
    show 0 < (1 : ℕ) from by decide,and_self,ite_true]

theorem bound {A : Type} (program : Program A) (position : ℕ) (world : World)
    (candidate : Candidate program position world) (dummy : Digest) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}])
      {other | EqualityCandidateKernel.Event candidate dummy other} ≤
      (candidate.family.selection.origin.geometry.geometry.1.val : ENNReal) / (NativeFields.goldilocksModulus^3 : ℕ) := by
  have primitive := EqualityCandidateKernel.conditional_bound (pending candidate.family.selection.family.input)
    (retained_replay (ParentFactorFiber.replay (OracleProgram.prefix_replay position program))) world candidate dummy
    (selected program position world candidate)
  simpa only [retained_packet] using primitive

theorem bound_63 {A : Type} (program : Program A) (position : ℕ) (world : World)
    (candidate : Candidate program position world) (dummy : Digest) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}])
      {other | EqualityCandidateKernel.Event candidate dummy other} ≤
      (63 : ENNReal) / (NativeFields.goldilocksModulus^3 : ℕ) := by
  have dimension : candidate.family.selection.origin.geometry.geometry.1.val ≤ 63 := by
    rw [candidate.family.selection.job.view.dimension]
    have shift := candidate.family.selection.job.view.shift
    omega
  have numerator : (candidate.family.selection.origin.geometry.geometry.1.val : ENNReal) ≤ 63 := by exact_mod_cast dimension
  exact (bound program position world candidate dummy).trans (ENNReal.div_le_div_right numerator _)

end
end FormalProof4FHE.HasteBoots.RefinedEqualityKernel
