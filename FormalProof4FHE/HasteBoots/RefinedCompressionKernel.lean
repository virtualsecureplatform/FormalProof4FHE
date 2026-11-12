module
public import FormalProof4FHE.HasteBoots.LookupInputSeparation
public import FormalProof4FHE.HasteBoots.LookupCompressionKernel
@[expose] public section

/-! Parent-seed and consumed-receipt auxiliary completion leave the original
lookup stream unseen. The exact compression kernel is bounded on the same
completed fiber that fixes the complete original source tuple test. -/
namespace FormalProof4FHE.HasteBoots.RefinedCompressionKernel
open InputIndexedOracle (World law)
open OracleProgram (Program runPrefix)
open NativeRootMessage (Digest)
open LookupSourceCandidate (Candidate)
open RefinedScalarSourceKernel (retained retained_replay retained_packet pending)
open MeasureTheory ProbabilityTheory
noncomputable section

def complexity {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) : ℕ :=
  (candidate.origin.ready.jobs.get candidate.index).tag.request.table.length *
    ((candidate.origin.ready.jobs.get candidate.index).tag.request.columns-1)

def rate {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) : ENNReal := (complexity candidate : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ)

theorem input_frames {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) :
    ∃ frames, candidate.draw.coefficients.phase.pending.input = TranscriptFrame.encodeMany frames := by
  obtain ⟨frames,_,decoded,_⟩ := NativeChildSeedView.quote_sound _ _
    (LookupDrawSeedQuote.quote candidate.origin candidate.job candidate.draw candidate.member)
  exact ⟨frames,(TranscriptFrame.decodeAll_sound _ _ decoded).2⟩

theorem unseen {A : Type} (program : Program A) (position : ℕ) (world : World) (candidate : Candidate program position world) :
    CausalStreamExposure.seen (ParentFactorFiber.extend (runPrefix position program) world).run.2
      candidate.draw.coefficients.phase.pending.input = false := by
  have oldFresh : CausalStreamExposure.seen (runPrefix position program world).run.2 candidate.draw.coefficients.phase.pending.input = false := by
    have fresh := candidate.first.fresh
    rwa [candidate.first_position] at fresh
  have parentFresh := ParentSeedCompletion.unseen (runPrefix position program) world _ oldFresh (LookupInputSeparation.original candidate)
  obtain ⟨frames,encoded⟩ := input_frames candidate
  apply ReceiptCandidateCompletion.unseen_extended (ParentSeedCompletion.extend (runPrefix position program)) world _ parentFresh
  intro raw _
  rw [encoded]
  exact NativeTranscript.receipt_not_frame_stream raw frames

theorem selected {A : Type} (program : Program A) (position : ℕ) (world : World) (candidate : Candidate program position world) :
    CausalStreamExposure.firstRead (pending candidate.draw.coefficients.phase.pending.input)
      (retained (ParentFactorFiber.extend (runPrefix position program)) world).run = some candidate.draw.coefficients.phase.pending.input := by
  simp only [CausalStreamExposure.firstRead,CausalSeedExposure.request,retained,WriterT.run_mk,pending,unseen program position world candidate,
    show 0 < (1 : ℕ) from by decide,and_self,ite_true]

theorem complexity_fixed {A : Type} (program : Program A) (position : ℕ) (world other : World)
    (left : Candidate program position world) (right : Candidate program position other) (dummy : Digest)
    (input : left.draw.coefficients.phase.pending.input = right.draw.coefficients.phase.pending.input)
    (ordinal : left.index.val = right.index.val)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run)
    (good : JobReferenceFixation.Good program position world dummy) (safe : ¬JobReferenceFixation.CounterBad program other) :
    complexity left = complexity right := by
  obtain ⟨_,_,requests,_⟩ := (LookupSourceCandidate.compare program position world other left right dummy input ordinal same).resolve_right
    (JobReferenceFixation.family_bad_false program position world other dummy good safe)
  exact congrArg (fun request : NativeSharedLookupStatement.Request => request.table.length*(request.columns-1))
    (OriginalJobOrdinal.request left.origin right.origin requests left.index right.index ordinal)

theorem bound {A : Type} (program : Program A) (position : ℕ) (world : World)
    (candidate : Candidate program position world) (dummy : Digest) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}])
      {other | LookupCompressionKernel.Event candidate dummy other} ≤ rate candidate := by
  have primitive := LookupCompressionKernel.conditional_bound (pending candidate.draw.coefficients.phase.pending.input)
    (retained_replay (ParentFactorFiber.replay (OracleProgram.prefix_replay position program))) world candidate dummy
    (selected program position world candidate)
  simpa only [retained_packet,rate,complexity,Nat.cast_mul,mul_div_assoc] using primitive

theorem bound_of_complexity {A : Type} (program : Program A) (position : ℕ) (world : World)
    (candidate : Candidate program position world) (dummy : Digest) (budget : ℕ) (bounded : complexity candidate ≤ budget) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}])
      {other | LookupCompressionKernel.Event candidate dummy other} ≤ (budget : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) := by
  have numerator : (complexity candidate : ENNReal) ≤ budget := by exact_mod_cast bounded
  exact (bound program position world candidate dummy).trans (ENNReal.div_le_div_right numerator _)

end
end FormalProof4FHE.HasteBoots.RefinedCompressionKernel
