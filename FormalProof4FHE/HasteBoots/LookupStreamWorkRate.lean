module
public import FormalProof4FHE.HasteBoots.OffsetDegreeBudget
public import FormalProof4FHE.HasteBoots.ScalarMetadataSize
@[expose] public section

/-! Original lookup stream keys retain their full quoted parent seed.
This byte lower bound prices the reciprocal degree budget; work is still the
specified interpreter's counter, with physical refinement separate. -/
namespace FormalProof4FHE.HasteBoots.LookupStreamWorkRate
open InputIndexedOracle (World)
open OracleProgram (Program)
noncomputable section

def rate : ENNReal := 1/(2 : ENNReal)^132

theorem key_length {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : LookupSourceCandidate.Candidate program position world) :
    64 ≤ candidate.draw.coefficients.phase.pending.input.length := by
  obtain ⟨frames,frame,decoded,present,_,_,message⟩ := NativeChildSeedView.quote_sound _ _
    (LookupDrawSeedQuote.quote candidate.origin candidate.job candidate.draw candidate.member)
  have bounded := ScalarMetadataSize.message_le frames frame (List.mem_of_getElem? present)
  rw [message,List.length_ofFn] at bounded
  rw [(TranscriptFrame.decodeAll_sound _ _ decoded).2]
  exact bounded

theorem budget_rate : (OffsetDegreeBudget.budget : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) ≤ 64*rate := by
  have finite : (OffsetDegreeBudget.budget : NNReal)/(NativeFields.goldilocksModulus^3 : NNReal) ≤
      64*(1/(2 : NNReal)^132) := by
    rw [← NNReal.coe_le_coe]
    norm_num [OffsetDegreeBudget.budget,NativeFields.goldilocksModulus]
  have cast := ENNReal.coe_le_coe.mpr finite
  simpa only [rate,ENNReal.coe_div (by norm_num [NativeFields.goldilocksModulus] : (NativeFields.goldilocksModulus^3 : NNReal) ≠ 0),
    ENNReal.coe_div (by positivity : (2 : NNReal)^132 ≠ 0),ENNReal.coe_mul,ENNReal.coe_pow,
    ENNReal.coe_ofNat,ENNReal.coe_natCast,ENNReal.coe_one,Nat.cast_pow] using cast

theorem input_rate {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : LookupOffsetCompressionFixation.Candidate program position world) :
    (OffsetDegreeBudget.budget : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) ≤
      (candidate.source.draw.coefficients.phase.pending.input.length : ENNReal)*rate :=
  budget_rate.trans (mul_le_mul' (Nat.cast_le.mpr (key_length candidate.source)) le_rfl)

end
end FormalProof4FHE.HasteBoots.LookupStreamWorkRate
