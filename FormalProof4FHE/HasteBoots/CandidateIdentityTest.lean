module
public import FormalProof4FHE.HasteBoots.CandidateScalarTest
@[expose] public section

/-! One native identity test selects its full or partial branch from the
input-bound identity metadata. Selection of a branch adds no union factor. -/
namespace FormalProof4FHE.HasteBoots.CandidateIdentityTest
open InputIndexedOracle (World)
open OracleProgram (Program runPrefix)
open NativeRootMessage (Digest)
open JobReferenceCandidate (Candidate)
open JobReferenceFixation (Fixed)
open CandidateScalarTest (info partialTest fullTest)
open MeasureTheory ProbabilityTheory
noncomputable section

abbrev test {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) (dummy : Digest) (radius : ℕ) (message : NativeScalarBatchWire.Message) :=
  if (info candidate).maxMultiplicands.val = 3 then fullTest candidate dummy radius message else partialTest candidate dummy radius message


theorem full_branch {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) (dummy : Digest) (radius : ℕ) (message : NativeScalarBatchWire.Message)
    (branch : (candidate.selection.origin.ready.jobs.get candidate.selection.index).tag.request.terminal.logicalLength.val =
      2^candidate.selection.origin.geometry.geometry.1.val) :
    test candidate dummy radius message = fullTest candidate dummy radius message := by
  simp only [List.get_eq_getElem] at branch
  simp [test,info,LookupScalarGrammar.identityInfo,branch]

theorem partial_branch {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) (dummy : Digest) (radius : ℕ) (message : NativeScalarBatchWire.Message)
    (branch : (candidate.selection.origin.ready.jobs.get candidate.selection.index).tag.request.terminal.logicalLength.val ≠
      2^candidate.selection.origin.geometry.geometry.1.val) :
    test candidate dummy radius message = partialTest candidate dummy radius message := by
  simp only [List.get_eq_getElem] at branch
  simp [test,info,LookupScalarGrammar.identityInfo,branch]

theorem degree_le {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) : (info candidate).maxMultiplicands.val ≤ 4 := by
  unfold info LookupScalarGrammar.identityInfo
  split_ifs <;> simp

theorem test_eq {A : Type} {program : Program A} {position : ℕ} {world other : World}
    (left : Candidate program position world) (right : Candidate program position other) (dummy : Digest) (radius : ℕ)
    (input : left.selection.family.input = right.selection.family.input)
    (ordinal : left.selection.index.val = right.selection.index.val) (fixed : Fixed left right dummy radius)
    (lm rm : NativeScalarBatchWire.Message)
    (leftAt : (CandidateScalarPacket.reader left).entry.packet.messages.val[2*left.selection.index.val+1]? = some lm)
    (rightAt : (CandidateScalarPacket.reader right).entry.packet.messages.val[2*right.selection.index.val+1]? = some rm) :
    test left dummy radius lm = test right dummy radius rm := by
  have metadata : info left = info right := CandidateScalarPacket.same_identity_info left right input ordinal
  unfold test
  rw [metadata,CandidateScalarTest.full_test left right dummy radius input ordinal fixed lm rm leftAt rightAt,
    CandidateScalarTest.partial_test left right dummy radius input ordinal fixed lm rm leftAt rightAt]

theorem bound {A : Type} (program : Program A) (position : ℕ) (world : World)
    (candidate : Candidate program position world) (dummy profile : Digest) (radius : ℕ)
    (configuration : ScalarRecoveredReplay.Configuration)
    (found : ScalarRecoveredReplay.recover candidate.selection.family.input = some configuration)
    (message : NativeScalarBatchWire.Message) :
    (InputIndexedOracle.law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}])
      {other | ScalarRecoveredUnboundedLaw.event candidate.selection.family.input configuration profile
        (test candidate dummy radius message) other} ≤ (4 : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) := by
  have degree : ((info candidate).maxMultiplicands.val : ENNReal) ≤ 4 := by exact_mod_cast degree_le candidate
  have risk := ENNReal.div_le_div_right degree (NativeFields.goldilocksModulus^3 : ℕ)
  unfold test
  split_ifs
  · exact (CandidateScalarTest.full_bound program position world candidate dummy profile radius configuration found message).trans risk
  · exact (CandidateScalarTest.partial_bound program position world candidate dummy profile radius configuration found message).trans risk

end
end FormalProof4FHE.HasteBoots.CandidateIdentityTest
