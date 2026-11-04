module

public import FormalProof4FHE.HasteBoots.NativeScalarBatchHistory

@[expose] public section

/-!
# Polynomial semantics of actual completed scalar-batch rounds

The received messages themselves supply bounded-degree polynomials. Actual
passed recurrences and actual interpolation updates identify their values
at zero, one and the retained common challenge, for every equation in order.
-/

namespace FormalProof4FHE.HasteBoots.NativeScalarBatchRoundMeaning

open NativeFields NativeExtensionFields NativeFieldWire NativeGoldExtensionArithmetic
open NativeScalarBatchWire NativeScalarBatchPreflight NativeScalarBatchVerifier NativeScalarBatchHistory
open NativeTranscript (Transcript)
open InputIndexedOracle (World)

noncomputable section

/-- The polynomial is constructed from the actual received vector, rather
than supplied with an independent degree or evaluation certificate. -/
def Equation (info : Info) (message : Message) (prior next challenge : Word) : Prop :=
  ∃ width : message.evaluations.val.length = info.maxMultiplicands.val + 1,
    let poly := NativeGoldInterpolationPolynomial.polynomial info.maxMultiplicands.val message.evaluations.val width
    poly.natDegree ≤ info.maxMultiplicands.val ∧
    poly.eval 0 + poly.eval 1 = goldExtensionValue prior ∧
    poly.eval (goldExtensionValue challenge) = goldExtensionValue next

theorem equations_related (statement : Statement) (accepted : dimensions statement = true)
    (infos : List Info) (messages : List Message) (prior next : List Word) (challenge : Word)
    (included : ∀ info ∈ infos, info ∈ statement.infos.val)
    (widths : List.Forall₂ (fun info message => message.evaluations.val.length = info.maxMultiplicands.val + 1) infos messages)
    (recurrences : List.Forall₂ (fun message value => recurrence message value = true) messages prior)
    (evaluations : List.Forall₂ (fun message value => NativeGoldInterpolation.interpolate message.evaluations.val challenge = some value)
      messages next) :
    List.Forall₂ (fun pair values => Equation pair.1 pair.2 values.1 values.2 challenge)
      (infos.zip messages) (prior.zip next) := by
  induction widths generalizing prior next with
  | nil => cases recurrences; cases evaluations; exact .nil
  | @cons info message infos messages width widths ih =>
    cases recurrences with
    | cons checked laterChecks =>
      cases evaluations with
      | cons executed laterEvaluations =>
        have interpretation := NativeGoldInterpolationPolynomial.message_value statement accepted info
          (included info (by simp)) message width challenge
        have checkedPolynomial := (NativeGoldInterpolationPolynomial.message_recurrence statement accepted info
          (included info (by simp)) message width _).mp checked
        have evaluated := interpretation.2
        rw [executed, Option.map_some] at evaluated
        exact .cons ⟨width, interpretation.1, checkedPolynomial, (Option.some.inj evaluated).symm⟩
          (ih _ _ (fun info member => included info (by simp [member])) laterChecks laterEvaluations)

def RoundMeaning (statement : Statement) (entry : CompletedRound) : Prop :=
  entry.priorExpected.length = statement.claims.val.length ∧
  entry.expected.length = statement.claims.val.length ∧
  entry.packet.messages.val.length = statement.claims.val.length ∧
  statement.infos.val.length = statement.claims.val.length ∧
  List.Forall₂ (fun pair values => Equation pair.1 pair.2 values.1 values.2 entry.challenge)
    (statement.infos.val.zip entry.packet.messages.val) (entry.priorExpected.zip entry.expected)

theorem round_polynomial (statement : Statement) (accepted : dimensions statement = true)
    (entry : CompletedRound) (valid : RoundValid statement entry) : RoundMeaning statement entry := by
  obtain ⟨widths, priorCount, messageCount, checked, updated, _⟩ := valid
  have count : entry.priorExpected.length = entry.packet.messages.val.length := priorCount.trans messageCount.symm
  have recurrences := (check_iff entry.packet.messages.val entry.priorExpected count.symm).mp checked
  have evaluations := NativeScalarBatchUpdate.update_related entry.priorExpected entry.packet.messages.val entry.challenge
    entry.expected count updated
  refine ⟨priorCount, ?_, messageCount, widths.length_eq.trans messageCount, ?_⟩
  · exact (NativeScalarBatchUpdate.update_length _ _ _ _ updated).trans priorCount
  · exact equations_related statement accepted statement.infos.val entry.packet.messages.val
      entry.priorExpected entry.expected entry.challenge (fun _ member => member) widths recurrences evaluations

/-- The retained challenge is assembled from the actual completed canonical
coefficient draw, not an unrelated mathematical field element. -/
theorem round_challenge (statement : Statement) (entry : CompletedRound) (valid : RoundValid statement entry) :
    goldExtensionValue entry.challenge = TypedFieldRequest.scalarValue goldilocksBasis entry.coefficients.values ∧
      ∀ i : Fin 3, (entry.challenge i).val = entry.coefficients.values[i.val]'(by
        have total := valid.2.2.2.2.2.2.1.1
        have done := valid.2.2.2.2.2.1
        have bound := i.isLt
        omega) ∧ (entry.challenge i).val < goldilocksModulus := by
  obtain ⟨_, _, _, _, _, done, fieldValid, decoded⟩ := valid
  have length : entry.coefficients.values.length = 3 := by have total := fieldValid.1; omega
  have constructed := NativeGoldLookupProducer.decode_complete entry.coefficients.values length fieldValid.2
  have same := Option.some.inj (constructed.symm.trans decoded)
  refine ⟨?_, ?_⟩
  · exact (congrArg goldExtensionValue same).symm.trans
      (NativeGoldLookupCompleted.fromCoefficients_value _ _ _)
  · intro i
    have coordinate := congrArg (fun value : Word => (value i).val) same
    refine ⟨coordinate.symm, ?_⟩
    calc
      (entry.challenge i).val = _ := coordinate.symm
      _ < goldilocksModulus := NativeGoldLookupCompleted.fromCoefficients_canonical _ _ _ i

/-- Every actually completed initialized round has all ordered polynomial
recurrences and evaluations, and comes from the actual submitted proof. -/
theorem initialized_rounds (transcript result : Transcript) (statement : Statement) (proof : Proof)
    (accepted : beginVerify transcript statement proof = .ok result) (fuel : ℕ) (world : World) :
    ∀ entry ∈ (execute statement proof fuel (initial transcript statement proof) world).1.completed,
      RoundMeaning statement entry ∧
      NativeScalarBatchRoundPacket.packet entry.packet.round proof = some entry.packet ∧
      goldExtensionValue entry.challenge = TypedFieldRequest.scalarValue goldilocksBasis entry.coefficients.values := by
  have preflight := (beginVerify_ok_iff transcript result statement proof).mp accepted
  have linked := initialized_linked transcript result statement proof accepted fuel world
  intro entry member
  have actual := chain_all linked.1 entry member
  exact ⟨round_polynomial statement preflight.2.1 entry actual.1, actual.2, (round_challenge statement entry actual.1).1⟩

end

end FormalProof4FHE.HasteBoots.NativeScalarBatchRoundMeaning
