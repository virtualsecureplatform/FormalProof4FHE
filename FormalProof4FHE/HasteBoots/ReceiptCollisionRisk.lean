module
public import FormalProof4FHE.HasteBoots.ReceiptDigestFixation
public import FormalProof4FHE.HasteBoots.FreshReceiptTargetRisk
@[expose] public section

/-! A distinct receipt key is charged when first named by a positive SHAKE
read or a hash query. Complete only the earlier keys for posterior analysis;
the newly named key remains wholly unseen, even with arbitrary prior partial
reads of other keys. This is a SHAKE collision risk, separate from hashbad. -/
namespace FormalProof4FHE.HasteBoots.ReceiptCollisionRisk
open InputIndexedOracle (Input World law)
open NativeTranscript (Execution)
open NativeIndexExposureRisk (Packet)
open ReceiptCandidateCompletion (digest)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
open scoped Classical
noncomputable section

def candidate : OracleProgram.Request → Option Input
  | .start _ => none
  | .read input _ count => if 0 < count then ReceiptPayloadView.read input else none
  | .hash input => ReceiptPayloadView.read input

def select {S A : Type} (step : S → OracleMachine.Command S A) (packet : Packet S A) : Option Input :=
  (CausalSeedExposure.request step packet.1).bind fun request =>
    (candidate request).bind fun raw => if raw ∈ ReceiptPayloadView.payloads packet.2 then none else some raw

theorem selected_new {S A : Type} (step : S → OracleMachine.Command S A) (packet : Packet S A) (raw : Input)
    (chosen : select step packet = some raw) : raw ∉ ReceiptPayloadView.payloads packet.2 := by
  obtain ⟨request,_,chosen⟩ := Option.bind_eq_some_iff.mp chosen
  obtain ⟨value,_,chosen⟩ := Option.bind_eq_some_iff.mp chosen
  split at chosen
  · contradiction
  · obtain rfl := Option.some.inj chosen
    assumption

def event {S A : Type} (step : S → OracleMachine.Command S A) (packet : Packet S A) (world : World) : Prop :=
  match select step packet with
  | none => False
  | some raw => ∃ old ∈ ReceiptPayloadView.payloads packet.2, digest world raw = digest world old

def risk {S A : Type} (step : S → OracleMachine.Command S A) (packet : Packet S A) : ENNReal :=
  match select step packet with
  | none => 0
  | some _ => ((ReceiptPayloadView.payloads packet.2).card : ENNReal)/(2 : ENNReal)^512

theorem fixed_measurable {S A : Type} (step : S → OracleMachine.Command S A) (packet : Packet S A) :
    MeasurableSet {world | event step packet world} := by
  cases chosen : select step packet with
  | none => simp only [event,chosen,Set.ofPred_false]; exact MeasurableSet.empty
  | some raw =>
    simp only [event,chosen,Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro old
    by_cases named : old ∈ ReceiptPayloadView.payloads packet.2
    · simp only [named,true_and]
      exact measurableSet_eq_fun (InputIndexedOracle.block_measurable (NativeReceiptPrefixView.key raw) 0 64)
        (InputIndexedOracle.block_measurable (NativeReceiptPrefixView.key old) 0 64)
    · simp only [named,false_and,Set.ofPred_false]
      exact MeasurableSet.empty

theorem event_measurable {S A : Type} (step : S → OracleMachine.Command S A)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) :
    MeasurableSet {world | event step (past world).run world} :=
  OracleProgramHistory.event_measurable replay (event step) (fixed_measurable step)

/-- Auxiliary completion reads earlier keys only; the new key is disjoint
from every completion query and has its full 512-bit conditional law. -/
theorem retained_bound {S A : Type} (step : S → OracleMachine.Command S A)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) (world : World) :
    (law[|{other | (ReceiptCandidateCompletion.extend past other).run = (ReceiptCandidateCompletion.extend past world).run}])
      {other | event step (past other).run other} ≤ risk step (past world).run := by
  let completed := ReceiptCandidateCompletion.extend past
  have rp := ReceiptCandidateCompletion.replay replay
  cases chosen : select step (past world).run with
  | none =>
    have equal : (law[|{other | (completed other).run = (completed world).run}]) {other | event step (past other).run other} = 0 := by
      calc _ = (law[|{other | (completed other).run = (completed world).run}]) {other | event step (past world).run other} := by
             apply NativeShakeProjection.conditional_event_congr rp world
             intro other same
             rw [ReceiptCandidateCompletion.old_packet past world other same]
           _ = 0 := by simp only [event,chosen,Set.ofPred_false,measure_empty]
    simp only [risk,chosen]
    exact equal.le
  | some raw =>
    have new := selected_new step (past world).run raw chosen
    have unseen : CausalStreamExposure.seen (past world).run.2 (NativeReceiptPrefixView.key raw) = false := by
      cases seen : CausalStreamExposure.seen (past world).run.2 (NativeReceiptPrefixView.key raw) with
      | false => rfl
      | true => exact False.elim (new (ReceiptPayloadView.seen raw _ seen))
    have fresh := ReceiptCandidateCompletion.unseen_extended past world (NativeReceiptPrefixView.key raw) unseen (by
      intro old named same
      exact new ((List.append_cancel_left same) ▸ named))
    let targets := (ReceiptPayloadView.payloads (past world).run.2).image (digest world)
    have probability := OracleSeedGuessing.fresh_seed_targets rp world (NativeReceiptPrefixView.key raw) targets
      (fun position => CausalStreamExposure.unseen_coordinates _ _ fresh position.val)
    have equal : (law[|{other | (completed other).run = (completed world).run}]) {other | event step (past other).run other} =
        (law[|{other | (completed other).run = (completed world).run}]) {other | InputIndexedOracle.block other (NativeReceiptPrefixView.key raw) 0 64 ∈ targets} := by
      apply NativeShakeProjection.conditional_event_congr rp world
      intro other same
      rw [ReceiptCandidateCompletion.old_packet past world other same]
      simp only [event,chosen,targets,Finset.mem_image]
      constructor
      · rintro ⟨old,named,matching⟩
        exact ⟨old,named,(ReceiptCandidateCompletion.digest_on_fiber replay world other old named same).symm.trans matching.symm⟩
      · rintro ⟨old,named,matching⟩
        exact ⟨old,named,matching.symm.trans (ReceiptCandidateCompletion.digest_on_fiber replay world other old named same).symm⟩
    rw [equal,probability]
    simp only [risk,chosen,div_eq_mul_inv]
    exact mul_le_mul_left (by exact_mod_cast Finset.card_image_le) _

theorem averaged_bound {S A : Type} (step : S → OracleMachine.Command S A)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) :
    law {world | event step (past world).run world} ≤ ∫⁻ world, risk step (past world).run ∂law := by
  rw [OracleHistoryComposition.average_event (ReceiptCandidateCompletion.replay replay) law _ (event_measurable step replay)]
  exact lintegral_mono (retained_bound step replay)

end
end FormalProof4FHE.HasteBoots.ReceiptCollisionRisk
