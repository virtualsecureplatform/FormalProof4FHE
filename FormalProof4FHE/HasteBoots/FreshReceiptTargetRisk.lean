module
public import FormalProof4FHE.HasteBoots.ReceiptDigestTargets
public import FormalProof4FHE.HasteBoots.ReceiptPayloadView
public import FormalProof4FHE.HasteBoots.OracleProgramHistory
@[expose] public section

/-! A first positive receipt-key read hits earlier named digest targets with
exact conditional probability targets/2^512, even at a far offset. Selection
sees only the real history. This is a probability charge, not physical work. -/
namespace FormalProof4FHE.HasteBoots.FreshReceiptTargetRisk
open InputIndexedOracle (Input World law)
open NativeTranscript (Execution)
open NativeIndexExposureRisk (Packet)
open NativeReceiptPrefixView (domain key)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
open scoped Classical
noncomputable section

theorem read_sound (input raw : Input) (parsed : ReceiptPayloadView.read input = some raw) : input = key raw := by
  unfold ReceiptPayloadView.read at parsed
  split at parsed
  next header =>
    have payload : input.drop domain.length = raw := Option.some.inj parsed
    calc input = input.take domain.length ++ input.drop domain.length := (List.take_append_drop _ _).symm
         _ = key raw := by rw [header,payload]; rfl
  next => contradiction

def select {S A : Type} (step : S → OracleMachine.Command S A) (packet : Packet S A) : Option Input :=
  (CausalStreamExposure.firstRead step packet).bind ReceiptPayloadView.read

theorem selected_first {S A : Type} (step : S → OracleMachine.Command S A) (packet : Packet S A) (raw : Input)
    (selected : select step packet = some raw) : CausalStreamExposure.firstRead step packet = some (key raw) := by
  obtain ⟨input,first,parsed⟩ := Option.bind_eq_some_iff.mp selected
  rw [read_sound input raw parsed] at first
  exact first

theorem selected_unseen {S A : Type} (step : S → OracleMachine.Command S A) (packet : Packet S A) (raw : Input)
    (selected : select step packet = some raw) : CausalStreamExposure.seen packet.2 (key raw) = false := by
  have first := selected_first step packet raw selected
  unfold CausalStreamExposure.firstRead at first
  split at first <;> simp at first
  obtain ⟨eligible,rfl⟩ := first
  exact eligible.2

def event {S A : Type} (step : S → OracleMachine.Command S A) (packet : Packet S A) (world : World) : Prop :=
  match select step packet with
  | none => False
  | some raw => InputIndexedOracle.block world (key raw) 0 64 ∈ ReceiptDigestTargets.targets packet.2

def risk {S A : Type} (step : S → OracleMachine.Command S A) (packet : Packet S A) : ENNReal :=
  match select step packet with
  | none => 0
  | some _ => ((ReceiptDigestTargets.targets packet.2).card : ENNReal)/(2 : ENNReal)^512

theorem byte_power : (256 : ENNReal)^64 = (2 : ENNReal)^512 := by
  rw [show (256 : ENNReal) = (2 : ENNReal)^8 from by norm_num,← pow_mul]

theorem conditional_event {S A : Type} (step : S → OracleMachine.Command S A)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) (world : World) :
    (law[|{other | (past other).run = (past world).run}]) {other | event step (past other).run other} =
      risk step (past world).run := by
  calc
    _ = (law[|{other | (past other).run = (past world).run}]) {other | event step (past world).run other} := by
      apply NativeShakeProjection.conditional_event_congr replay world
      intro other same
      rw [same]
    _ = _ := by
      cases selected : select step (past world).run with
      | none => simp [event,risk,selected]
      | some raw =>
        simp only [event,risk,selected]
        simpa only [byte_power] using NativeEarlyReceiptPrefixRisk.fresh_targets replay world (key raw) 64
          (ReceiptDigestTargets.targets (past world).run.2) (selected_unseen step (past world).run raw selected)

theorem event_measurable {S A : Type} (step : S → OracleMachine.Command S A)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) :
    MeasurableSet {world | event step (past world).run world} := by
  apply OracleProgramHistory.event_measurable replay (fun packet world => event step packet world)
  intro packet
  cases selected : select step packet with
  | none => simp [event,selected]
  | some raw =>
    simpa only [event,selected,Set.preimage,Finset.mem_coe] using
      (InputIndexedOracle.block_measurable (key raw) 0 64) (ReceiptDigestTargets.targets packet.2).measurableSet

theorem averaged_event {S A : Type} (step : S → OracleMachine.Command S A)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) :
    law {world | event step (past world).run world} = ∫⁻ world, risk step (past world).run ∂law := by
  rw [OracleHistoryComposition.average_event replay law _ (event_measurable step replay)]
  exact lintegral_congr (fun world => conditional_event step replay world)

theorem risk_le_input_bytes {S A : Type} (step : S → OracleMachine.Command S A) (packet : Packet S A) :
    risk step packet ≤ (ReceiptDigestTargets.inputBytes packet.2 : ENNReal)/(2 : ENNReal)^512 := by
  cases selected : select step packet with
  | none => simp only [risk,selected]; exact zero_le
  | some raw =>
    simp only [risk,selected,div_eq_mul_inv]
    exact mul_le_mul_left (by exact_mod_cast ReceiptDigestTargets.card packet.2) _

end
end FormalProof4FHE.HasteBoots.FreshReceiptTargetRisk
