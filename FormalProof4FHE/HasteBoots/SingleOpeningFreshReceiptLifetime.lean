module
public import FormalProof4FHE.HasteBoots.SingleOpeningFreshReceiptDigest
@[expose] public section

/-! The fresh receipt-digest event over every collector budget and every
actual machine prefix. Completed native states are stable, so taking the
budget union costs no retry factor or success-floor normalization. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningFreshReceiptLifetime
open InputIndexedOracle (World law)
open NativeRootMessage (Digest)
open NativeTranscript (Execution)
open NativeIndexExposureRisk (Packet)
open SingleOpeningFreshReceiptDigest (event collected)
open SingleOpeningEarlyReceiptPrefixRisk (select)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section

theorem event_monotone {S A : Type} (profile : Digest) (step : S → OracleMachine.Command S A) (packet : Packet S A) :
    Monotone (fun fuel => {world | event profile fuel step packet world}) := by
  intro first second ordered world member
  change event profile first step packet world at member
  change event profile second step packet world
  cases chosen : select step packet with
  | none => simp only [event,SingleOpeningFreshReceiptDigest.run_none profile first step packet world chosen,SingleOpeningFreshReceiptDigest.after] at member
  | some view =>
    obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le ordered
    simp only [event,SingleOpeningFreshReceiptDigest.run_some profile first step packet world view chosen] at member
    have complete := member.1
    dsimp only [collected] at complete
    have same : (collected profile (first+extra) view world).1 = (collected profile first view world).1 := by
      unfold collected
      rw [NativeFieldVector.execute_add]
      dsimp only
      rw [NativeFieldVector.execute_complete NativeFields.goldilocksModulus extra _ world complete]
    simp only [event,SingleOpeningFreshReceiptDigest.run_some profile (first+extra) step packet world view chosen,same]
    exact member

def ever {S A : Type} (profile : Digest) (step : S → OracleMachine.Command S A) (packet : Packet S A) (world : World) : Prop :=
  ∃ fuel, event profile fuel step packet world

def risk {S A : Type} (step : S → OracleMachine.Command S A) (packet : Packet S A) : ENNReal :=
  match select step packet with | none => 0 | some _ => 1/(2 : ENNReal)^512

theorem adaptive_monotone {S A : Type} (past : World → Execution (S ⊕ A)) (profile : Digest) (step : S → OracleMachine.Command S A) :
    Monotone (fun fuel => {world | event profile fuel step (past world).run world}) := by
  intro first second ordered world member
  exact event_monotone profile step (past world).run ordered member

theorem conditional_ever_bound {S A : Type} {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (profile : Digest) (step : S → OracleMachine.Command S A) (world : World) :
    (law[|{other | (past other).run = (past world).run}]) {other | ever profile step (past other).run other} ≤
      risk step (past world).run := by
  cases chosen : select step (past world).run with
  | none =>
    have fixed : (law[|{other | (past other).run = (past world).run}]) {other | ever profile step (past other).run other} =
        (law[|{other | (past other).run = (past world).run}]) {other | ever profile step (past world).run other} := by
      apply NativeShakeProjection.conditional_event_congr replay world
      intro other same
      rw [same]
    rw [fixed]
    have empty : {other | ever profile step (past world).run other} = ∅ := by
      ext other
      simp only [ever,Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false,not_exists]
      intro fuel
      change ¬ SingleOpeningFreshReceiptDigest.after (past world).run
        (OracleProgram.run (SingleOpeningFreshReceiptDigest.program profile fuel step (past world).run) other).run.1 other
      rw [SingleOpeningFreshReceiptDigest.run_none profile fuel step (past world).run other chosen]
      exact id
    rw [empty,measure_empty]
    simp only [risk,chosen,le_refl]

  | some view =>
    have union : {other | ever profile step (past other).run other} = ⋃ fuel : ℕ,
        {other | event profile fuel step (past other).run other} := by ext other; simp [ever]
    rw [union,(adaptive_monotone past profile step).measure_iUnion]
    simp only [risk,chosen]
    exact iSup_le (fun fuel => SingleOpeningFreshReceiptDigest.conditional_bound replay profile fuel step world)

theorem ever_measurable {S A : Type} {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (profile : Digest) (step : S → OracleMachine.Command S A) :
    MeasurableSet {world | ever profile step (past world).run world} := by
  have union : {world | ever profile step (past world).run world} = ⋃ fuel : ℕ,
      {world | event profile fuel step (past world).run world} := by ext world; simp [ever]
  rw [union]
  exact MeasurableSet.iUnion (fun fuel => SingleOpeningFreshReceiptDigest.event_measurable replay profile fuel step)

theorem averaged_ever_bound {S A : Type} {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (profile : Digest) (step : S → OracleMachine.Command S A) :
    law {world | ever profile step (past world).run world} ≤ ∫⁻ world, risk step (past world).run ∂law := by
  rw [OracleHistoryComposition.average_event replay law _ (ever_measurable replay profile step)]
  exact lintegral_mono (fun world => conditional_ever_bound replay profile step world)

def totalCharge {P S A : Type} (past : World → Execution P) (initial : P → S)
    (step : S → OracleMachine.Command S A) (world : World) : ENNReal :=
  ∑' fuel : ℕ, risk step (CausalExposureLifetime.history past initial step fuel world).run

theorem lifetime_le {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (profile : Digest) (step : S → OracleMachine.Command S A) (inherited : Set World) :
    law (inherited ∪ {world | ∃ fuel, ever profile step (CausalExposureLifetime.history past initial step fuel world).run world}) ≤
      law inherited + ∫⁻ world, totalCharge past initial step world ∂law := by
  have union : {world | ∃ fuel, ever profile step (CausalExposureLifetime.history past initial step fuel world).run world} =
      ⋃ fuel : ℕ, {world | ever profile step (CausalExposureLifetime.history past initial step fuel world).run world} := by ext world; simp
  rw [union]
  apply (measure_union_le _ _).trans
  apply add_le_add le_rfl
  calc _ ≤ ∑' fuel : ℕ, law {world | ever profile step (CausalExposureLifetime.history past initial step fuel world).run world} := measure_iUnion_le _
       _ ≤ ∑' fuel : ℕ, ∫⁻ world, risk step (CausalExposureLifetime.history past initial step fuel world).run ∂law :=
          ENNReal.tsum_le_tsum (fun fuel => averaged_ever_bound (CausalExposureLifetime.history_replay replay initial step fuel) profile step)
       _ = _ := (lintegral_tsum (fun fuel =>
          (OracleExecutionLaw.score_measurable (CausalExposureLifetime.history_replay replay initial step fuel) (risk step)).aemeasurable)).symm
end
end FormalProof4FHE.HasteBoots.SingleOpeningFreshReceiptLifetime
