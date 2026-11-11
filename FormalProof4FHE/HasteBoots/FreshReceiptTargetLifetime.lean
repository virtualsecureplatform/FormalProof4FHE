module
public import FormalProof4FHE.HasteBoots.FreshReceiptTargetRisk
@[expose] public section

/-! First receipt-target hits over all actual machine prefixes are bounded by
one lifetime sum of causal charges. No collector-budget or retry multiplier
is introduced. Physical work and native false-acceptance coverage are separate. -/
namespace FormalProof4FHE.HasteBoots.FreshReceiptTargetLifetime
open InputIndexedOracle (World law)
open NativeTranscript (Execution)
open FreshReceiptTargetRisk (event risk)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section

def totalCharge {P S A : Type} (past : World → Execution P) (initial : P → S)
    (step : S → OracleMachine.Command S A) (world : World) : ENNReal :=
  ∑' fuel : ℕ, risk step (CausalExposureLifetime.history past initial step fuel world).run

theorem lifetime_le {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (step : S → OracleMachine.Command S A) (inherited : Set World) :
    law (inherited ∪ {world | ∃ fuel, event step (CausalExposureLifetime.history past initial step fuel world).run world}) ≤
      law inherited + ∫⁻ world, totalCharge past initial step world ∂law := by
  have union : {world | ∃ fuel, event step (CausalExposureLifetime.history past initial step fuel world).run world} =
      ⋃ fuel : ℕ, {world | event step (CausalExposureLifetime.history past initial step fuel world).run world} := by ext world; simp
  rw [union]
  apply (measure_union_le _ _).trans
  apply add_le_add le_rfl
  calc _ ≤ ∑' fuel : ℕ, law {world | event step (CausalExposureLifetime.history past initial step fuel world).run world} := measure_iUnion_le _
       _ = ∑' fuel : ℕ, ∫⁻ world, risk step (CausalExposureLifetime.history past initial step fuel world).run ∂law := by
         congr 1
         funext fuel
         exact FreshReceiptTargetRisk.averaged_event step (CausalExposureLifetime.history_replay replay initial step fuel)
       _ = _ := (lintegral_tsum (fun fuel =>
         (OracleExecutionLaw.score_measurable (CausalExposureLifetime.history_replay replay initial step fuel) (risk step)).aemeasurable)).symm

end
end FormalProof4FHE.HasteBoots.FreshReceiptTargetLifetime
