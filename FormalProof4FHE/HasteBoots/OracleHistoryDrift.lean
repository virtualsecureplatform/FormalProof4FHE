module

public import FormalProof4FHE.HasteBoots.OracleHistoryCharge
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

@[expose] public section

/-!
# Unconditional drift from bounds on complete oracle histories

A charge is fixed before the next answer, by the entire retained result
and log. Averaging preserves all histories and all inherited risk. No
runtime bound or finite expectation is assumed.
-/

namespace FormalProof4FHE.HasteBoots.OracleHistoryDrift

open MeasureTheory ProbabilityTheory
open InputIndexedOracle (World law)
open NativeTranscript (Execution)

noncomputable section

theorem conditional_bound {A : Type} {past : World → Execution A}
    (replay : ObservationReplay.Replayable past) (bad : Set World)
    (measurable : MeasurableSet bad) (bound : A × List NativeTranscript.Observation → ENNReal)
    (localBound : ∀ world,
      (law[|{other | (past other).run = (past world).run}]) bad ≤ bound (past world).run) :
    law bad ≤ ∫⁻ world, bound (past world).run ∂law := by
  have averaged := OracleHistoryCharge.average_bound replay bad measurable
    (fun world => bound (past world).run) 1 ?_
  · simpa only [one_mul] using averaged
  intro history
  obtain ⟨world, same⟩ := history.property
  have conditioned := localBound world
  have integral :
      (∫⁻ other, bound (past other).run ∂law.restrict (OracleHistoryCharge.fiber past history)) =
        law (OracleHistoryCharge.fiber past history) * bound history.val := by
    calc
      _ = ∫⁻ _, bound history.val ∂law.restrict (OracleHistoryCharge.fiber past history) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem (OracleHistoryCharge.fiber_measurable replay history)] with other equal
        rw [show (past other).run = history.val from equal]
      _ = _ := by simp [mul_comm]
  rw [one_mul, integral]
  unfold OracleHistoryCharge.fiber
  rw [← same]
  calc
    _ = (law[|{other | (past other).run = (past world).run}]) bad *
        law {other | (past other).run = (past world).run} :=
      (cond_mul_eq_inter (ObservationReplay.fiber_measurable replay world) bad law).symm
    _ ≤ bound (past world).run * law {other | (past other).run = (past world).run} :=
      mul_le_mul_left conditioned _
    _ = _ := mul_comm _ _

/-- The earlier risk is averaged at its true probability, rather than
being reset by conditioning on a later successful answer. -/
theorem additive_drift {A : Type} {past : World → Execution A}
    (replay : ObservationReplay.Replayable past) (bad : Set World)
    (measurable : MeasurableSet bad)
    (risk charge : A × List NativeTranscript.Observation → ENNReal)
    (localBound : ∀ world,
      (law[|{other | (past other).run = (past world).run}]) bad ≤
        risk (past world).run + charge (past world).run) :
    law bad ≤ (∫⁻ world, risk (past world).run ∂law) +
      ∫⁻ world, charge (past world).run ∂law := by
  have bound := conditional_bound replay bad measurable (fun history => risk history + charge history) localBound
  rwa [lintegral_add_left (OracleExecutionLaw.score_measurable replay risk)] at bound

end

end FormalProof4FHE.HasteBoots.OracleHistoryDrift
