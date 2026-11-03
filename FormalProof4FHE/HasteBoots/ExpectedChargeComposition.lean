module

public import FormalProof4FHE.HasteBoots.ExpectedHazard

@[expose] public section

/-!
# Exact sequential composition of actual interpreter charges

The second program starts at the actual state and may depend on the entire
first result. Charges are added through all return branches, including
computed verifier rejection, with no bound on query count or expected work.
-/

open OracleSpec OracleComp MeasureTheory

namespace FormalProof4FHE.HasteBoots.ExpectedChargeComposition

noncomputable section

variable {ι : Type} {spec : OracleSpec ι} {State A B : Type}

/-- Exact charge additivity at the actual intermediate result/state. -/
theorem bind (impl : QueryImpl spec (StateT State ProbComp))
    (loss : spec.Domain → State → ENNReal) (before : OracleComp spec A)
    (next : A → OracleComp spec B) (initial : State) :
    ExpectedHazard.charge impl loss (before >>= next) initial =
      ExpectedHazard.charge impl loss before initial +
      ∫⁻ value, value ∂𝒟[(fun outcome => ExpectedHazard.charge impl loss (next outcome.1) outcome.2) <$>
        (simulateQ impl before).run initial] := by
  induction before using OracleComp.inductionOn generalizing initial with
  | pure first =>
    simp only [pure_bind, ExpectedHazard.charge_pure, simulateQ_pure, StateT.run_pure,
      map_pure, evalDist_pure, lintegral_dirac, zero_add]
  | query_bind query tail ih =>
    rw [bind_assoc, ExpectedHazard.charge_query_bind, ExpectedHazard.charge_query_bind]
    simp only [ih]
    rw [lintegral_id_evalDist_map_add, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      lintegral_id_evalDist_map_bind]
    exact (add_assoc _ _ _).symm

/-- Returning a pure observation of the result adds no queries or charge. -/
theorem map (impl : QueryImpl spec (StateT State ProbComp))
    (loss : spec.Domain → State → ENNReal) (program : OracleComp spec A)
    (f : A → B) (initial : State) :
    ExpectedHazard.charge impl loss (f <$> program) initial = ExpectedHazard.charge impl loss program initial := by
  rw [map_eq_bind_pure_comp, bind]
  simp only [Function.comp_apply, ExpectedHazard.charge_pure, OracleComp.evalDist_map_const,
    lintegral_dirac, add_zero]

end

end FormalProof4FHE.HasteBoots.ExpectedChargeComposition
