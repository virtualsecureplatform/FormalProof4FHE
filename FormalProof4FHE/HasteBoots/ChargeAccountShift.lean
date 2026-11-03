module

public import FormalProof4FHE.HasteBoots.ChargedExecution

@[expose] public section

/-!
# Existing recorded work survives arbitrary later execution

The original handler cannot observe the analysis account. Starting from an
existing account is therefore exactly a shift of the zero-account run,
with identical primitive answers, return values and actual final state.
-/

open OracleSpec OracleComp

namespace FormalProof4FHE.HasteBoots.ChargeAccountShift

noncomputable section

variable {ι : Type} {spec : OracleSpec ι} {State Result : Type}

def shift (spent : ENNReal) (outcome : Result × State × ENNReal) : Result × State × ENNReal :=
  (outcome.1, (outcome.2.1, spent + outcome.2.2))

/-- Exact query-program identity retains all earlier charged work, including
on branches which later return a computed rejection. Infinite accounts are
allowed; no subtraction or integrability assumption is needed. -/
theorem run (impl : QueryImpl spec (StateT State ProbComp))
    (loss : spec.Domain → State → ENNReal) (program : OracleComp spec Result)
    (initial : State) (spent : ENNReal) :
    (simulateQ (ChargedExecution.handler impl loss) program).run (initial, spent) =
      shift spent <$> (simulateQ (ChargedExecution.handler impl loss) program).run (initial, 0) := by
  induction program using OracleComp.inductionOn generalizing initial spent with
  | pure result => simp only [simulateQ_pure, StateT.run_pure, map_pure, shift, add_zero]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, ChargedExecution.run_handler,
      bind_map_left, map_bind, zero_add]
    congr 1
    funext outcome
    rw [ih outcome.1 outcome.2 (spent + loss query initial), ih outcome.1 outcome.2 (loss query initial)]
    simp only [Functor.map_map]
    congr 1
    funext last
    simp only [shift, add_assoc]

end

end FormalProof4FHE.HasteBoots.ChargeAccountShift
