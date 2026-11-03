module

public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.OracleComp.ProbComp.Basic

@[expose] public section

/-!
# Responses sampled after an earlier challenge

The response procedure may depend on the whole earlier challenge and use its
own probabilistic computation. Pairing its output with the challenge cannot
increase any event depending only on that earlier challenge. No uniform or
independent response law, fixed random tape or response enumeration is assumed.
-/

open OracleComp

namespace FormalProof4FHE.HasteBoots.AdaptiveResponse

noncomputable section

variable {Challenge Response : Type}

def choose (coins : ProbComp Challenge) (respond : Challenge → ProbComp Response) :
    ProbComp (Challenge × Response) := do
  let challenge ← coins
  let response ← respond challenge
  pure (challenge, response)

/-- The challenge marginal is bounded by the original challenge law, without
a losslessness premise about the response procedure. -/
theorem event_le (coins : ProbComp Challenge) (respond : Challenge → ProbComp Response)
    (bad : Challenge → Prop) :
    Pr{let pair ← choose coins respond}[bad pair.1] ≤ Pr{let challenge ← coins}[bad challenge] := by
  unfold choose
  apply prEvent_bind_le_prEvent_of_forall_eq_zero coins _ bad
  intro challenge outside
  simpa only [prEvent_norm] using
    prEvent_eq_zero_of_forall_not (respond challenge) (fun _ => bad challenge) (fun _ event => outside event)


/-- A later adaptive computation can contribute an additional failure event,
but cannot increase the probability of an already determined earlier event.
The two failures may be arbitrarily correlated. -/
theorem event_le_add (coins : ProbComp Challenge) (respond : Challenge → ProbComp Response)
    (event : Challenge × Response → Prop) (earlier : Challenge → Prop)
    (later : Challenge × Response → Prop)
    (dominates : ∀ pair, event pair → earlier pair.1 ∨ later pair) :
    Pr{let pair ← choose coins respond}[event pair] ≤
      Pr{let challenge ← coins}[earlier challenge] + Pr{let pair ← choose coins respond}[later pair] :=
  ((prEvent_mono _ event (fun pair => earlier pair.1 ∨ later pair) dominates).trans
    (prEvent_or_le _ _ _)).trans (add_le_add (event_le coins respond earlier) le_rfl)

end

end FormalProof4FHE.HasteBoots.AdaptiveResponse
