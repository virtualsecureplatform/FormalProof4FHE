module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

@[expose] public section

/-!
# Public evaluation as an application extractor

This is the generic bridge described in HasteBoots `docs/unmasked-polyfrim.md`.
The evaluator and its trace-validity theorem are explicit inputs: this file
does NOT instantiate them with the native Rust evaluator. It extracts an
application trace, not tables matching the prover's internal commitments.
-/

namespace FormalProof4FHE.HasteBoots.ApplicationKnowledge

variable {Key Input Output Trace : Type*} [DecidableEq Output]

/-- The extractor uses only the public key and inputs. -/
def extract (evaluate : Key → Input → Output × Trace)
    (key : Key) (input : Input) (claimed : Output) : Option Trace :=
  if (evaluate key input).1 = claimed then some (evaluate key input).2 else none

/-- Correct public evaluation gives precisely the successful application extractions. -/
theorem succeeds_iff (evaluate : Key → Input → Output × Trace)
    (Valid : Key → Input → Output → Trace → Prop)
    (key : Key) (input : Input) (claimed : Output)
    (correct : Valid key input (evaluate key input).1 (evaluate key input).2) :
    (∃ trace, extract evaluate key input claimed = some trace ∧
      Valid key input claimed trace) ↔ (evaluate key input).1 = claimed := by
  constructor
  · rintro ⟨trace, htrace, _⟩
    by_contra h
    simp [extract, h] at htrace
  · intro h
    refine ⟨(evaluate key input).2, ?_, ?_⟩
    · simp [extract, h]
    · simpa only [← h] using correct

/-- Every accepting extraction failure is exactly an accepting incorrect output.
This identity holds for any joint execution law, including adaptive transcripts. -/
theorem failure_measure_eq_falseOutput {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (evaluate : Key → Input → Output × Trace)
    (Valid : Key → Input → Output → Trace → Prop) (key : Key)
    (inputs : Ω → Input) (claims : Ω → Output) (accept : Ω → Prop)
    (correct : ∀ input, Valid key input (evaluate key input).1 (evaluate key input).2) :
    μ {ω | accept ω ∧ ¬ ∃ trace,
      extract evaluate key (inputs ω) (claims ω) = some trace ∧
        Valid key (inputs ω) (claims ω) trace} =
    μ {ω | accept ω ∧ (evaluate key (inputs ω)).1 ≠ claims ω} := by
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq]
  rw [succeeds_iff evaluate Valid key (inputs ω) (claims ω) (correct (inputs ω))]

end FormalProof4FHE.HasteBoots.ApplicationKnowledge
