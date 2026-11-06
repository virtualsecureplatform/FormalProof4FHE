module
public import FormalProof4FHE.HasteBoots.OptionalUniformSequence
@[expose] public section

/-! One shared candidate budget for sequential optional uniform draws.
Rejection consumes a candidate without advancing the coefficient index.
Suspension is retained, and successful values have their actual completion
mass times the joint uniform law. This is not a native retry cap. -/
namespace FormalProof4FHE.HasteBoots.BudgetedUniformSequence
open OracleSpec OracleComp MeasureTheory
open scoped Classical BigOperators
noncomputable section
variable {A : Type} [Fintype A] [SampleableType A]

def program (step : ProbComp (Option A)) : (fuel count : ℕ) → ProbComp (Option (Fin count → A))
  | _,0 => pure (some Fin.elim0)
  | 0,_+1 => pure none
  | fuel+1,count+1 => do
    let candidate ← step
    match candidate with
    | none => program step fuel (count+1)
    | some head => (Option.map (Fin.cons head)) <$> program step fuel count

def mass (reject accept : ENNReal) : ℕ → ℕ → ENNReal
  | _,0 => 1
  | 0,_+1 => 0
  | fuel+1,count+1 => reject*mass reject accept fuel (count+1) + accept*mass reject accept fuel count

def completion (step : ProbComp (Option A)) (fuel count : ℕ) : ENNReal :=
  Pr{let values ← program step fuel count}[values.elim False (fun _ => True)]

theorem probability_mass (step : ProbComp (Option A)) (accept : ENNReal)
    (law : ∀ event : A → Prop,
      Pr{let value ← step}[value.elim False event] = accept * Pr{let value ← $ᵗ A}[event value])
    (fuel count : ℕ) (event : (Fin count → A) → Prop) :
    Pr{let values ← program step fuel count}[values.elim False event] =
      mass (Pr{let value ← step}[value = none]) accept fuel count * Pr{let values ← $ᵗ (Fin count → A)}[event values] := by
  induction fuel generalizing count with
  | zero =>
    cases count with
    | zero =>
      simp only [program,mass,prEvent_pure,Option.elim_some,one_mul]
      calc _ = Pr{let _ ← $ᵗ (Fin 0 → A)}[event Fin.elim0] := by
              by_cases yes : event Fin.elim0 <;> simp [yes,prEvent_norm]
           _ = _ := prEvent_congr _ _ _ (fun values => by rw [Subsingleton.elim values Fin.elim0])
    | succ count => simp [program,mass,prEvent_norm]
  | succ fuel ih =>
    cases count with
    | zero =>
      simp only [program,mass,prEvent_pure,Option.elim_some,one_mul]
      calc _ = Pr{let _ ← $ᵗ (Fin 0 → A)}[event Fin.elim0] := by
              by_cases yes : event Fin.elim0 <;> simp [yes,prEvent_norm]
           _ = _ := prEvent_congr _ _ _ (fun values => by rw [Subsingleton.elim values Fin.elim0])
    | succ count =>
      have singleton (value : A) : Pr{let result ← step}[result = some value] =
          accept * Pr{let result ← $ᵗ A}[result = value] := by
        have same := prEvent_congr step (fun result => result = some value)
          (fun result => result.elim False (fun result => result = value)) (by intro result; cases result <;> simp)
        exact same.trans (law _)
      have tailLaw (head : A) :
          Pr{let value ← (Option.map (Fin.cons head)) <$> program step fuel count}[value.elim False event] =
          mass (Pr{let value ← step}[value = none]) accept fuel count * Pr{let tail ← $ᵗ (Fin count → A)}[event (Fin.cons head tail)] := by
        rw [prEvent_map]
        have same := prEvent_congr (program step fuel count)
          (fun tail => (Option.map (Fin.cons head) tail).elim False event)
          (fun tail => tail.elim False (fun values => event (Fin.cons head values))) (by intro tail; cases tail <;> rfl)
        exact same.trans (ih count _)
      rw [program,prEvent_bind_eq_tsum,tsum_fintype,Fintype.sum_option]
      simp_rw [singleton,tailLaw]
      rw [ih (count+1) event]
      have weighted : (∑ head : A, Pr{let value ← $ᵗ A}[value = head] *
          Pr{let tail ← $ᵗ (Fin count → A)}[event (Fin.cons head tail)]) =
          Pr{let values ← $ᵗ (Fin (count+1) → A)}[event values] := by
        rw [← OptionalUniformSequence.uniform_cons event,prEvent_bind_eq_tsum_prEvent,tsum_fintype]
      have sumEq : (∑ head : A, (accept*Pr{let value ← $ᵗ A}[value = head]) *
          (mass (Pr{let value ← step}[value = none]) accept fuel count * Pr{let tail ← $ᵗ (Fin count → A)}[event (Fin.cons head tail)])) =
          (accept*mass (Pr{let value ← step}[value = none]) accept fuel count) * Pr{let values ← $ᵗ (Fin (count+1) → A)}[event values] := by
        rw [← weighted,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro head _
        ac_rfl
      rw [sumEq,mass,add_mul]
      ac_rfl

theorem completion_eq_mass [Nonempty A] (step : ProbComp (Option A)) (accept : ENNReal)
    (law : ∀ event : A → Prop,
      Pr{let value ← step}[value.elim False event] = accept * Pr{let value ← $ᵗ A}[event value]) (fuel count : ℕ) :
    completion step fuel count = mass (Pr{let value ← step}[value = none]) accept fuel count := by
  simpa [completion,prEvent_norm] using probability_mass step accept law fuel count (fun _ => True)

/-- Completion is derived from the actual shared-budget computation. -/
theorem probability [Nonempty A] (step : ProbComp (Option A)) (accept : ENNReal)
    (law : ∀ event : A → Prop,
      Pr{let value ← step}[value.elim False event] = accept * Pr{let value ← $ᵗ A}[event value])
    (fuel count : ℕ) (event : (Fin count → A) → Prop) :
    Pr{let values ← program step fuel count}[values.elim False event] =
      completion step fuel count * Pr{let values ← $ᵗ (Fin count → A)}[event values] := by
  rw [completion_eq_mass step accept law,probability_mass step accept law]

omit [Fintype A] [SampleableType A] in
theorem completion_le_one (step : ProbComp (Option A)) (fuel count : ℕ) : completion step fuel count ≤ 1 := prEvent_le_one _

theorem probability_le_uniform [Nonempty A] (step : ProbComp (Option A)) (accept : ENNReal)
    (law : ∀ event : A → Prop,
      Pr{let value ← step}[value.elim False event] = accept * Pr{let value ← $ᵗ A}[event value])
    (fuel count : ℕ) (event : (Fin count → A) → Prop) :
    Pr{let values ← program step fuel count}[values.elim False event] ≤ Pr{let values ← $ᵗ (Fin count → A)}[event values] := by
  rw [probability step accept law]
  exact mul_le_of_le_one_left' (completion_le_one step fuel count)

theorem mass_step_mono (reject accept : ENNReal) (fuel count : ℕ) : mass reject accept fuel count ≤ mass reject accept (fuel+1) count := by
  induction fuel generalizing count with
  | zero => cases count <;> simp [mass]
  | succ fuel ih =>
    cases count with
    | zero => simp [mass]
    | succ count =>
      simp only [mass]
      exact add_le_add (mul_le_mul' le_rfl (ih (count+1))) (mul_le_mul' le_rfl (ih count))

theorem completion_monotone [Nonempty A] (step : ProbComp (Option A)) (accept : ENNReal)
    (law : ∀ event : A → Prop,
      Pr{let value ← step}[value.elim False event] = accept * Pr{let value ← $ᵗ A}[event value]) (count : ℕ) :
    Monotone (fun fuel => completion step fuel count) := by
  apply monotone_nat_of_le_succ
  intro fuel
  simp only [completion_eq_mass step accept law]
  exact mass_step_mono _ _ _ _
end
end FormalProof4FHE.HasteBoots.BudgetedUniformSequence
