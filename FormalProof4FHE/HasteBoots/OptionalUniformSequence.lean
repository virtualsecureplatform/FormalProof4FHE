module

public import FormalProof4FHE.HasteBoots.CanonicalByteSampler
public import Mathlib.Algebra.BigOperators.Option

@[expose] public section

/-!
# Sequential optional uniform draws with computed completion mass

An optional draw's successful law is scaled by its actual completion mass.
Sequential execution stops at the first suspended draw. The successful tuple
law and its completion factor are proved for this exact control flow; callers
of the native byte wrapper will derive the single-draw premise internally.
-/

open OracleSpec OracleComp MeasureTheory
open scoped Classical BigOperators

namespace FormalProof4FHE.HasteBoots.OptionalUniformSequence

noncomputable section

variable {A : Type} [Fintype A] [SampleableType A]

def program (step : ProbComp (Option A)) : (count : ℕ) → ProbComp (Option (Fin count → A))
  | 0 => pure (some Fin.elim0)
  | count + 1 => do
    let head ← step
    match head with
    | none => pure none
    | some value => (Option.map (Fin.cons value)) <$> program step count

omit [Fintype A] in
/-- Native coefficient order is head first, followed by every later index. -/
theorem uniform_cons {count : ℕ} (event : (Fin (count + 1) → A) → Prop) :
    Pr{let head ← $ᵗ A; let tail ← $ᵗ (Fin count → A)}[event (Fin.cons head tail)] =
      Pr{let values ← $ᵗ (Fin (count + 1) → A)}[event values] := by
  apply SampleableType.prEvent_uniformSample_pair_of_bijective
  constructor
  · rintro ⟨first, tail⟩ ⟨other, rest⟩ equal
    apply Prod.ext
    · simpa only [Function.uncurry_apply_pair, Fin.cons_zero] using congrFun equal 0
    · have same := congrArg Fin.tail equal
      simpa only [Function.uncurry_apply_pair, Fin.tail_cons] using same
  · intro values
    exact ⟨(values 0, Fin.tail values), Fin.cons_self_tail values⟩

/-- The optional successful tuple law is the uniform tuple law times the
actual single-draw completion factor to the number of sequential draws. -/
theorem probability (step : ProbComp (Option A)) (completion : ENNReal)
    (law : ∀ event : A → Prop,
      Pr{let value ← step}[value.elim False event] = completion * Pr{let value ← $ᵗ A}[event value])
    (count : ℕ) (event : (Fin count → A) → Prop) :
    Pr{let values ← program step count}[values.elim False event] =
      completion ^ count * Pr{let values ← $ᵗ (Fin count → A)}[event values] := by
  induction count with
  | zero =>
    simp only [program, prEvent_pure, Option.elim_some, pow_zero, one_mul]
    calc _ = Pr{let _ ← $ᵗ (Fin 0 → A)}[event Fin.elim0] := by
            by_cases yes : event Fin.elim0 <;> simp [yes, prEvent_norm]
         _ = _ := prEvent_congr _ _ _ (fun values => by rw [Subsingleton.elim values Fin.elim0])
  | succ count ih =>
    have singleton (value : A) : Pr{let result ← step}[result = some value] =
        completion * Pr{let result ← $ᵗ A}[result = value] := by
      have same := prEvent_congr step (fun result => result = some value)
        (fun result => result.elim False (fun result => result = value)) (by
          intro result
          cases result <;> simp)
      exact same.trans (law _)
    have tailLaw (head : A) :
        Pr{let value ← (Option.map (Fin.cons head)) <$> program step count}[value.elim False event] =
        completion ^ count * Pr{let tail ← $ᵗ (Fin count → A)}[event (Fin.cons head tail)] := by
      rw [prEvent_map]
      have same := prEvent_congr (program step count)
        (fun tail => (Option.map (Fin.cons head) tail).elim False event)
        (fun tail => tail.elim False (fun values => event (Fin.cons head values))) (by
          intro tail
          cases tail <;> rfl)
      exact same.trans (ih _)
    have noneZero : Pr{let value ← (pure none : ProbComp (Option (Fin (count + 1) → A)))}[value.elim False event] = 0 := by
      simp [prEvent_norm]
    rw [program, prEvent_bind_eq_tsum, tsum_fintype, Fintype.sum_option]
    simp only [noneZero, mul_zero, zero_add]
    simp_rw [singleton, tailLaw]
    have weighted : (∑ head : A, Pr{let value ← $ᵗ A}[value = head] *
        Pr{let tail ← $ᵗ (Fin count → A)}[event (Fin.cons head tail)]) =
        Pr{let values ← $ᵗ (Fin (count + 1) → A)}[event values] := by
      rw [← uniform_cons event, prEvent_bind_eq_tsum_prEvent, tsum_fintype]
    calc _ = completion ^ (count + 1) * (∑ head : A,
          Pr{let value ← $ᵗ A}[value = head] * Pr{let tail ← $ᵗ (Fin count → A)}[event (Fin.cons head tail)]) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro head _
            rw [pow_succ]
            ac_rfl
         _ = _ := by rw [weighted]

/-- Optional composition preserves successful mass and suspends without
calling the continuation when no candidate has completed. -/
def bindProgram {B : Type} (step : ProbComp (Option A)) (next : A → ProbComp (Option B)) : ProbComp (Option B) := do
  let candidate ← step
  match candidate with
  | none => pure none
  | some value => next value

/-- A scaled uniform optional kernel can be followed by any continuation;
its real incomplete mass is retained rather than conditioned away. -/
theorem bind_probability {B : Type} (step : ProbComp (Option A)) (completion : ENNReal)
    (law : ∀ event : A → Prop,
      Pr{let value ← step}[value.elim False event] = completion * Pr{let value ← $ᵗ A}[event value])
    (next : A → ProbComp (Option B)) (event : B → Prop) :
    Pr{let result ← bindProgram step next}[result.elim False event] =
      completion * Pr{let result ← ($ᵗ A >>= next)}[result.elim False event] := by
  have singleton (value : A) : Pr{let result ← step}[result = some value] =
      completion * Pr{let result ← $ᵗ A}[result = value] := by
    have same := prEvent_congr step (fun result => result = some value)
      (fun result => result.elim False (fun result => result = value)) (by intro result; cases result <;> simp)
    exact same.trans (law _)
  have noneZero : Pr{let value ← (pure none : ProbComp (Option B))}[value.elim False event] = 0 := by simp [prEvent_norm]
  rw [bindProgram, prEvent_bind_eq_tsum, tsum_fintype, Fintype.sum_option]
  simp only [noneZero, mul_zero, zero_add]
  simp_rw [singleton]
  rw [prEvent_bind_eq_tsum, tsum_fintype, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro value _
  exact mul_assoc _ _ _

/-- Successful optional outputs may be observed by an arbitrary nonnegative
cost function. The actual incomplete mass is retained, not normalized away. -/
theorem successful_expectation (step : ProbComp (Option A)) (completion : ENNReal)
    (law : ∀ event : A → Prop,
      Pr{let value ← step}[value.elim False event] = completion * Pr{let value ← $ᵗ A}[event value])
    (cost : A → ENNReal) :
    (∫⁻ value, value ∂𝒟[(fun result => result.elim 0 cost) <$> step]) =
      completion * (∫⁻ value, value ∂𝒟[cost <$> ($ᵗ A)]) := by
  let _ : MeasurableSpace (Option A) := ⊤
  let _ : MeasurableSpace A := ⊤
  have singleton (value : A) : Pr{let result ← step}[result = some value] =
      completion * Pr{let result ← $ᵗ A}[result = value] := by
    have same := prEvent_congr step (fun result => result = some value)
      (fun result => result.elim False (fun result => result = value)) (by intro result; cases result <;> simp)
    exact same.trans (law _)
  rw [lintegral_id_evalDist_map, lintegral_evalDist_eq_tsum, tsum_fintype, Fintype.sum_option]
  simp only [Option.elim_none, Option.elim_some, mul_zero, zero_add]
  simp_rw [singleton]
  rw [lintegral_id_evalDist_map, lintegral_evalDist_eq_tsum, tsum_fintype, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro value _
  exact mul_assoc _ _ _

end

end FormalProof4FHE.HasteBoots.OptionalUniformSequence
