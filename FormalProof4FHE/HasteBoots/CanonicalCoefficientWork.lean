module

public import FormalProof4FHE.HasteBoots.CanonicalCoefficientVector

@[expose] public section

/-!
# Byte cost of sequential canonical coefficients, including suspension

The observation counts the complete retained raw trace. Every head read is
charged; later coefficients run only after actual head completion. The
unbounded expected cost is derived from all operational approximations.
No retry maximum or byte budget is imposed on the native protocol.
-/

open OracleSpec OracleComp MeasureTheory
open scoped Classical BigOperators
open FormalProof4FHE.HasteBoots.CanonicalByteMask
open FormalProof4FHE.HasteBoots.CanonicalCoefficientVector

namespace FormalProof4FHE.HasteBoots.CanonicalCoefficientWork

noncomputable section

private theorem expected_const {A : Type} (program : ProbComp A) (cost : ENNReal) :
    (∫⁻ value, value ∂𝒟[(fun _ => cost) <$> program]) = cost := by
  let _ : MeasurableSpace A := ⊤
  rw [lintegral_id_evalDist_map]
  simp

private theorem expected_ite {A : Type} (program : ProbComp A) (event : A → Prop) [DecidablePred event] (cost : ENNReal) :
    (∫⁻ value, value ∂𝒟[(fun value => if event value then cost else 0) <$> program]) =
      Pr{let value ← program}[event value] * cost := by
  let _ : MeasurableSpace A := ⊤
  rw [lintegral_id_evalDist_map, prEvent_eq_evalDist_of_discrete]
  have same : (fun value => if event value then cost else 0) =
      {value | event value}.indicator (fun _ => cost) := by
    funext value
    by_cases present : event value <;> simp [present, Set.indicator]
  rw [same, lintegral_indicator_const MeasurableSet.of_discrete, mul_comm]

def consumedBytes {count : ℕ} (p : ℕ) (result : Result p count) : ℕ :=
  CanonicalByteSampler.byteCount p * result.chunks.length

theorem consumed_cons {p count : ℕ} (raw : Bytes (CanonicalByteSampler.byteCount p))
    (trace : List (Bytes (CanonicalByteSampler.byteCount p))) (tail : Result p count) :
    consumedBytes p (cons raw trace tail) = CanonicalByteSampler.byteCount p * trace.length + consumedBytes p tail := by
  simp [consumedBytes, cons, List.length_append, Nat.mul_add]

def expectedBytes (p fuel count : ℕ) : ENNReal :=
  ∫⁻ value, value ∂𝒟[(fun result => (consumedBytes p result : ENNReal)) <$> program p fuel count]

theorem expectedBytes_zero (p fuel : ℕ) : expectedBytes p fuel 0 = 0 := by
  simp [expectedBytes, program, consumedBytes, evalDist_pure]

/-- Every started coefficient incurs its actual bytes, and only a completed
head starts the suffix. Prefix suspension retains all work already issued. -/
theorem expectedBytes_succ (p fuel count : ℕ) :
    expectedBytes p fuel (count + 1) = CanonicalByteSampler.expectedBytes p fuel + completion p fuel * expectedBytes p fuel count := by
  rw [expectedBytes, program, lintegral_id_evalDist_map_bind]
  have point : ∀ first : RejectionSampling.Result (Bytes (CanonicalByteSampler.byteCount p)),
      (∫⁻ value, value ∂𝒟[(fun result : Result p (count + 1) => (consumedBytes p result : ENNReal)) <$>
        (match first.1 with
         | none => pure (⟨none, [], first.2⟩ : Result p (count + 1))
         | some raw => cons raw first.2 <$> program p fuel count)]) =
      (CanonicalByteSampler.consumedBytes p first : ENNReal) +
        if first.1.elim False (fun _ => True) then expectedBytes p fuel count else 0 := by
    intro first
    cases first.1 with
    | none => simp [consumedBytes, CanonicalByteSampler.consumedBytes, evalDist_pure]
    | some raw =>
      simp only [Functor.map_map]
      have splitCost : (fun tail : Result p count => (consumedBytes p (cons raw first.2 tail) : ENNReal)) =
          (fun tail => (CanonicalByteSampler.consumedBytes p first : ENNReal) + (consumedBytes p tail : ENNReal)) := by
        funext tail
        rw [consumed_cons, Nat.cast_add]
        rfl
      rw [splitCost, lintegral_id_evalDist_map_add, expected_const]
      simp [expectedBytes]
  have observed := congrArg (fun observation : RejectionSampling.Result (Bytes (CanonicalByteSampler.byteCount p)) → ENNReal =>
    ∫⁻ value, value ∂𝒟[observation <$> CanonicalByteSampler.runPrefix p fuel]) (funext point)
  refine observed.trans ?_
  rw [lintegral_id_evalDist_map_add, expected_ite]
  rfl

theorem expectedBytes_monotone (p count : ℕ) : Monotone (fun fuel => expectedBytes p fuel count) := by
  induction count with
  | zero => intro first second ordered; simp only [expectedBytes_zero, le_refl]
  | succ count ih =>
    intro first second ordered
    dsimp only
    rw [expectedBytes_succ, expectedBytes_succ]
    have firstCost : CanonicalByteSampler.expectedBytes p first ≤ CanonicalByteSampler.expectedBytes p second := by
      rw [CanonicalByteSampler.expectedBytes_eq, CanonicalByteSampler.expectedBytes_eq]
      exact mul_le_mul_right (RejectionSampling.expectedAttempts_monotone (CanonicalByteSampler.accepted p) ordered) _
    exact add_le_add firstCost (mul_le_mul' (completion_monotone p ordered) (ih ordered))

/-- Finite prefixes converge to the exact coefficient-count multiple of the
single-coefficient unbounded byte cost. -/
theorem expectedBytes_tends_to (p : ℕ) (valid : 1 < p) [NeZero p] (count : ℕ) :
    Filter.Tendsto (fun fuel => expectedBytes p fuel count) Filter.atTop
      (nhds ((count : ENNReal) * CanonicalByteSampler.totalExpectedBytes p)) := by
  induction count with
  | zero => simpa only [expectedBytes_zero, Nat.cast_zero, zero_mul] using (tendsto_const_nhds (x := (0 : ENNReal)))
  | succ count ih =>
    have suffix := ENNReal.Tendsto.mul (completion_tends_to_one p valid) (Or.inl (by simp)) ih (Or.inr (by simp))
    have total := (CanonicalByteSampler.expectedBytes_tends_to_total p).add suffix
    have sumCost : CanonicalByteSampler.totalExpectedBytes p + (count : ENNReal) * CanonicalByteSampler.totalExpectedBytes p =
        ((count + 1 : ℕ) : ENNReal) * CanonicalByteSampler.totalExpectedBytes p := by
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      exact add_comm _ _
    simpa only [expectedBytes_succ, one_mul, sumCost] using total

def totalExpectedBytes (p count : ℕ) : ENNReal := ⨆ fuel, expectedBytes p fuel count

/-- Exact unbounded raw-byte work for every requested coefficient. -/
theorem totalExpectedBytes_eq (p : ℕ) (valid : 1 < p) [NeZero p] (count : ℕ) :
    totalExpectedBytes p count = (count : ENNReal) * CanonicalByteSampler.totalExpectedBytes p :=
  tendsto_nhds_unique (tendsto_atTop_iSup (expectedBytes_monotone p count)) (expectedBytes_tends_to p valid count)

/-- Substituting the native mask/rejection cost preserves the explicit
characteristic, bit width, byte width and actual coefficient count. -/
theorem totalExpectedBytes_formula (p : ℕ) (valid : 1 < p) [NeZero p] (count : ℕ) :
    totalExpectedBytes p count = (count : ENNReal) * ((CanonicalByteSampler.byteCount p : ENNReal) *
      (((2 ^ CanonicalByteSampler.bits p : ℕ) : ENNReal) / p)) := by
  rw [totalExpectedBytes_eq p valid, CanonicalByteSampler.totalExpectedBytes_eq p valid]

end

end FormalProof4FHE.HasteBoots.CanonicalCoefficientWork
