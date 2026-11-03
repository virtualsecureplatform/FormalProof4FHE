module

public import FormalProof4FHE.HasteBoots.OptionalUniformSequence
public import FormalProof4FHE.HasteBoots.PrivateSampling

@[expose] public section

/-!
# Sequential canonical coefficients with complete raw-byte traces

The native loop fills each coefficient before starting the next. Suspension
retains partial accepted coefficients and every rejected byte chunk; later
coefficients are not sampled. Every per-coefficient prefix length is an
analysis approximation to the unbounded loops, not a native retry budget.
The successful vector law derives its completion factor from the raw sampler.
-/

open OracleSpec OracleComp MeasureTheory BinaryTree
open scoped Classical BigOperators
open FormalProof4FHE.HasteBoots.CanonicalByteMask

namespace FormalProof4FHE.HasteBoots.CanonicalCoefficientVector

noncomputable section

structure Result (p count : ℕ) where
  values : Option (Fin count → ZMod p)
  completed : List (ZMod p)
  chunks : List (Bytes (CanonicalByteSampler.byteCount p))

def value (p : ℕ) (raw : Bytes (CanonicalByteSampler.byteCount p)) : ZMod p :=
  masked (CanonicalByteSampler.bits p) raw

def cons {p count : ℕ} (raw : Bytes (CanonicalByteSampler.byteCount p))
    (trace : List (Bytes (CanonicalByteSampler.byteCount p))) (tail : Result p count) : Result p (count + 1) :=
  ⟨Option.map (Fin.cons (value p raw)) tail.values, value p raw :: tail.completed, trace ++ tail.chunks⟩

def program (p fuel : ℕ) : (count : ℕ) → ProbComp (Result p count)
  | 0 => pure ⟨some Fin.elim0, [], []⟩
  | count + 1 => do
    let first ← CanonicalByteSampler.runPrefix p fuel
    match first.1 with
    | none => pure ⟨none, [], first.2⟩
    | some raw => cons raw first.2 <$> program p fuel count

def scalar (p fuel : ℕ) : ProbComp (Option (ZMod p)) :=
  (fun result => result.1.map (value p)) <$> CanonicalByteSampler.runPrefix p fuel

/-- Removing proof-observation fields preserves the exact oracle program,
including all issued raw-byte queries and the suspension control flow. -/
theorem values_erasure (p fuel count : ℕ) :
    (fun result => result.values) <$> program p fuel count = OptionalUniformSequence.program (scalar p fuel) count := by
  induction count with
  | zero => simp [program, OptionalUniformSequence.program]
  | succ count ih =>
    rw [program, OptionalUniformSequence.program, scalar, map_bind, bind_map_left]
    congr 1
    funext first
    cases tag : first.1 with
    | none => simp
    | some raw =>
      have mapped := congrArg (fun computation : ProbComp (Option (Fin count → ZMod p)) =>
        (Option.map (fun tail : Fin count → ZMod p => Fin.cons (n := count) (α := fun _ => ZMod p) (value p raw) tail)) <$> computation) ih
      simpa only [cons, Functor.map_map, Option.map_some, scalar] using mapped

def completion (p fuel : ℕ) : ENNReal :=
  Pr{let result ← CanonicalByteSampler.runPrefix p fuel}[result.1.elim False (fun _ => True)]

/-- The finite prefix's value law is derived with its actual successful mass,
not normalized by silently discarding unfinished coefficient samples. -/
theorem scalar_law (p : ℕ) (valid : 1 < p) [NeZero p] (fuel : ℕ) (event : ZMod p → Prop) :
    Pr{let result ← scalar p fuel}[result.elim False event] = completion p fuel * Pr{let result ← $ᵗ (ZMod p)}[event result] := by
  rw [scalar, prEvent_map]
  calc _ = Pr{let result ← CanonicalByteSampler.runPrefix p fuel}[result.1.elim False (fun raw => event (value p raw))] :=
          prEvent_congr _ _ _ (fun result => by cases result.1 <;> rfl)
       _ = completion p fuel * CanonicalByteSampler.eventProbability p (fun candidate => event (candidate : ZMod p)) := by
          rw [completion, CanonicalByteSampler.eventProbability_eq]
          simpa only [CanonicalByteSampler.runPrefix_eq, value] using
            RejectionSampling.success_scaled (CanonicalByteSampler.accepted p) (CanonicalByteSampler.accepted_nonempty p valid)
              fuel (fun raw => event (value p raw))
       _ = _ := by rw [CanonicalByteSampler.uniform_zmod p valid]

/-- Successful coefficients are jointly uniform, scaled by the actual chance
of completing every requested coefficient in this operational approximation. -/
theorem probability (p : ℕ) (valid : 1 < p) [NeZero p] (fuel count : ℕ) (event : (Fin count → ZMod p) → Prop) :
    Pr{let result ← program p fuel count}[result.values.elim False event] =
      completion p fuel ^ count * Pr{let values ← $ᵗ (Fin count → ZMod p)}[event values] := by
  have law := OptionalUniformSequence.probability (scalar p fuel) (completion p fuel) (scalar_law p valid fuel) count event
  rw [← values_erasure] at law
  simpa only [prEvent_map] using law

theorem completion_tends_to_one (p : ℕ) (valid : 1 < p) [NeZero p] :
    Filter.Tendsto (completion p) Filter.atTop (nhds 1) := by
  change Filter.Tendsto (fun fuel => Pr{let result ← CanonicalByteSampler.runPrefix p fuel}[
    result.1.elim False (fun _ => True)]) Filter.atTop (nhds 1)
  have known := CanonicalByteSampler.value_tends_to_uniform p valid (fun _ => True)
  simpa [prEvent_norm] using known

theorem completion_monotone (p : ℕ) : Monotone (completion p) := by
  intro first second ordered
  unfold completion
  simp_rw [CanonicalByteSampler.runPrefix_eq]
  exact RejectionSampling.success_monotone (CanonicalByteSampler.accepted p) (fun _ => True) ordered

theorem completion_le_one (p fuel : ℕ) : completion p fuel ≤ 1 := prEvent_le_one _

theorem probability_monotone (p : ℕ) (valid : 1 < p) [NeZero p]
    (count : ℕ) (event : (Fin count → ZMod p) → Prop) :
    Monotone (fun fuel => Pr{let result ← program p fuel count}[result.values.elim False event]) := by
  intro first second ordered
  dsimp only
  rw [probability p valid, probability p valid]
  gcongr
  exact completion_monotone p ordered

/-- The actual successful tuple laws converge to full uniform tuples; failed
coefficient prefixes are retained as suspension rather than normalized away. -/
theorem values_tends_to_uniform (p : ℕ) (valid : 1 < p) [NeZero p]
    (count : ℕ) (event : (Fin count → ZMod p) → Prop) :
    Filter.Tendsto (fun fuel => Pr{let result ← program p fuel count}[result.values.elim False event])
      Filter.atTop (nhds (Pr{let values ← $ᵗ (Fin count → ZMod p)}[event values])) := by
  have powers := ENNReal.Tendsto.pow (n := count) (completion_tends_to_one p valid)
  have constant : Filter.Tendsto (fun _ : ℕ => Pr{let values ← $ᵗ (Fin count → ZMod p)}[event values])
      Filter.atTop (nhds (Pr{let values ← $ᵗ (Fin count → ZMod p)}[event values])) := tendsto_const_nhds
  have scaled := ENNReal.Tendsto.mul powers (Or.inl (by simp)) constant (Or.inr (by simp))
  simpa only [probability p valid, one_pow, one_mul] using scaled

def eventProbability (p count : ℕ) (event : (Fin count → ZMod p) → Prop) : ENNReal :=
  ⨆ fuel, Pr{let result ← program p fuel count}[result.values.elim False event]

/-- Unbounded sequential canonical coefficient values have their derived
uniform joint law. No independence certificate is supplied by the caller. -/
theorem uniform_values (p : ℕ) (valid : 1 < p) [NeZero p] (count : ℕ) (event : (Fin count → ZMod p) → Prop) :
    eventProbability p count event = Pr{let values ← $ᵗ (Fin count → ZMod p)}[event values] :=
  tendsto_nhds_unique (tendsto_atTop_iSup (probability_monotone p valid count event)) (values_tends_to_uniform p valid count event)

end

end FormalProof4FHE.HasteBoots.CanonicalCoefficientVector
