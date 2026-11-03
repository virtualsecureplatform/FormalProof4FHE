module

public import FormalProof4FHE.HasteBoots.TupleHash
public import FormalProof4FHE.HasteBoots.ReciprocalDetection

@[expose] public section

/-!
# Hash/reciprocal pair composition and independent repetitions

One pair samples y, hashes the fixed public table, then samples r uniformly
from its accepted domain. Public multiplicities and original tuples precede
all pairs. The error retains both the tuple-hash union and reciprocal-domain
loss. Repeated independent pairs amplify that combined error; coordinate or
packing width does not substitute for a repetition count. Native rejection-
loop/FS/work refinement and authenticated lookup acceptance remain open.
-/

open scoped Classical
open OracleSpec OracleComp

namespace FormalProof4FHE.HasteBoots.TupleLookupPair

noncomputable section

def error (q width count size : ℕ) : ENNReal :=
  (size : ENNReal) * (((width - 1 : ℕ) : ENNReal) / q) +
    ((count + size - 1 : ℕ) : ENNReal) / ((q - size - 1 : ℕ) : ENNReal)

variable {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq K] [Fintype K] [SampleableType K]
  {width count size : ℕ}

def sample (table : Fin size → Fin width → F) : OptionT ProbComp (K × K) :=
  OptionT.lift ($ᵗ K) >>= fun y =>
    (fun r => (y, r)) <$> ReciprocalDetection.sample (fun i => TupleHash.hash y (table i))

def Passes (sources : Fin count → Fin width → F) (table : Fin size → Fin width → F)
    (multiplicities : Fin size → K) (pair : K × K) : Prop :=
  ReciprocalDetection.Passes (fun i => TupleHash.hash pair.1 (sources i))
    (fun i => TupleHash.hash pair.1 (table i)) multiplicities pair.2

def repeats (table : Fin size → Fin width → F) : ℕ → OptionT ProbComp (List (K × K))
  | 0 => pure []
  | repetitions + 1 => sample table >>= fun pair => List.cons pair <$> repeats table repetitions

def AllPass (sources : Fin count → Fin width → F) (table : Fin size → Fin width → F)
    (multiplicities : Fin size → K) (pairs : List (K × K)) : Prop :=
  ∀ pair ∈ pairs, Passes sources table multiplicities pair

theorem sample_total (table : Fin size → Fin width → F) (enough : size + 1 < Fintype.card K) :
    Pr{let _ ← sample (K := K) table}[True] = 1 := by
  apply prEvent_bind_eq_of_forall_eq (OptionT.lift ($ᵗ K)) (by simp [prEvent_norm])
  intro y
  rw [prEvent_map]
  exact ReciprocalDetection.sample_total _ enough

omit [DecidableEq K] [Fintype K] [SampleableType K] in
theorem allPass_cons (sources : Fin count → Fin width → F) (table : Fin size → Fin width → F)
    (multiplicities : Fin size → K) (pair : K × K) (pairs : List (K × K)) :
    AllPass sources table multiplicities (pair :: pairs) ↔
      Passes sources table multiplicities pair ∧ AllPass sources table multiplicities pairs := by
  simp [AllPass]

theorem repeats_total (table : Fin size → Fin width → F) (enough : size + 1 < Fintype.card K) (repetitions : ℕ) :
    Pr{let _ ← repeats (K := K) table repetitions}[True] = 1 := by
  induction repetitions with
  | zero => simp [repeats, prEvent_norm]
  | succ repetitions ih =>
    apply prEvent_bind_eq_of_forall_eq (sample (K := K) table) (sample_total table enough)
    intro pair
    rw [prEvent_map]
    exact ih

/-- Exact independence law for fresh pairs. It is not valid for reuse of a
previously sampled pair, nor for repetitions inferred from packing width. -/
theorem repeated_probability (sources : Fin count → Fin width → F) (table : Fin size → Fin width → F)
    (multiplicities : Fin size → K) (repetitions : ℕ) :
    Pr{let pairs ← repeats (K := K) table repetitions}[AllPass sources table multiplicities pairs] =
      Pr{let pair ← sample (K := K) table}[Passes sources table multiplicities pair] ^ repetitions := by
  induction repetitions with
  | zero => simp [repeats, AllPass, prEvent_norm]
  | succ repetitions ih =>
    have independent := prEvent_bind_and_eq_mul (sample (K := K) table)
      (fun _ : K × K => repeats (K := K) table repetitions)
      (AllPass sources table multiplicities) (Passes sources table multiplicities) (fun _ => rfl)
    calc _ = Pr{let pair ← sample (K := K) table; let rest ← repeats (K := K) table repetitions}[
          AllPass sources table multiplicities rest ∧ Passes sources table multiplicities pair] := by
            simp only [repeats, prEvent_norm, allPass_cons, and_comm]
         _ = Pr{let pairs ← repeats (K := K) table repetitions}[AllPass sources table multiplicities pairs] *
           Pr{let pair ← sample (K := K) table}[Passes sources table multiplicities pair] := independent
         _ = _ := by rw [ih, pow_succ]

variable {p : ℕ} [CharP K p]

theorem single_bound (sources : Fin count → Fin width → F) (table : Fin size → Fin width → F)
    (multiplicities : Fin size → K) (bad : ∃ i, ∀ j, sources i ≠ table j) (small : count < p) :
    Pr{let pair ← sample (K := K) table}[Passes sources table multiplicities pair] ≤
      error (Fintype.card K) width count size := by
  obtain ⟨i, outside⟩ := bad
  have conditional (y : K) (safe : ¬∃ j, TupleHash.hash y (sources i) = TupleHash.hash y (table j)) :
      Pr{let pair ← (fun r => (y, r)) <$> ReciprocalDetection.sample (fun j => TupleHash.hash y (table j))}[
        Passes sources table multiplicities pair] ≤
        ((count + size - 1 : ℕ) : ENNReal) / ((Fintype.card K - size - 1 : ℕ) : ENNReal) := by
    rw [prEvent_map]
    change Pr{let r ← ReciprocalDetection.sample (fun j => TupleHash.hash y (table j))}[
      ReciprocalDetection.Passes (fun j => TupleHash.hash y (sources j))
        (fun j => TupleHash.hash y (table j)) multiplicities r] ≤ _
    exact ReciprocalDetection.detection_bound (K := K) (p := p) (count := count) (size := size)
      (fun j => TupleHash.hash y (sources j)) (fun j => TupleHash.hash y (table j)) multiplicities
      ⟨i, fun j equal => safe ⟨j, equal⟩⟩ small
  have composed := prEvent_bind_le_prEvent_add (OptionT.lift ($ᵗ K))
    (fun y => (fun r => (y, r)) <$> ReciprocalDetection.sample (fun j => TupleHash.hash y (table j)))
    (fun y => ∃ j, TupleHash.hash y (sources i) = TupleHash.hash y (table j))
    (Passes sources table multiplicities) conditional
  rw [OptionT.prEvent_lift] at composed
  exact composed.trans (add_le_add (TupleHash.table_collision_bound (K := K) (sources i) table outside) le_rfl)

theorem repeated_bound (sources : Fin count → Fin width → F) (table : Fin size → Fin width → F)
    (multiplicities : Fin size → K) (bad : ∃ i, ∀ j, sources i ≠ table j) (small : count < p) (repetitions : ℕ) :
    Pr{let pairs ← repeats (K := K) table repetitions}[AllPass sources table multiplicities pairs] ≤
      error (Fintype.card K) width count size ^ repetitions := by
  induction repetitions with
  | zero => simp [repeats, AllPass, prEvent_norm]
  | succ repetitions ih =>
    rw [repeats]
    have bound := prEvent_bind_le_prEvent_mul_of_forall_le (sample (K := K) table)
      (fun pair => List.cons pair <$> repeats (K := K) table repetitions)
      (Passes sources table multiplicities) (AllPass sources table multiplicities)
      (ε := error (Fintype.card K) width count size ^ repetitions) ?_ ?_
    · apply bound.trans
      rw [pow_succ']
      gcongr
      exact single_bound sources table multiplicities bad small
    · intro pair passed
      simpa only [prEvent_map, allPass_cons, passed, true_and] using ih
    · intro pair failed
      simp only [prEvent_map, allPass_cons, failed, false_and, prEvent_false]

end

end FormalProof4FHE.HasteBoots.TupleLookupPair
