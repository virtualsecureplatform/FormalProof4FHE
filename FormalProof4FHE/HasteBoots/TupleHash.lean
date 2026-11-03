module

public import FormalProof4FHE.HasteBoots.PackedSumcheckProbability
public import Mathlib.Algebra.Polynomial.OfFn

@[expose] public section

/-!
# Native tuple hashing in a base or extension field

One fresh scalar challenge hashes an entire ordered tuple. The native power
loop, zip and left-to-right sum equal polynomial evaluation. Distinct base
tuples give distinct extension-field polynomials of degree at most width-1.
A fixed nonmember collides with the public table only within its table-size
union bound. Selecting one bad source before the challenge avoids an extra
source-count factor. Reciprocal detection, repetition, authenticated lookup
execution and native field/Fiat--Shamir refinement remain separate obligations.
-/

open scoped BigOperators
open OracleSpec OracleComp Polynomial

namespace FormalProof4FHE.HasteBoots.TupleHash

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] {width : ℕ}

def powers (y start : K) : ℕ → List K
  | 0 => []
  | count + 1 => start :: powers y (start * y) count

theorem powers_eq (y start : K) (count : ℕ) :
    powers y start count = List.ofFn (fun i : Fin count => start * y ^ i.val) := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    simp only [powers, List.ofFn_succ, Fin.val_zero, pow_zero, mul_one, ih, Fin.val_succ, pow_succ]
    congr 1
    apply congrArg List.ofFn
    funext i
    ring

private theorem zip_vectors {A B C : Type} {count : ℕ} (f : A → B → C)
    (first : Fin count → A) (second : Fin count → B) :
    (List.ofFn first).zipWith f (List.ofFn second) = List.ofFn (fun i => f (first i) (second i)) := by
  induction count with
  | zero => rfl
  | succ count ih => rw [List.ofFn_succ, List.ofFn_succ, List.zipWith_cons_cons, ih, List.ofFn_succ]

private theorem foldl_add (values : List K) (initial : K) :
    values.foldl (fun sum value => sum + value) initial = initial + values.sum := by
  induction values generalizing initial with
  | nil => simp
  | cons value rest ih => simp only [List.foldl_cons, ih, List.sum_cons, add_assoc]

def hash (y : K) (row : Fin width → F) : K :=
  ((powers y 1 width).zipWith (fun power coefficient => power * algebraMap F K coefficient)
    (List.ofFn row)).foldl (fun sum term => sum + term) 0

theorem hash_eq_sum (y : K) (row : Fin width → F) :
    hash y row = ∑ i, y ^ i.val * algebraMap F K (row i) := by
  rw [hash, powers_eq, zip_vectors, foldl_add, zero_add, List.sum_ofFn]
  simp only [one_mul]

theorem hash_add (y : K) (first second : Fin width → F) :
    hash y (first + second) = hash y first + hash y second := by
  simp only [hash_eq_sum, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem hash_smul (y : K) (coefficient : F) (row : Fin width → F) :
    hash y (coefficient • row) = coefficient • hash y row := by
  simp only [hash_eq_sum, Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply,
    Algebra.algebraMap_self_apply, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

variable [DecidableEq K]

def polynomial (row : Fin width → F) : K[X] :=
  Polynomial.ofFn width (fun i => algebraMap F K (row i))

theorem polynomial_injective : Function.Injective (polynomial (F := F) (K := K) (width := width)) := by
  intro first second equal
  have coefficients := Polynomial.injective_ofFn width equal
  funext i
  exact (algebraMap F K).injective (congrFun coefficients i)

theorem polynomial_degree (row : Fin width → F) : (polynomial (K := K) row).natDegree ≤ width - 1 := by
  by_cases empty : width = 0
  · subst width
    simp [polynomial]
  · have small := Polynomial.ofFn_natDegree_lt (by omega : 1 ≤ width)
      (fun i => algebraMap F K (row i))
    change (Polynomial.ofFn width (fun i => algebraMap F K (row i))).natDegree ≤ width - 1
    omega

theorem polynomial_eval (row : Fin width → F) (y : K) :
    (polynomial row).eval y = hash y row := by
  rw [hash_eq_sum, polynomial, Polynomial.ofFn_eq_sum_monomial]
  simp [Polynomial.eval_finsetSum, mul_comm]

variable [Fintype K]

theorem collision_card (first second : Fin width → F) (different : first ≠ second) :
    (Finset.univ.filter (fun y : K => hash y first = hash y second)).card ≤ width - 1 := by
  simpa only [← polynomial_eval] using
    PackedSumcheckProbability.agreement_card (polynomial (K := K) first) (polynomial second) (width - 1)
      (fun same => different (polynomial_injective same)) (polynomial_degree first) (polynomial_degree second)

variable [SampleableType K]

theorem collision_bound (first second : Fin width → F) (different : first ≠ second) :
    Pr{let y ← $ᵗ K}[hash y first = hash y second] ≤ (width - 1 : ℕ) / (Fintype.card K : ENNReal) := by
  rw [SampleableType.prEvent_uniformSample]
  apply ENNReal.div_le_div_right
  exact_mod_cast collision_card (K := K) first second different

/-- Table entries all share this one scalar challenge. -/
theorem table_collision_bound {size : ℕ} (row : Fin width → F) (table : Fin size → Fin width → F)
    (outside : ∀ i, row ≠ table i) :
    Pr{let y ← $ᵗ K}[∃ i, hash y row = hash y (table i)] ≤
      (size : ENNReal) * ((width - 1 : ℕ) / (Fintype.card K : ENNReal)) := by
  simpa only [Fintype.card_fin] using
    (prEvent_exists_le_card_mul ($ᵗ K) (fun i y => hash y row = hash y (table i))
      (fun i => collision_bound row (table i) (outside i)))

/-- Pick a fixed bad source before y. No extra union over source positions is
needed, even when all sources share the same scalar hash challenge. -/
theorem family_miss_bound {Position : Type} {size : ℕ}
    (sources : Position → Fin width → F) (table : Fin size → Fin width → F)
    (bad : ∃ position, ∀ i, sources position ≠ table i) :
    Pr{let y ← $ᵗ K}[∀ position, ∃ i, hash y (sources position) = hash y (table i)] ≤
      (size : ENNReal) * ((width - 1 : ℕ) / (Fintype.card K : ENNReal)) := by
  obtain ⟨position, outside⟩ := bad
  exact (prEvent_mono _ _ _ (fun _ all => all position)).trans (table_collision_bound _ _ outside)

/-- Literal ordered native public table, including possible duplicate rows. -/
theorem list_collision_bound (row : Fin width → F) (table : List (Fin width → F)) (outside : row ∉ table) :
    Pr{let y ← $ᵗ K}[∃ entry ∈ table, hash y row = hash y entry] ≤
      (table.length : ENNReal) * ((width - 1 : ℕ) / (Fintype.card K : ENNReal)) := by
  have each (i : Fin table.length) : row ≠ table.get i := by
    intro equal
    exact outside (equal ▸ List.get_mem table i)
  have bound := table_collision_bound (K := K) row (fun i => table.get i) each
  apply le_trans (prEvent_mono _ _ _ ?_) bound
  intro y hit
  obtain ⟨entry, member, equal⟩ := hit
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp member
  exact ⟨i, equal⟩

theorem list_family_miss_bound {Position : Type} (sources : Position → Fin width → F)
    (table : List (Fin width → F)) (bad : ∃ position, sources position ∉ table) :
    Pr{let y ← $ᵗ K}[∀ position, ∃ entry ∈ table, hash y (sources position) = hash y entry] ≤
      (table.length : ENNReal) * ((width - 1 : ℕ) / (Fintype.card K : ENNReal)) := by
  obtain ⟨position, outside⟩ := bad
  exact (prEvent_mono _ _ _ (fun _ all => all position)).trans (list_collision_bound _ _ outside)

end

end FormalProof4FHE.HasteBoots.TupleHash
