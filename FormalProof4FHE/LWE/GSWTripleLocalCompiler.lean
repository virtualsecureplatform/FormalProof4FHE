/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/
import FormalProof4FHE.LWE.GSWPairLocalCompiler
import FormalProof4FHE.LWE.GSWLinearCharacterCompiler
import FormalProof4FHE.LWE.RecursiveFeatureCubicApproximation

/-!
# Candidate keys for public triple-local cubic controls

A fixed public quadratic on each three-bit target excludes at least one
assignment when eight times the residual bound is below the centered target
weight. If every triple is covered, compatible binary keys have VC dimension
at most two and cardinality at most 1+n+choose(n,2).

This is a pointwise statement, allowing coefficients computed from the whole
public transcript. It does not apply to dense quadratic corrections involving
other secret coordinates. The character-compiler connection below concerns
the restricted target-pair shortcut only, not the existing dense compiler.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.LWE.GSWTripleLocalCompiler

open RecursiveFeatureCubicApproximation GSWLinearCharacterCompiler

def discrepancy {q : ℕ} [NeZero q] (weight : ZMod q)
    (polynomial : RecursiveQuadratic.Polynomial (ZMod q) 3 1) (a b c : Bool) : ℕ :=
  magnitude (weight * (RecursiveFeatureGSW.corner3 a b c : Fin 3 → ZMod q) 0 *
    (RecursiveFeatureGSW.corner3 a b c) 1 * (RecursiveFeatureGSW.corner3 a b c) 2 -
      RecursiveQuadratic.message polynomial (RecursiveFeatureGSW.corner3 a b c) 0)

theorem not_shatters_triple {α : Type} [DecidableEq α] {q : ℕ} [NeZero q]
    (family : Finset (Finset α)) (i j k : α) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (weight : ZMod q) (polynomial : RecursiveQuadratic.Polynomial (ZMod q) 3 1)
    (bound : ℕ) (hweight : 8 * bound < magnitude weight)
    (hgood : ∀ s ∈ family, discrepancy weight polynomial
      (decide (i ∈ s)) (decide (j ∈ s)) (decide (k ∈ s)) ≤ bound) :
    ¬ family.Shatters {i, j, k} := by
  intro hs
  obtain ⟨a, b, c, habc⟩ := exists_bad_corner weight polynomial bound hweight
  let target : Finset α :=
    (if a then {i} else ∅) ∪ (if b then {j} else ∅) ∪ (if c then {k} else ∅)
  have ht : target ⊆ {i, j, k} := by
    cases a <;> cases b <;> cases c <;> simp [target, Finset.insert_subset_iff]
  obtain ⟨s, hsf, heq⟩ := hs ht
  have hi : decide (i ∈ s) = a := by
    have hm := Finset.ext_iff.mp heq i
    cases a <;> cases b <;> cases c <;> simp [target, hij, hik] at hm <;> simp [hm]
  have hj : decide (j ∈ s) = b := by
    have hm := Finset.ext_iff.mp heq j
    cases a <;> cases b <;> cases c <;> simp [target, Ne.symm hij, hjk] at hm <;> simp [hm]
  have hk : decide (k ∈ s) = c := by
    have hm := Finset.ext_iff.mp heq k
    cases a <;> cases b <;> cases c <;> simp [target, Ne.symm hik, Ne.symm hjk] at hm <;> simp [hm]
  have hb := hgood s hsf
  rw [hi, hj, hk] at hb
  exact (Nat.not_lt_of_ge hb) habc

theorem vcDim_le_two {α : Type} [DecidableEq α] [Fintype α]
    (family : Finset (Finset α))
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ family.Shatters {i, j, k}) :
    family.vcDim ≤ 2 := by
  apply Finset.sup_le
  intro s hs
  by_contra h
  obtain ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩ := Finset.two_lt_card_iff.mp (Nat.lt_of_not_ge h)
  exact htriple i j k hij hik hjk ((Finset.mem_shatterer.mp hs).mono_right
    (by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hi, hj, hk⟩))

theorem card_le_of_no_shattered_triple {α : Type} [DecidableEq α] [Fintype α]
    (family : Finset (Finset α))
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ family.Shatters {i, j, k}) :
    family.card ≤ 1 + Fintype.card α + (Fintype.card α).choose 2 := by
  have hvc := vcDim_le_two family htriple
  calc
    family.card ≤ family.shatterer.card := Finset.card_le_card_shatterer family
    _ ≤ ∑ d ∈ Finset.Iic family.vcDim, (Fintype.card α).choose d :=
      Finset.card_shatterer_le_sum_vcDim
    _ ≤ ∑ d ∈ Finset.Iic 2, (Fintype.card α).choose d := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.Iic_subset_Iic.mpr hvc
      · intro d _ _; exact Nat.zero_le _
    _ = _ := by
      have hi : Finset.Iic (2 : ℕ) = {0, 1, 2} := by
        ext d
        simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_singleton]
        omega
      simp [hi, Nat.add_assoc]

/-- All weights and quadratic coefficients may be chosen from the complete
transcript before applying this theorem. No coefficient independence is used. -/
theorem candidate_key_bound {α : Type} [DecidableEq α] [Fintype α]
    {q : ℕ} [NeZero q] (family : Finset (Finset α))
    (weight : α → α → α → ZMod q)
    (polynomial : α → α → α → RecursiveQuadratic.Polynomial (ZMod q) 3 1)
    (bound : ℕ)
    (hweight : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → 8 * bound < magnitude (weight i j k))
    (hgood : ∀ s ∈ family, ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      discrepancy (weight i j k) (polynomial i j k)
        (decide (i ∈ s)) (decide (j ∈ s)) (decide (k ∈ s)) ≤ bound) :
    family.card ≤ 1 + Fintype.card α + (Fintype.card α).choose 2 := by
  apply card_le_of_no_shattered_triple
  intro i j k hij hik hjk
  exact not_shatters_triple family i j k hij hik hjk (weight i j k) (polynomial i j k)
    bound (hweight i j k hij hik hjk) (fun s hs ↦ hgood s hs i j k hij hik hjk)

theorem sort_triple {n : ℕ} (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ a b c : Fin n, a < b ∧ b < c ∧ ({i, j, k} : Finset (Fin n)) = {a, b, c} := by
  have hs (a b c : Fin n) (horder : a < b ∧ b < c)
      (heq : ({i, j, k} : Finset (Fin n)) = {a, b, c}) :
      ∃ a b c : Fin n, a < b ∧ b < c ∧ ({i, j, k} : Finset (Fin n)) = {a, b, c} :=
    ⟨a, b, c, horder.1, horder.2, heq⟩
  by_cases h : i < j
  · by_cases h' : j < k
    · exact hs i j k ⟨h, h'⟩ rfl
    · by_cases h'' : i < k
      · apply hs i k j (by omega)
        ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
      · apply hs k i j (by omega)
        ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · by_cases h' : i < k
    · apply hs j i k (by omega)
      ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    · by_cases h'' : j < k
      · apply hs j k i (by omega)
        ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
      · apply hs k j i (by omega)
        ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

/-- One public constraint per unordered triple is sufficient; six copies in
different target/feature orders are not required. -/
theorem sorted_candidate_key_bound {n q : ℕ} [NeZero q]
    (family : Finset (Finset (Fin n))) (weight : Fin n → Fin n → Fin n → ZMod q)
    (polynomial : Fin n → Fin n → Fin n → RecursiveQuadratic.Polynomial (ZMod q) 3 1)
    (bound : ℕ)
    (hweight : ∀ i j k, i < j → j < k → 8 * bound < magnitude (weight i j k))
    (hgood : ∀ s ∈ family, ∀ i j k, i < j → j < k →
      discrepancy (weight i j k) (polynomial i j k)
        (decide (i ∈ s)) (decide (j ∈ s)) (decide (k ∈ s)) ≤ bound) :
    family.card ≤ 1 + n + n.choose 2 := by
  have hc := card_le_of_no_shattered_triple family (by
    intro i j k hij hik hjk
    obtain ⟨a, b, c, hab, hbc, heq⟩ := sort_triple i j k hij hik hjk
    rw [heq]
    exact not_shatters_triple family a b c (ne_of_lt hab) (ne_of_lt (hab.trans hbc)) (ne_of_lt hbc)
      (weight a b c) (polynomial a b c) bound (hweight a b c hab hbc)
      (fun s hs ↦ hgood s hs a b c hab hbc))
  simpa using hc

/-- Partial assignments also have a polynomial candidate bound: bits outside
the current public prefix are fixed false, and only completed triples need
constraints. This supports incremental public enumeration, rather than an
exhaustive search over all 2^n assignments. -/
theorem prefix_candidate_key_bound {α : Type} [DecidableEq α] [Fintype α]
    {q : ℕ} [NeZero q] (family : Finset (Finset α)) (known : Finset α)
    (weight : α → α → α → ZMod q)
    (polynomial : α → α → α → RecursiveQuadratic.Polynomial (ZMod q) 3 1) (bound : ℕ)
    (hinside : ∀ s ∈ family, s ⊆ known)
    (hweight : ∀ i j k, i ∈ known → j ∈ known → k ∈ known →
      i ≠ j → i ≠ k → j ≠ k → 8 * bound < magnitude (weight i j k))
    (hgood : ∀ s ∈ family, ∀ i j k, i ∈ known → j ∈ known → k ∈ known →
      i ≠ j → i ≠ k → j ≠ k → discrepancy (weight i j k) (polynomial i j k)
        (decide (i ∈ s)) (decide (j ∈ s)) (decide (k ∈ s)) ≤ bound) :
    family.card ≤ 1 + Fintype.card α + (Fintype.card α).choose 2 := by
  apply card_le_of_no_shattered_triple
  intro i j k hij hik hjk
  by_cases hall : i ∈ known ∧ j ∈ known ∧ k ∈ known
  · exact not_shatters_triple family i j k hij hik hjk (weight i j k) (polynomial i j k) bound
      (hweight i j k hall.1 hall.2.1 hall.2.2 hij hik hjk)
      (fun s hs ↦ hgood s hs i j k hall.1 hall.2.1 hall.2.2 hij hik hjk)
  · have hout : ∃ x ∈ ({i, j, k} : Finset α), x ∉ known := by
      by_cases hi : i ∈ known
      · by_cases hj : j ∈ known
        · exact ⟨k, by simp, fun hk ↦ hall ⟨hi, hj, hk⟩⟩
        · exact ⟨j, by simp, hj⟩
      · exact ⟨i, by simp, hi⟩
    obtain ⟨x, hx, hnot⟩ := hout
    intro hshatters
    obtain ⟨s, hs, heq⟩ := hshatters (Finset.singleton_subset_iff.mpr hx)
    have hxinter : x ∈ {i, j, k} ∩ s := by rw [heq]; simp
    exact hnot (hinside s hs (Finset.mem_inter.mp hxinter).2)

/-- Rows of the same source restricted to its target triple; no source body is
resampled. A public row permutation puts any chosen triple in this position. -/
def headMask {R : Type} {k m : ℕ} (a : Matrix (Fin (3 + k)) (Fin m) R) :
    Matrix (Fin 3) (Fin m) R := fun row column ↦ a (row.castAdd k) column

/-- The actual target-pair coefficient certificate: only three pairs are used,
and outside-triple coefficients vanish after multiplication by four. The
resulting FULL ambient cubic phase is exactly the target-triple phase. -/
theorem target_pair_cubic_phase {R : Type} [CommRing R] {k m : ℕ}
    (a : Matrix (Fin (3 + k)) (Fin m) R) (u : Matrix (Fin 3) (Fin m) R)
    (houtside : ∀ (pair : Fin 3) (row : Fin k), 4 * projectedMask a u pair (row.natAdd 3) = 0)
    (head : Fin 3 → R) (tail : Fin k → R) :
    cubicPhase (fun pair ↦ (first3 pair).castAdd k) (fun pair ↦ (second3 pair).castAdd k)
        a u (Fin.append head tail) =
      4 * coefficient3 (headMask a) u * head 0 * head 1 * head 2 := by
  have hmain : cubicPhase (fun pair ↦ (first3 pair).castAdd k) (fun pair ↦ (second3 pair).castAdd k)
      a u (Fin.append head tail) = cubicPhase first3 second3 (headMask a) u head := by
    unfold cubicPhase tailPhase
    apply Finset.sum_congr rfl
    intro pair _
    simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, mul_add]
    have hzero : 4 * head (first3 pair) * head (second3 pair) *
        (∑ row : Fin k, if row.natAdd 3 ≠ (first3 pair).castAdd k ∧
          row.natAdd 3 ≠ (second3 pair).castAdd k then
            projectedMask a u pair (row.natAdd 3) * tail row else 0) = 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro row _
      split_ifs
      · linear_combination head (first3 pair) * head (second3 pair) * tail row * houtside pair row
      · simp
    rw [hzero, add_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro row _
    simp only [ne_eq, Fin.castAdd_inj]
    rfl
  rw [hmain, cubicPhase_three]

/-- The target-pair shortcut's outside-triple coefficient equations force
these confined projections. This lemma accounts for their actual source noise. -/
theorem confined_projection {R : Type} [CommRing R] {k m : ℕ}
    (a : Matrix (Fin (3 + k)) (Fin m) R) (u : Matrix (Fin 3) (Fin m) R)
    (houtside : ∀ (pair : Fin 3) (row : Fin k), projectedMask a u pair (row.natAdd 3) = 0)
    (head : Fin 3 → R) (tail : Fin k → R) (error : Fin m → R) (pair : Fin 3) :
    dotProduct (u pair) (vecMul (Fin.append head tail) a + error) =
      dotProduct (u pair) (vecMul head (headMask a) + error) := by
  rw [dotProduct_add, dotProduct_add]
  congr 1
  rw [dotProduct_comm (u pair) (vecMul (Fin.append head tail) a), ← dotProduct_mulVec,
    dotProduct_comm (u pair) (vecMul head (headMask a)), ← dotProduct_mulVec]
  change dotProduct (Fin.append head tail) (projectedMask a u pair) = _
  simp only [dotProduct, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  simp_rw [houtside pair]
  simp only [mul_zero, Finset.sum_const_zero, add_zero]
  rfl

theorem compileCanonical_eq_of_projections {R P : Type} [CommRing R] [Fintype P] {n m : ℕ}
    (first second : P → Fin n) (a : Matrix (Fin n) (Fin m) R) (u : Matrix P (Fin m) R)
    (left right : Fin m → R) (heq : ∀ pair, dotProduct (u pair) left = dotProduct (u pair) right) :
    compileCanonical first second a u left = compileCanonical first second a u right := by
  simp only [compileCanonical, compile, GSWLinearCharacterCompiler.polynomial, heq]

theorem decrypt_compile_message {R P : Type} [CommRing R] [Fintype P] {n m : ℕ}
    (first second : P → Fin n) (a : Matrix (Fin n) (Fin m) R) (u : Matrix P (Fin m) R)
    (body : Fin m → R) (secret : Fin n → R) :
    RecursiveQuadratic.decrypt secret (compile first second a u body) =
      RecursiveQuadratic.message (GSWLinearCharacterCompiler.polynomial first second a u body) secret 0 := by
  simp only [RecursiveQuadratic.decrypt, compile, RecursiveQuadratic.message,
    vecMul, dotProduct, Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib]
  ring

/-- A small confined-source character certificate produces a PUBLIC quadratic
on just the three target bits, even though all original source bodies are
retained and the other secret coordinates are arbitrary. Thus the candidate
key bound applies to this shortcut before any recursive-zero rerandomization.
The generic dense compiler has no outside-projection hypothesis of this form. -/
theorem local_compiler_error_bound {q k m : ℕ} [NeZero q]
    (a : Matrix (Fin (3 + k)) (Fin m) (ZMod q)) (u : Matrix (Fin 3) (Fin m) (ZMod q))
    (houtside : ∀ (pair : Fin 3) (row : Fin k), projectedMask a u pair (row.natAdd 3) = 0)
    (weight : ZMod q) (hcoefficient : 4 * coefficient3 (headMask a) u = weight)
    (bits : Fin 3 → Bool) (tail : Fin k → ZMod q) (error : Fin m → ZMod q) (E : ℕ)
    (herror : ∀ column, (LatticeCrypto.centeredRepr (error column)).natAbs ≤ E) :
    discrepancy weight
      (GSWLinearCharacterCompiler.polynomial first3 second3 (headMask a) u
        (vecMul (Fin.append (GSWSelfKey.binaryEmbed bits) tail) a + error))
      (bits 0) (bits 1) (bits 2) ≤
        (∑ pair, ∑ column, (LatticeCrypto.centeredRepr (u pair column)).natAbs) * E := by
  let body := vecMul (Fin.append (GSWSelfKey.binaryEmbed bits) tail) a + error
  have hproj := compileCanonical_eq_of_projections first3 second3 (headMask a) u body
    (vecMul (GSWSelfKey.binaryEmbed bits) (headMask a) + error)
    (confined_projection a u houtside (GSWSelfKey.binaryEmbed bits) tail error)
  have he := phase_error_bound first3 second3 first3_ne_second3 (headMask a) u bits error E herror
  rw [cubicPhase_three, hcoefficient, ← hproj] at he
  rw [compileCanonical, normalize_decrypt _ _ (GSWSelfKey.binaryEmbed_idempotent bits),
    decrypt_compile_message] at he
  have hbits : GSWSelfKey.binaryEmbed (R := ZMod q) bits =
      RecursiveFeatureGSW.corner3 (bits 0) (bits 1) (bits 2) := by
    funext row
    fin_cases row <;> rfl
  rw [hbits] at he
  unfold discrepancy
  rw [← neg_sub, magnitude, LatticeCrypto.centeredRepr_natAbs_neg]
  exact he

def scaleCoefficients {R : Type} [CommRing R] {m : ℕ}
    (scale : R) (u : Matrix (Fin 3) (Fin m) R) : Matrix (Fin 3) (Fin m) R :=
  fun pair column ↦ scale * u pair column

theorem projectedMask_scaleCoefficients {R : Type} [CommRing R] {n m : ℕ}
    (a : Matrix (Fin n) (Fin m) R) (scale : R) (u : Matrix (Fin 3) (Fin m) R)
    (pair : Fin 3) (row : Fin n) :
    projectedMask a (scaleCoefficients scale u) pair row = scale * projectedMask a u pair row := by
  simp only [projectedMask, mulVec, dotProduct, scaleCoefficients, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro column _
  ring

theorem coefficient3_scaleCoefficients {R : Type} [CommRing R] {m : ℕ}
    (a : Matrix (Fin 3) (Fin m) R) (scale : R) (u : Matrix (Fin 3) (Fin m) R) :
    coefficient3 a (scaleCoefficients scale u) = scale * coefficient3 a u := by
  simp only [coefficient3, projectedMask_scaleCoefficients]
  ring

theorem scaled_coefficient_bound {q m : ℕ} [NeZero q] (scale : ℕ)
    (u : Matrix (Fin 3) (Fin m) (ZMod q)) :
    (∑ pair, ∑ column, (LatticeCrypto.centeredRepr (scaleCoefficients (scale : ZMod q) u pair column)).natAbs) ≤
      scale * (∑ pair, ∑ column, (LatticeCrypto.centeredRepr (u pair column)).natAbs) := by
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro pair _
  apply Finset.sum_le_sum
  intro column _
  exact (TFHE.NoiseBounds.centeredRepr_mul_natAbs_le _ _).trans
    (Nat.mul_le_mul_right _ (TFHE.NoiseBounds.centeredRepr_natCast_natAbs_le scale))

/-- Exact character equations modulo q/4 force 4*A*u=0 outside the triple,
not A*u=0 modulo q. The public scaled correction handles that torsion and
has residual at most 4*E*||u||_1. Its target is 4*weight: the key-list margin
must be checked at THAT weight, so top weights that scale to zero do not qualify. -/
theorem local_compiler_scaled_error_bound {q k m : ℕ} [NeZero q]
    (a : Matrix (Fin (3 + k)) (Fin m) (ZMod q)) (u : Matrix (Fin 3) (Fin m) (ZMod q))
    (houtside : ∀ (pair : Fin 3) (row : Fin k), 4 * projectedMask a u pair (row.natAdd 3) = 0)
    (weight : ZMod q) (hcoefficient : 4 * coefficient3 (headMask a) u = weight)
    (bits : Fin 3 → Bool) (tail : Fin k → ZMod q) (error : Fin m → ZMod q) (E : ℕ)
    (herror : ∀ column, (LatticeCrypto.centeredRepr (error column)).natAbs ≤ E) :
    discrepancy (4 * weight)
      (GSWLinearCharacterCompiler.polynomial first3 second3 (headMask a) (scaleCoefficients 4 u)
        (vecMul (Fin.append (GSWSelfKey.binaryEmbed bits) tail) a + error))
      (bits 0) (bits 1) (bits 2) ≤
        4 * (∑ pair, ∑ column, (LatticeCrypto.centeredRepr (u pair column)).natAbs) * E := by
  have hout : ∀ (pair : Fin 3) (row : Fin k),
      projectedMask a (scaleCoefficients 4 u) pair (row.natAdd 3) = 0 := by
    intro pair row
    rw [projectedMask_scaleCoefficients, houtside pair row]
  have hc : 4 * coefficient3 (headMask a) (scaleCoefficients 4 u) = 4 * weight := by
    rw [coefficient3_scaleCoefficients, ← hcoefficient]
  exact (local_compiler_error_bound a (scaleCoefficients 4 u) hout (4 * weight) hc
    bits tail error E herror).trans (Nat.mul_le_mul_right E (scaled_coefficient_bound 4 u))

/-- Four times the level-(levels-4) gadget weight is the nonzero quarter turn.
This avoids applying the candidate argument at top weights annihilated by four. -/
theorem scaled_lower_weight_magnitude (levels : ℕ) (hlevels : 4 ≤ levels) :
    magnitude (4 * ((2 ^ (levels - 4) : ℕ) : ZMod (2 ^ levels))) = 2 ^ (levels - 2) := by
  have hnat : 4 * 2 ^ (levels - 4) = 2 ^ (levels - 2) := by
    rw [show levels - 2 = (levels - 4) + 2 from by omega, pow_add]
    ring
  have hcast : (4 : ZMod (2 ^ levels)) * ((2 ^ (levels - 4) : ℕ) : ZMod (2 ^ levels)) =
      ((2 ^ (levels - 2) : ℕ) : ZMod (2 ^ levels)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      congrArg (fun value : ℕ ↦ (value : ZMod (2 ^ levels))) hnat
  have hq : 2 ^ levels = 4 * 2 ^ (levels - 2) := by
    calc
      _ = 2 ^ ((levels - 2) + 2) := by congr 1; omega
      _ = _ := by rw [pow_add]; ring
  have hhalf : 2 ^ (levels - 2) ≤ 2 ^ levels / 2 := by rw [hq]; omega
  rw [hcast, magnitude, LatticeCrypto.centeredRepr_eq_valMinAbs,
    ZMod.valMinAbs_natCast_of_le_half hhalf, Int.natAbs_natCast]

theorem scaled_lower_weight_gap (levels : ℕ) (hlevels : 4 ≤ levels) (J : ℕ)
    (hbudget : 128 * J < 2 ^ levels) :
    8 * (4 * J) < magnitude (4 * ((2 ^ (levels - 4) : ℕ) : ZMod (2 ^ levels))) := by
  rw [scaled_lower_weight_magnitude levels hlevels]
  have hq : 2 ^ levels = 4 * 2 ^ (levels - 2) := by
    calc
      _ = 2 ^ ((levels - 2) + 2) := by congr 1; omega
      _ = _ := by rw [pow_add]; ring
  rw [hq] at hbudget
  omega

theorem scaled_gap_of_control_budget (levels : ℕ) (hlevels : 4 ≤ levels) (J K F : ℕ)
    (hJK : J ≤ K) (hF : 32 ≤ F) (hbudget : 4 * F * K < 2 ^ levels) :
    8 * (4 * J) < magnitude (4 * ((2 ^ (levels - 4) : ℕ) : ZMod (2 ^ levels))) := by
  apply scaled_lower_weight_gap levels hlevels J
  have hmul := Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right K hF)
  have hj := Nat.mul_le_mul_left 128 hJK
  nlinarith

/-- The public whole-table norm threshold at one lower gadget level already
forces a quadratic-size key list for the exact target-pair shortcut. -/
theorem scaled_candidate_key_bound {n levels : ℕ} (hlevels : 4 ≤ levels) (J : ℕ)
    (hbudget : 128 * J < 2 ^ levels) (family : Finset (Finset (Fin n)))
    (polynomial : Fin n → Fin n → Fin n → RecursiveQuadratic.Polynomial (ZMod (2 ^ levels)) 3 1)
    (hgood : ∀ s ∈ family, ∀ i j k, i < j → j < k →
      discrepancy (4 * ((2 ^ (levels - 4) : ℕ) : ZMod (2 ^ levels))) (polynomial i j k)
        (decide (i ∈ s)) (decide (j ∈ s)) (decide (k ∈ s)) ≤ 4 * J) :
    family.card ≤ 1 + n + n.choose 2 := by
  exact sorted_candidate_key_bound family (fun _ _ _ ↦
    4 * ((2 ^ (levels - 4) : ℕ) : ZMod (2 ^ levels))) polynomial (4 * J)
    (fun _ _ _ _ _ ↦ scaled_lower_weight_gap levels hlevels J hbudget) hgood

end FormalProof4FHE.LWE.GSWTripleLocalCompiler
