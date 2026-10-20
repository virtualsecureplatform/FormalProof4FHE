/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/
import FormalProof4FHE.LWE.RecursiveFeatureCubicApproximation
import FormalProof4FHE.LWE.GSWRotatedTrapdoorSource

/-!
# Testing affine processing of a complete same-key LWE source

An affine public map may mix source masks and noisy outputs across all
columns. Its recursive-ciphertext phase is affine
in the source masks, with a quadratic constant term. At a power-of-two
modulus this still cannot approximate a genuine cubic control with
overwhelming probability: the failure fraction is at least 1/16.

The source key may be any fixed function of the uniform binary output key;
it need not be binary or have the same dimension. The source masks remain
uniform and independent of those keys. Source errors and simulator coins
are independent of the output key and masks. This is not a public
distinguishing attack or an exclusion of nonlinear processing, public mask
rejection, or key-dependent simulator coefficients. No source hardness
assumption is made here.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.LWE.RecursiveFeatureAffineSource

open RecursiveFeatureCubicApproximation

def offsetPolynomial {R : Type} [CommRing R] {n : ℕ}
    (ciphertext : RecursiveQuadratic.Ciphertext R n) : RecursiveQuadratic.Polynomial R n 1 where
  quadratic := fun _ ↦ -ciphertext.1
  linear := fun _ ↦ ciphertext.2.1
  constant := fun _ ↦ ciphertext.2.2

theorem message_offsetPolynomial {R : Type} [CommRing R] {n : ℕ}
    (ciphertext : RecursiveQuadratic.Ciphertext R n) (secret : Fin n → R) :
    RecursiveQuadratic.message (offsetPolynomial ciphertext) secret 0 =
      RecursiveQuadratic.decrypt secret ciphertext := by
  simp [RecursiveQuadratic.message, offsetPolynomial, RecursiveQuadratic.decrypt,
    vecMul, dotProduct, Finset.sum_neg_distrib, mul_neg]
  ring

def decryptLinear {R : Type} [CommRing R] {n : ℕ} (secret : Fin n → R) :
    RecursiveQuadratic.Ciphertext R n →ₗ[R] R where
  toFun := RecursiveQuadratic.decrypt secret
  map_add' first second := by
    simp only [RecursiveQuadratic.decrypt, Prod.fst_add, Prod.snd_add,
      vecMul_add, add_dotProduct]
    ring
  map_smul' scalar ciphertext := by
    simp [RecursiveQuadratic.decrypt, vecMul, dotProduct, Finset.mul_sum,
      mul_sub, mul_add, mul_left_comm, mul_comm]

def sourceLinear {R : Type} [CommRing R] {n p : ℕ} (secret : Fin n → R) :
    Matrix (Fin n) (Fin p) R →ₗ[R] BatchTranscript R n p where
  toFun := fun masks ↦ (masks, vecMul secret masks)
  map_add' first second := by simp [vecMul_add]
  map_smul' scalar masks := by
    apply Prod.ext
    · rfl
    · funext column
      simp [vecMul, dotProduct, Finset.mul_sum, mul_left_comm]

/-- The entire affine map is public; its constant term after fixing independent
source errors remains a fixed ciphertext, whose phase is quadratic in the key. -/
theorem affine_source_phase {R : Type} [CommRing R] {d n p : ℕ}
    (transform : BatchTranscript R d p →ₗ[R] RecursiveQuadratic.Ciphertext R n)
    (offset : RecursiveQuadratic.Ciphertext R n) (errors : Fin p → R)
    (sourceSecret : Fin d → R) (outputSecret : Fin n → R)
    (masks : Matrix (Fin d) (Fin p) R) :
    RecursiveQuadratic.decrypt outputSecret
        (transform (masks, vecMul sourceSecret masks + errors) + offset) =
      ((decryptLinear outputSecret).comp (transform.comp (sourceLinear sourceSecret))) masks +
        RecursiveQuadratic.message (offsetPolynomial (transform (0, errors) + offset)) outputSecret 0 := by
  rw [message_offsetPolynomial]
  change (decryptLinear outputSecret) _ = _
  have hraw : (masks, vecMul sourceSecret masks + errors) =
      sourceLinear sourceSecret masks + (0, errors) := by ext <;> simp [sourceLinear]
  rw [hraw, map_add, map_add, map_add]
  change _ = _ + (decryptLinear outputSecret) (transform (0, errors) + offset)
  simp only [map_add, LinearMap.comp_apply]
  abel

theorem magnitude_sub_comm {q : ℕ} [NeZero q] (first second : ZMod q) :
    magnitude (first - second) = magnitude (second - first) := by
  rw [← neg_sub second first]
  exact LatticeCrypto.centeredRepr_natAbs_neg _

/-- Translation by a half-turn pairs every good source with a bad source.
The linear map and its nonzero coefficient can depend on the fixed secret. -/
theorem affine_bad_source_count {levels : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    [AddCommGroup X] [Module (ZMod (2 ^ levels)) X]
    (linear : X →ₗ[ZMod (2 ^ levels)] ZMod (2 ^ levels))
    (offset : ZMod (2 ^ levels)) (bound : ℕ)
    (hsmall : 2 * bound < magnitude ((2 ^ (levels - 1) : ℕ) : ZMod (2 ^ levels)))
    (hgap : bound < magnitude offset) :
    Fintype.card X ≤ 2 * (Finset.univ.filter fun x : X ↦
      bound < magnitude (linear x + offset)).card := by
  classical
  by_cases hzero : linear = 0
  · simp only [hzero, LinearMap.zero_apply, zero_add, hgap, Finset.filter_true,
      Finset.card_univ]
    omega
  · have hexists : ∃ x : X, linear x ≠ 0 := by
      by_contra h
      push Not at h
      exact hzero (LinearMap.ext h)
    obtain ⟨x, hx⟩ := hexists
    obtain ⟨level, hlevel⟩ := GSWRotatedTrapdoorSource.exists_half_turn (linear x) hx
    let shift : X := ((2 ^ level.val : ℕ) : ZMod (2 ^ levels)) • x
    have hshift : linear shift = ((2 ^ (levels - 1) : ℕ) : ZMod (2 ^ levels)) := by
      simpa only [shift, map_smul, smul_eq_mul] using hlevel
    have hbad (a : X) (ha : magnitude (linear a + offset) ≤ bound) :
        bound < magnitude (linear (a + shift) + offset) := by
      by_contra hb
      have hb' : magnitude (linear (a + shift) + offset) ≤ bound := by omega
      have htriangle := TFHE.NoiseBounds.centeredRepr_sub_natAbs_le
        (linear (a + shift) + offset) (linear a + offset)
      have hdiff : (linear (a + shift) + offset) - (linear a + offset) =
          ((2 ^ (levels - 1) : ℕ) : ZMod (2 ^ levels)) := by
        rw [map_add, hshift]
        ring
      change magnitude _ ≤ magnitude _ + magnitude _ at htriangle
      rw [hdiff] at htriangle
      omega
    let translate : {a : X // magnitude (linear a + offset) ≤ bound} →
        {a : X // bound < magnitude (linear a + offset)} :=
      fun a ↦ ⟨a.val + shift, hbad a.val a.property⟩
    have hinjective : Function.Injective translate := by
      intro a b hab
      apply Subtype.ext
      exact add_right_cancel (congrArg Subtype.val hab)
    have hcount := Fintype.card_le_of_injective translate hinjective
    simp only [Fintype.card_subtype] at hcount
    have hpartition := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset X))
      (fun a ↦ magnitude (linear a + offset) ≤ bound)
    simp only [not_le, Finset.card_univ] at hpartition
    omega

/-- Counting form of the constant 1/16 failure bound, allowing arbitrary
key-dependent linear source coefficients. The offset alone must be quadratic. -/
theorem cubic_affine_failure_sum {levels k : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    [AddCommGroup X] [Module (ZMod (2 ^ levels)) X]
    (linear : (Fin (3 + k) → Bool) → X →ₗ[ZMod (2 ^ levels)] ZMod (2 ^ levels))
    (polynomial : RecursiveQuadratic.Polynomial (ZMod (2 ^ levels)) (3 + k) 1)
    (bound : ℕ)
    (hweight : 8 * bound < magnitude ((2 ^ (levels - 1) : ℕ) : ZMod (2 ^ levels))) :
    2 ^ (3 + k) * Fintype.card X ≤ 16 * ∑ bits : Fin (3 + k) → Bool,
      (Finset.univ.filter fun x : X ↦ bound < magnitude
        (linear bits x + RecursiveQuadratic.message polynomial (GSWSelfKey.binaryEmbed bits) 0 -
          ((2 ^ (levels - 1) : ℕ) : ZMod (2 ^ levels)) *
            GSWSelfKey.binaryEmbed bits 0 * GSWSelfKey.binaryEmbed bits 1 *
              GSWSelfKey.binaryEmbed bits 2)).card := by
  classical
  let weight : ZMod (2 ^ levels) := ((2 ^ (levels - 1) : ℕ) : ZMod (2 ^ levels))
  let badCount (bits : Fin (3 + k) → Bool) :=
    (Finset.univ.filter fun x : X ↦ bound < magnitude
      (linear bits x + RecursiveQuadratic.message polynomial (GSWSelfKey.binaryEmbed bits) 0 -
        weight * GSWSelfKey.binaryEmbed bits 0 * GSWSelfKey.binaryEmbed bits 1 *
          GSWSelfKey.binaryEmbed bits 2)).card
  have hpoint (bits : Fin (3 + k) → Bool) :
      (if bound < discrepancy weight polynomial bits then Fintype.card X else 0) ≤
        2 * badCount bits := by
    split_ifs with hbad
    · have hgap : bound < magnitude
          (RecursiveQuadratic.message polynomial (GSWSelfKey.binaryEmbed bits) 0 -
            weight * GSWSelfKey.binaryEmbed bits 0 * GSWSelfKey.binaryEmbed bits 1 *
              GSWSelfKey.binaryEmbed bits 2) := by
        rw [magnitude_sub_comm]
        exact hbad
      simpa only [badCount, add_sub_assoc] using
        affine_bad_source_count (linear bits) _ bound (by omega) hgap
    · exact Nat.zero_le _
  have hsum := Finset.sum_le_sum (fun bits (_ : bits ∈ Finset.univ) ↦ hpoint bits)
  have hleft : (∑ bits : Fin (3 + k) → Bool,
        if bound < discrepancy weight polynomial bits then Fintype.card X else 0) =
      (Finset.univ.filter fun bits : Fin (3 + k) → Bool ↦
        bound < discrepancy weight polynomial bits).card * Fintype.card X := by
    rw [← Finset.sum_filter]
    simp
  rw [hleft, ← Finset.mul_sum] at hsum
  have hkeys := bad_key_count weight polynomial bound hweight
  have hcombined := (Nat.mul_le_mul_right (Fintype.card X) hkeys).trans hsum
  have hfinal := Nat.mul_le_mul_left 8 hcombined
  simpa only [pow_add, show 2 ^ 3 = 8 from rfl, ← Nat.mul_assoc,
    show 8 * 2 = 16 from rfl, badCount, weight] using hfinal

/-- Instantiation for an arbitrary affine map of the COMPLETE source, with any
fixed source-key transport and errors. Masks are independent of the output key.
No source column is supplied as unproved auxiliary input. -/
theorem source_simulator_failure_sum {levels d k p : ℕ}
    (transform : BatchTranscript (ZMod (2 ^ levels)) d p →ₗ[ZMod (2 ^ levels)]
      RecursiveQuadratic.Ciphertext (ZMod (2 ^ levels)) (3 + k))
    (offset : RecursiveQuadratic.Ciphertext (ZMod (2 ^ levels)) (3 + k))
    (sourceSecret : (Fin (3 + k) → Bool) → Fin d → ZMod (2 ^ levels))
    (errors : Fin p → ZMod (2 ^ levels)) (bound : ℕ)
    (hweight : 8 * bound < magnitude ((2 ^ (levels - 1) : ℕ) : ZMod (2 ^ levels))) :
    2 ^ (3 + k) * Fintype.card (Matrix (Fin d) (Fin p) (ZMod (2 ^ levels))) ≤
      16 * ∑ bits : Fin (3 + k) → Bool,
        (Finset.univ.filter fun masks : Matrix (Fin d) (Fin p) (ZMod (2 ^ levels)) ↦
          bound < magnitude
            (RecursiveQuadratic.decrypt (GSWSelfKey.binaryEmbed bits)
                (transform (masks, vecMul (sourceSecret bits) masks + errors) + offset) -
              ((2 ^ (levels - 1) : ℕ) : ZMod (2 ^ levels)) *
                GSWSelfKey.binaryEmbed bits 0 * GSWSelfKey.binaryEmbed bits 1 *
                  GSWSelfKey.binaryEmbed bits 2)).card := by
  simpa only [affine_source_phase] using
    cubic_affine_failure_sum
      (fun bits ↦ (decryptLinear (GSWSelfKey.binaryEmbed bits)).comp
        (transform.comp (sourceLinear (sourceSecret bits))))
      (offsetPolynomial (transform (0, errors) + offset)) bound hweight

open OracleComp

/-- A quantitative affine phase-simulation obstruction, not an IND-CPA
lower bound. The uniform sampler is on pairs of a binary key and source masks. -/
theorem source_simulator_failure_probability {levels d k p : ℕ}
    (transform : BatchTranscript (ZMod (2 ^ levels)) d p →ₗ[ZMod (2 ^ levels)]
      RecursiveQuadratic.Ciphertext (ZMod (2 ^ levels)) (3 + k))
    (offset : RecursiveQuadratic.Ciphertext (ZMod (2 ^ levels)) (3 + k))
    (sourceSecret : (Fin (3 + k) → Bool) → Fin d → ZMod (2 ^ levels))
    (errors : Fin p → ZMod (2 ^ levels)) (bound : ℕ)
    (hweight : 8 * bound < magnitude ((2 ^ (levels - 1) : ℕ) : ZMod (2 ^ levels))) :
    (1 / 16 : ℝ) ≤ (Pr[(fun draw : (Fin (3 + k) → Bool) ×
        Matrix (Fin d) (Fin p) (ZMod (2 ^ levels)) ↦
      bound < magnitude
        (RecursiveQuadratic.decrypt (GSWSelfKey.binaryEmbed draw.1)
            (transform (draw.2, vecMul (sourceSecret draw.1) draw.2 + errors) + offset) -
          ((2 ^ (levels - 1) : ℕ) : ZMod (2 ^ levels)) *
            GSWSelfKey.binaryEmbed draw.1 0 * GSWSelfKey.binaryEmbed draw.1 1 *
              GSWSelfKey.binaryEmbed draw.1 2)) | ($ᵗ _)]).toReal := by
  classical
  let Bad (bits : Fin (3 + k) → Bool)
      (masks : Matrix (Fin d) (Fin p) (ZMod (2 ^ levels))) : Prop :=
    bound < magnitude
      (RecursiveQuadratic.decrypt (GSWSelfKey.binaryEmbed bits)
          (transform (masks, vecMul (sourceSecret bits) masks + errors) + offset) -
        ((2 ^ (levels - 1) : ℕ) : ZMod (2 ^ levels)) *
          GSWSelfKey.binaryEmbed bits 0 * GSWSelfKey.binaryEmbed bits 1 *
            GSWSelfKey.binaryEmbed bits 2)
  have hcard : (Finset.univ.filter fun draw : (Fin (3 + k) → Bool) ×
        Matrix (Fin d) (Fin p) (ZMod (2 ^ levels)) ↦ Bad draw.1 draw.2).card =
      ∑ bits : Fin (3 + k) → Bool, (Finset.univ.filter (Bad bits)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [← Finset.univ_product_univ, Finset.sum_product]
  have hcount := source_simulator_failure_sum transform offset sourceSecret errors bound hweight
  change _ ≤ 16 * ∑ bits : Fin (3 + k) → Bool,
    (Finset.univ.filter (Bad bits)).card at hcount
  rw [← hcard] at hcount
  rw [probEvent_uniformSample, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  apply (le_div_iff₀ (by positivity)).mpr
  have hreal := (by exact_mod_cast hcount :
    (2 : ℝ) ^ (3 + k) *
        Fintype.card (Matrix (Fin d) (Fin p) (ZMod (2 ^ levels))) ≤
      16 * ((Finset.univ.filter fun draw : (Fin (3 + k) → Bool) ×
        Matrix (Fin d) (Fin p) (ZMod (2 ^ levels)) ↦ Bad draw.1 draw.2).card : ℝ))
  dsimp only [Bad] at hreal
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hreal ⊢
  nlinarith

end FormalProof4FHE.LWE.RecursiveFeatureAffineSource
