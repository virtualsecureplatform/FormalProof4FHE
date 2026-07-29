/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.TwoBlock
import FormalProof4FHE.Probability.SquaredBias
import FormalProof4FHE.RLWE.RankOneHNFLossinessSupportAware
import FormalProof4FHE.TFHE.BootstrappingSecurity
import FormalProof4FHE.TFHE.RingSquareTopWeightCoefficientAffine

/-!
# Coefficient-dependent RGSW circular security

This module formalizes the finite, concrete content of
`sketch/rgsw_coefficient_circular_security.tex`.

The proof has four checked parts.

* A generic squared-bias theorem removes a deterministic, finite-valued function of an
  arbitrarily distributed secret.  The loss is the paper's
  `Gamma(p, nu) = sum_lambda p_lambda / nu_lambda`.  An optimized auxiliary law gives the
  order-`1/2` Renyi concentration, while a uniform auxiliary value gives the unconditional
  cardinality loss.
* Adding the rank-one TGSW gadget matrix for a leaked coefficient is a public permutation of a
  homogeneous RLWE transcript.  The mask block has message `-g * h(S) * S` and the body block has
  message `g * h(S)`.
* One coefficient, or one finite tuple of coefficients encoded as a single leakage value, is
  therefore bounded by a doubled-sample ordinary RLWE reduction plus the ordinary zero-message
  RLWE hybrid.
* Publicly aggregating the top gadget-one rows of the complete coefficient family produces the
  quadratic row `Abar * S - eta * S^2 + Ebar`.  This proves the quadratic aggregation barrier and
  records why the one-coordinate theorem cannot simply be iterated over the full key.

All games are finite `ProbComp` games.  Efficiency is represented, as elsewhere in the project,
by an external predicate on distinguishers.  The optimized-law theorem assumes that the stated
auxiliary probability law is realized by a `ProbComp`; this is the exact finite counterpart of
the paper's efficient-samplability premise.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.RGSWCoefficientCircularSecurity

noncomputable section

/-! ## Finite order-`1/2` concentration -/

/-- Real probability mass of one output of a finite computation. -/
def probabilityMass {A : Type} (sampler : ProbComp A) (value : A) : ℝ :=
  Pr[= value | sampler].toReal

/-- Order-`1/2` Renyi concentration `(sum_x sqrt(p_x))^2`. -/
def halfRenyiConcentration {A : Type} [Fintype A] (sampler : ProbComp A) : ℝ :=
  (∑ value, Real.sqrt (probabilityMass sampler value)) ^ 2

theorem probabilityMass_nonneg {A : Type} (sampler : ProbComp A) (value : A) :
    0 ≤ probabilityMass sampler value :=
  ENNReal.toReal_nonneg

/-- The real masses of a finite total computation sum to one. -/
theorem sum_probabilityMass_eq_one {A : Type} [Fintype A] (sampler : ProbComp A) :
    ∑ value, probabilityMass sampler value = 1 := by
  classical
  unfold probabilityMass
  rw [← ENNReal.toReal_sum (fun value _ ↦ probOutput_ne_top),
    sum_probOutput_eq_one (by simp), ENNReal.toReal_one]

/-- Grouping an expectation through a deterministic leakage map is exact. -/
theorem expectation_map_leakage
    {Secret Leakage : Type} [Fintype Secret] [Fintype Leakage]
    (secretSampler : ProbComp Secret) (leakage : Secret → Leakage)
    (observable : Leakage → ℝ) :
    BoundedMoment.expectation secretSampler (fun secret ↦ observable (leakage secret)) =
      BoundedMoment.expectation (leakage <$> secretSampler) observable := by
  rw [BoundedMoment.expectation_map]

/-- The Renyi-half concentration of a uniform finite type is exactly its cardinality. -/
theorem halfRenyiConcentration_uniform
    {A : Type} [Fintype A] [Nonempty A] [SampleableType A] :
    halfRenyiConcentration ($ᵗ A) = Fintype.card A := by
  classical
  let card : ℝ := Fintype.card A
  have hcard : 0 < card := by
    dsimp [card]
    exact_mod_cast Fintype.card_pos
  have hsqrt : Real.sqrt (card⁻¹) ^ 2 = card⁻¹ := by
    rw [Real.sq_sqrt]
    exact inv_nonneg.mpr hcard.le
  unfold halfRenyiConcentration probabilityMass
  simp_rw [probOutput_uniformSample, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [Finset.sum_const, Finset.card_univ]
  simp only [nsmul_eq_mul]
  change ((Fintype.card A : ℝ) * Real.sqrt card⁻¹) ^ 2 = Fintype.card A
  rw [mul_pow, hsqrt]
  dsimp [card]
  field_simp

/-- Every distribution on a finite carrier has Renyi-half concentration at most the carrier
cardinality.  Choosing the leakage carrier to be its actual support yields the paper's support
bound. -/
theorem halfRenyiConcentration_le_card
    {A : Type} [Fintype A] (sampler : ProbComp A) :
    halfRenyiConcentration sampler ≤ Fintype.card A := by
  classical
  have hCauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : A ↦ (1 : ℝ))
    (fun value ↦ Real.sqrt (probabilityMass sampler value))
  have hSquares :
      (∑ value : A, Real.sqrt (probabilityMass sampler value) ^ 2) = 1 := by
    simp_rw [Real.sq_sqrt (probabilityMass_nonneg sampler _)]
    exact sum_probabilityMass_eq_one sampler
  unfold halfRenyiConcentration
  simpa [hSquares] using hCauchy

/-- Uniform binary leakage has concentration two. -/
theorem halfRenyiConcentration_uniform_bool :
    halfRenyiConcentration ($ᵗ Bool) = 2 := by
  simpa using (halfRenyiConcentration_uniform (A := Bool))

/-- Uniform centered-ternary leakage, represented by `Fin 3`, has concentration three. -/
theorem halfRenyiConcentration_uniform_ternary :
    halfRenyiConcentration ($ᵗ (Fin 3)) = 3 := by
  simpa using (halfRenyiConcentration_uniform (A := Fin 3))

/-- A joint uniform binary tuple has concentration `2^count`. -/
theorem halfRenyiConcentration_uniform_binaryTuple (count : ℕ) :
    halfRenyiConcentration ($ᵗ (Fin count → Bool)) = 2 ^ count := by
  rw [halfRenyiConcentration_uniform]
  simp

/-- A joint uniform ternary tuple has concentration `3^count`. -/
theorem halfRenyiConcentration_uniform_ternaryTuple (count : ℕ) :
    halfRenyiConcentration ($ᵗ (Fin count → Fin 3)) = 3 ^ count := by
  rw [halfRenyiConcentration_uniform]
  simp

/-- Any distribution of a ternary tuple has concentration at most `3^count`. -/
theorem halfRenyiConcentration_ternaryTuple_le (count : ℕ)
    (sampler : ProbComp (Fin count → Fin 3)) :
    halfRenyiConcentration sampler ≤ 3 ^ count := by
  simpa [Fintype.card_fun] using halfRenyiConcentration_le_card sampler

/-! ## The generic weighted squared-bias inequality -/

/-- Finite weighted Cauchy--Schwarz in exactly the diagonal form needed by leakage removal. -/
theorem weighted_diagonal_cauchy
    {A : Type} [Fintype A]
    (p nu delta : A → ℝ)
    (hp : ∀ value, 0 ≤ p value)
    (hnu : ∀ value, 0 ≤ nu value)
    (hcover : ∀ value, p value ≠ 0 → nu value ≠ 0) :
    (∑ value, p value * delta value) ^ 2 ≤
      (∑ value, p value * nu value * delta value ^ 2) *
        ∑ value, p value / nu value := by
  classical
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
  · intro value _
    exact mul_nonneg (mul_nonneg (hp value) (hnu value)) (sq_nonneg _)
  · intro value _
    exact div_nonneg (hp value) (hnu value)
  · intro value _
    by_cases hpzero : p value = 0
    · simp [hpzero]
    · have hnuzero := hcover value hpzero
      field_simp
      ring_nf
      exact le_rfl

/-- The paper's `Gamma(p,nu)`, written as an expectation over the genuine secret. -/
def leakageGamma
    {Secret Leakage : Type} [Fintype Secret]
    (secretSampler : ProbComp Secret) (auxiliarySampler : ProbComp Leakage)
    (leakage : Secret → Leakage) : ℝ :=
  BoundedMoment.expectation secretSampler fun secret ↦
    1 / probabilityMass auxiliarySampler (leakage secret)

/-- The matching diagonal second moment retained after discarding wrong leakage guesses. -/
def matchingSecondMoment
    {Secret Leakage : Type} [Fintype Secret]
    (secretSampler : ProbComp Secret) (auxiliarySampler : ProbComp Leakage)
    (leakage : Secret → Leakage) (delta : Leakage → Secret → ℝ) : ℝ :=
  BoundedMoment.expectation secretSampler fun secret ↦
    probabilityMass auxiliarySampler (leakage secret) * delta (leakage secret) secret ^ 2

/-- Full second moment obtained by independently guessing a leakage value and sampling a secret. -/
def guessedSecondMoment
    {Secret Leakage : Type} [Fintype Secret] [Fintype Leakage]
    (secretSampler : ProbComp Secret) (auxiliarySampler : ProbComp Leakage)
    (delta : Leakage → Secret → ℝ) : ℝ :=
  BoundedMoment.expectation auxiliarySampler fun guessed ↦
    BoundedMoment.expectation secretSampler fun secret ↦ delta guessed secret ^ 2

/-- The true diagonal signed gap is controlled by `Gamma` times its matching second moment. -/
theorem sq_expectation_diagonal_le_gamma_mul_matching
    {Secret Leakage : Type} [Fintype Secret]
    (secretSampler : ProbComp Secret) (auxiliarySampler : ProbComp Leakage)
    (leakage : Secret → Leakage) (delta : Leakage → Secret → ℝ)
    (hcover : ∀ secret, probabilityMass secretSampler secret ≠ 0 →
      probabilityMass auxiliarySampler (leakage secret) ≠ 0) :
    BoundedMoment.expectation secretSampler
        (fun secret ↦ delta (leakage secret) secret) ^ 2 ≤
      leakageGamma secretSampler auxiliarySampler leakage *
        matchingSecondMoment secretSampler auxiliarySampler leakage delta := by
  classical
  have h := weighted_diagonal_cauchy
    (fun secret ↦ probabilityMass secretSampler secret)
    (fun secret ↦ probabilityMass auxiliarySampler (leakage secret))
    (fun secret ↦ delta (leakage secret) secret)
    (probabilityMass_nonneg secretSampler)
    (fun secret ↦ probabilityMass_nonneg auxiliarySampler (leakage secret)) hcover
  change
    (∑ secret, probabilityMass secretSampler secret *
      delta (leakage secret) secret) ^ 2 ≤
      (∑ secret, probabilityMass secretSampler secret *
        (1 / probabilityMass auxiliarySampler (leakage secret))) *
      ∑ secret, probabilityMass secretSampler secret *
        (probabilityMass auxiliarySampler (leakage secret) *
          delta (leakage secret) secret ^ 2)
  calc
    _ ≤
      (∑ secret, probabilityMass secretSampler secret *
        probabilityMass auxiliarySampler (leakage secret) *
          delta (leakage secret) secret ^ 2) *
      ∑ secret, probabilityMass secretSampler secret /
        probabilityMass auxiliarySampler (leakage secret) := h
    _ = _ := by
      rw [mul_comm]
      congr 1
      · apply Finset.sum_congr rfl
        intro secret _
        ring
      · apply Finset.sum_congr rfl
        intro secret _
        ring

/-- Keeping only guesses equal to the genuine leakage can only decrease the nonnegative full
second moment. -/
theorem matchingSecondMoment_le_guessedSecondMoment
    {Secret Leakage : Type} [Fintype Secret] [Fintype Leakage]
    (secretSampler : ProbComp Secret) (auxiliarySampler : ProbComp Leakage)
    (leakage : Secret → Leakage) (delta : Leakage → Secret → ℝ) :
    matchingSecondMoment secretSampler auxiliarySampler leakage delta ≤
      guessedSecondMoment secretSampler auxiliarySampler delta := by
  classical
  unfold matchingSecondMoment guessedSecondMoment BoundedMoment.expectation probabilityMass
  calc
    (∑ secret,
        Pr[= secret | secretSampler].toReal *
          (Pr[= leakage secret | auxiliarySampler].toReal *
            delta (leakage secret) secret ^ 2)) ≤
      ∑ secret, Pr[= secret | secretSampler].toReal *
        (∑ guessed,
          Pr[= guessed | auxiliarySampler].toReal * delta guessed secret ^ 2) := by
      apply Finset.sum_le_sum
      intro secret _
      gcongr
      exact Finset.single_le_sum
        (s := Finset.univ)
        (f := fun guessed : Leakage ↦
          Pr[= guessed | auxiliarySampler].toReal * delta guessed secret ^ 2)
        (fun guessed _ ↦ mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
        (Finset.mem_univ (leakage secret))
    _ = ∑ guessed, Pr[= guessed | auxiliarySampler].toReal *
        (∑ secret,
          Pr[= secret | secretSampler].toReal * delta guessed secret ^ 2) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro guessed _
      apply Finset.sum_congr rfl
      intro secret _
      ring

/-! ## Abstract leakage-removal games -/

/-- Conditional signed gap for one guessed leakage value and one fixed secret. -/
def conditionalGap
    {Secret Leakage : Type}
    (real ideal : Leakage → Secret → ProbComp Bool)
    (guessed : Leakage) (secret : Secret) : ℝ :=
  SquaredBias.signedGap (real guessed secret) (ideal guessed secret)

/-- Real game carrying the genuine deterministic leakage of the secret. -/
def leakedRealGame
    {Secret Leakage : Type}
    (secretSampler : ProbComp Secret) (leakage : Secret → Leakage)
    (real : Leakage → Secret → ProbComp Bool) : ProbComp Bool := do
  let secret ← secretSampler
  real (leakage secret) secret

/-- Ideal game carrying the same genuine leakage value. -/
def leakedIdealGame
    {Secret Leakage : Type}
    (secretSampler : ProbComp Secret) (leakage : Secret → Leakage)
    (ideal : Leakage → Secret → ProbComp Bool) : ProbComp Bool := do
  let secret ← secretSampler
  ideal (leakage secret) secret

/-- Absolute distinguishing advantage in the genuine leaked experiment. -/
def leakedAdvantage
    {Secret Leakage : Type}
    (secretSampler : ProbComp Secret) (leakage : Secret → Leakage)
    (real ideal : Leakage → Secret → ProbComp Bool) : ℝ :=
  (leakedRealGame secretSampler leakage real).boolDistAdvantage
    (leakedIdealGame secretSampler leakage ideal)

/-- Independent auxiliary leakage guess and genuine secret. -/
def guessedContext
    {Secret Leakage : Type}
    (secretSampler : ProbComp Secret) (auxiliarySampler : ProbComp Leakage) :
    ProbComp (Leakage × Secret) := do
  let guessed ← auxiliarySampler
  let secret ← secretSampler
  return (guessed, secret)

/-- Real two-copy squared-bias game. -/
def leakageRemovalRealGame
    {Secret Leakage : Type}
    (secretSampler : ProbComp Secret) (auxiliarySampler : ProbComp Leakage)
    (real ideal : Leakage → Secret → ProbComp Bool) : ProbComp Bool :=
  SquaredBias.contextualExperiment (guessedContext secretSampler auxiliarySampler)
    (fun context ↦ real context.1 context.2)
    (fun context ↦ ideal context.1 context.2)

/-- Uniform endpoint of the two-copy reduction.  Both paired calls use the ideal conditional
game, so the result is exactly a fair bit. -/
def leakageRemovalIdealGame
    {Secret Leakage : Type}
    (secretSampler : ProbComp Secret) (auxiliarySampler : ProbComp Leakage)
    (ideal : Leakage → Secret → ProbComp Bool) : ProbComp Bool :=
  SquaredBias.contextualExperiment (guessedContext secretSampler auxiliarySampler)
    (fun context ↦ ideal context.1 context.2)
    (fun context ↦ ideal context.1 context.2)

/-- Advantage of the doubled-sample squared-bias reduction. -/
def leakageRemovalAdvantage
    {Secret Leakage : Type}
    (secretSampler : ProbComp Secret) (auxiliarySampler : ProbComp Leakage)
    (real ideal : Leakage → Secret → ProbComp Bool) : ℝ :=
  (leakageRemovalRealGame secretSampler auxiliarySampler real ideal).boolDistAdvantage
    (leakageRemovalIdealGame secretSampler auxiliarySampler ideal)

/-- The genuine leaked signed gap is the expectation of the diagonal conditional gap. -/
theorem signedGap_leakedGames
    {Secret Leakage : Type} [Fintype Secret]
    (secretSampler : ProbComp Secret) (leakage : Secret → Leakage)
    (real ideal : Leakage → Secret → ProbComp Bool) :
    SquaredBias.signedGap
        (leakedRealGame secretSampler leakage real)
        (leakedIdealGame secretSampler leakage ideal) =
      BoundedMoment.expectation secretSampler fun secret ↦
        conditionalGap real ideal (leakage secret) secret := by
  exact SquaredBias.signedGap_bind secretSampler
    (fun secret ↦ real (leakage secret) secret)
    (fun secret ↦ ideal (leakage secret) secret)

/-- The nested guessed second moment is the expectation on the independent context sampler. -/
theorem expectation_guessedContext_sq
    {Secret Leakage : Type} [Fintype Secret] [Fintype Leakage]
    (secretSampler : ProbComp Secret) (auxiliarySampler : ProbComp Leakage)
    (delta : Leakage → Secret → ℝ) :
    BoundedMoment.expectation (guessedContext secretSampler auxiliarySampler)
        (fun context ↦ delta context.1 context.2 ^ 2) =
      guessedSecondMoment secretSampler auxiliarySampler delta := by
  unfold guessedContext guessedSecondMoment
  rw [SquaredBias.expectation_bind_nested]
  apply congrArg (BoundedMoment.expectation auxiliarySampler)
  funext guessed
  rw [SquaredBias.expectation_bind_nested]
  simp only [BoundedMoment.expectation_pure]

/-- Exact true-output probability of the real two-copy reduction. -/
theorem probOutput_leakageRemovalRealGame_true
    {Secret Leakage : Type} [Fintype Secret] [Fintype Leakage]
    (secretSampler : ProbComp Secret) (auxiliarySampler : ProbComp Leakage)
    (real ideal : Leakage → Secret → ProbComp Bool) :
    Pr[= true |
      leakageRemovalRealGame secretSampler auxiliarySampler real ideal].toReal =
      (1 + guessedSecondMoment secretSampler auxiliarySampler
        (conditionalGap real ideal)) / 2 := by
  rw [leakageRemovalRealGame,
    SquaredBias.probOutput_contextualExperiment_true]
  have hMoment :=
    expectation_guessedContext_sq secretSampler auxiliarySampler
      (conditionalGap real ideal)
  simpa only [conditionalGap] using congrArg (fun moment : ℝ ↦ (1 + moment) / 2) hMoment

/-- The ideal two-copy reduction is exactly fair. -/
theorem probOutput_leakageRemovalIdealGame_true
    {Secret Leakage : Type} [Fintype Secret] [Fintype Leakage]
    (secretSampler : ProbComp Secret) (auxiliarySampler : ProbComp Leakage)
    (ideal : Leakage → Secret → ProbComp Bool) :
    Pr[= true |
      leakageRemovalIdealGame secretSampler auxiliarySampler ideal].toReal = 1 / 2 := by
  unfold leakageRemovalIdealGame
  rw [SquaredBias.probOutput_contextualExperiment_true]
  simp only [SquaredBias.signedGap, sub_self, OfNat.ofNat]
  rw [BoundedMoment.expectation_const]
  norm_num

/-- The doubled-sample source advantage is exactly half the guessed conditional second moment. -/
theorem leakageRemovalAdvantage_eq_half_guessedSecondMoment
    {Secret Leakage : Type} [Fintype Secret] [Fintype Leakage]
    (secretSampler : ProbComp Secret) (auxiliarySampler : ProbComp Leakage)
    (real ideal : Leakage → Secret → ProbComp Bool) :
    leakageRemovalAdvantage secretSampler auxiliarySampler real ideal =
      guessedSecondMoment secretSampler auxiliarySampler
        (conditionalGap real ideal) / 2 := by
  have hnonneg :
      0 ≤ guessedSecondMoment secretSampler auxiliarySampler
        (conditionalGap real ideal) := by
    unfold guessedSecondMoment BoundedMoment.expectation
    apply Finset.sum_nonneg
    intro guessed _
    apply mul_nonneg ENNReal.toReal_nonneg
    apply Finset.sum_nonneg
    intro secret _
    exact mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  unfold leakageRemovalAdvantage ProbComp.boolDistAdvantage
  rw [probOutput_leakageRemovalRealGame_true,
    probOutput_leakageRemovalIdealGame_true, abs_of_nonneg]
  · ring
  · linarith

/-- `Gamma` is nonnegative. -/
theorem leakageGamma_nonneg
    {Secret Leakage : Type} [Fintype Secret]
    (secretSampler : ProbComp Secret) (auxiliarySampler : ProbComp Leakage)
    (leakage : Secret → Leakage) :
    0 ≤ leakageGamma secretSampler auxiliarySampler leakage := by
  unfold leakageGamma BoundedMoment.expectation
  apply Finset.sum_nonneg
  intro secret _
  exact mul_nonneg ENNReal.toReal_nonneg
    (one_div_nonneg.mpr (probabilityMass_nonneg auxiliarySampler (leakage secret)))

/-- **Squared-bias leakage removal.**  The genuine leaked advantage squared is bounded by twice
`Gamma(p,nu)` times the advantage of the doubled-sample source reduction. -/
theorem leakedAdvantage_sq_le_two_mul_gamma_mul_removal
    {Secret Leakage : Type} [Fintype Secret] [Fintype Leakage]
    (secretSampler : ProbComp Secret) (auxiliarySampler : ProbComp Leakage)
    (leakage : Secret → Leakage)
    (real ideal : Leakage → Secret → ProbComp Bool)
    (hcover : ∀ secret, probabilityMass secretSampler secret ≠ 0 →
      probabilityMass auxiliarySampler (leakage secret) ≠ 0) :
    leakedAdvantage secretSampler leakage real ideal ^ 2 ≤
      2 * leakageGamma secretSampler auxiliarySampler leakage *
        leakageRemovalAdvantage secretSampler auxiliarySampler real ideal := by
  have hDiagonal := sq_expectation_diagonal_le_gamma_mul_matching
    secretSampler auxiliarySampler leakage (conditionalGap real ideal) hcover
  have hDiscard := matchingSecondMoment_le_guessedSecondMoment
    secretSampler auxiliarySampler leakage (conditionalGap real ideal)
  unfold leakedAdvantage ProbComp.boolDistAdvantage
  rw [show
      |Pr[= true | leakedRealGame secretSampler leakage real].toReal -
        Pr[= true | leakedIdealGame secretSampler leakage ideal].toReal| ^ 2 =
        SquaredBias.signedGap
          (leakedRealGame secretSampler leakage real)
          (leakedIdealGame secretSampler leakage ideal) ^ 2 by
      rw [sq_abs]
      rfl,
    signedGap_leakedGames]
  rw [leakageRemovalAdvantage_eq_half_guessedSecondMoment]
  calc
    _ ≤ leakageGamma secretSampler auxiliarySampler leakage *
        matchingSecondMoment secretSampler auxiliarySampler leakage
          (conditionalGap real ideal) := hDiagonal
    _ ≤ leakageGamma secretSampler auxiliarySampler leakage *
        guessedSecondMoment secretSampler auxiliarySampler
          (conditionalGap real ideal) := by
      gcongr
      exact leakageGamma_nonneg secretSampler auxiliarySampler leakage
    _ = 2 * leakageGamma secretSampler auxiliarySampler leakage *
        (guessedSecondMoment secretSampler auxiliarySampler
          (conditionalGap real ideal) / 2) := by ring

/-- Square-root form of the generic leakage-removal theorem. -/
theorem leakedAdvantage_le_sqrt_two_mul_gamma_mul_removal
    {Secret Leakage : Type} [Fintype Secret] [Fintype Leakage]
    (secretSampler : ProbComp Secret) (auxiliarySampler : ProbComp Leakage)
    (leakage : Secret → Leakage)
    (real ideal : Leakage → Secret → ProbComp Bool)
    (hcover : ∀ secret, probabilityMass secretSampler secret ≠ 0 →
      probabilityMass auxiliarySampler (leakage secret) ≠ 0) :
    leakedAdvantage secretSampler leakage real ideal ≤
      Real.sqrt (2 * leakageGamma secretSampler auxiliarySampler leakage *
        leakageRemovalAdvantage secretSampler auxiliarySampler real ideal) := by
  exact Real.le_sqrt_of_sq_le
    (leakedAdvantage_sq_le_two_mul_gamma_mul_removal
      secretSampler auxiliarySampler leakage real ideal hcover)

/-! ## Optimized and finite-alphabet leakage laws -/

/-- Marginal law of a deterministic leakage value. -/
def leakageLaw
    {Secret Leakage : Type}
    (secretSampler : ProbComp Secret) (leakage : Secret → Leakage) :
    ProbComp Leakage :=
  leakage <$> secretSampler

/-- Normalizing constant `sum_lambda sqrt(p_lambda)` for the optimized auxiliary law. -/
def halfRenyiNormalizer
    {Secret Leakage : Type} [Fintype Leakage]
    (secretSampler : ProbComp Secret) (leakage : Secret → Leakage) : ℝ :=
  ∑ value, Real.sqrt (probabilityMass (leakageLaw secretSampler leakage) value)

theorem halfRenyiConcentration_leakageLaw
    {Secret Leakage : Type} [Fintype Leakage]
    (secretSampler : ProbComp Secret) (leakage : Secret → Leakage) :
    halfRenyiConcentration (leakageLaw secretSampler leakage) =
      halfRenyiNormalizer secretSampler leakage ^ 2 :=
  rfl

/-- A finite leakage law has a positive Renyi-half normalizer. -/
theorem halfRenyiNormalizer_pos
    {Secret Leakage : Type} [Fintype Leakage]
    (secretSampler : ProbComp Secret) (leakage : Secret → Leakage) :
    0 < halfRenyiNormalizer secretSampler leakage := by
  classical
  let law := leakageLaw secretSampler leakage
  have hexists : ∃ value : Leakage, 0 < probabilityMass law value := by
    by_contra hnone
    push Not at hnone
    have hsumle : ∑ value : Leakage, probabilityMass law value ≤ 0 := by
      exact Finset.sum_nonpos fun value _ ↦ hnone value
    rw [sum_probabilityMass_eq_one] at hsumle
    norm_num at hsumle
  obtain ⟨value, hvalue⟩ := hexists
  have hterm :
      Real.sqrt (probabilityMass law value) ≤
        ∑ candidate : Leakage, Real.sqrt (probabilityMass law candidate) := by
    exact Finset.single_le_sum
      (s := Finset.univ)
      (f := fun candidate : Leakage ↦ Real.sqrt (probabilityMass law candidate))
      (fun candidate _ ↦ Real.sqrt_nonneg _)
      (Finset.mem_univ value)
  exact (Real.sqrt_pos.2 hvalue).trans_le hterm

/-- Expectation form of `Gamma` equals the paper's grouped sum `sum p_lambda / nu_lambda`. -/
theorem leakageGamma_eq_sum_ratio
    {Secret Leakage : Type} [Fintype Secret] [Fintype Leakage]
    (secretSampler : ProbComp Secret) (auxiliarySampler : ProbComp Leakage)
    (leakage : Secret → Leakage) :
    leakageGamma secretSampler auxiliarySampler leakage =
      ∑ value,
        probabilityMass (leakageLaw secretSampler leakage) value /
          probabilityMass auxiliarySampler value := by
  calc
    leakageGamma secretSampler auxiliarySampler leakage =
        BoundedMoment.expectation secretSampler
          (fun secret ↦
            (fun value ↦ 1 / probabilityMass auxiliarySampler value)
              (leakage secret)) := rfl
    _ = BoundedMoment.expectation (leakage <$> secretSampler)
          (fun value ↦ 1 / probabilityMass auxiliarySampler value) :=
      expectation_map_leakage secretSampler leakage
        (fun value : Leakage ↦ 1 / probabilityMass auxiliarySampler value)
    _ = ∑ value,
          probabilityMass (leakageLaw secretSampler leakage) value /
            probabilityMass auxiliarySampler value := by
      unfold BoundedMoment.expectation leakageLaw probabilityMass
      apply Finset.sum_congr rfl
      intro value _
      ring

/-- If an auxiliary sampler realizes probabilities proportional to `sqrt(p_lambda)`, its exact
`Gamma` is the order-`1/2` Renyi concentration.  Existence/efficient implementation of this
sampler is intentionally an explicit premise. -/
theorem leakageGamma_eq_halfRenyiConcentration_of_optimizedLaw
    {Secret Leakage : Type} [Fintype Secret] [Fintype Leakage]
    (secretSampler : ProbComp Secret) (auxiliarySampler : ProbComp Leakage)
    (leakage : Secret → Leakage)
    (hoptimized : ∀ value,
      probabilityMass auxiliarySampler value =
        Real.sqrt (probabilityMass (leakageLaw secretSampler leakage) value) /
          halfRenyiNormalizer secretSampler leakage) :
    leakageGamma secretSampler auxiliarySampler leakage =
      halfRenyiConcentration (leakageLaw secretSampler leakage) := by
  classical
  let normalizer := halfRenyiNormalizer secretSampler leakage
  have hnormalizer : 0 < normalizer := halfRenyiNormalizer_pos secretSampler leakage
  rw [leakageGamma_eq_sum_ratio]
  calc
    (∑ value,
        probabilityMass (leakageLaw secretSampler leakage) value /
          probabilityMass auxiliarySampler value) =
      ∑ value, normalizer *
        Real.sqrt (probabilityMass (leakageLaw secretSampler leakage) value) := by
      apply Finset.sum_congr rfl
      intro value _
      rw [hoptimized]
      by_cases hzero :
          probabilityMass (leakageLaw secretSampler leakage) value = 0
      · simp [hzero]
      · have hpositive :
            0 < probabilityMass (leakageLaw secretSampler leakage) value :=
          lt_of_le_of_ne (probabilityMass_nonneg _ _) (Ne.symm hzero)
        have hsqrt :
            Real.sqrt (probabilityMass (leakageLaw secretSampler leakage) value) ≠ 0 :=
          (Real.sqrt_pos.2 hpositive).ne'
        let p := probabilityMass (leakageLaw secretSampler leakage) value
        let root := Real.sqrt p
        have hrootSquare : root ^ 2 = p := Real.sq_sqrt hpositive.le
        change p / (root / halfRenyiNormalizer secretSampler leakage) =
          normalizer * root
        rw [← hrootSquare]
        field_simp
        ring
    _ = normalizer * normalizer := by
      rw [← Finset.mul_sum]
      rfl
    _ = halfRenyiConcentration (leakageLaw secretSampler leakage) := by
      rw [halfRenyiConcentration_leakageLaw]
      simp [normalizer, pow_two]

/-- Uniformly guessing a value in a nonempty finite leakage carrier has exact loss equal to the
carrier cardinality.  Taking the carrier to be the support gives the finite-support corollary. -/
theorem leakageGamma_uniform
    {Secret Leakage : Type} [Fintype Secret]
    [Fintype Leakage] [Nonempty Leakage] [SampleableType Leakage]
    (secretSampler : ProbComp Secret) (leakage : Secret → Leakage) :
    leakageGamma secretSampler ($ᵗ Leakage) leakage = Fintype.card Leakage := by
  have hcard : (Fintype.card Leakage : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt Fintype.card_pos)
  unfold leakageGamma probabilityMass
  simp_rw [probOutput_uniformSample, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [show (fun _ : Secret ↦ 1 / (Fintype.card Leakage : ℝ)⁻¹) =
      (fun _ : Secret ↦ (Fintype.card Leakage : ℝ)) by
    funext secret
    field_simp]
  exact BoundedMoment.expectation_const secretSampler (Fintype.card Leakage : ℝ)

/-- A uniform auxiliary guess covers every genuine leakage value. -/
theorem uniformAuxiliary_covers
    {Secret Leakage : Type} [Fintype Leakage] [Nonempty Leakage]
    [SampleableType Leakage]
    (secretSampler : ProbComp Secret) (leakage : Secret → Leakage) :
    ∀ secret, probabilityMass secretSampler secret ≠ 0 →
      probabilityMass ($ᵗ Leakage) (leakage secret) ≠ 0 := by
  intro secret _
  unfold probabilityMass
  rw [probOutput_uniformSample, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  exact inv_ne_zero (by exact_mod_cast (Nat.ne_of_gt Fintype.card_pos))

/-- Unconditional finite-carrier leakage removal. -/
theorem leakedAdvantage_le_sqrt_two_mul_card_mul_removal
    {Secret Leakage : Type} [Fintype Secret]
    [Fintype Leakage] [Nonempty Leakage] [SampleableType Leakage]
    (secretSampler : ProbComp Secret) (leakage : Secret → Leakage)
    (real ideal : Leakage → Secret → ProbComp Bool) :
    leakedAdvantage secretSampler leakage real ideal ≤
      Real.sqrt (2 * Fintype.card Leakage *
        leakageRemovalAdvantage secretSampler ($ᵗ Leakage) real ideal) := by
  simpa [leakageGamma_uniform secretSampler leakage] using
    (leakedAdvantage_le_sqrt_two_mul_gamma_mul_removal
      secretSampler ($ᵗ Leakage) leakage real ideal
        (uniformAuxiliary_covers secretSampler leakage))

/-! ## Native rank-one RGSW games -/

/-- Rank-one native RGSW challenge carrier. -/
abbrev RGSWChallenge (R : Type) (levels : ℕ) :=
  TGSW.Ciphertext R 1 levels

/-- Boolean distinguisher for one rank-one RGSW ciphertext. -/
abbrev RGSWDistinguisher (R : Type) (levels : ℕ) :=
  RGSWChallenge R levels → ProbComp Bool

/-- Remove a fixed native RGSW gadget translation. -/
def removeGadget {R : Type} [Ring R] {levels : ℕ}
    (gadget : Fin levels → R) (message : R)
    (ciphertext : RGSWChallenge R levels) : RGSWChallenge R levels :=
  (ciphertext.1 - TGSW.gadgetMaskShift gadget message,
    ciphertext.2 - TGSW.gadgetBodyShift gadget message)

@[simp]
theorem removeGadget_addGadget {R : Type} [Ring R] {levels : ℕ}
    (gadget : Fin levels → R) (message : R)
    (ciphertext : RGSWChallenge R levels) :
    removeGadget gadget message (TGSW.addGadget gadget message ciphertext) = ciphertext := by
  apply Prod.ext
  · funext coordinate row
    simp [removeGadget, TGSW.addGadget]
  · funext row
    simp [removeGadget, TGSW.addGadget]

@[simp]
theorem addGadget_removeGadget {R : Type} [Ring R] {levels : ℕ}
    (gadget : Fin levels → R) (message : R)
    (ciphertext : RGSWChallenge R levels) :
    TGSW.addGadget gadget message (removeGadget gadget message ciphertext) = ciphertext := by
  apply Prod.ext
  · funext coordinate row
    simp [removeGadget, TGSW.addGadget]
  · funext row
    simp [removeGadget, TGSW.addGadget]

/-- Adding a fixed rank-one gadget matrix is a public permutation. -/
theorem addGadget_bijective {R : Type} [Ring R] {levels : ℕ}
    (gadget : Fin levels → R) (message : R) :
    Function.Bijective
      (TGSW.addGadget (dimension := 1) gadget message) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨removeGadget gadget message,
      removeGadget_addGadget gadget message,
      addGadget_removeGadget gadget message⟩

/-- Fixed-message gadget translation preserves the uniform complete ciphertext law. -/
theorem addGadget_uniform_evalDist
    {R : Type} [Ring R] [Fintype R] [SampleableType R] {levels : ℕ}
    (gadget : Fin levels → R) (message : R) :
    evalDist
        (TGSW.addGadget gadget message <$> ($ᵗ (RGSWChallenge R levels))) =
      evalDist ($ᵗ (RGSWChallenge R levels)) := by
  exact evalDist_map_bijective_uniform_cross
    (α := RGSWChallenge R levels) (β := RGSWChallenge R levels)
    (TGSW.addGadget gadget message) (addGadget_bijective gadget message)

/-- The native upper gadget row is the bilinear coefficient-product row from the paper. -/
theorem coefficient_gadgetPhase_upper
    {R Secret Leakage : Type} [CommRing R] {levels : ℕ}
    (embed : Secret → Fin 1 → R) (encode : Leakage → R)
    (leakage : Secret → Leakage) (gadget : Fin levels → R)
    (secret : Secret) (level : Fin levels) :
    TGSW.gadgetPhase (embed secret) gadget (encode (leakage secret))
        (finProdFinEquiv (Fin.castSucc (0 : Fin 1), level)) =
      -(embed secret 0 * (encode (leakage secret) * gadget level)) :=
  TGSW.gadgetPhase_castSucc (embed secret) gadget (encode (leakage secret)) 0 level

/-- The native lower gadget row is the linear coefficient row from the paper. -/
theorem coefficient_gadgetPhase_lower
    {R Secret Leakage : Type} [Ring R] {levels : ℕ}
    (embed : Secret → Fin 1 → R) (encode : Leakage → R)
    (leakage : Secret → Leakage) (gadget : Fin levels → R)
    (secret : Secret) (level : Fin levels) :
    TGSW.gadgetPhase (embed secret) gadget (encode (leakage secret))
        (finProdFinEquiv (Fin.last 1, level)) =
      encode (leakage secret) * gadget level :=
  TGSW.gadgetPhase_last (embed secret) gadget (encode (leakage secret)) level

/-- Conditional native RGSW game for a guessed leakage value and fixed secret. -/
def conditionalRGSWReal
    {R Secret Leakage : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (embed : Secret → Fin 1 → R)
    (encode : Leakage → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : RGSWDistinguisher R levels)
    (guessed : Leakage) (secret : Secret) : ProbComp Bool := do
  let ciphertext ← TGSW.encrypt 1 levels errorSampler (embed secret) gadget (encode guessed)
  distinguisher ciphertext

/-- Conditional ideal game.  Its uniform ciphertext is independent of both the guess and secret. -/
def conditionalRGSWIdeal
    {R Secret Leakage : Type}
    [SampleableType R]
    (levels : ℕ) (_embed : Secret → Fin 1 → R)
    (_encode : Leakage → R) (_gadget : Fin levels → R)
    (distinguisher : RGSWDistinguisher R levels)
    (_guessed : Leakage) (_secret : Secret) : ProbComp Bool := do
  let ciphertext ← $ᵗ (RGSWChallenge R levels)
  distinguisher ciphertext

/-- Honest coefficient-dependent rank-one RGSW game. -/
def rgswRealGame
    {R Secret Leakage : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (leakage : Secret → Leakage)
    (encode : Leakage → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : RGSWDistinguisher R levels) :
    ProbComp Bool := do
  let secret ← secretSampler
  let ciphertext ← TGSW.encrypt 1 levels errorSampler (embed secret) gadget
    (encode (leakage secret))
  distinguisher ciphertext

/-- Zero-message RGSW game under the same secret distribution. -/
def rgswZeroGame
    {R Secret : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : RGSWDistinguisher R levels) :
    ProbComp Bool := do
  let secret ← secretSampler
  let ciphertext ← TGSW.encryptZero 1 levels errorSampler (embed secret) gadget
  distinguisher ciphertext

/-- Matched uniform game.  Sampling and discarding a secret makes it definitionally align with
the generic leaked game without changing anything visible to the distinguisher. -/
def rgswUniformGame
    {R Secret : Type} [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (distinguisher : RGSWDistinguisher R levels) : ProbComp Bool := do
  let _secret ← secretSampler
  let ciphertext ← $ᵗ (RGSWChallenge R levels)
  distinguisher ciphertext

/-- Real-versus-zero coefficient-dependent RGSW advantage. -/
def rgswKDMAdvantage
    {R Secret Leakage : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (leakage : Secret → Leakage)
    (encode : Leakage → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : RGSWDistinguisher R levels) : ℝ :=
  (rgswRealGame levels secretSampler embed leakage encode errorSampler gadget
    distinguisher).boolDistAdvantage
  (rgswZeroGame levels secretSampler embed errorSampler gadget distinguisher)

/-- Real-versus-uniform coefficient-circular advantage. -/
def rgswCircularAdvantage
    {R Secret Leakage : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (leakage : Secret → Leakage)
    (encode : Leakage → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : RGSWDistinguisher R levels) : ℝ :=
  (rgswRealGame levels secretSampler embed leakage encode errorSampler gadget
    distinguisher).boolDistAdvantage
  (rgswUniformGame levels secretSampler distinguisher)

/-- Ordinary zero-message RGSW/RLWE advantage. -/
def rgswZeroAdvantage
    {R Secret : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : RGSWDistinguisher R levels) : ℝ :=
  (rgswZeroGame levels secretSampler embed errorSampler gadget
    distinguisher).boolDistAdvantage
  (rgswUniformGame levels secretSampler distinguisher)

/-- The native circular game is exactly the generic genuinely leaked game. -/
theorem rgswCircularAdvantage_eq_leakedAdvantage
    {R Secret Leakage : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (leakage : Secret → Leakage)
    (encode : Leakage → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : RGSWDistinguisher R levels) :
    rgswCircularAdvantage levels secretSampler embed leakage encode errorSampler gadget
        distinguisher =
      leakedAdvantage secretSampler leakage
        (conditionalRGSWReal levels embed encode errorSampler gadget distinguisher)
        (conditionalRGSWIdeal levels embed encode gadget distinguisher) := by
  rfl

/-- Triangle hybrid: coefficient-dependent RGSW versus zero is circular-RLWE versus uniform plus
ordinary zero-message RLWE versus uniform. -/
theorem rgswKDMAdvantage_le_circular_add_zero
    {R Secret Leakage : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (leakage : Secret → Leakage)
    (encode : Leakage → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : RGSWDistinguisher R levels) :
    rgswKDMAdvantage levels secretSampler embed leakage encode errorSampler gadget
        distinguisher ≤
      rgswCircularAdvantage levels secretSampler embed leakage encode errorSampler gadget
          distinguisher +
        rgswZeroAdvantage levels secretSampler embed errorSampler gadget distinguisher := by
  have h := ProbComp.boolDistAdvantage_triangle
    (rgswRealGame levels secretSampler embed leakage encode errorSampler gadget distinguisher)
    (rgswUniformGame levels secretSampler distinguisher)
    (rgswZeroGame levels secretSampler embed errorSampler gadget distinguisher)
  unfold rgswKDMAdvantage rgswCircularAdvantage rgswZeroAdvantage
  rw [show
      (rgswUniformGame levels secretSampler distinguisher).boolDistAdvantage
          (rgswZeroGame levels secretSampler embed errorSampler gadget distinguisher) =
        (rgswZeroGame levels secretSampler embed errorSampler gadget
          distinguisher).boolDistAdvantage
          (rgswUniformGame levels secretSampler distinguisher) by
      unfold ProbComp.boolDistAdvantage
      rw [abs_sub_comm]] at h
  exact h

/-- Source reduction advantage for native coefficient-dependent RGSW.  Each real conditional call
contains `2 * levels` same-secret RLWE rows; squaring uses two such calls. -/
def rgswLeakageRemovalAdvantage
    {R Secret Leakage : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (auxiliarySampler : ProbComp Leakage)
    (embed : Secret → Fin 1 → R) (encode : Leakage → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (distinguisher : RGSWDistinguisher R levels) : ℝ :=
  leakageRemovalAdvantage secretSampler auxiliarySampler
    (conditionalRGSWReal levels embed encode errorSampler gadget distinguisher)
    (conditionalRGSWIdeal levels embed encode gadget distinguisher)

/-- **One-coordinate RGSW circular-security theorem with arbitrary auxiliary law.** -/
theorem rgswKDMAdvantage_le_sqrt_gamma_add_zero
    {R Secret Leakage : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [Fintype Leakage]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (auxiliarySampler : ProbComp Leakage)
    (embed : Secret → Fin 1 → R) (leakage : Secret → Leakage)
    (encode : Leakage → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : RGSWDistinguisher R levels)
    (hcover : ∀ secret, probabilityMass secretSampler secret ≠ 0 →
      probabilityMass auxiliarySampler (leakage secret) ≠ 0) :
    rgswKDMAdvantage levels secretSampler embed leakage encode errorSampler gadget
        distinguisher ≤
      Real.sqrt (2 * leakageGamma secretSampler auxiliarySampler leakage *
        rgswLeakageRemovalAdvantage levels secretSampler auxiliarySampler embed encode
          errorSampler gadget distinguisher) +
      rgswZeroAdvantage levels secretSampler embed errorSampler gadget distinguisher := by
  apply (rgswKDMAdvantage_le_circular_add_zero levels secretSampler embed leakage encode
    errorSampler gadget distinguisher).trans
  gcongr
  rw [rgswCircularAdvantage_eq_leakedAdvantage]
  exact leakedAdvantage_le_sqrt_two_mul_gamma_mul_removal
    secretSampler auxiliarySampler leakage
      (conditionalRGSWReal levels embed encode errorSampler gadget distinguisher)
      (conditionalRGSWIdeal levels embed encode gadget distinguisher) hcover

/-- Optimized Renyi-half form of one-coordinate RGSW security. -/
theorem rgswKDMAdvantage_le_sqrt_concentration_add_zero
    {R Secret Leakage : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [Fintype Leakage]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (auxiliarySampler : ProbComp Leakage)
    (embed : Secret → Fin 1 → R) (leakage : Secret → Leakage)
    (encode : Leakage → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : RGSWDistinguisher R levels)
    (hcover : ∀ secret, probabilityMass secretSampler secret ≠ 0 →
      probabilityMass auxiliarySampler (leakage secret) ≠ 0)
    (hoptimized : ∀ value,
      probabilityMass auxiliarySampler value =
        Real.sqrt (probabilityMass (leakageLaw secretSampler leakage) value) /
          halfRenyiNormalizer secretSampler leakage) :
    rgswKDMAdvantage levels secretSampler embed leakage encode errorSampler gadget
        distinguisher ≤
      Real.sqrt (2 * halfRenyiConcentration (leakageLaw secretSampler leakage) *
        rgswLeakageRemovalAdvantage levels secretSampler auxiliarySampler embed encode
          errorSampler gadget distinguisher) +
      rgswZeroAdvantage levels secretSampler embed errorSampler gadget distinguisher := by
  rw [← leakageGamma_eq_halfRenyiConcentration_of_optimizedLaw
    secretSampler auxiliarySampler leakage hoptimized]
  exact rgswKDMAdvantage_le_sqrt_gamma_add_zero levels secretSampler auxiliarySampler
    embed leakage encode errorSampler gadget distinguisher hcover

/-- Unconditional finite-range form.  For binary and ternary coefficient carriers, the loss is
respectively two and three. -/
theorem rgswKDMAdvantage_le_sqrt_card_add_zero
    {R Secret Leakage : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [Fintype Leakage] [Nonempty Leakage] [SampleableType Leakage]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (leakage : Secret → Leakage)
    (encode : Leakage → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : RGSWDistinguisher R levels) :
    rgswKDMAdvantage levels secretSampler embed leakage encode errorSampler gadget
        distinguisher ≤
      Real.sqrt (2 * Fintype.card Leakage *
        rgswLeakageRemovalAdvantage levels secretSampler ($ᵗ Leakage) embed encode
          errorSampler gadget distinguisher) +
      rgswZeroAdvantage levels secretSampler embed errorSampler gadget distinguisher := by
  simpa [leakageGamma_uniform secretSampler leakage] using
    (rgswKDMAdvantage_le_sqrt_gamma_add_zero levels secretSampler ($ᵗ Leakage)
      embed leakage encode errorSampler gadget distinguisher
        (uniformAuxiliary_covers secretSampler leakage))

/-- The doubled source contains exactly `4 * levels` ordinary RLWE rows. -/
theorem oneCoordinate_sourceRowCount (levels : ℕ) :
    2 * TGSW.rowCount 1 levels = 4 * levels := by
  change 2 * ((1 + 1) * levels) = 4 * levels
  omega

/-! ## Joint security for a bounded coefficient set -/

/-- A family of `count` rank-one RGSW ciphertexts. -/
abbrev RGSWFamily (R : Type) (count levels : ℕ) :=
  Fin count → RGSWChallenge R levels

/-- Distinguisher for a joint family of RGSW ciphertexts. -/
abbrev RGSWFamilyDistinguisher (R : Type) (count levels : ℕ) :=
  RGSWFamily R count levels → ProbComp Bool

/-- Conditional real family for a guessed tuple and a fixed common secret. -/
def conditionalRGSWFamilyReal
    {R Secret Value : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (count levels : ℕ) (embed : Secret → Fin 1 → R)
    (encode : Value → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R)
    (distinguisher : RGSWFamilyDistinguisher R count levels)
    (guessed : Fin count → Value) (secret : Secret) : ProbComp Bool := do
  let family ← Fin.mOfFn count fun coordinate ↦
    TGSW.encrypt 1 levels errorSampler (embed secret) gadget (encode (guessed coordinate))
  distinguisher family

/-- Conditional ideal family of independent uniform ciphertexts. -/
def conditionalRGSWFamilyIdeal
    {R Secret Value : Type} [SampleableType R]
    (count levels : ℕ) (_embed : Secret → Fin 1 → R)
    (_encode : Value → R) (_gadget : Fin levels → R)
    (distinguisher : RGSWFamilyDistinguisher R count levels)
    (_guessed : Fin count → Value) (_secret : Secret) : ProbComp Bool := do
  let family ← Fin.mOfFn count fun _ ↦ $ᵗ (RGSWChallenge R levels)
  distinguisher family

/-- Honest family encrypting every component of the joint leakage tuple. -/
def rgswFamilyRealGame
    {R Secret Value : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (count levels : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R)
    (leakage : Secret → Fin count → Value) (encode : Value → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (distinguisher : RGSWFamilyDistinguisher R count levels) : ProbComp Bool := do
  let secret ← secretSampler
  let family ← Fin.mOfFn count fun coordinate ↦
    TGSW.encrypt 1 levels errorSampler (embed secret) gadget
      (encode (leakage secret coordinate))
  distinguisher family

/-- Joint zero-message family under the same common secret. -/
def rgswFamilyZeroGame
    {R Secret : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (count levels : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R)
    (distinguisher : RGSWFamilyDistinguisher R count levels) : ProbComp Bool := do
  let secret ← secretSampler
  let family ← Fin.mOfFn count fun _ ↦
    TGSW.encryptZero 1 levels errorSampler (embed secret) gadget
  distinguisher family

/-- Matched joint uniform family. -/
def rgswFamilyUniformGame
    {R Secret : Type} [SampleableType R]
    (count levels : ℕ) (secretSampler : ProbComp Secret)
    (distinguisher : RGSWFamilyDistinguisher R count levels) : ProbComp Bool := do
  let _secret ← secretSampler
  let family ← Fin.mOfFn count fun _ ↦ $ᵗ (RGSWChallenge R levels)
  distinguisher family

/-- Joint real-versus-zero RGSW advantage. -/
def rgswFamilyKDMAdvantage
    {R Secret Value : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (count levels : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R)
    (leakage : Secret → Fin count → Value) (encode : Value → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (distinguisher : RGSWFamilyDistinguisher R count levels) : ℝ :=
  (rgswFamilyRealGame count levels secretSampler embed leakage encode errorSampler gadget
    distinguisher).boolDistAdvantage
  (rgswFamilyZeroGame count levels secretSampler embed errorSampler gadget distinguisher)

/-- Joint real-versus-uniform coefficient-circular advantage. -/
def rgswFamilyCircularAdvantage
    {R Secret Value : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (count levels : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R)
    (leakage : Secret → Fin count → Value) (encode : Value → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (distinguisher : RGSWFamilyDistinguisher R count levels) : ℝ :=
  (rgswFamilyRealGame count levels secretSampler embed leakage encode errorSampler gadget
    distinguisher).boolDistAdvantage
  (rgswFamilyUniformGame count levels secretSampler distinguisher)

/-- Joint zero-message-versus-uniform RLWE advantage. -/
def rgswFamilyZeroAdvantage
    {R Secret : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (count levels : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R)
    (distinguisher : RGSWFamilyDistinguisher R count levels) : ℝ :=
  (rgswFamilyZeroGame count levels secretSampler embed errorSampler gadget
    distinguisher).boolDistAdvantage
  (rgswFamilyUniformGame count levels secretSampler distinguisher)

theorem rgswFamilyCircularAdvantage_eq_leakedAdvantage
    {R Secret Value : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (count levels : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R)
    (leakage : Secret → Fin count → Value) (encode : Value → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (distinguisher : RGSWFamilyDistinguisher R count levels) :
    rgswFamilyCircularAdvantage count levels secretSampler embed leakage encode errorSampler
        gadget distinguisher =
      leakedAdvantage secretSampler leakage
        (conditionalRGSWFamilyReal count levels embed encode errorSampler gadget distinguisher)
        (conditionalRGSWFamilyIdeal count levels embed encode gadget distinguisher) := by
  rfl

theorem rgswFamilyKDMAdvantage_le_circular_add_zero
    {R Secret Value : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (count levels : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R)
    (leakage : Secret → Fin count → Value) (encode : Value → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (distinguisher : RGSWFamilyDistinguisher R count levels) :
    rgswFamilyKDMAdvantage count levels secretSampler embed leakage encode errorSampler gadget
        distinguisher ≤
      rgswFamilyCircularAdvantage count levels secretSampler embed leakage encode errorSampler
          gadget distinguisher +
        rgswFamilyZeroAdvantage count levels secretSampler embed errorSampler gadget
          distinguisher := by
  have h := ProbComp.boolDistAdvantage_triangle
    (rgswFamilyRealGame count levels secretSampler embed leakage encode errorSampler gadget
      distinguisher)
    (rgswFamilyUniformGame count levels secretSampler distinguisher)
    (rgswFamilyZeroGame count levels secretSampler embed errorSampler gadget distinguisher)
  unfold rgswFamilyKDMAdvantage rgswFamilyCircularAdvantage rgswFamilyZeroAdvantage
  rw [show
      (rgswFamilyUniformGame count levels secretSampler distinguisher).boolDistAdvantage
          (rgswFamilyZeroGame count levels secretSampler embed errorSampler gadget
            distinguisher) =
        (rgswFamilyZeroGame count levels secretSampler embed errorSampler gadget
          distinguisher).boolDistAdvantage
          (rgswFamilyUniformGame count levels secretSampler distinguisher) by
      unfold ProbComp.boolDistAdvantage
      rw [abs_sub_comm]] at h
  exact h

/-- Doubled-source advantage for the joint family. -/
def rgswFamilyLeakageRemovalAdvantage
    {R Secret Value : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (count levels : ℕ) (secretSampler : ProbComp Secret)
    (auxiliarySampler : ProbComp (Fin count → Value))
    (embed : Secret → Fin 1 → R) (encode : Value → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (distinguisher : RGSWFamilyDistinguisher R count levels) : ℝ :=
  leakageRemovalAdvantage secretSampler auxiliarySampler
    (conditionalRGSWFamilyReal count levels embed encode errorSampler gadget distinguisher)
    (conditionalRGSWFamilyIdeal count levels embed encode gadget distinguisher)

/-- **Composable bounded-joint-leakage RGSW security.** -/
theorem rgswFamilyKDMAdvantage_le_sqrt_gamma_add_zero
    {R Secret Value : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [Fintype Value]
    (count levels : ℕ) (secretSampler : ProbComp Secret)
    (auxiliarySampler : ProbComp (Fin count → Value))
    (embed : Secret → Fin 1 → R)
    (leakage : Secret → Fin count → Value) (encode : Value → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (distinguisher : RGSWFamilyDistinguisher R count levels)
    (hcover : ∀ secret, probabilityMass secretSampler secret ≠ 0 →
      probabilityMass auxiliarySampler (leakage secret) ≠ 0) :
    rgswFamilyKDMAdvantage count levels secretSampler embed leakage encode errorSampler gadget
        distinguisher ≤
      Real.sqrt (2 * leakageGamma secretSampler auxiliarySampler leakage *
        rgswFamilyLeakageRemovalAdvantage count levels secretSampler auxiliarySampler embed
          encode errorSampler gadget distinguisher) +
      rgswFamilyZeroAdvantage count levels secretSampler embed errorSampler gadget
        distinguisher := by
  apply (rgswFamilyKDMAdvantage_le_circular_add_zero count levels secretSampler embed leakage
    encode errorSampler gadget distinguisher).trans
  gcongr
  rw [rgswFamilyCircularAdvantage_eq_leakedAdvantage]
  exact leakedAdvantage_le_sqrt_two_mul_gamma_mul_removal
    secretSampler auxiliarySampler leakage
      (conditionalRGSWFamilyReal count levels embed encode errorSampler gadget distinguisher)
      (conditionalRGSWFamilyIdeal count levels embed encode gadget distinguisher) hcover

/-- Optimized order-`1/2` concentration form of joint security. -/
theorem rgswFamilyKDMAdvantage_le_sqrt_concentration_add_zero
    {R Secret Value : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [Fintype Value]
    (count levels : ℕ) (secretSampler : ProbComp Secret)
    (auxiliarySampler : ProbComp (Fin count → Value))
    (embed : Secret → Fin 1 → R)
    (leakage : Secret → Fin count → Value) (encode : Value → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (distinguisher : RGSWFamilyDistinguisher R count levels)
    (hcover : ∀ secret, probabilityMass secretSampler secret ≠ 0 →
      probabilityMass auxiliarySampler (leakage secret) ≠ 0)
    (hoptimized : ∀ value,
      probabilityMass auxiliarySampler value =
        Real.sqrt (probabilityMass (leakageLaw secretSampler leakage) value) /
          halfRenyiNormalizer secretSampler leakage) :
    rgswFamilyKDMAdvantage count levels secretSampler embed leakage encode errorSampler gadget
        distinguisher ≤
      Real.sqrt (2 * halfRenyiConcentration (leakageLaw secretSampler leakage) *
        rgswFamilyLeakageRemovalAdvantage count levels secretSampler auxiliarySampler embed
          encode errorSampler gadget distinguisher) +
      rgswFamilyZeroAdvantage count levels secretSampler embed errorSampler gadget
        distinguisher := by
  rw [← leakageGamma_eq_halfRenyiConcentration_of_optimizedLaw
    secretSampler auxiliarySampler leakage hoptimized]
  exact rgswFamilyKDMAdvantage_le_sqrt_gamma_add_zero count levels secretSampler
    auxiliarySampler embed leakage encode errorSampler gadget distinguisher hcover

/-- Unconditional finite-alphabet joint theorem. -/
theorem rgswFamilyKDMAdvantage_le_sqrt_card_add_zero
    {R Secret Value : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [Fintype Value] [Nonempty Value] [SampleableType Value]
    (count levels : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R)
    (leakage : Secret → Fin count → Value) (encode : Value → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (distinguisher : RGSWFamilyDistinguisher R count levels) :
    rgswFamilyKDMAdvantage count levels secretSampler embed leakage encode errorSampler gadget
        distinguisher ≤
      Real.sqrt (2 * (Fintype.card Value : ℝ) ^ count *
        rgswFamilyLeakageRemovalAdvantage count levels secretSampler
          ($ᵗ (Fin count → Value)) embed encode errorSampler gadget distinguisher) +
      rgswFamilyZeroAdvantage count levels secretSampler embed errorSampler gadget
        distinguisher := by
  have h := rgswFamilyKDMAdvantage_le_sqrt_gamma_add_zero count levels secretSampler
    ($ᵗ (Fin count → Value)) embed leakage encode errorSampler gadget distinguisher
      (uniformAuxiliary_covers secretSampler leakage)
  rw [leakageGamma_uniform secretSampler leakage] at h
  simpa [Fintype.card_fun, Nat.cast_pow] using h

/-- The joint source contains exactly `4 * levels * count` ordinary RLWE rows. -/
theorem joint_sourceRowCount (count levels : ℕ) :
    2 * (count * TGSW.rowCount 1 levels) = 4 * levels * count := by
  change 2 * (count * ((1 + 1) * levels)) = 4 * levels * count
  ring

/-! ## Further concrete concentration factors -/

/-- A uniformly sampled exact-weight signed ternary secret has concentration equal to its exact
support cardinality `2^weight * choose dimension weight`. -/
theorem halfRenyiConcentration_uniform_fixedWeightTernary
    (dimension weight : ℕ)
    [Nonempty
      (RLWE.RankOneHNFLossinessSupportAware.FixedWeightTernarySecret dimension weight)] :
    halfRenyiConcentration
        ($ᵗ (RLWE.RankOneHNFLossinessSupportAware.FixedWeightTernarySecret
          dimension weight)) =
      (2 ^ weight * dimension.choose weight : ℕ) := by
  rw [halfRenyiConcentration_uniform]
  exact_mod_cast
    RLWE.RankOneHNFLossinessSupportAware.card_fixedWeightTernarySecret dimension weight

/-- Any one-coordinate signed ternary law, including the marginal of an exact-weight secret, has
concentration at most three. -/
theorem halfRenyiConcentration_signedTernary_le
    (sampler : ProbComp (Fin 3)) :
    halfRenyiConcentration sampler ≤ 3 := by
  simpa using halfRenyiConcentration_le_card sampler

/-! ## The complete-family quadratic aggregation barrier -/

/-- A two-component ring row `(A,B)`. -/
abbrev RingRow (R : Type) := R × R

/-- Public coefficient-basis aggregation of a family of two-component rows. -/
def aggregateRows {R : Type} [AddCommMonoid R] [Mul R] {count : ℕ}
    (basis : Fin count → R) (rows : Fin count → RingRow R) : RingRow R :=
  (∑ coordinate, basis coordinate * (rows coordinate).1,
    ∑ coordinate, basis coordinate * (rows coordinate).2)

/-- Aggregate error corresponding to `aggregateRows`. -/
def aggregateErrors {R : Type} [AddCommMonoid R] [Mul R] {count : ℕ}
    (basis : Fin count → R) (errors : Fin count → R) : R :=
  ∑ coordinate, basis coordinate * errors coordinate

/-- Deterministic top gadget-one row in sign convention `eta`: the public mask is shifted by
`eta * coefficient`, while its body remains homogeneous RLWE. -/
def signedTopRow {R : Type} [Semiring R]
    (eta coefficient secret mask error : R) : RingRow R :=
  (mask + eta * coefficient, mask * secret + error)

/-- Each selected top row is an encryption of `-eta * coefficient * secret`. -/
theorem signedTopRow_body
    {R : Type} [CommRing R]
    (eta coefficient secret mask error : R) :
    (signedTopRow eta coefficient secret mask error).2 =
      (signedTopRow eta coefficient secret mask error).1 * secret -
        eta * coefficient * secret + error := by
  simp [signedTopRow]
  ring

/-- Algebraic form of a family of top rows, abstracting only the row equation needed below. -/
def HasSignedTopRowForm
    {R : Type} [Ring R] {count : ℕ}
    (eta secret : R) (coefficients masks errors : Fin count → R)
    (rows : Fin count → RingRow R) : Prop :=
  ∀ coordinate,
    rows coordinate =
      signedTopRow eta (coefficients coordinate) secret
        (masks coordinate) (errors coordinate)

/-- **Exact quadratic aggregation identity.**  If
`secret = sum_i basis_i * coefficient_i`, aggregating all signed top rows produces
`Bbar = Abar * secret - eta * secret^2 + Ebar`. -/
theorem aggregateRows_body_eq_quadratic
    {R : Type} [CommRing R] {count : ℕ}
    (eta secret : R) (basis coefficients masks errors : Fin count → R)
    (rows : Fin count → RingRow R)
    (hsecret : ∑ coordinate, basis coordinate * coefficients coordinate = secret)
    (hrows : HasSignedTopRowForm eta secret coefficients masks errors rows) :
    (aggregateRows basis rows).2 =
      (aggregateRows basis rows).1 * secret - eta * secret ^ 2 +
        aggregateErrors basis errors := by
  have hrowBody (coordinate : Fin count) :
      (rows coordinate).2 =
        (rows coordinate).1 * secret -
          eta * coefficients coordinate * secret + errors coordinate := by
    rw [hrows coordinate]
    exact signedTopRow_body eta (coefficients coordinate) secret
      (masks coordinate) (errors coordinate)
  unfold aggregateRows aggregateErrors
  simp_rw [hrowBody, mul_add, mul_sub]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [show ∀ coordinate : Fin count,
      basis coordinate * ((rows coordinate).1 * secret) =
        (basis coordinate * (rows coordinate).1) * secret by
      intro coordinate
      ring]
  rw [← Finset.sum_mul]
  simp_rw [show ∀ coordinate : Fin count,
      basis coordinate * (eta * coefficients coordinate * secret) =
        eta * (basis coordinate * coefficients coordinate) * secret by
      intro coordinate
      ring]
  have hmiddle :
      (∑ coordinate : Fin count,
        eta * (basis coordinate * coefficients coordinate) * secret) =
        eta * secret ^ 2 := by
    calc
      _ = (∑ coordinate : Fin count,
          eta * (basis coordinate * coefficients coordinate)) * secret := by
        rw [Finset.sum_mul]
      _ = (eta * (∑ coordinate : Fin count,
          basis coordinate * coefficients coordinate)) * secret := by
        rw [Finset.mul_sum]
      _ = eta * secret ^ 2 := by rw [hsecret]; ring
  rw [hmiddle]

/-- The zero-message counterpart of the aggregation identity. -/
theorem aggregateRows_body_eq_zero
    {R : Type} [CommRing R] {count : ℕ}
    (secret : R) (basis masks errors : Fin count → R)
    (rows : Fin count → RingRow R)
    (hrows : ∀ coordinate,
      rows coordinate = (masks coordinate, masks coordinate * secret + errors coordinate)) :
    (aggregateRows basis rows).2 =
      (aggregateRows basis rows).1 * secret + aggregateErrors basis errors := by
  unfold aggregateRows aggregateErrors
  simp_rw [hrows, mul_add]
  rw [Finset.sum_add_distrib]
  simp_rw [show ∀ coordinate : Fin count,
      basis coordinate * (masks coordinate * secret) =
        (basis coordinate * masks coordinate) * secret by
      intro coordinate
      ring]
  rw [← Finset.sum_mul]

/-- Select one upper gadget row from each native rank-one RGSW ciphertext and aggregate it in the
public coefficient basis. -/
def aggregateUpperRows
    {R : Type} [AddCommMonoid R] [Mul R] {count levels : ℕ}
    (basis : Fin count → R) (level : Fin levels)
    (family : RGSWFamily R count levels) : RingRow R :=
  aggregateRows basis fun coordinate ↦
    let row := TLWE.entry (family coordinate)
      (finProdFinEquiv (Fin.castSucc (0 : Fin 1), level))
    (row.mask 0, row.body)

/-- Public post-processing of a finite sampler. -/
def postprocessGame
    {Input Output : Type}
    (sampler : ProbComp Input) (process : Input → Output)
    (distinguisher : Output → ProbComp Bool) : ProbComp Bool := do
  let input ← sampler
  distinguisher (process input)

/-- A distinguisher after public post-processing is exactly the lifted source distinguisher. -/
theorem postprocessGame_eq_lifted
    {Input Output : Type}
    (sampler : ProbComp Input) (process : Input → Output)
    (distinguisher : Output → ProbComp Bool) :
    postprocessGame sampler process distinguisher =
      (sampler >>= fun input ↦ (fun value ↦ distinguisher (process value)) input) := by
  rfl

/-- Computational indistinguishability is closed under deterministic public post-processing. -/
theorem postprocessAdvantage_le_of_sourceHardness
    {Input Output : Type}
    (real ideal : ProbComp Input) (process : Input → Output)
    (allowed : (Input → ProbComp Bool) → Prop) (bound : ℝ)
    (hHard : ∀ distinguisher, allowed distinguisher →
      (real >>= distinguisher).boolDistAdvantage (ideal >>= distinguisher) ≤ bound)
    (distinguisher : Output → ProbComp Bool)
    (hAllowed : allowed (fun input ↦ distinguisher (process input))) :
    (postprocessGame real process distinguisher).boolDistAdvantage
        (postprocessGame ideal process distinguisher) ≤ bound := by
  exact hHard (fun input ↦ distinguisher (process input)) hAllowed

/-- **Quadratic aggregation barrier.**  Security of a complete RGSW coefficient family implies
security of the publicly aggregated two-component row.  Combined with
`aggregateRows_body_eq_quadratic`, the real aggregate encrypts `-eta * secret^2`, while the zero
aggregate encrypts zero under the same key and aggregate error law. -/
theorem quadraticAggregationBarrier
    {R : Type} [AddCommMonoid R] [Mul R] {count levels : ℕ}
    (real zero : ProbComp (RGSWFamily R count levels))
    (basis : Fin count → R) (level : Fin levels)
    (allowed : (RGSWFamily R count levels → ProbComp Bool) → Prop)
    (bound : ℝ)
    (hFamily : ∀ distinguisher, allowed distinguisher →
      (real >>= distinguisher).boolDistAdvantage
        (zero >>= distinguisher) ≤ bound)
    (distinguisher : RingRow R → ProbComp Bool)
    (hAllowed : allowed
      (fun family ↦ distinguisher (aggregateUpperRows basis level family))) :
    (postprocessGame real (aggregateUpperRows basis level) distinguisher).boolDistAdvantage
        (postprocessGame zero (aggregateUpperRows basis level) distinguisher) ≤ bound := by
  exact postprocessAdvantage_le_of_sourceHardness real zero
    (aggregateUpperRows basis level) allowed bound hFamily distinguisher hAllowed

/-- Translation of a uniform anchor by any fixed aggregate of the remaining masks stays uniform.
This is the finite-ring form of the paper's observation that `Abar` is uniform because it contains
the independent `A_0` summand with coefficient one. -/
theorem uniformAnchor_add_offset_evalDist
    {R : Type} [AddCommGroup R] [Fintype R] [SampleableType R]
    (offset : R) :
    evalDist (($ᵗ R) >>= fun anchor ↦ pure (anchor + offset)) =
      evalDist ($ᵗ R) := by
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using
    (evalDist_map_bijective_uniform_cross
      (α := R) (β := R) (fun anchor ↦ anchor + offset)
      (Function.bijective_iff_has_inverse.mpr
        ⟨fun value ↦ value - offset,
          fun value ↦ by simp,
          fun value ↦ by simp⟩))

/-! ## Native binary coefficient expansion for the barrier -/

/-- The executable negacyclic binary polynomial is exactly the sum of its monomial basis values
times its scalar Boolean coefficients. -/
theorem embedBinaryPolynomial_eq_sum_binaryBasis_mul_coefficient
    (q degree : ℕ) [NeZero q]
    (secret : Fin (degree + 1) → Bool) :
    embedBinaryPolynomial q (degree + 1) secret =
      ∑ coordinate,
        TGSW.RingSquare.TopWeightCoefficientAffine.binaryBasis
            q (degree + 1) coordinate *
          (embedBit (secret coordinate) : RLWE.Rq q (degree + 1)) := by
  rw [TGSW.RingSquare.TopWeightCoefficientAffine.embedBinaryPolynomial_eq_sum_basis]
  apply Finset.sum_congr rfl
  intro coordinate _
  cases secret coordinate <;> simp [embedBit]

/-- Fully instantiated binary-ring aggregation identity.  No coefficient-expansion premise
remains: it is discharged by the executable negacyclic basis theorem above. -/
theorem aggregateBinaryTopRows_body_eq_quadratic
    (q degree : ℕ) [NeZero q]
    (eta : RLWE.Rq q (degree + 1))
    (binarySecret : Fin (degree + 1) → Bool)
    (masks errors : Fin (degree + 1) → RLWE.Rq q (degree + 1))
    (rows : Fin (degree + 1) → RingRow (RLWE.Rq q (degree + 1)))
    (hrows : HasSignedTopRowForm eta
      (embedBinaryPolynomial q (degree + 1) binarySecret)
      (fun coordinate ↦ (embedBit (binarySecret coordinate) : RLWE.Rq q (degree + 1)))
      masks errors rows) :
    let basis := fun coordinate ↦
      TGSW.RingSquare.TopWeightCoefficientAffine.binaryBasis
        q (degree + 1) coordinate
    let secret := embedBinaryPolynomial q (degree + 1) binarySecret
    (aggregateRows basis rows).2 =
      (aggregateRows basis rows).1 * secret - eta * secret ^ 2 +
        aggregateErrors basis errors := by
  dsimp only
  apply aggregateRows_body_eq_quadratic eta
    (embedBinaryPolynomial q (degree + 1) binarySecret)
    (fun coordinate ↦ TGSW.RingSquare.TopWeightCoefficientAffine.binaryBasis
      q (degree + 1) coordinate)
    (fun coordinate ↦ (embedBit (binarySecret coordinate) : RLWE.Rq q (degree + 1)))
    masks errors rows
  · exact embedBinaryPolynomial_eq_sum_binaryBasis_mul_coefficient q degree binarySecret |>.symm
  · exact hrows

/-- Under the usual matrix-plus-gadget sign `eta = +1`, the aggregate message is `-S^2`. -/
theorem aggregateBinaryTopRows_positiveSign
    (q degree : ℕ) [NeZero q]
    (binarySecret : Fin (degree + 1) → Bool)
    (masks errors : Fin (degree + 1) → RLWE.Rq q (degree + 1))
    (rows : Fin (degree + 1) → RingRow (RLWE.Rq q (degree + 1)))
    (hrows : HasSignedTopRowForm (1 : RLWE.Rq q (degree + 1))
      (embedBinaryPolynomial q (degree + 1) binarySecret)
      (fun coordinate ↦ (embedBit (binarySecret coordinate) : RLWE.Rq q (degree + 1)))
      masks errors rows) :
    let basis := fun coordinate ↦
      TGSW.RingSquare.TopWeightCoefficientAffine.binaryBasis
        q (degree + 1) coordinate
    let secret := embedBinaryPolynomial q (degree + 1) binarySecret
    (aggregateRows basis rows).2 =
      (aggregateRows basis rows).1 * secret - secret ^ 2 +
        aggregateErrors basis errors := by
  simpa using aggregateBinaryTopRows_body_eq_quadratic q degree
    (1 : RLWE.Rq q (degree + 1)) binarySecret masks errors rows hrows

/-- Under the opposite sign `eta = -1`, the aggregate message is `+S^2`. -/
theorem aggregateBinaryTopRows_negativeSign
    (q degree : ℕ) [NeZero q]
    (binarySecret : Fin (degree + 1) → Bool)
    (masks errors : Fin (degree + 1) → RLWE.Rq q (degree + 1))
    (rows : Fin (degree + 1) → RingRow (RLWE.Rq q (degree + 1)))
    (hrows : HasSignedTopRowForm (-1 : RLWE.Rq q (degree + 1))
      (embedBinaryPolynomial q (degree + 1) binarySecret)
      (fun coordinate ↦ (embedBit (binarySecret coordinate) : RLWE.Rq q (degree + 1)))
      masks errors rows) :
    let basis := fun coordinate ↦
      TGSW.RingSquare.TopWeightCoefficientAffine.binaryBasis
        q (degree + 1) coordinate
    let secret := embedBinaryPolynomial q (degree + 1) binarySecret
    (aggregateRows basis rows).2 =
      (aggregateRows basis rows).1 * secret + secret ^ 2 +
        aggregateErrors basis errors := by
  have h := aggregateBinaryTopRows_body_eq_quadratic q degree
    (-1 : RLWE.Rq q (degree + 1)) binarySecret masks errors rows hrows
  dsimp only at h ⊢
  convert h using 1
  all_goals ring

/-! ## Concrete binary and ternary coefficient instances -/

/-- Selected coefficient of a native rank-one binary ring secret. -/
def selectedBinaryCoefficient
    {degree : ℕ} (coordinate : Fin degree)
    (secret : RingBinarySecret 1 degree) : Bool :=
  secret 0 coordinate

/-- The selected binary coefficient embedded as a constant ring polynomial. -/
def encodeBinaryCoefficient (q degree : ℕ) (bit : Bool) : RLWE.Rq q degree :=
  embedConstantBit q degree bit

/-- **Concrete one-coordinate binary RGSW theorem.**  One native RGSW encryption of a selected
binary coefficient is bounded by a `4 * levels`-row ordinary same-secret RLWE squared-bias
reduction and a `2 * levels`-row zero-message RLWE hybrid. -/
theorem nativeBinaryCoefficient_rgswKDMAdvantage_le
    (q degree levels : ℕ) [NeZero q]
    (coordinate : Fin degree)
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree)
    (distinguisher : RGSWDistinguisher (RLWE.Rq q degree) levels) :
    rgswKDMAdvantage levels (Native.sampleRingSecret 1 degree)
        (embedRingSecret q) (selectedBinaryCoefficient coordinate)
        (encodeBinaryCoefficient q degree) errorSampler gadget distinguisher ≤
      Real.sqrt (4 *
        rgswLeakageRemovalAdvantage levels (Native.sampleRingSecret 1 degree) ($ᵗ Bool)
          (embedRingSecret q) (encodeBinaryCoefficient q degree)
          errorSampler gadget distinguisher) +
      rgswZeroAdvantage levels (Native.sampleRingSecret 1 degree)
        (embedRingSecret q) errorSampler gadget distinguisher := by
  have h :=
    rgswKDMAdvantage_le_sqrt_card_add_zero
      (R := RLWE.Rq q degree) (Secret := RingBinarySecret 1 degree) (Leakage := Bool)
      levels (Native.sampleRingSecret 1 degree) (embedRingSecret q)
      (selectedBinaryCoefficient coordinate) (encodeBinaryCoefficient q degree)
      errorSampler gadget distinguisher
  convert h using 1
  all_goals norm_num

/-- Centered ternary digit embedding `0, +1, -1`. -/
def embedTernaryDigit {R : Type} [Ring R] (digit : Fin 3) : R :=
  match digit with
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => -1

@[simp] theorem embedTernaryDigit_zero {R : Type} [Ring R] :
    embedTernaryDigit (R := R) (0 : Fin 3) = 0 := rfl

@[simp] theorem embedTernaryDigit_one {R : Type} [Ring R] :
    embedTernaryDigit (R := R) (1 : Fin 3) = 1 := rfl

@[simp] theorem embedTernaryDigit_two {R : Type} [Ring R] :
    embedTernaryDigit (R := R) (2 : Fin 3) = -1 := rfl

/-- Coefficientwise centered-ternary negacyclic polynomial. -/
def embedTernaryPolynomial (q degree : ℕ)
    (secret : Fin degree → Fin 3) : RLWE.Rq q degree :=
  LatticeCrypto.Poly.ofPi fun coordinate ↦
    embedTernaryDigit (R := ZMod q) (secret coordinate)

/-- Rank-one ring embedding of a centered-ternary polynomial secret. -/
def embedTernaryRingSecret (q degree : ℕ)
    (secret : Fin degree → Fin 3) : Fin 1 → RLWE.Rq q degree :=
  fun _ ↦ embedTernaryPolynomial q degree secret

/-- Embed one centered-ternary coefficient as a constant ring polynomial. -/
def encodeTernaryCoefficient (q degree : ℕ) (digit : Fin 3) : RLWE.Rq q degree :=
  LatticeCrypto.Poly.ofPi fun coordinate ↦
    if coordinate.val = 0 then embedTernaryDigit (R := ZMod q) digit else 0

/-- **Concrete one-coordinate ternary RGSW theorem.** -/
theorem nativeTernaryCoefficient_rgswKDMAdvantage_le
    (q degree levels : ℕ) [NeZero q]
    (coordinate : Fin degree)
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree)
    (distinguisher : RGSWDistinguisher (RLWE.Rq q degree) levels) :
    rgswKDMAdvantage levels ($ᵗ (Fin degree → Fin 3))
        (embedTernaryRingSecret q degree) (fun secret ↦ secret coordinate)
        (encodeTernaryCoefficient q degree) errorSampler gadget distinguisher ≤
      Real.sqrt (6 *
        rgswLeakageRemovalAdvantage levels ($ᵗ (Fin degree → Fin 3)) ($ᵗ (Fin 3))
          (embedTernaryRingSecret q degree) (encodeTernaryCoefficient q degree)
          errorSampler gadget distinguisher) +
      rgswZeroAdvantage levels ($ᵗ (Fin degree → Fin 3))
        (embedTernaryRingSecret q degree) errorSampler gadget distinguisher := by
  have h :=
    rgswKDMAdvantage_le_sqrt_card_add_zero
      (R := RLWE.Rq q degree) (Secret := Fin degree → Fin 3) (Leakage := Fin 3)
      levels ($ᵗ (Fin degree → Fin 3)) (embedTernaryRingSecret q degree)
      (fun secret ↦ secret coordinate) (encodeTernaryCoefficient q degree)
      errorSampler gadget distinguisher
  convert h using 1
  all_goals norm_num

/-! ## Exact bridge to the ordinary batch-RLWE interface -/

/-- Two independently sampled homogeneous RLWE batches sharing one fixed secret. -/
def fixedSecretHomogeneousPair
    {R Secret : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (samples : ℕ) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (secret : Secret) :
    ProbComp
      (LWE.BatchTranscript R 1 samples × LWE.BatchTranscript R 1 samples) := do
  let first ← TLWE.batchEncrypt 1 samples errorSampler (embed secret) 0
  let second ← TLWE.batchEncrypt 1 samples errorSampler (embed secret) 0
  return (first, second)

/-- Splitting the real two-block LWE transcript into two public transcripts is exactly two fresh
homogeneous batches under one sampled secret. -/
theorem twoBlockReal_toTranscriptPair_evalDist
    {R Secret : Type}
    [Semiring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (samples : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R) :
    evalDist
        (LearningWithErrors.distr
            (LWE.TwoBlock.problem 1 samples samples secretSampler embed errorSampler) >>=
          fun transcript ↦ pure (LWE.TwoBlock.toTranscriptPair transcript)) =
      evalDist (secretSampler >>= fun secret ↦
        fixedSecretHomogeneousPair samples embed errorSampler secret) := by
  let Challenges : ProbComp
      (Matrix (Fin 1) (Fin samples) R × Matrix (Fin 1) (Fin samples) R) :=
    $ᵗ (Matrix (Fin 1) (Fin samples) R × Matrix (Fin 1) (Fin samples) R)
  let FirstChallenge : ProbComp (Matrix (Fin 1) (Fin samples) R) :=
    $ᵗ Matrix (Fin 1) (Fin samples) R
  let SecondChallenge : ProbComp (Matrix (Fin 1) (Fin samples) R) :=
    $ᵗ Matrix (Fin 1) (Fin samples) R
  let FirstError : ProbComp (Fin samples → R) :=
    ProbComp.sampleIID samples errorSampler
  let SecondError : ProbComp (Fin samples → R) :=
    ProbComp.sampleIID samples errorSampler
  let finish := fun
      (firstChallenge secondChallenge : Matrix (Fin 1) (Fin samples) R)
      (secret : Secret) (firstError secondError : Fin samples → R) ↦
    (pure
      ((firstChallenge, vecMul (embed secret) firstChallenge + firstError),
        (secondChallenge, vecMul (embed secret) secondChallenge + secondError)) :
      ProbComp (LWE.BatchTranscript R 1 samples × LWE.BatchTranscript R 1 samples))
  have hChallenges : evalDist Challenges =
      evalDist (FirstChallenge >>= fun first ↦
        SecondChallenge >>= fun second ↦ pure (first, second)) := by
    exact
      (FormalProof4FHE.FiniteProduct.evalDist_independent_uniform_product
        (first := Matrix (Fin 1) (Fin samples) R)
        (second := Matrix (Fin 1) (Fin samples) R)).symm
  have hActual :
      evalDist (LearningWithErrors.distr
          (LWE.TwoBlock.problem 1 samples samples secretSampler embed errorSampler) >>=
        fun transcript ↦ pure (LWE.TwoBlock.toTranscriptPair transcript)) =
      evalDist (Challenges >>= fun challenges ↦
          secretSampler >>= fun secret ↦
            FirstError >>= fun firstError ↦
              SecondError >>= fun secondError ↦
                finish challenges.1 challenges.2 secret firstError secondError) := by
    unfold LearningWithErrors.distr LWE.TwoBlock.problem
      LWE.TwoBlock.heterogeneousProblem
    simp [LWE.TwoBlock.toTranscriptPair, FirstError, SecondError, finish,
      Challenges, monad_norm]
  have hContext :
      (secretSampler >>= fun secret ↦
        fixedSecretHomogeneousPair samples embed errorSampler secret) =
      (secretSampler >>= fun secret ↦
        FirstChallenge >>= fun firstChallenge ↦
          FirstError >>= fun firstError ↦
            SecondChallenge >>= fun secondChallenge ↦
              SecondError >>= fun secondError ↦
                finish firstChallenge secondChallenge secret firstError secondError) := by
    simp [fixedSecretHomogeneousPair, TLWE.batchEncrypt, TLWE.batchAssemble,
      FirstChallenge, SecondChallenge, FirstError, SecondError, finish, monad_norm]
  rw [hActual, hContext]
  calc
    evalDist (Challenges >>= fun challenges ↦
          secretSampler >>= fun secret ↦
            FirstError >>= fun firstError ↦
              SecondError >>= fun secondError ↦
                finish challenges.1 challenges.2 secret firstError secondError) =
      evalDist (FirstChallenge >>= fun firstChallenge ↦
        SecondChallenge >>= fun secondChallenge ↦
          secretSampler >>= fun secret ↦
            FirstError >>= fun firstError ↦
              SecondError >>= fun secondError ↦
                finish firstChallenge secondChallenge secret firstError secondError) := by
      simpa [bind_assoc, monad_norm] using
        (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hChallenges
          (fun challenges ↦
            secretSampler >>= fun secret ↦
              FirstError >>= fun firstError ↦
                SecondError >>= fun secondError ↦
                  finish challenges.1 challenges.2 secret firstError secondError))
    _ =
      evalDist (FirstChallenge >>= fun firstChallenge ↦
        secretSampler >>= fun secret ↦
          SecondChallenge >>= fun secondChallenge ↦
            FirstError >>= fun firstError ↦
              SecondError >>= fun secondError ↦
                finish firstChallenge secondChallenge secret firstError secondError) := by
      apply evalDist_bind_congr' FirstChallenge
      intro firstChallenge
      exact evalDist_bind_bind_swap SecondChallenge secretSampler _
    _ = evalDist (secretSampler >>= fun secret ↦
        FirstChallenge >>= fun firstChallenge ↦
          SecondChallenge >>= fun secondChallenge ↦
            FirstError >>= fun firstError ↦
              SecondError >>= fun secondError ↦
                finish firstChallenge secondChallenge secret firstError secondError) := by
      exact evalDist_bind_bind_swap FirstChallenge secretSampler _
    _ = evalDist (secretSampler >>= fun secret ↦
        FirstChallenge >>= fun firstChallenge ↦
          FirstError >>= fun firstError ↦
            SecondChallenge >>= fun secondChallenge ↦
              SecondError >>= fun secondError ↦
                finish firstChallenge secondChallenge secret firstError secondError) := by
      apply evalDist_bind_congr' secretSampler
      intro secret
      apply evalDist_bind_congr' FirstChallenge
      intro firstChallenge
      exact evalDist_bind_bind_swap SecondChallenge FirstError _

/-- Run one real/control pair of the squared-bias test on a supplied homogeneous block. -/
def rgswPairedOutput
    {R Leakage : Type}
    [Semiring R] [SampleableType R]
    (levels : ℕ) (encode : Leakage → R) (gadget : Fin levels → R)
    (distinguisher : RGSWDistinguisher R levels)
    (guessed : Leakage) (homogeneous : RGSWChallenge R levels) :
    ProbComp (Bool × Bool) :=
  SquaredBias.paired
    (distinguisher (TGSW.addGadget gadget (encode guessed) homogeneous))
    (($ᵗ (RGSWChallenge R levels)) >>= distinguisher)

/-- The paper's doubled-block squared-bias test after the auxiliary leakage guess is fixed. -/
def rgswSquaredBiasTest
    {R Leakage : Type}
    [Semiring R] [SampleableType R]
    (levels : ℕ) (encode : Leakage → R) (gadget : Fin levels → R)
    (distinguisher : RGSWDistinguisher R levels)
    (guessed : Leakage)
    (blocks : RGSWChallenge R levels × RGSWChallenge R levels) : ProbComp Bool := do
  let first ← rgswPairedOutput levels encode gadget distinguisher guessed blocks.1
  let second ← rgswPairedOutput levels encode gadget distinguisher guessed blocks.2
  SquaredBias.combine first.1 first.2 second.1 second.2

/-- Concrete adversary for two equal RLWE blocks.  Each block has `2 * levels` rows, and the two
blocks share the challenge secret exactly as required by the squared-bias argument. -/
def rgswSquaredBiasTwoBlockAdversary
    {R Secret Leakage : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (auxiliarySampler : ProbComp Leakage) (embed : Secret → Fin 1 → R)
    (encode : Leakage → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : RGSWDistinguisher R levels) :
    LearningWithErrors.Adversary
      (LWE.TwoBlock.problem 1 (TGSW.rowCount 1 levels) (TGSW.rowCount 1 levels)
        secretSampler embed errorSampler) :=
  fun transcript ↦ do
    let guessed ← auxiliarySampler
    rgswSquaredBiasTest levels encode gadget distinguisher guessed
      (LWE.TwoBlock.toTranscriptPair transcript)

/-- Source-oriented expansion of the real squared-bias game. -/
def rgswSquaredBiasSourceRealGame
    {R Secret Leakage : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (auxiliarySampler : ProbComp Leakage) (embed : Secret → Fin 1 → R)
    (encode : Leakage → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : RGSWDistinguisher R levels) :
    ProbComp Bool := do
  let secret ← secretSampler
  let blocks ← fixedSecretHomogeneousPair (TGSW.rowCount 1 levels) embed errorSampler secret
  let guessed ← auxiliarySampler
  rgswSquaredBiasTest levels encode gadget distinguisher guessed blocks

/-- The standard two-block real RLWE game with the concrete reduction is exactly its
source-oriented expansion. -/
theorem rgswSquaredBiasTwoBlock_game0_evalDist
    {R Secret Leakage : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (auxiliarySampler : ProbComp Leakage) (embed : Secret → Fin 1 → R)
    (encode : Leakage → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : RGSWDistinguisher R levels) :
    evalDist
        (LearningWithErrors.game0
          (LWE.TwoBlock.problem 1 (TGSW.rowCount 1 levels) (TGSW.rowCount 1 levels)
            secretSampler embed errorSampler)
          (rgswSquaredBiasTwoBlockAdversary levels secretSampler auxiliarySampler embed encode
            errorSampler gadget distinguisher)) =
      evalDist
        (rgswSquaredBiasSourceRealGame levels secretSampler auxiliarySampler embed encode
          errorSampler gadget distinguisher) := by
  rw [LearningWithErrors.game0]
  rw [show
      (LearningWithErrors.distr
          (LWE.TwoBlock.problem 1 (TGSW.rowCount 1 levels) (TGSW.rowCount 1 levels)
            secretSampler embed errorSampler) >>=
        rgswSquaredBiasTwoBlockAdversary levels secretSampler auxiliarySampler embed encode
          errorSampler gadget distinguisher) =
        ((LearningWithErrors.distr
            (LWE.TwoBlock.problem 1 (TGSW.rowCount 1 levels) (TGSW.rowCount 1 levels)
              secretSampler embed errorSampler) >>=
          fun transcript ↦ pure (LWE.TwoBlock.toTranscriptPair transcript)) >>=
            fun blocks ↦ auxiliarySampler >>= fun guessed ↦
              rgswSquaredBiasTest levels encode gadget distinguisher guessed blocks) by
    unfold rgswSquaredBiasTwoBlockAdversary
    simp [bind_assoc, monad_norm]]
  calc
    _ = evalDist
        ((secretSampler >>= fun secret ↦
            fixedSecretHomogeneousPair (TGSW.rowCount 1 levels) embed errorSampler secret) >>=
          fun blocks ↦ auxiliarySampler >>= fun guessed ↦
            rgswSquaredBiasTest levels encode gadget distinguisher guessed blocks) := by
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        (twoBlockReal_toTranscriptPair_evalDist
          (TGSW.rowCount 1 levels) secretSampler embed errorSampler) _
    _ = _ := by
      simp [rgswSquaredBiasSourceRealGame, bind_assoc, monad_norm]

/-- Context-first normal form of the real two-copy game. -/
def rgswSquaredBiasOrganizedRealGame
    {R Secret Leakage : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (auxiliarySampler : ProbComp Leakage) (embed : Secret → Fin 1 → R)
    (encode : Leakage → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : RGSWDistinguisher R levels) :
    ProbComp Bool := do
  let guessed ← auxiliarySampler
  let secret ← secretSampler
  let firstHomogeneous ← TLWE.batchEncrypt 1 (TGSW.rowCount 1 levels)
    errorSampler (embed secret) 0
  let first ← rgswPairedOutput levels encode gadget distinguisher guessed firstHomogeneous
  let secondHomogeneous ← TLWE.batchEncrypt 1 (TGSW.rowCount 1 levels)
    errorSampler (embed secret) 0
  let second ← rgswPairedOutput levels encode gadget distinguisher guessed secondHomogeneous
  SquaredBias.combine first.1 first.2 second.1 second.2

/-- Reordering independent samplers puts the standard two-block real source into the same
context-first order as the abstract leakage-removal experiment. -/
theorem rgswSquaredBiasSourceRealGame_evalDist_organized
    {R Secret Leakage : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (auxiliarySampler : ProbComp Leakage) (embed : Secret → Fin 1 → R)
    (encode : Leakage → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : RGSWDistinguisher R levels) :
    evalDist
        (rgswSquaredBiasSourceRealGame levels secretSampler auxiliarySampler embed encode
          errorSampler gadget distinguisher) =
      evalDist
        (rgswSquaredBiasOrganizedRealGame levels secretSampler auxiliarySampler embed encode
          errorSampler gadget distinguisher) := by
  let Homogeneous := fun secret ↦
    TLWE.batchEncrypt 1 (TGSW.rowCount 1 levels) errorSampler (embed secret) 0
  let Paired := fun guessed homogeneous ↦
    rgswPairedOutput levels encode gadget distinguisher guessed homogeneous
  let Finish := fun (first second : Bool × Bool) ↦
    SquaredBias.combine first.1 first.2 second.1 second.2
  have hSource :
      rgswSquaredBiasSourceRealGame levels secretSampler auxiliarySampler embed encode
          errorSampler gadget distinguisher =
        (secretSampler >>= fun secret ↦
          Homogeneous secret >>= fun firstHomogeneous ↦
            Homogeneous secret >>= fun secondHomogeneous ↦
              auxiliarySampler >>= fun guessed ↦
                Paired guessed firstHomogeneous >>= fun first ↦
                  Paired guessed secondHomogeneous >>= fun second ↦
                    Finish first second) := by
    simp [rgswSquaredBiasSourceRealGame, fixedSecretHomogeneousPair,
      rgswSquaredBiasTest, Homogeneous, Paired, Finish, bind_assoc, monad_norm]
  have hTarget :
      rgswSquaredBiasOrganizedRealGame levels secretSampler auxiliarySampler embed encode
          errorSampler gadget distinguisher =
        (auxiliarySampler >>= fun guessed ↦
          secretSampler >>= fun secret ↦
            Homogeneous secret >>= fun firstHomogeneous ↦
              Paired guessed firstHomogeneous >>= fun first ↦
                Homogeneous secret >>= fun secondHomogeneous ↦
                  Paired guessed secondHomogeneous >>= fun second ↦
                    Finish first second) := by
    rfl
  rw [hSource, hTarget]
  calc
    evalDist (secretSampler >>= fun secret ↦
        Homogeneous secret >>= fun firstHomogeneous ↦
          Homogeneous secret >>= fun secondHomogeneous ↦
            auxiliarySampler >>= fun guessed ↦
              Paired guessed firstHomogeneous >>= fun first ↦
                Paired guessed secondHomogeneous >>= fun second ↦
                  Finish first second) =
      evalDist (secretSampler >>= fun secret ↦
        Homogeneous secret >>= fun firstHomogeneous ↦
          auxiliarySampler >>= fun guessed ↦
            Homogeneous secret >>= fun secondHomogeneous ↦
              Paired guessed firstHomogeneous >>= fun first ↦
                Paired guessed secondHomogeneous >>= fun second ↦
                  Finish first second) := by
      apply evalDist_bind_congr' secretSampler
      intro secret
      apply evalDist_bind_congr' (Homogeneous secret)
      intro firstHomogeneous
      exact evalDist_bind_bind_swap (Homogeneous secret) auxiliarySampler _
    _ = evalDist (secretSampler >>= fun secret ↦
        Homogeneous secret >>= fun firstHomogeneous ↦
          auxiliarySampler >>= fun guessed ↦
            Paired guessed firstHomogeneous >>= fun first ↦
              Homogeneous secret >>= fun secondHomogeneous ↦
                Paired guessed secondHomogeneous >>= fun second ↦
                  Finish first second) := by
      apply evalDist_bind_congr' secretSampler
      intro secret
      apply evalDist_bind_congr' (Homogeneous secret)
      intro firstHomogeneous
      apply evalDist_bind_congr' auxiliarySampler
      intro guessed
      exact evalDist_bind_bind_swap (Homogeneous secret)
        (Paired guessed firstHomogeneous) _
    _ = evalDist (secretSampler >>= fun secret ↦
        auxiliarySampler >>= fun guessed ↦
          Homogeneous secret >>= fun firstHomogeneous ↦
            Paired guessed firstHomogeneous >>= fun first ↦
              Homogeneous secret >>= fun secondHomogeneous ↦
                Paired guessed secondHomogeneous >>= fun second ↦
                  Finish first second) := by
      apply evalDist_bind_congr' secretSampler
      intro secret
      exact evalDist_bind_bind_swap (Homogeneous secret) auxiliarySampler _
    _ = evalDist (auxiliarySampler >>= fun guessed ↦
        secretSampler >>= fun secret ↦
          Homogeneous secret >>= fun firstHomogeneous ↦
            Paired guessed firstHomogeneous >>= fun first ↦
              Homogeneous secret >>= fun secondHomogeneous ↦
                Paired guessed secondHomogeneous >>= fun second ↦
                  Finish first second) := by
      exact evalDist_bind_bind_swap secretSampler auxiliarySampler _

/-- The organized real source is definitionally the contextual leakage-removal experiment after
expanding native RGSW encryption into a homogeneous block followed by gadget addition. -/
theorem rgswSquaredBiasOrganizedRealGame_eq_removalRealGame
    {R Secret Leakage : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (auxiliarySampler : ProbComp Leakage) (embed : Secret → Fin 1 → R)
    (encode : Leakage → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : RGSWDistinguisher R levels) :
    rgswSquaredBiasOrganizedRealGame levels secretSampler auxiliarySampler embed encode
        errorSampler gadget distinguisher =
      leakageRemovalRealGame secretSampler auxiliarySampler
        (conditionalRGSWReal levels embed encode errorSampler gadget distinguisher)
        (conditionalRGSWIdeal levels embed encode gadget distinguisher) := by
  simp [rgswSquaredBiasOrganizedRealGame, leakageRemovalRealGame,
    SquaredBias.contextualExperiment, guessedContext, SquaredBias.experiment,
    SquaredBias.paired, conditionalRGSWReal, conditionalRGSWIdeal,
    TGSW.encrypt, rgswPairedOutput, bind_assoc, monad_norm]

/-- Exact real-game identification for the ordinary two-block RLWE reduction. -/
theorem rgswSquaredBiasTwoBlock_game0_eq_removalReal_evalDist
    {R Secret Leakage : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (auxiliarySampler : ProbComp Leakage) (embed : Secret → Fin 1 → R)
    (encode : Leakage → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : RGSWDistinguisher R levels) :
    evalDist
        (LearningWithErrors.game0
          (LWE.TwoBlock.problem 1 (TGSW.rowCount 1 levels) (TGSW.rowCount 1 levels)
            secretSampler embed errorSampler)
          (rgswSquaredBiasTwoBlockAdversary levels secretSampler auxiliarySampler embed encode
            errorSampler gadget distinguisher)) =
      evalDist
        (leakageRemovalRealGame secretSampler auxiliarySampler
          (conditionalRGSWReal levels embed encode errorSampler gadget distinguisher)
          (conditionalRGSWIdeal levels embed encode gadget distinguisher)) := by
  rw [rgswSquaredBiasTwoBlock_game0_evalDist,
    rgswSquaredBiasSourceRealGame_evalDist_organized,
    rgswSquaredBiasOrganizedRealGame_eq_removalRealGame]

/-- Regrouping a uniform two-block transcript gives two independent uniform native ciphertext
carriers. -/
theorem twoBlockUniform_toTranscriptPair_evalDist
    {R Secret : Type}
    [Semiring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (samples : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R) :
    evalDist
        (LearningWithErrors.uniformDistr
            (LWE.TwoBlock.problem 1 samples samples secretSampler embed errorSampler) >>=
          fun transcript ↦ pure (LWE.TwoBlock.toTranscriptPair transcript)) =
      evalDist (do
        let first ← $ᵗ (LWE.BatchTranscript R 1 samples)
        let second ← $ᵗ (LWE.BatchTranscript R 1 samples)
        return (first, second)) := by
  rw [LWE.TwoBlock.uniformDistr_eq_uniformSample]
  calc
    evalDist
        (($ᵗ (LWE.TwoBlock.Transcript R 1 samples samples)) >>= fun transcript ↦
          pure (LWE.TwoBlock.toTranscriptPair transcript)) =
      evalDist
        (LWE.TwoBlock.toTranscriptPair <$>
          ($ᵗ (LWE.TwoBlock.Transcript R 1 samples samples))) := by
      simp [monad_norm]
    _ = evalDist
        ($ᵗ (LWE.BatchTranscript R 1 samples × LWE.BatchTranscript R 1 samples)) := by
      exact evalDist_map_bijective_uniform_cross
        (α := LWE.TwoBlock.Transcript R 1 samples samples)
        (β := LWE.BatchTranscript R 1 samples × LWE.BatchTranscript R 1 samples)
        (LWE.TwoBlock.toTranscriptPair :
          LWE.TwoBlock.Transcript R 1 samples samples →
            LWE.BatchTranscript R 1 samples × LWE.BatchTranscript R 1 samples)
        LWE.TwoBlock.toTranscriptPair_bijective
    _ = _ :=
      (FormalProof4FHE.FiniteProduct.evalDist_independent_uniform_product
        (first := LWE.BatchTranscript R 1 samples)
        (second := LWE.BatchTranscript R 1 samples)).symm

/-- Source-oriented expansion of the uniform two-block reduction game. -/
def rgswSquaredBiasSourceUniformGame
    {R Leakage : Type}
    [Semiring R] [SampleableType R]
    (levels : ℕ) (auxiliarySampler : ProbComp Leakage)
    (encode : Leakage → R) (gadget : Fin levels → R)
    (distinguisher : RGSWDistinguisher R levels) : ProbComp Bool := do
  let first ← $ᵗ (RGSWChallenge R levels)
  let second ← $ᵗ (RGSWChallenge R levels)
  let guessed ← auxiliarySampler
  rgswSquaredBiasTest levels encode gadget distinguisher guessed (first, second)

/-- The standard two-block uniform game with the concrete reduction is exactly its independent
uniform-block expansion. -/
theorem rgswSquaredBiasTwoBlock_game1_evalDist
    {R Secret Leakage : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (auxiliarySampler : ProbComp Leakage) (embed : Secret → Fin 1 → R)
    (encode : Leakage → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : RGSWDistinguisher R levels) :
    evalDist
        (LearningWithErrors.game1
          (LWE.TwoBlock.problem 1 (TGSW.rowCount 1 levels) (TGSW.rowCount 1 levels)
            secretSampler embed errorSampler)
          (rgswSquaredBiasTwoBlockAdversary levels secretSampler auxiliarySampler embed encode
            errorSampler gadget distinguisher)) =
      evalDist
        (rgswSquaredBiasSourceUniformGame levels auxiliarySampler encode gadget
          distinguisher) := by
  rw [LearningWithErrors.game1]
  rw [show
      (LearningWithErrors.uniformDistr
          (LWE.TwoBlock.problem 1 (TGSW.rowCount 1 levels) (TGSW.rowCount 1 levels)
            secretSampler embed errorSampler) >>=
        rgswSquaredBiasTwoBlockAdversary levels secretSampler auxiliarySampler embed encode
          errorSampler gadget distinguisher) =
        ((LearningWithErrors.uniformDistr
            (LWE.TwoBlock.problem 1 (TGSW.rowCount 1 levels) (TGSW.rowCount 1 levels)
              secretSampler embed errorSampler) >>=
          fun transcript ↦ pure (LWE.TwoBlock.toTranscriptPair transcript)) >>=
            fun blocks ↦ auxiliarySampler >>= fun guessed ↦
              rgswSquaredBiasTest levels encode gadget distinguisher guessed blocks) by
    unfold rgswSquaredBiasTwoBlockAdversary
    simp [bind_assoc, monad_norm]]
  calc
    _ = evalDist
        ((do
            let first ← $ᵗ (RGSWChallenge R levels)
            let second ← $ᵗ (RGSWChallenge R levels)
            return (first, second)) >>= fun blocks ↦
          auxiliarySampler >>= fun guessed ↦
            rgswSquaredBiasTest levels encode gadget distinguisher guessed blocks) := by
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        (twoBlockUniform_toTranscriptPair_evalDist
          (TGSW.rowCount 1 levels) secretSampler embed errorSampler) _
    _ = _ := by
      simp [rgswSquaredBiasSourceUniformGame, bind_assoc, monad_norm]

/-- One ideal/control output pair, with both ciphertexts sampled uniformly. -/
def rgswIdealPairedOutput
    {R : Type} [SampleableType R]
    (levels : ℕ) (distinguisher : RGSWDistinguisher R levels) :
    ProbComp (Bool × Bool) :=
  SquaredBias.paired
    (($ᵗ (RGSWChallenge R levels)) >>= distinguisher)
    (($ᵗ (RGSWChallenge R levels)) >>= distinguisher)

/-- Adding the guessed gadget to a uniform source block leaves the whole paired-output law
unchanged. -/
theorem rgswPairedOutput_uniform_evalDist
    {R Leakage : Type}
    [Ring R] [Fintype R] [SampleableType R]
    (levels : ℕ) (encode : Leakage → R) (gadget : Fin levels → R)
    (distinguisher : RGSWDistinguisher R levels) (guessed : Leakage) :
    evalDist
        (($ᵗ (RGSWChallenge R levels)) >>= fun homogeneous ↦
          rgswPairedOutput levels encode gadget distinguisher guessed homogeneous) =
      evalDist (rgswIdealPairedOutput levels distinguisher) := by
  have hTranslated :
      evalDist
          (($ᵗ (RGSWChallenge R levels)) >>= fun homogeneous ↦
            distinguisher (TGSW.addGadget gadget (encode guessed) homogeneous)) =
        evalDist (($ᵗ (RGSWChallenge R levels)) >>= distinguisher) := by
    have h := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
      (addGadget_uniform_evalDist gadget (encode guessed)) distinguisher
    simpa [bind_assoc, monad_norm] using h
  simpa [rgswPairedOutput, rgswIdealPairedOutput, SquaredBias.paired, bind_assoc,
    monad_norm] using
      (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hTranslated
        (fun firstOutput ↦
          ($ᵗ (RGSWChallenge R levels)) >>= fun idealCiphertext ↦
            distinguisher idealCiphertext >>= fun idealOutput ↦
              pure (firstOutput, idealOutput)))

/-- One uniform source block followed by its translated real/control paired test. -/
def rgswUniformPairedBlock
    {R Leakage : Type}
    [Semiring R] [SampleableType R]
    (levels : ℕ) (encode : Leakage → R) (gadget : Fin levels → R)
    (distinguisher : RGSWDistinguisher R levels) (guessed : Leakage) :
    ProbComp (Bool × Bool) := do
  let homogeneous ← $ᵗ (RGSWChallenge R levels)
  rgswPairedOutput levels encode gadget distinguisher guessed homogeneous

/-- Guess-first normal form of the uniform two-block source game. -/
def rgswSquaredBiasOrganizedUniformGame
    {R Leakage : Type}
    [Semiring R] [SampleableType R]
    (levels : ℕ) (auxiliarySampler : ProbComp Leakage)
    (encode : Leakage → R) (gadget : Fin levels → R)
    (distinguisher : RGSWDistinguisher R levels) : ProbComp Bool := do
  let guessed ← auxiliarySampler
  let first ← rgswUniformPairedBlock levels encode gadget distinguisher guessed
  let second ← rgswUniformPairedBlock levels encode gadget distinguisher guessed
  SquaredBias.combine first.1 first.2 second.1 second.2

/-- Reordering the independent guess and uniform blocks yields the guess-first normal form. -/
theorem rgswSquaredBiasSourceUniformGame_evalDist_organized
    {R Leakage : Type}
    [Semiring R] [SampleableType R]
    (levels : ℕ) (auxiliarySampler : ProbComp Leakage)
    (encode : Leakage → R) (gadget : Fin levels → R)
    (distinguisher : RGSWDistinguisher R levels) :
    evalDist
        (rgswSquaredBiasSourceUniformGame levels auxiliarySampler encode gadget
          distinguisher) =
      evalDist
        (rgswSquaredBiasOrganizedUniformGame levels auxiliarySampler encode gadget
          distinguisher) := by
  let Uniform : ProbComp (RGSWChallenge R levels) := $ᵗ (RGSWChallenge R levels)
  let Paired := fun guessed homogeneous ↦
    rgswPairedOutput levels encode gadget distinguisher guessed homogeneous
  let Finish := fun (first second : Bool × Bool) ↦
    SquaredBias.combine first.1 first.2 second.1 second.2
  simp only [rgswSquaredBiasSourceUniformGame, rgswSquaredBiasTest,
    rgswSquaredBiasOrganizedUniformGame, rgswUniformPairedBlock]
  simp only [bind_assoc]
  change evalDist (Uniform >>= fun firstHomogeneous ↦
      Uniform >>= fun secondHomogeneous ↦
        auxiliarySampler >>= fun guessed ↦
          Paired guessed firstHomogeneous >>= fun first ↦
            Paired guessed secondHomogeneous >>= fun second ↦ Finish first second) =
    evalDist (auxiliarySampler >>= fun guessed ↦
      Uniform >>= fun firstHomogeneous ↦
        Paired guessed firstHomogeneous >>= fun first ↦
          Uniform >>= fun secondHomogeneous ↦
            Paired guessed secondHomogeneous >>= fun second ↦ Finish first second)
  calc
    evalDist (Uniform >>= fun firstHomogeneous ↦
        Uniform >>= fun secondHomogeneous ↦
          auxiliarySampler >>= fun guessed ↦
            Paired guessed firstHomogeneous >>= fun first ↦
              Paired guessed secondHomogeneous >>= fun second ↦ Finish first second) =
      evalDist (Uniform >>= fun firstHomogeneous ↦
        auxiliarySampler >>= fun guessed ↦
          Uniform >>= fun secondHomogeneous ↦
            Paired guessed firstHomogeneous >>= fun first ↦
              Paired guessed secondHomogeneous >>= fun second ↦ Finish first second) := by
      apply evalDist_bind_congr' Uniform
      intro firstHomogeneous
      exact evalDist_bind_bind_swap Uniform auxiliarySampler _
    _ = evalDist (Uniform >>= fun firstHomogeneous ↦
        auxiliarySampler >>= fun guessed ↦
          Paired guessed firstHomogeneous >>= fun first ↦
            Uniform >>= fun secondHomogeneous ↦
              Paired guessed secondHomogeneous >>= fun second ↦ Finish first second) := by
      apply evalDist_bind_congr' Uniform
      intro firstHomogeneous
      apply evalDist_bind_congr' auxiliarySampler
      intro guessed
      exact evalDist_bind_bind_swap Uniform (Paired guessed firstHomogeneous) _
    _ = evalDist (auxiliarySampler >>= fun guessed ↦
        Uniform >>= fun firstHomogeneous ↦
          Paired guessed firstHomogeneous >>= fun first ↦
            Uniform >>= fun secondHomogeneous ↦
              Paired guessed secondHomogeneous >>= fun second ↦ Finish first second) := by
      exact evalDist_bind_bind_swap Uniform auxiliarySampler _

/-- Guess-first ideal endpoint, with two independently paired uniform/control calls. -/
def rgswSquaredBiasOrganizedIdealGame
    {R Leakage : Type} [SampleableType R]
    (levels : ℕ) (auxiliarySampler : ProbComp Leakage)
    (distinguisher : RGSWDistinguisher R levels) : ProbComp Bool := do
  let _guessed ← auxiliarySampler
  let first ← rgswIdealPairedOutput levels distinguisher
  let second ← rgswIdealPairedOutput levels distinguisher
  SquaredBias.combine first.1 first.2 second.1 second.2

/-- Both translated source blocks in the uniform normal form may be replaced by genuinely uniform
blocks. -/
theorem rgswSquaredBiasOrganizedUniformGame_evalDist_ideal
    {R Leakage : Type}
    [Ring R] [Fintype R] [SampleableType R]
    (levels : ℕ) (auxiliarySampler : ProbComp Leakage)
    (encode : Leakage → R) (gadget : Fin levels → R)
    (distinguisher : RGSWDistinguisher R levels) :
    evalDist
        (rgswSquaredBiasOrganizedUniformGame levels auxiliarySampler encode gadget
          distinguisher) =
      evalDist
        (rgswSquaredBiasOrganizedIdealGame levels auxiliarySampler distinguisher) := by
  unfold rgswSquaredBiasOrganizedUniformGame rgswSquaredBiasOrganizedIdealGame
  apply evalDist_bind_congr' auxiliarySampler
  intro guessed
  have hPair :
      evalDist (rgswUniformPairedBlock levels encode gadget distinguisher guessed) =
        evalDist (rgswIdealPairedOutput levels distinguisher) := by
    simpa only [rgswUniformPairedBlock] using
      (rgswPairedOutput_uniform_evalDist levels encode gadget distinguisher guessed)
  calc
    _ = evalDist (rgswIdealPairedOutput levels distinguisher >>= fun first ↦
        rgswUniformPairedBlock levels encode gadget distinguisher guessed >>= fun second ↦
          SquaredBias.combine first.1 first.2 second.1 second.2) := by
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hPair _
    _ = _ := by
      apply evalDist_bind_congr' (rgswIdealPairedOutput levels distinguisher)
      intro first
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hPair _

/-- After discarding the total dummy-secret sampler, the organized ideal endpoint is exactly the
abstract leakage-removal ideal game. -/
theorem rgswSquaredBiasOrganizedIdealGame_eq_removalIdeal_evalDist
    {R Secret Leakage : Type}
    [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (auxiliarySampler : ProbComp Leakage)
    (embed : Secret → Fin 1 → R) (encode : Leakage → R)
    (gadget : Fin levels → R) (distinguisher : RGSWDistinguisher R levels)
    (hSecretTotal : Pr[⊥ | secretSampler] = 0) :
    evalDist (rgswSquaredBiasOrganizedIdealGame levels auxiliarySampler distinguisher) =
      evalDist
        (leakageRemovalIdealGame secretSampler auxiliarySampler
          (conditionalRGSWIdeal levels embed encode gadget distinguisher)) := by
  have hExpanded :
      leakageRemovalIdealGame secretSampler auxiliarySampler
          (conditionalRGSWIdeal levels embed encode gadget distinguisher) =
        (auxiliarySampler >>= fun _guessed ↦
          secretSampler >>= fun _secret ↦
            rgswIdealPairedOutput levels distinguisher >>= fun first ↦
              rgswIdealPairedOutput levels distinguisher >>= fun second ↦
                SquaredBias.combine first.1 first.2 second.1 second.2) := by
    simp [leakageRemovalIdealGame, SquaredBias.contextualExperiment, guessedContext,
      SquaredBias.experiment, SquaredBias.paired, conditionalRGSWIdeal,
      rgswIdealPairedOutput, bind_assoc, monad_norm]
  rw [hExpanded]
  apply Eq.symm
  apply evalDist_bind_congr' auxiliarySampler
  intro _guessed
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
    secretSampler hSecretTotal _

/-- Exact uniform-game identification for the ordinary two-block RLWE reduction. -/
theorem rgswSquaredBiasTwoBlock_game1_eq_removalIdeal_evalDist
    {R Secret Leakage : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (auxiliarySampler : ProbComp Leakage) (embed : Secret → Fin 1 → R)
    (encode : Leakage → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : RGSWDistinguisher R levels)
    (hSecretTotal : Pr[⊥ | secretSampler] = 0) :
    evalDist
        (LearningWithErrors.game1
          (LWE.TwoBlock.problem 1 (TGSW.rowCount 1 levels) (TGSW.rowCount 1 levels)
            secretSampler embed errorSampler)
          (rgswSquaredBiasTwoBlockAdversary levels secretSampler auxiliarySampler embed encode
            errorSampler gadget distinguisher)) =
      evalDist
        (leakageRemovalIdealGame secretSampler auxiliarySampler
          (conditionalRGSWIdeal levels embed encode gadget distinguisher)) := by
  rw [rgswSquaredBiasTwoBlock_game1_evalDist,
    rgswSquaredBiasSourceUniformGame_evalDist_organized,
    rgswSquaredBiasOrganizedUniformGame_evalDist_ideal,
    rgswSquaredBiasOrganizedIdealGame_eq_removalIdeal_evalDist
      levels secretSampler auxiliarySampler embed encode gadget distinguisher hSecretTotal]

/-- The abstract leakage-removal advantage is exactly the advantage of the paper's concrete
two-block RLWE adversary. -/
theorem rgswLeakageRemovalAdvantage_eq_twoBlockRLWE
    {R Secret Leakage : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (auxiliarySampler : ProbComp Leakage) (embed : Secret → Fin 1 → R)
    (encode : Leakage → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : RGSWDistinguisher R levels)
    (hSecretTotal : Pr[⊥ | secretSampler] = 0) :
    rgswLeakageRemovalAdvantage levels secretSampler auxiliarySampler embed encode
        errorSampler gadget distinguisher =
      LearningWithErrors.advantage
        (LWE.TwoBlock.problem 1 (TGSW.rowCount 1 levels) (TGSW.rowCount 1 levels)
          secretSampler embed errorSampler)
        (rgswSquaredBiasTwoBlockAdversary levels secretSampler auxiliarySampler embed encode
          errorSampler gadget distinguisher) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold rgswLeakageRemovalAdvantage leakageRemovalAdvantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (rgswSquaredBiasTwoBlock_game0_eq_removalReal_evalDist levels secretSampler
        auxiliarySampler embed encode errorSampler gadget distinguisher) true,
    evalDist_ext_iff.mp
      (rgswSquaredBiasTwoBlock_game1_eq_removalIdeal_evalDist levels secretSampler
        auxiliarySampler embed encode errorSampler gadget distinguisher hSecretTotal) true]

/-- Exact ordinary batch-RLWE form of the doubled source.  Its sample count is
`rowCount + rowCount = 4 * levels`. -/
theorem rgswLeakageRemovalAdvantage_eq_batchRLWE
    {R Secret Leakage : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (auxiliarySampler : ProbComp Leakage) (embed : Secret → Fin 1 → R)
    (encode : Leakage → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : RGSWDistinguisher R levels)
    (hSecretTotal : Pr[⊥ | secretSampler] = 0) :
    rgswLeakageRemovalAdvantage levels secretSampler auxiliarySampler embed encode
        errorSampler gadget distinguisher =
      LearningWithErrors.advantage
        (LWE.embeddedBatchProblem 1
          (TGSW.rowCount 1 levels + TGSW.rowCount 1 levels)
          secretSampler embed errorSampler)
        (LWE.TwoBlock.reduction
          (rgswSquaredBiasTwoBlockAdversary levels secretSampler auxiliarySampler embed encode
            errorSampler gadget distinguisher)) := by
  calc
    _ = LearningWithErrors.advantage
        (LWE.TwoBlock.problem 1 (TGSW.rowCount 1 levels) (TGSW.rowCount 1 levels)
          secretSampler embed errorSampler)
        (rgswSquaredBiasTwoBlockAdversary levels secretSampler auxiliarySampler embed encode
          errorSampler gadget distinguisher) :=
      rgswLeakageRemovalAdvantage_eq_twoBlockRLWE levels secretSampler auxiliarySampler
        embed encode errorSampler gadget distinguisher hSecretTotal
    _ = _ := LWE.TwoBlock.advantage_eq_batch 1
      (TGSW.rowCount 1 levels) (TGSW.rowCount 1 levels)
      secretSampler embed errorSampler
      (rgswSquaredBiasTwoBlockAdversary levels secretSampler auxiliarySampler embed encode
        errorSampler gadget distinguisher)

/-- One ordinary real batch is exactly a fixed-secret homogeneous native block after reordering
the independent public challenge and secret samplers. -/
theorem batchReal_fixedSecretHomogeneous_evalDist
    {R Secret : Type}
    [Semiring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (samples : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R) :
    evalDist
        (LearningWithErrors.distr
          (LWE.embeddedBatchProblem 1 samples secretSampler embed errorSampler)) =
      evalDist (secretSampler >>= fun secret ↦
        TLWE.batchEncrypt 1 samples errorSampler (embed secret) 0) := by
  let Challenge : ProbComp (Matrix (Fin 1) (Fin samples) R) :=
    $ᵗ Matrix (Fin 1) (Fin samples) R
  let Error : ProbComp (Fin samples → R) := ProbComp.sampleIID samples errorSampler
  let Finish := fun (challenge : Matrix (Fin 1) (Fin samples) R)
      (secret : Secret) (error : Fin samples → R) ↦
    (pure (challenge, vecMul (embed secret) challenge + error) :
      ProbComp (LWE.BatchTranscript R 1 samples))
  have hLeft :
      LearningWithErrors.distr
          (LWE.embeddedBatchProblem 1 samples secretSampler embed errorSampler) =
        (Challenge >>= fun challenge ↦
          secretSampler >>= fun secret ↦
            Error >>= fun error ↦ Finish challenge secret error) := by
    simp [LearningWithErrors.distr, LWE.embeddedBatchProblem, Challenge, Error, Finish,
      monad_norm]
  have hRight :
      (secretSampler >>= fun secret ↦
        TLWE.batchEncrypt 1 samples errorSampler (embed secret) 0) =
        (secretSampler >>= fun secret ↦
          Challenge >>= fun challenge ↦
            Error >>= fun error ↦ Finish challenge secret error) := by
    simp [TLWE.batchEncrypt, TLWE.batchAssemble, Challenge, Error, Finish, monad_norm]
  rw [hLeft, hRight]
  exact evalDist_bind_bind_swap Challenge secretSampler _

/-- Direct adversary for the ordinary `2 * levels`-row zero-message RLWE hop. -/
def rgswZeroBatchAdversary
    {R Secret : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (distinguisher : RGSWDistinguisher R levels) :
    LearningWithErrors.Adversary
      (LWE.embeddedBatchProblem 1 (TGSW.rowCount 1 levels)
        secretSampler embed errorSampler) :=
  distinguisher

/-- The native zero-message RGSW advantage is exactly ordinary `2 * levels`-sample RLWE. -/
theorem rgswZeroAdvantage_eq_batchRLWE
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : RGSWDistinguisher R levels)
    (hSecretTotal : Pr[⊥ | secretSampler] = 0) :
    rgswZeroAdvantage levels secretSampler embed errorSampler gadget distinguisher =
      LearningWithErrors.advantage
        (LWE.embeddedBatchProblem 1 (TGSW.rowCount 1 levels)
          secretSampler embed errorSampler)
        (rgswZeroBatchAdversary levels secretSampler embed errorSampler distinguisher) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold rgswZeroAdvantage ProbComp.boolDistAdvantage
  have hReal :
      evalDist
          (LearningWithErrors.game0
            (LWE.embeddedBatchProblem 1 (TGSW.rowCount 1 levels)
              secretSampler embed errorSampler)
            (rgswZeroBatchAdversary levels secretSampler embed errorSampler distinguisher)) =
        evalDist
          (rgswZeroGame levels secretSampler embed errorSampler gadget distinguisher) := by
    rw [LearningWithErrors.game0]
    unfold rgswZeroBatchAdversary
    calc
      _ = evalDist
          ((secretSampler >>= fun secret ↦
            TLWE.batchEncrypt 1 (TGSW.rowCount 1 levels) errorSampler (embed secret) 0) >>=
              distinguisher) := by
        exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
          (batchReal_fixedSecretHomogeneous_evalDist
            (TGSW.rowCount 1 levels) secretSampler embed errorSampler) _
      _ = _ := by
        simp [rgswZeroGame, TGSW.encryptZero, TGSW.encrypt, bind_assoc, monad_norm]
  have hUniform :
      evalDist
          (LearningWithErrors.game1
            (LWE.embeddedBatchProblem 1 (TGSW.rowCount 1 levels)
              secretSampler embed errorSampler)
            (rgswZeroBatchAdversary levels secretSampler embed errorSampler distinguisher)) =
        evalDist (rgswUniformGame levels secretSampler distinguisher) := by
    rw [LearningWithErrors.game1,
      LWE.TwoBlock.batchUniformDistr_eq_uniformSample]
    unfold rgswZeroBatchAdversary rgswUniformGame
    apply Eq.symm
    exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
      secretSampler hSecretTotal _
  rw [evalDist_ext_iff.mp hReal true, evalDist_ext_iff.mp hUniform true]

/-- **Paper theorem in ordinary batch-RLWE form.**  The coefficient-dependent RGSW advantage is
bounded by a doubled `4 * levels`-row RLWE reduction and one `2 * levels`-row zero-message RLWE
reduction, with the exact arbitrary-law leakage factor. -/
theorem rgswKDMAdvantage_le_sqrt_gamma_add_batchRLWE
    {R Secret Leakage : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [Fintype Leakage]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (auxiliarySampler : ProbComp Leakage)
    (embed : Secret → Fin 1 → R) (leakage : Secret → Leakage)
    (encode : Leakage → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : RGSWDistinguisher R levels)
    (hcover : ∀ secret, probabilityMass secretSampler secret ≠ 0 →
      probabilityMass auxiliarySampler (leakage secret) ≠ 0)
    (hSecretTotal : Pr[⊥ | secretSampler] = 0) :
    rgswKDMAdvantage levels secretSampler embed leakage encode errorSampler gadget
        distinguisher ≤
      Real.sqrt (2 * leakageGamma secretSampler auxiliarySampler leakage *
        LearningWithErrors.advantage
          (LWE.embeddedBatchProblem 1
            (TGSW.rowCount 1 levels + TGSW.rowCount 1 levels)
            secretSampler embed errorSampler)
          (LWE.TwoBlock.reduction
            (rgswSquaredBiasTwoBlockAdversary levels secretSampler auxiliarySampler embed encode
              errorSampler gadget distinguisher))) +
      LearningWithErrors.advantage
        (LWE.embeddedBatchProblem 1 (TGSW.rowCount 1 levels)
          secretSampler embed errorSampler)
        (rgswZeroBatchAdversary levels secretSampler embed errorSampler distinguisher) := by
  simpa [rgswLeakageRemovalAdvantage_eq_batchRLWE levels secretSampler auxiliarySampler
      embed encode errorSampler gadget distinguisher hSecretTotal,
    rgswZeroAdvantage_eq_batchRLWE levels secretSampler embed errorSampler gadget distinguisher
      hSecretTotal] using
    (rgswKDMAdvantage_le_sqrt_gamma_add_zero levels secretSampler auxiliarySampler
      embed leakage encode errorSampler gadget distinguisher hcover)

/-- Optimized order-`1/2` concentration form of the ordinary batch-RLWE theorem. -/
theorem rgswKDMAdvantage_le_sqrt_concentration_add_batchRLWE
    {R Secret Leakage : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [Fintype Leakage]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (auxiliarySampler : ProbComp Leakage)
    (embed : Secret → Fin 1 → R) (leakage : Secret → Leakage)
    (encode : Leakage → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : RGSWDistinguisher R levels)
    (hcover : ∀ secret, probabilityMass secretSampler secret ≠ 0 →
      probabilityMass auxiliarySampler (leakage secret) ≠ 0)
    (hoptimized : ∀ value,
      probabilityMass auxiliarySampler value =
        Real.sqrt (probabilityMass (leakageLaw secretSampler leakage) value) /
          halfRenyiNormalizer secretSampler leakage)
    (hSecretTotal : Pr[⊥ | secretSampler] = 0) :
    rgswKDMAdvantage levels secretSampler embed leakage encode errorSampler gadget
        distinguisher ≤
      Real.sqrt (2 * halfRenyiConcentration (leakageLaw secretSampler leakage) *
        LearningWithErrors.advantage
          (LWE.embeddedBatchProblem 1
            (TGSW.rowCount 1 levels + TGSW.rowCount 1 levels)
            secretSampler embed errorSampler)
          (LWE.TwoBlock.reduction
            (rgswSquaredBiasTwoBlockAdversary levels secretSampler auxiliarySampler embed encode
              errorSampler gadget distinguisher))) +
      LearningWithErrors.advantage
        (LWE.embeddedBatchProblem 1 (TGSW.rowCount 1 levels)
          secretSampler embed errorSampler)
        (rgswZeroBatchAdversary levels secretSampler embed errorSampler distinguisher) := by
  simpa [rgswLeakageRemovalAdvantage_eq_batchRLWE levels secretSampler auxiliarySampler
      embed encode errorSampler gadget distinguisher hSecretTotal,
    rgswZeroAdvantage_eq_batchRLWE levels secretSampler embed errorSampler gadget distinguisher
      hSecretTotal] using
    (rgswKDMAdvantage_le_sqrt_concentration_add_zero levels secretSampler auxiliarySampler
      embed leakage encode errorSampler gadget distinguisher hcover hoptimized)

/-- Unconditional finite-carrier form of the ordinary batch-RLWE theorem. -/
theorem rgswKDMAdvantage_le_sqrt_card_add_batchRLWE
    {R Secret Leakage : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [Fintype Leakage] [Nonempty Leakage] [SampleableType Leakage]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (leakage : Secret → Leakage)
    (encode : Leakage → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (distinguisher : RGSWDistinguisher R levels)
    (hSecretTotal : Pr[⊥ | secretSampler] = 0) :
    rgswKDMAdvantage levels secretSampler embed leakage encode errorSampler gadget
        distinguisher ≤
      Real.sqrt (2 * Fintype.card Leakage *
        LearningWithErrors.advantage
          (LWE.embeddedBatchProblem 1
            (TGSW.rowCount 1 levels + TGSW.rowCount 1 levels)
            secretSampler embed errorSampler)
          (LWE.TwoBlock.reduction
            (rgswSquaredBiasTwoBlockAdversary levels secretSampler ($ᵗ Leakage) embed encode
              errorSampler gadget distinguisher))) +
      LearningWithErrors.advantage
        (LWE.embeddedBatchProblem 1 (TGSW.rowCount 1 levels)
          secretSampler embed errorSampler)
        (rgswZeroBatchAdversary levels secretSampler embed errorSampler distinguisher) := by
  simpa [rgswLeakageRemovalAdvantage_eq_batchRLWE levels secretSampler ($ᵗ Leakage)
      embed encode errorSampler gadget distinguisher hSecretTotal,
    rgswZeroAdvantage_eq_batchRLWE levels secretSampler embed errorSampler gadget distinguisher
      hSecretTotal] using
    (rgswKDMAdvantage_le_sqrt_card_add_zero levels secretSampler embed leakage encode
      errorSampler gadget distinguisher)

/-- The zero-message hybrid uses exactly `2 * levels` ordinary RLWE rows. -/
theorem oneCoordinate_zeroRowCount (levels : ℕ) :
    TGSW.rowCount 1 levels = 2 * levels := by
  change (1 + 1) * levels = 2 * levels
  omega

end

end FormalProof4FHE.TFHE.RGSWCoefficientCircularSecurity
