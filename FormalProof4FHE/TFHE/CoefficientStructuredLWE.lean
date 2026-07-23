/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.CutCycleSecurity
import FormalProof4FHE.RLWE.CenteredBinomial

/-!
# Coefficient Presentation of Native Binary-Secret Structured LWE

This module exposes the finite ring/module-LWE problem used by native TFHE as a coefficient-level
negacyclic structured-LWE game.  It records, without a hardness assumption or a sampler
identification, all data needed to compare the game with foundational structured-LWE statements:

* coefficient modulus `q`;
* negacyclic degree `degree`;
* module rank and sample count;
* independently uniform Boolean secret coefficients; and
* the exact coefficient image of the supplied ring-error sampler.

The coefficient presentation is obtained through the executable carrier equivalence
`Rq q degree ≃ (Fin degree → ZMod q)`.  Real and uniform games, and hence every distinguishing
advantage, are preserved exactly.  At rank one this is a coefficient presentation of
binary-secret RLWE, not uniform-secret RLWE.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE

noncomputable section

/-- One coefficient vector in `ZMod q[X] / (X^degree + 1)`. -/
abbrev Coefficients (q degree : ℕ) := Fin degree → ZMod q

/-- Public coefficient matrices for rank-`rank`, `sampleCount` structured-LWE. -/
abbrev Challenge (q degree rank sampleCount : ℕ) :=
  Matrix (Fin rank) (Fin sampleCount) (Coefficients q degree)

/-- Coefficient-vector right-hand sides for `sampleCount` structured-LWE samples. -/
abbrev Output (q degree sampleCount : ℕ) :=
  Fin sampleCount → Coefficients q degree

/-- Public coefficient-level transcript. -/
abbrev Transcript (q degree rank sampleCount : ℕ) :=
  Challenge q degree rank sampleCount × Output q degree sampleCount

/-- The executable ring carrier is exactly its finite coefficient function. -/
def coefficientEquiv (q degree : ℕ) :
    RLWE.Rq q degree ≃ Coefficients q degree where
  toFun := LatticeCrypto.Poly.toPi
  invFun := LatticeCrypto.Poly.ofPi
  left_inv := LatticeCrypto.Poly.ofPi_toPi
  right_inv := LatticeCrypto.Poly.toPi_ofPi

/-- Apply the coefficient equivalence to every entry of a public matrix. -/
def challengeEquiv (q degree rank sampleCount : ℕ) :
    RLWE.ModuleSample q degree rank sampleCount ≃
      Challenge q degree rank sampleCount where
  toFun challenge := fun row sample ↦
    coefficientEquiv q degree (challenge row sample)
  invFun challenge := fun row sample ↦
    (coefficientEquiv q degree).symm (challenge row sample)
  left_inv challenge := by
    funext row sample
    exact (coefficientEquiv q degree).symm_apply_apply (challenge row sample)
  right_inv challenge := by
    funext row sample
    exact (coefficientEquiv q degree).apply_symm_apply (challenge row sample)

/-- Apply the coefficient equivalence to every right-hand side. -/
def outputEquiv (q degree sampleCount : ℕ) :
    RLWE.ModuleOutput q degree sampleCount ≃
      Output q degree sampleCount where
  toFun output := fun sample ↦ coefficientEquiv q degree (output sample)
  invFun output := fun sample ↦
    (coefficientEquiv q degree).symm (output sample)
  left_inv output := by
    funext sample
    exact (coefficientEquiv q degree).symm_apply_apply (output sample)
  right_inv output := by
    funext sample
    exact (coefficientEquiv q degree).apply_symm_apply (output sample)

/-- Coefficientwise public transcript equivalence. -/
def transcriptEquiv (q degree rank sampleCount : ℕ) :
    (RLWE.ModuleSample q degree rank sampleCount ×
      RLWE.ModuleOutput q degree sampleCount) ≃
      Transcript q degree rank sampleCount :=
  (challengeEquiv q degree rank sampleCount).prodCongr
    (outputEquiv q degree sampleCount)

@[simp]
theorem coefficientEquiv_add (q degree : ℕ) (left right : RLWE.Rq q degree) :
    coefficientEquiv q degree (left + right) =
      coefficientEquiv q degree left + coefficientEquiv q degree right := by
  funext coefficient
  exact LatticeCrypto.NegacyclicRing.coeff_add
    (RLWE.negacyclicRing q degree) left right coefficient

@[simp]
theorem outputEquiv_add (q degree sampleCount : ℕ)
    (left right : RLWE.ModuleOutput q degree sampleCount) :
    outputEquiv q degree sampleCount (left + right) =
      outputEquiv q degree sampleCount left + outputEquiv q degree sampleCount right := by
  funext sample
  change coefficientEquiv q degree (left sample + right sample) =
    coefficientEquiv q degree (left sample) + coefficientEquiv q degree (right sample)
  exact coefficientEquiv_add q degree (left sample) (right sample)

@[simp]
theorem coefficientEquiv_zero (q degree : ℕ) :
    coefficientEquiv q degree (0 : RLWE.Rq q degree) = 0 := by
  funext coefficient
  exact LatticeCrypto.NegacyclicRing.zero_coeff
    (RLWE.negacyclicRing q degree) coefficient

/-- The same additive law through the proof-facing `CommRing` instance used by matrix LWE. -/
theorem coefficientEquiv_semiring_add (q degree : ℕ)
    (left right : RLWE.Rq q degree) :
    coefficientEquiv q degree
        (@Add.add (RLWE.Rq q degree)
          (LatticeCrypto.vectorNegacyclicRing_instCommRing
            (ZMod q) degree).toAdd left right) =
      coefficientEquiv q degree left + coefficientEquiv q degree right := by
  cases degree with
  | zero =>
      funext coefficient
      exact coefficient.elim0
  | succ degree =>
      exact coefficientEquiv_add q (degree + 1) left right

/-- The proof-facing `CommRing` zero has the all-zero coefficient vector. -/
theorem coefficientEquiv_semiring_zero (q degree : ℕ) :
    coefficientEquiv q degree
        (@OfNat.ofNat (RLWE.Rq q degree) 0
          (@Zero.toOfNat0 (RLWE.Rq q degree)
            (LatticeCrypto.vectorNegacyclicRing_instCommRing
              (ZMod q) degree).toAddGroupWithOne.toAddZeroClass.toZero)) = 0 := by
  cases degree with
  | zero =>
      funext coefficient
      exact coefficient.elim0
  | succ degree =>
      exact coefficientEquiv_zero q (degree + 1)

/-- The coefficient equivalence bundled as an additive equivalence. -/
def coefficientAddEquiv (q degree : ℕ) :
    RLWE.Rq q degree ≃+ Coefficients q degree where
  toEquiv := coefficientEquiv q degree
  map_add' := coefficientEquiv_add q degree

/-- The coefficient equivalence bundled as an additive-monoid homomorphism. -/
def coefficientAddMonoidHom (q degree : ℕ) :
    RLWE.Rq q degree →+ Coefficients q degree where
  toFun := coefficientEquiv q degree
  map_zero' := coefficientEquiv_semiring_zero q degree
  map_add' := coefficientEquiv_semiring_add q degree

@[simp]
theorem coefficientEquiv_sum {Index : Type} [Fintype Index]
    (q degree : ℕ) (values : Index → RLWE.Rq q degree) :
    coefficientEquiv q degree (∑ index, values index) =
      ∑ index, coefficientEquiv q degree (values index) :=
  map_sum (coefficientAddMonoidHom q degree) values Finset.univ

/-- Explicit schoolbook negacyclic product on coefficient functions. -/
def negacyclicProduct {q degree : ℕ}
    (left right : Coefficients q degree) : Coefficients q degree :=
  fun coefficient ↦ LatticeCrypto.negacyclicConvCoeff left right coefficient

/-- Executable `Rq` multiplication is exactly schoolbook negacyclic convolution after taking
coefficients. -/
@[simp]
theorem coefficientEquiv_mul (q degree : ℕ) (left right : RLWE.Rq q degree) :
    coefficientEquiv q degree (left * right) =
      negacyclicProduct (coefficientEquiv q degree left)
        (coefficientEquiv q degree right) := by
  funext coefficient
  change (LatticeCrypto.vectorBackend (ZMod q) degree).coeff
      (LatticeCrypto.negacyclicMulPure
        (LatticeCrypto.vectorKernel (ZMod q) degree) left right) coefficient =
    LatticeCrypto.negacyclicConvCoeff
      ((LatticeCrypto.vectorBackend (ZMod q) degree).coeff left)
      ((LatticeCrypto.vectorBackend (ZMod q) degree).coeff right) coefficient
  exact LatticeCrypto.negacyclicMulPure_coeff
    (LatticeCrypto.vectorKernel (ZMod q) degree) left right coefficient

/-- The proof-facing `CommRing` multiplication is the same schoolbook negacyclic product. -/
theorem coefficientEquiv_semiring_mul (q degree : ℕ)
    (left right : RLWE.Rq q degree) :
    coefficientEquiv q degree
        (@Mul.mul (RLWE.Rq q degree)
          (LatticeCrypto.vectorNegacyclicRing_instCommRing
            (ZMod q) degree).toMul left right) =
      negacyclicProduct (coefficientEquiv q degree left)
        (coefficientEquiv q degree right) := by
  cases degree with
  | zero =>
      funext coefficient
      exact coefficient.elim0
  | succ degree =>
      exact coefficientEquiv_mul q (degree + 1) left right

/-- Embed a Boolean polynomial directly as zero-one coefficients modulo `q`. -/
def binaryCoefficients (q : ℕ) {degree : ℕ}
    (polynomial : Fin degree → Bool) : Coefficients q degree :=
  fun coefficient ↦ embedBit (polynomial coefficient)

@[simp]
theorem coefficientEquiv_embedBinaryPolynomial
    (q degree : ℕ) (polynomial : Fin degree → Bool) :
    coefficientEquiv q degree (embedBinaryPolynomial q degree polynomial) =
      binaryCoefficients q polynomial := by
  funext coefficient
  simp [coefficientEquiv, embedBinaryPolynomial, binaryCoefficients,
    LatticeCrypto.Poly.toPi, LatticeCrypto.Poly.ofPi, Vector.get]

/-! ## Exact Boolean-secret entropy data -/

/-- A rank-by-degree Boolean polynomial secret space has exactly `2^(rank*degree)` elements. -/
theorem card_ringBinarySecret (rank degree : ℕ) :
    Fintype.card (RingBinarySecret rank degree) = 2 ^ (rank * degree) := by
  change Fintype.card (Fin rank → Fin degree → Bool) = 2 ^ (rank * degree)
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  rw [← pow_mul]
  congr 1
  exact Nat.mul_comm degree rank

/-- Every concrete native ring secret has point probability exactly `2^(-rank*degree)`.

Equivalently, the uniform Boolean-coefficient secret has min-entropy exactly `rank*degree` bits;
the probability form avoids introducing an analytic logarithm solely for that statement. -/
theorem probOutput_sampleRingSecret (rank degree : ℕ)
    (secret : RingBinarySecret rank degree) :
    Pr[= secret | sampleRingSecret rank degree] =
      ((2 ^ (rank * degree) : ℕ) : ENNReal)⁻¹ := by
  rw [show sampleRingSecret rank degree = $ᵗ (RingBinarySecret rank degree) from rfl]
  rw [probOutput_uniformSample, card_ringBinarySecret]

/-- The complete explicit coefficient formula for module-LWE multiplication. -/
def negacyclicVecMul {q degree rank sampleCount : ℕ}
    (secret : RingBinarySecret rank degree)
    (challenge : Challenge q degree rank sampleCount) :
    Output q degree sampleCount :=
  fun sample ↦ ∑ row,
    negacyclicProduct (binaryCoefficients q (secret row)) (challenge row sample)

/-- The exact coefficient image of an arbitrary ring-error sampler. -/
def coefficientErrorSampler (q degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq q degree)) :
    ProbComp (Coefficients q degree) :=
  coefficientEquiv q degree <$> errorSampler

/-- Direct coefficient sampler for centered-binomial errors of width `eta`. -/
def centeredBinomialErrorSampler (q degree eta : ℕ) [NeZero q] :
    ProbComp (Coefficients q degree) := do
  let coins ← $ᵗ (RLWE.CenteredBinomial.CoinTable degree eta)
  return fun coefficient ↦
    (RLWE.CenteredBinomial.signedWeight (coins coefficient) : ZMod q)

/-- The ring centered-binomial sampler has exactly the direct independent coefficient law. -/
theorem coefficientErrorSampler_centeredBinomial
    (q degree eta : ℕ) [NeZero q] :
    coefficientErrorSampler q degree
        (RLWE.CenteredBinomial.sampler q degree eta) =
      centeredBinomialErrorSampler q degree eta := by
  simp [coefficientErrorSampler, RLWE.CenteredBinomial.sampler,
    centeredBinomialErrorSampler, RLWE.CenteredBinomial.errorFromCoins,
    coefficientEquiv, monad_norm]

/-- The ring-carrier binary-secret module-LWE problem before public coefficient transport. -/
noncomputable def ringProblem
    (q degree rank sampleCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree)) :
    LearningWithErrors.Problem
      (RLWE.ModuleSample q degree rank sampleCount)
      (RingBinarySecret rank degree)
      (RLWE.ModuleOutput q degree sampleCount) :=
  FormalProof4FHE.LWE.embeddedBatchProblem rank sampleCount
    (sampleRingSecret rank degree) (embedRingSecret q) errorSampler

/-- Binary-secret structured-LWE in coefficient form.

The public challenge, errors, noiseless products, and uniform endpoint are transported through
coefficient equivalences.  Subsequent theorems normalize these fields to independent uniform
coefficient matrices, explicit negacyclic convolution, and the exact coefficient error law. -/
noncomputable def problem
    (q degree rank sampleCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree)) :
    LearningWithErrors.Problem
      (Challenge q degree rank sampleCount)
      (RingBinarySecret rank degree)
      (Output q degree sampleCount) where
  sampleChallenge := challengeEquiv q degree rank sampleCount <$>
    ($ᵗ RLWE.ModuleSample q degree rank sampleCount)
  sampleSecret := sampleRingSecret rank degree
  sampleError := outputEquiv q degree sampleCount <$>
    ProbComp.sampleIID sampleCount errorSampler
  noiseless := fun secret challenge ↦
    outputEquiv q degree sampleCount
      (vecMul (embedRingSecret q secret)
        ((challengeEquiv q degree rank sampleCount).symm challenge))
  sampleUniform := outputEquiv q degree sampleCount <$>
    ($ᵗ RLWE.ModuleOutput q degree sampleCount)

/-- The transported noiseless map is the explicit sum of negacyclic convolutions of the binary
secret components with the corresponding public coefficient polynomials. -/
theorem problem_noiseless_eq_negacyclicVecMul
    (q degree rank sampleCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (secret : RingBinarySecret rank degree)
    (challenge : Challenge q degree rank sampleCount) :
    (problem q degree rank sampleCount errorSampler).noiseless secret challenge =
      negacyclicVecMul secret challenge := by
  change outputEquiv q degree sampleCount
      (vecMul (embedRingSecret q secret)
        ((challengeEquiv q degree rank sampleCount).symm challenge)) =
    negacyclicVecMul secret challenge
  apply funext
  intro sample
  change coefficientEquiv q degree
      ((vecMul (embedRingSecret q secret)
        ((challengeEquiv q degree rank sampleCount).symm challenge)) sample) =
    negacyclicVecMul secret challenge sample
  rw [Matrix.vecMul_apply_eq_sum]
  rw [coefficientEquiv_sum]
  unfold negacyclicVecMul
  apply Finset.sum_congr rfl
  intro row _
  calc
    _ = negacyclicProduct
          (coefficientEquiv q degree (embedRingSecret q secret row))
          (coefficientEquiv q degree
            ((challengeEquiv q degree rank sampleCount).symm challenge row sample)) :=
      coefficientEquiv_semiring_mul q degree _ _
    _ = negacyclicProduct (binaryCoefficients q (secret row))
          (challenge row sample) := by
      simp [challengeEquiv, embedRingSecret]

/-- The coefficient problem samples the hidden key uniformly from all rank-by-degree Boolean
coefficient arrays. -/
theorem problem_sampleSecret
    (q degree rank sampleCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree)) :
    (problem q degree rank sampleCount errorSampler).sampleSecret =
      $ᵗ (RingBinarySecret rank degree) := by
  rfl

/-- The public coefficient challenge is exactly uniform on its complete finite matrix space. -/
theorem problem_sampleChallenge_evalDist_eq_uniform
    (q degree rank sampleCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree)) :
    evalDist (problem q degree rank sampleCount errorSampler).sampleChallenge =
      evalDist ($ᵗ (Challenge q degree rank sampleCount)) := by
  exact evalDist_map_bijective_uniform_cross
    (α := RLWE.ModuleSample q degree rank sampleCount)
    (β := Challenge q degree rank sampleCount)
    (challengeEquiv q degree rank sampleCount)
    (challengeEquiv q degree rank sampleCount).bijective

/-- The coefficient-level ideal right-hand side is exactly uniform. -/
theorem problem_sampleUniform_evalDist_eq_uniform
    (q degree rank sampleCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree)) :
    evalDist (problem q degree rank sampleCount errorSampler).sampleUniform =
      evalDist ($ᵗ (Output q degree sampleCount)) := by
  exact evalDist_map_bijective_uniform_cross
    (α := RLWE.ModuleOutput q degree sampleCount)
    (β := Output q degree sampleCount)
    (outputEquiv q degree sampleCount)
    (outputEquiv q degree sampleCount).bijective

/-- Mapping an IID ring-error vector coefficientwise is distributionally identical to taking
independent samples from the coefficient image of the ring-error law. -/
theorem problem_sampleError_evalDist_eq_sampleIID
    (q degree rank sampleCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree)) :
    evalDist (problem q degree rank sampleCount errorSampler).sampleError =
      evalDist (ProbComp.sampleIID sampleCount
        (coefficientErrorSampler q degree errorSampler)) := by
  change evalDist (outputEquiv q degree sampleCount <$>
      ProbComp.sampleIID sampleCount errorSampler) = _
  apply evalDist_ext
  intro values
  rw [probOutput_map_equiv]
  simp only [ProbComp.sampleIID,
    FormalProof4FHE.FiniteProduct.probOutput_fin_mOfFn]
  apply Fintype.prod_congr
  intro sample
  change Pr[= (outputEquiv q degree sampleCount).symm values sample | errorSampler] =
    Pr[= values sample | coefficientEquiv q degree <$> errorSampler]
  rw [probOutput_map_equiv]
  rfl

/-- Preprocess a ring-carrier transcript coefficientwise for a structured-LWE adversary. -/
def reduction
    {q degree rank sampleCount : ℕ} [NeZero q]
    {errorSampler : ProbComp (RLWE.Rq q degree)}
    (adversary : LearningWithErrors.Adversary
      (problem q degree rank sampleCount errorSampler)) :
    LearningWithErrors.Adversary
      (ringProblem q degree rank sampleCount errorSampler) :=
  fun transcript ↦ adversary (transcriptEquiv q degree rank sampleCount transcript)

/-- Transport a ring-carrier distinguisher back to the public coefficient transcript. -/
def ofRingAdversary
    {q degree rank sampleCount : ℕ} [NeZero q]
    {errorSampler : ProbComp (RLWE.Rq q degree)}
    (adversary : LearningWithErrors.Adversary
      (ringProblem q degree rank sampleCount errorSampler)) :
    LearningWithErrors.Adversary
      (problem q degree rank sampleCount errorSampler) :=
  fun transcript ↦ adversary
    ((transcriptEquiv q degree rank sampleCount).symm transcript)

/-- Coefficient preprocessing after inverse preprocessing is the identity on ring adversaries. -/
@[simp]
theorem reduction_ofRingAdversary
    {q degree rank sampleCount : ℕ} [NeZero q]
    {errorSampler : ProbComp (RLWE.Rq q degree)}
    (adversary : LearningWithErrors.Adversary
      (ringProblem q degree rank sampleCount errorSampler)) :
    reduction (ofRingAdversary adversary) = adversary := by
  funext transcript
  simp [reduction, ofRingAdversary]

/-- Inverse preprocessing after coefficient preprocessing is the identity as well. -/
@[simp]
theorem ofRingAdversary_reduction
    {q degree rank sampleCount : ℕ} [NeZero q]
    {errorSampler : ProbComp (RLWE.Rq q degree)}
    (adversary : LearningWithErrors.Adversary
      (problem q degree rank sampleCount errorSampler)) :
    ofRingAdversary (reduction adversary) = adversary := by
  funext transcript
  simp [reduction, ofRingAdversary]

/-- Mapping a ring-carrier real transcript coefficientwise gives the coefficient problem's real
transcript computation exactly. -/
theorem map_distr_eq
    (q degree rank sampleCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree)) :
    (LearningWithErrors.distr (ringProblem q degree rank sampleCount errorSampler) >>=
      fun transcript ↦ pure (transcriptEquiv q degree rank sampleCount transcript)) =
      LearningWithErrors.distr (problem q degree rank sampleCount errorSampler) := by
  simp [LearningWithErrors.distr, ringProblem, problem, transcriptEquiv,
    FormalProof4FHE.LWE.embeddedBatchProblem, bind_assoc, monad_norm]

/-- Mapping the ring-carrier uniform transcript coefficientwise gives the coefficient problem's
uniform transcript computation exactly. -/
theorem map_uniformDistr_eq
    (q degree rank sampleCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree)) :
    (LearningWithErrors.uniformDistr
        (ringProblem q degree rank sampleCount errorSampler) >>=
      fun transcript ↦ pure (transcriptEquiv q degree rank sampleCount transcript)) =
      LearningWithErrors.uniformDistr
        (problem q degree rank sampleCount errorSampler) := by
  simp [LearningWithErrors.uniformDistr, ringProblem, problem, transcriptEquiv,
    FormalProof4FHE.LWE.embeddedBatchProblem, bind_assoc, monad_norm]

/-- Exact real-game equality under coefficient preprocessing. -/
theorem game0_evalDist_eq
    (q degree rank sampleCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (adversary : LearningWithErrors.Adversary
      (problem q degree rank sampleCount errorSampler)) :
    evalDist (LearningWithErrors.game0
        (problem q degree rank sampleCount errorSampler) adversary) =
      evalDist (LearningWithErrors.game0
        (ringProblem q degree rank sampleCount errorSampler)
        (reduction adversary)) := by
  rw [LearningWithErrors.game0, LearningWithErrors.game0]
  simp only [reduction]
  rw [← map_distr_eq q degree rank sampleCount errorSampler]
  simp [bind_assoc, monad_norm]

/-- Exact uniform-game equality under coefficient preprocessing. -/
theorem game1_evalDist_eq
    (q degree rank sampleCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (adversary : LearningWithErrors.Adversary
      (problem q degree rank sampleCount errorSampler)) :
    evalDist (LearningWithErrors.game1
        (problem q degree rank sampleCount errorSampler) adversary) =
      evalDist (LearningWithErrors.game1
        (ringProblem q degree rank sampleCount errorSampler)
        (reduction adversary)) := by
  rw [LearningWithErrors.game1, LearningWithErrors.game1]
  simp only [reduction]
  rw [← map_uniformDistr_eq q degree rank sampleCount errorSampler]
  simp [bind_assoc, monad_norm]

/-- Coefficient transport preserves every binary-secret structured-LWE advantage with no loss. -/
theorem advantage_eq_ring
    (q degree rank sampleCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (adversary : LearningWithErrors.Adversary
      (problem q degree rank sampleCount errorSampler)) :
    LearningWithErrors.advantage
        (problem q degree rank sampleCount errorSampler) adversary =
      LearningWithErrors.advantage
        (ringProblem q degree rank sampleCount errorSampler)
        (reduction adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage,
    FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (game0_evalDist_eq q degree rank sampleCount errorSampler adversary) true,
    evalDist_ext_iff.mp
      (game1_evalDist_eq q degree rank sampleCount errorSampler adversary) true]

/-- Pulling a ring adversary back to coefficients preserves its advantage exactly. -/
theorem advantage_ofRingAdversary_eq
    (q degree rank sampleCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (adversary : LearningWithErrors.Adversary
      (ringProblem q degree rank sampleCount errorSampler)) :
    LearningWithErrors.advantage
        (problem q degree rank sampleCount errorSampler)
        (ofRingAdversary adversary) =
      LearningWithErrors.advantage
        (ringProblem q degree rank sampleCount errorSampler) adversary := by
  rw [advantage_eq_ring]
  simp

/-- At rank one and the native BRK sample count, coefficient structured-LWE is exactly the
explicit binary-secret RLWE game, including both endpoints and every distinguisher advantage. -/
theorem advantage_eq_binarySecretRLWE
    (q degree tgswLevels lweDimension : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (adversary : LearningWithErrors.Adversary
      (problem q degree 1
        (lweDimension * TGSW.rowCount 1 tgswLevels) errorSampler)) :
    LearningWithErrors.advantage
        (problem q degree 1
          (lweDimension * TGSW.rowCount 1 tgswLevels) errorSampler) adversary =
      LearningWithErrors.advantage
        (Native.BootstrapCutSecurity.binarySecretRLWEProblem q degree
          (lweDimension * TGSW.rowCount 1 tgswLevels) errorSampler)
        (reduction adversary) := by
  rw [advantage_eq_ring]
  exact Native.BootstrapCutSecurity.batchModuleLweProblem_one_advantage_eq_binarySecretRLWE
      q degree tgswLevels lweDimension errorSampler (reduction adversary)

end

end FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE
