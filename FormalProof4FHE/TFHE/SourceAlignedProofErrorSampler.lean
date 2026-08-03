/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.CenteredBinomialMoment
import FormalProof4FHE.TFHE.SourceAlignedBRKKSKJointLaw
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Finite proof-aligned error sampler

This file defines the finite scalar error law used by the source-aligned lvl02 candidate.  One
integer error is the sum of two independent parts:

* 255 independent Rademacher signs, each scaled by `2^38`; and
* a 32-bit unit-resolution dither, written as the difference of two independent uniform binary
  integers.

The dither makes the error uniform modulo `2^32`, avoiding the divisibility leak of a naively
scaled centered-binomial law.  The complete sampler uses only uniform bits and has an explicit
subgaussian proxy strictly below `2^84 = (2^42)^2`.
-/

open OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.SourceAlignedProofErrorSampler

noncomputable section

open FormalProof4FHE.BoundedMoment

/-- Number of equal-weight Rademacher signs in the coarse component. -/
def coarseCount : ℕ := 255

/-- Base-two logarithm of the coarse sign weight. -/
def coarseScaleLog : ℕ := 38

/-- Number of binary digits in each side of the fine dither. -/
def ditherBits : ℕ := 32

/-- Coarse and fine uniform coins for one scalar error. -/
abbrev CoarseCoins := Fin coarseCount → Bool
abbrev DitherCoins := Fin ditherBits → Bool × Bool
abbrev ScalarCoins := CoarseCoins × DitherCoins

/-- A fair bit interpreted as a Rademacher sign. -/
def rademacherInteger (bit : Bool) : ℤ :=
  if bit then 1 else -1

/-- Real interpretation of one Rademacher sign. -/
def rademacherReal (bit : Bool) : ℝ :=
  (rademacherInteger bit : ℝ)

/-- Integer weight of one fine binary digit. -/
def ditherWeight (index : Fin ditherBits) : ℕ :=
  2 ^ index.val

/-- The signed coarse component. -/
def coarseInteger (coins : CoarseCoins) : ℤ :=
  (2 ^ coarseScaleLog : ℤ) * ∑ index, rademacherInteger (coins index)

/-- Difference of two independently uniform 32-bit nonnegative integers. -/
def ditherInteger (coins : DitherCoins) : ℤ :=
  ∑ index, (ditherWeight index : ℤ) *
    FormalProof4FHE.RLWE.CenteredBinomial.pairDifference (coins index)

/-- Exact signed integer emitted by one scalar coin block. -/
def decodeInteger (coins : ScalarCoins) : ℤ :=
  coarseInteger coins.1 + ditherInteger coins.2

/-- Real lift used by the finite MGF certificate. -/
def decodeReal (coins : ScalarCoins) : ℝ :=
  (decodeInteger coins : ℝ)

/-- Real lift of the coarse component alone. -/
def coarseReal (coins : CoarseCoins) : ℝ :=
  (coarseInteger coins : ℝ)

/-- Real lift of the fine dither alone. -/
def ditherReal (coins : DitherCoins) : ℝ :=
  (ditherInteger coins : ℝ)

/-- Constant weights of the coarse Rademacher block. -/
def coarseWeights : Fin coarseCount → ℝ :=
  fun _ ↦ (2 : ℝ) ^ coarseScaleLog

/-- Binary place-value weights of the fine dither. -/
def ditherWeights : Fin ditherBits → ℝ :=
  fun index ↦ (2 : ℝ) ^ index.val

/-- MGF proxy supplied by the coarse block. -/
def coarseProxy : ℝ :=
  ∑ index : Fin coarseCount, coarseWeights index ^ 2

/-- Convenient MGF proxy supplied by the fine block. -/
def ditherProxy : ℝ :=
  ∑ index : Fin ditherBits, ditherWeights index ^ 2

/-- Additive scalar proxy proved for the complete finite sampler. -/
def scalarProxy : ℝ :=
  coarseProxy + ditherProxy

/-- Modular encoding used by RLWE and aligned-KSK error samplers. -/
def decodeMod (q : ℕ) (coins : ScalarCoins) : ZMod q :=
  (decodeInteger coins : ZMod q)

/-- Exact uniform-coin scalar sampler. -/
def scalarCoinSampler : ProbComp ScalarCoins :=
  do
    let coarse ← $ᵗ CoarseCoins
    let dither ← $ᵗ DitherCoins
    return (coarse, dither)

/-- Exact modular scalar sampler. -/
def scalarSampler (q : ℕ) [NeZero q] : ProbComp (ZMod q) :=
  decodeMod q <$> scalarCoinSampler

/-! ## Decoder normal forms -/

/-- The integer coarse decoder is the corresponding real weighted sum. -/
theorem coarseReal_eq_weightedSum (coins : CoarseCoins) :
    coarseReal coins =
      FormalProof4FHE.BoundedMoment.weightedSum
        coarseWeights rademacherReal coins := by
  unfold coarseReal coarseInteger FormalProof4FHE.BoundedMoment.weightedSum
    coarseWeights rademacherReal
  push_cast
  rw [Finset.mul_sum]

/-- The integer dither decoder is the corresponding real weighted sum. -/
theorem ditherReal_eq_weightedSum (coins : DitherCoins) :
    ditherReal coins =
      FormalProof4FHE.BoundedMoment.weightedSum ditherWeights
        FormalProof4FHE.RLWE.CenteredBinomial.pairDifferenceReal coins := by
  unfold ditherReal ditherInteger FormalProof4FHE.BoundedMoment.weightedSum
    ditherWeights ditherWeight
    FormalProof4FHE.RLWE.CenteredBinomial.pairDifferenceReal
  push_cast
  apply Finset.sum_congr rfl
  intro index _
  norm_num

/-- The complete real decoder is the sum of its independent components. -/
theorem decodeReal_eq_add (coins : ScalarCoins) :
    decodeReal coins = coarseReal coins.1 + ditherReal coins.2 := by
  simp [decodeReal, decodeInteger, coarseReal, ditherReal]

/-- Exact coarse proxy in the selected integer scale. -/
theorem coarseProxy_eq :
    coarseProxy = (255 : ℝ) * 2 ^ 76 := by
  norm_num [coarseProxy, coarseWeights, coarseCount, coarseScaleLog]

/-- Exact geometric-series proxy of the 32-bit dither. -/
theorem ditherProxy_eq :
    ditherProxy = ((2 : ℝ) ^ 64 - 1) / 3 := by
  have hTerm (index : ℕ) :
      ((2 : ℝ) ^ index) ^ 2 = (4 : ℝ) ^ index := by
    calc
      ((2 : ℝ) ^ index) ^ 2 = (2 : ℝ) ^ (index * 2) := by
        rw [pow_mul]
      _ = (2 : ℝ) ^ (2 * index) := by rw [Nat.mul_comm]
      _ = ((2 : ℝ) ^ 2) ^ index := by rw [pow_mul]
      _ = (4 : ℝ) ^ index := by norm_num
  unfold ditherProxy ditherWeights
  change (∑ index : Fin 32, ((2 : ℝ) ^ index.val) ^ 2) =
    ((2 : ℝ) ^ 64 - 1) / 3
  rw [Finset.sum_fin_eq_sum_range]
  simp_rw [hTerm]
  have hRange :
      (∑ index ∈ Finset.range 32,
          if h : index < 32 then (4 : ℝ) ^ index else 0) =
        ∑ index ∈ Finset.range 32, (4 : ℝ) ^ index := by
    apply Finset.sum_congr rfl
    intro index hIndex
    simp [Finset.mem_range.mp hIndex]
  rw [hRange, geom_sum_eq (by norm_num : (4 : ℝ) ≠ 1)]
  norm_num

/-- The complete finite law fits beneath the historical `2^84` evaluator-noise proxy. -/
theorem scalarProxy_le : scalarProxy ≤ (2 : ℝ) ^ 84 := by
  rw [scalarProxy, coarseProxy_eq, ditherProxy_eq]
  norm_num

/-! ## One-coin exponential moments -/

/-- The Rademacher exponential moment is `cosh`. -/
theorem expectation_exp_rademacher (rate : ℝ) :
    expectation ($ᵗ Bool)
        (fun bit ↦ Real.exp (rate * rademacherReal bit)) =
      Real.cosh rate := by
  classical
  unfold expectation rademacherReal rademacherInteger
  rw [Real.cosh_eq]
  simp [probOutput_uniformSample, Fintype.card_bool]
  ring

/-- One Rademacher sign is subgaussian with proxy one. -/
theorem expectation_exp_rademacher_le (rate : ℝ) :
    expectation ($ᵗ Bool)
        (fun bit ↦ Real.exp (rate * rademacherReal bit)) ≤
      Real.exp (rate ^ 2 / 2) := by
  rw [expectation_exp_rademacher]
  exact Real.cosh_le_exp_half_sq rate

/-- Exact exponential moment of one fair bit-pair difference. -/
theorem expectation_exp_pairDifference (rate : ℝ) :
    expectation ($ᵗ (Bool × Bool))
        (fun coin ↦ Real.exp
          (rate * FormalProof4FHE.RLWE.CenteredBinomial.pairDifferenceReal coin)) =
      (1 + Real.cosh rate) / 2 := by
  classical
  unfold expectation FormalProof4FHE.RLWE.CenteredBinomial.pairDifferenceReal
    FormalProof4FHE.RLWE.CenteredBinomial.pairDifference
  rw [Real.cosh_eq]
  simp [probOutput_uniformSample, Fintype.card_prod, Fintype.card_bool,
    Fintype.sum_prod_type]
  ring

/-- A fair bit-pair difference has the sharp subgaussian proxy `1 / 2`.  Equivalently, its
exponential moment is at most `exp(rate² / 4)`. -/
theorem expectation_exp_pairDifference_le_sharp (rate : ℝ) :
    expectation ($ᵗ (Bool × Bool))
        (fun coin ↦ Real.exp
          (rate * FormalProof4FHE.RLWE.CenteredBinomial.pairDifferenceReal coin)) ≤
      Real.exp (rate ^ 2 / 4) := by
  rw [expectation_exp_pairDifference]
  have hhalf :
      (1 + Real.cosh rate) / 2 = Real.cosh (rate / 2) ^ 2 := by
    have htwo := Real.cosh_two_mul (rate / 2)
    have hsq := Real.cosh_sq_sub_sinh_sq (rate / 2)
    rw [show 2 * (rate / 2) = rate by ring] at htwo
    nlinarith
  rw [hhalf]
  have hcosh := Real.cosh_le_exp_half_sq (rate / 2)
  have hcosh_nonneg : 0 ≤ Real.cosh (rate / 2) := (Real.cosh_pos _).le
  have hexp_nonneg : 0 ≤ Real.exp ((rate / 2) ^ 2 / 2) := (Real.exp_pos _).le
  calc
    Real.cosh (rate / 2) ^ 2 ≤
        Real.exp ((rate / 2) ^ 2 / 2) ^ 2 := by nlinarith
    _ = Real.exp (rate ^ 2 / 4) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring

/-- A bit-pair difference is subgaussian with the convenient proxy one.  Its sharp proxy is
`1/2`, but the looser value keeps the finite proof elementary and still fits the lvl02 budget. -/
theorem expectation_exp_pairDifference_le (rate : ℝ) :
    expectation ($ᵗ (Bool × Bool))
        (fun coin ↦ Real.exp
          (rate * FormalProof4FHE.RLWE.CenteredBinomial.pairDifferenceReal coin)) ≤
      Real.exp (rate ^ 2 / 2) := by
  rw [expectation_exp_pairDifference]
  calc
    (1 + Real.cosh rate) / 2 ≤ Real.cosh rate := by
      linarith [Real.one_le_cosh rate]
    _ ≤ Real.exp (rate ^ 2 / 2) := Real.cosh_le_exp_half_sq rate

/-! ## Finite-product MGF calculus -/

/-- An exponential observable has nonnegative finite expectation. -/
theorem expectation_exp_nonneg {A : Type} [Fintype A]
    (sampler : ProbComp A) (observable : A → ℝ) :
    0 ≤ expectation sampler (fun value ↦ Real.exp (observable value)) := by
  classical
  unfold expectation
  exact Finset.sum_nonneg fun value _ ↦
    mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos (observable value)).le

/-- Expectation of a product of two observables under independent finite samplers factors. -/
theorem expectation_independent_pair_mul
    {A B : Type} [Fintype A] [Fintype B]
    (left : ProbComp A) (right : ProbComp B)
    (leftObservable : A → ℝ) (rightObservable : B → ℝ) :
    expectation (do
        let leftValue ← left
        let rightValue ← right
        return (leftValue, rightValue))
      (fun pair ↦ leftObservable pair.1 * rightObservable pair.2) =
      expectation left leftObservable * expectation right rightObservable := by
  classical
  rw [expectation_bind]
  calc
    (∑ leftValue,
        Pr[= leftValue | left].toReal *
          expectation
            (right >>= fun rightValue ↦ pure (leftValue, rightValue))
            (fun pair ↦ leftObservable pair.1 * rightObservable pair.2)) =
      ∑ leftValue,
        Pr[= leftValue | left].toReal *
          (leftObservable leftValue * expectation right rightObservable) := by
            apply Finset.sum_congr rfl
            intro leftValue _
            congr 1
            calc
              expectation
                  (right >>= fun rightValue ↦ pure (leftValue, rightValue))
                  (fun pair ↦
                    leftObservable pair.1 * rightObservable pair.2) =
                expectation right (fun rightValue ↦
                  leftObservable leftValue * rightObservable rightValue) := by
                    rw [expectation_bind]
                    apply Finset.sum_congr rfl
                    intro rightValue _
                    rw [expectation_pure]
              _ = leftObservable leftValue *
                  expectation right rightObservable :=
                    expectation_const_mul right _ _
    _ = expectation left
          (fun leftValue ↦
            leftObservable leftValue * expectation right rightObservable) := rfl
    _ = expectation left
          (fun leftValue ↦
            expectation right rightObservable * leftObservable leftValue) := by
              apply congrArg (expectation left)
              funext leftValue
              ring
    _ = expectation right rightObservable *
          expectation left leftObservable :=
            expectation_const_mul left _ _
    _ = expectation left leftObservable *
          expectation right rightObservable := by ring

/-- Scalar subgaussian bounds tensor over an IID finite product.  The conclusion is stated for
arbitrary real weights because evaluator tails test every real linear functional. -/
theorem expectation_exp_weightedSum_le
    {A : Type} [Fintype A]
    (sampler : ProbComp A) (lift : A → ℝ) (proxy : ℝ)
    (hScalar : ∀ rate,
      expectation sampler (fun value ↦ Real.exp (rate * lift value)) ≤
        Real.exp (rate ^ 2 * proxy / 2)) :
    ∀ (count : ℕ) (weights : Fin count → ℝ) (rate : ℝ),
      expectation (ProbComp.sampleIID count sampler)
          (fun values ↦ Real.exp
            (rate * FormalProof4FHE.BoundedMoment.weightedSum weights lift values)) ≤
        Real.exp
          (rate ^ 2 *
            (proxy * ∑ index : Fin count, weights index ^ 2) / 2) := by
  intro count
  induction count with
  | zero =>
      intro weights rate
      simp [ProbComp.sampleIID, Fin.mOfFn,
        FormalProof4FHE.BoundedMoment.weightedSum, expectation_pure]
  | succ count inductionHypothesis =>
      intro weights rate
      let tailWeights : Fin count → ℝ := fun index ↦ weights index.succ
      let tailSampler : ProbComp (Fin count → A) :=
        ProbComp.sampleIID count sampler
      let tailMoment : ℝ := expectation tailSampler
        (fun values ↦ Real.exp
          (rate * FormalProof4FHE.BoundedMoment.weightedSum
            tailWeights lift values))
      have hInner (head : A) :
          expectation
              (Fin.mOfFn count (fun _ ↦ sampler) >>=
                fun tail ↦ pure (Fin.cons head tail))
              (fun values ↦ Real.exp
                (rate * FormalProof4FHE.BoundedMoment.weightedSum
                  weights lift values)) =
            Real.exp (rate * weights 0 * lift head) * tailMoment := by
        calc
          expectation
              (Fin.mOfFn count (fun _ ↦ sampler) >>=
                fun tail ↦ pure (Fin.cons head tail))
              (fun values ↦ Real.exp
                (rate * FormalProof4FHE.BoundedMoment.weightedSum
                  weights lift values)) =
            expectation tailSampler
              (fun tail ↦ Real.exp
                (rate * FormalProof4FHE.BoundedMoment.weightedSum
                  weights lift (Fin.cons head tail))) := by
              unfold tailSampler ProbComp.sampleIID
              rw [expectation_bind]
              apply Finset.sum_congr rfl
              intro tail _
              rw [expectation_pure]
          _ = expectation tailSampler
              (fun tail ↦ Real.exp (rate * weights 0 * lift head) *
                Real.exp
                  (rate * FormalProof4FHE.BoundedMoment.weightedSum
                    tailWeights lift tail)) := by
              apply congrArg (expectation tailSampler)
              funext tail
              rw [FormalProof4FHE.BoundedMoment.weightedSum_cons]
              rw [show rate *
                    (weights 0 * lift head +
                      FormalProof4FHE.BoundedMoment.weightedSum
                        tailWeights lift tail) =
                    rate * weights 0 * lift head +
                      rate * FormalProof4FHE.BoundedMoment.weightedSum
                        tailWeights lift tail by ring]
              exact Real.exp_add _ _
          _ = Real.exp (rate * weights 0 * lift head) * tailMoment := by
              exact expectation_const_mul tailSampler
                (Real.exp (rate * weights 0 * lift head)) _
      unfold ProbComp.sampleIID
      simp only [Fin.mOfFn]
      rw [expectation_bind]
      calc
        (∑ head,
            Pr[= head | sampler].toReal *
              expectation
                (Fin.mOfFn count (fun _ ↦ sampler) >>=
                  fun tail ↦ pure (Fin.cons head tail))
                (fun values ↦ Real.exp
                  (rate * FormalProof4FHE.BoundedMoment.weightedSum
                    weights lift values))) =
            expectation sampler
              (fun head ↦ tailMoment *
                Real.exp (rate * weights 0 * lift head)) := by
              apply Finset.sum_congr rfl
              intro head _
              rw [hInner]
              ring
        _ = tailMoment * expectation sampler
              (fun head ↦ Real.exp (rate * weights 0 * lift head)) :=
            expectation_const_mul sampler tailMoment _
        _ ≤ Real.exp
              (rate ^ 2 *
                (proxy * ∑ index : Fin count, tailWeights index ^ 2) / 2) *
            expectation sampler
              (fun head ↦ Real.exp (rate * weights 0 * lift head)) := by
              apply mul_le_mul_of_nonneg_right
                (inductionHypothesis tailWeights rate)
              exact expectation_exp_nonneg sampler _
        _ ≤ Real.exp
              (rate ^ 2 *
                (proxy * ∑ index : Fin count, tailWeights index ^ 2) / 2) *
            Real.exp ((rate * weights 0) ^ 2 * proxy / 2) := by
              apply mul_le_mul_of_nonneg_left
              · exact hScalar (rate * weights 0)
              · exact (Real.exp_pos _).le
        _ = Real.exp
              (rate ^ 2 *
                (proxy * ∑ index : Fin (count + 1), weights index ^ 2) / 2) := by
              rw [← Real.exp_add]
              congr 1
              rw [Fin.sum_univ_succ]
              change rate ^ 2 *
                    (proxy * ∑ index : Fin count, weights index.succ ^ 2) / 2 +
                  (rate * weights 0) ^ 2 * proxy / 2 =
                rate ^ 2 *
                  (proxy *
                    (weights 0 ^ 2 +
                      ∑ index : Fin count, weights index.succ ^ 2)) / 2
              ring

/-! ## Component and scalar certificates -/

/-- MGF certificate for the complete 255-sign coarse block. -/
theorem expectation_exp_coarseReal_le (rate : ℝ) :
    expectation ($ᵗ CoarseCoins)
        (fun coins ↦ Real.exp (rate * coarseReal coins)) ≤
      Real.exp (rate ^ 2 * coarseProxy / 2) := by
  have hIID := expectation_exp_weightedSum_le
    ($ᵗ Bool) rademacherReal 1 (by
      intro scalarRate
      simpa using expectation_exp_rademacher_le scalarRate)
      coarseCount coarseWeights rate
  have hDist := FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
    (alpha := Bool) coarseCount
  calc
    expectation ($ᵗ CoarseCoins)
        (fun coins ↦ Real.exp (rate * coarseReal coins)) =
      expectation ($ᵗ CoarseCoins)
        (fun coins ↦ Real.exp
          (rate * FormalProof4FHE.BoundedMoment.weightedSum
            coarseWeights rademacherReal coins)) := by
              apply congrArg (expectation ($ᵗ CoarseCoins))
              funext coins
              rw [coarseReal_eq_weightedSum]
    _ = expectation (ProbComp.sampleIID coarseCount ($ᵗ Bool))
        (fun coins ↦ Real.exp
          (rate * FormalProof4FHE.BoundedMoment.weightedSum
            coarseWeights rademacherReal coins)) := by
              exact (expectation_congr_evalDist hDist _).symm
    _ ≤ Real.exp (rate ^ 2 * coarseProxy / 2) := by
      simpa [coarseProxy] using hIID

/-- MGF certificate for the complete 32-bit fine dither. -/
theorem expectation_exp_ditherReal_le (rate : ℝ) :
    expectation ($ᵗ DitherCoins)
        (fun coins ↦ Real.exp (rate * ditherReal coins)) ≤
      Real.exp (rate ^ 2 * ditherProxy / 2) := by
  have hIID := expectation_exp_weightedSum_le
    ($ᵗ (Bool × Bool))
      FormalProof4FHE.RLWE.CenteredBinomial.pairDifferenceReal 1
      (by
        intro scalarRate
        simpa using expectation_exp_pairDifference_le scalarRate)
      ditherBits ditherWeights rate
  have hDist := FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
    (alpha := Bool × Bool) ditherBits
  calc
    expectation ($ᵗ DitherCoins)
        (fun coins ↦ Real.exp (rate * ditherReal coins)) =
      expectation ($ᵗ DitherCoins)
        (fun coins ↦ Real.exp
          (rate * FormalProof4FHE.BoundedMoment.weightedSum ditherWeights
            FormalProof4FHE.RLWE.CenteredBinomial.pairDifferenceReal coins)) := by
              apply congrArg (expectation ($ᵗ DitherCoins))
              funext coins
              rw [ditherReal_eq_weightedSum]
    _ = expectation (ProbComp.sampleIID ditherBits ($ᵗ (Bool × Bool)))
        (fun coins ↦ Real.exp
          (rate * FormalProof4FHE.BoundedMoment.weightedSum ditherWeights
            FormalProof4FHE.RLWE.CenteredBinomial.pairDifferenceReal coins)) := by
              exact (expectation_congr_evalDist hDist _).symm
    _ ≤ Real.exp (rate ^ 2 * ditherProxy / 2) := by
      simpa [ditherProxy] using hIID

/-- The complete scalar MGF factors into its two independent finite components. -/
theorem expectation_exp_decodeReal_eq_mul (rate : ℝ) :
    expectation scalarCoinSampler
        (fun coins ↦ Real.exp (rate * decodeReal coins)) =
      expectation ($ᵗ CoarseCoins)
          (fun coins ↦ Real.exp (rate * coarseReal coins)) *
        expectation ($ᵗ DitherCoins)
          (fun coins ↦ Real.exp (rate * ditherReal coins)) := by
  calc
    expectation scalarCoinSampler
        (fun coins ↦ Real.exp (rate * decodeReal coins)) =
      expectation scalarCoinSampler
        (fun coins ↦
          Real.exp (rate * coarseReal coins.1) *
            Real.exp (rate * ditherReal coins.2)) := by
              apply congrArg (expectation scalarCoinSampler)
              funext coins
              rw [decodeReal_eq_add]
              rw [show rate * (coarseReal coins.1 + ditherReal coins.2) =
                    rate * coarseReal coins.1 +
                      rate * ditherReal coins.2 by ring]
              exact Real.exp_add _ _
    _ = expectation ($ᵗ CoarseCoins)
            (fun coarse ↦ Real.exp (rate * coarseReal coarse)) *
          expectation ($ᵗ DitherCoins)
            (fun dither ↦ Real.exp (rate * ditherReal dither)) := by
          unfold scalarCoinSampler
          exact expectation_independent_pair_mul
            (left := ($ᵗ CoarseCoins))
            (right := ($ᵗ DitherCoins))
            (leftObservable :=
              fun coarse ↦ Real.exp (rate * coarseReal coarse))
            (rightObservable :=
              fun dither ↦ Real.exp (rate * ditherReal dither))

/-- Exact scalar finite sampler MGF certificate with its additive proxy. -/
theorem expectation_exp_decodeReal_le (rate : ℝ) :
    expectation scalarCoinSampler
        (fun coins ↦ Real.exp (rate * decodeReal coins)) ≤
      Real.exp (rate ^ 2 * scalarProxy / 2) := by
  rw [expectation_exp_decodeReal_eq_mul]
  calc
    expectation ($ᵗ CoarseCoins)
          (fun coins ↦ Real.exp (rate * coarseReal coins)) *
        expectation ($ᵗ DitherCoins)
          (fun coins ↦ Real.exp (rate * ditherReal coins)) ≤
      Real.exp (rate ^ 2 * coarseProxy / 2) *
        expectation ($ᵗ DitherCoins)
          (fun coins ↦ Real.exp (rate * ditherReal coins)) := by
            apply mul_le_mul_of_nonneg_right
              (expectation_exp_coarseReal_le rate)
            exact expectation_exp_nonneg _ _
    _ ≤ Real.exp (rate ^ 2 * coarseProxy / 2) *
        Real.exp (rate ^ 2 * ditherProxy / 2) := by
            apply mul_le_mul_of_nonneg_left
              (expectation_exp_ditherReal_le rate)
            exact (Real.exp_pos _).le
    _ = Real.exp (rate ^ 2 * scalarProxy / 2) := by
      rw [← Real.exp_add]
      congr 1
      unfold scalarProxy
      ring

/-- Public scalar certificate at the implementation's historical `2^42` standard-deviation
proxy. -/
theorem expectation_exp_decodeReal_le_two_pow (rate : ℝ) :
    expectation scalarCoinSampler
        (fun coins ↦ Real.exp (rate * decodeReal coins)) ≤
      Real.exp (rate ^ 2 * (2 : ℝ) ^ 84 / 2) := by
  calc
    expectation scalarCoinSampler
        (fun coins ↦ Real.exp (rate * decodeReal coins)) ≤
      Real.exp (rate ^ 2 * scalarProxy / 2) :=
        expectation_exp_decodeReal_le rate
    _ ≤ Real.exp (rate ^ 2 * (2 : ℝ) ^ 84 / 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [scalarProxy_le, sq_nonneg rate]

/-! ## IID vector certificate for evaluator tails -/

/-- Complete coin tape for a vector of independent proof-aligned errors. -/
abbrev VectorCoins (count : ℕ) := Fin count → ScalarCoins

/-- Coordinatewise independent finite error sampler. -/
def vectorCoinSampler (count : ℕ) : ProbComp (VectorCoins count) :=
  ProbComp.sampleIID count scalarCoinSampler

/-- Real vector decoded from a complete vector coin tape. -/
def noiseVector (count : ℕ) (coins : VectorCoins count) : Fin count → ℝ :=
  fun index ↦ decodeReal (coins index)

/-- Spherical covariance proxy advertised to the evaluator-tail theorem. -/
def sphericalCovariance (count : ℕ) : Matrix (Fin count) (Fin count) ℝ :=
  ((2 : ℝ) ^ 84) • (1 : Matrix (Fin count) (Fin count) ℝ)

/-- Energy normal form for the advertised spherical covariance proxy. -/
theorem covarianceEnergy_spherical (count : ℕ) (factor : Fin count → ℝ) :
    SourceAlignedBRKKSKJointLaw.NativeCompiler.EvaluatorTail.covarianceEnergy
        (sphericalCovariance count) factor =
      (2 : ℝ) ^ 84 * ∑ index : Fin count, factor index ^ 2 := by
  unfold SourceAlignedBRKKSKJointLaw.NativeCompiler.EvaluatorTail.covarianceEnergy
    sphericalCovariance
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
  simp [dotProduct, pow_two, Finset.mul_sum]

/-- Every real linear functional of the decoded IID vector has the spherical MGF bound. -/
theorem expectation_exp_dotProduct_noiseVector_le
    (count : ℕ) (factor : Fin count → ℝ) (rate : ℝ) :
    expectation (vectorCoinSampler count)
        (fun coins ↦ Real.exp
          (rate * dotProduct factor (noiseVector count coins))) ≤
      Real.exp
        (rate ^ 2 *
          SourceAlignedBRKKSKJointLaw.NativeCompiler.EvaluatorTail.covarianceEnergy
            (sphericalCovariance count) factor / 2) := by
  have hMGF := expectation_exp_weightedSum_le
    scalarCoinSampler decodeReal ((2 : ℝ) ^ 84)
      expectation_exp_decodeReal_le_two_pow count factor rate
  rw [covarianceEnergy_spherical]
  simpa [vectorCoinSampler, noiseVector,
    FormalProof4FHE.BoundedMoment.weightedSum, dotProduct] using hMGF

/-- Concrete finite `EvaluatorTail.Certificate` for any family of residual vectors. -/
theorem sphericalCertificate (count : ℕ) {Factor : Type}
    (residual : Factor → Fin count → ℝ) :
    SourceAlignedBRKKSKJointLaw.NativeCompiler.EvaluatorTail.Certificate
      (VectorCoins count) (Fin count) Factor
      (vectorCoinSampler count) (noiseVector count) residual
      (sphericalCovariance count) := by
  constructor
  · intro factor
    rw [covarianceEnergy_spherical]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun index _ ↦
      sq_nonneg (residual factor index))
  · intro factor rate
    exact expectation_exp_dotProduct_noiseVector_le
      count (residual factor) rate

end

end FormalProof4FHE.TFHE.SourceAlignedProofErrorSampler
