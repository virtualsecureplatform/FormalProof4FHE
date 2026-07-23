/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.BoundedMoment
import FormalProof4FHE.RLWE.CenteredBinomialCharacteristicTwo
import LatticeCrypto.Ring.Norms

/-!
# Exact Moments of Centered-Binomial Coefficients

One centered-binomial coefficient of width `eta` is a sum of `eta` independent differences of
two fair bits.  This file proves in the finite `ProbComp` model that its mean is zero and its
second moment is exactly `eta / 2`.  It then transfers the identity to the modular coefficient
sampler whenever the centered representative cannot wrap.
-/

open OracleComp
open scoped BigOperators

namespace FormalProof4FHE.RLWE.CenteredBinomial

noncomputable section

open FormalProof4FHE.BoundedMoment

/-- Integer contribution of one pair of centered-binomial coins. -/
def pairDifference (coin : Bool × Bool) : ℤ :=
  (if coin.1 then 1 else 0) - (if coin.2 then 1 else 0)

/-- Real view of one pair contribution. -/
def pairDifferenceReal (coin : Bool × Bool) : ℝ :=
  (pairDifference coin : ℝ)

/-- Real view of the unreduced centered-binomial coefficient. -/
def signedWeightReal {eta : ℕ} (coins : CoinRow eta) : ℝ :=
  (signedWeight coins : ℝ)

/-- Adding the head coin pair adds its signed contribution. -/
theorem signedWeight_cons {eta : ℕ} (head : Bool × Bool)
    (tail : CoinRow eta) :
    signedWeight (Fin.cons head tail) =
      pairDifference head + signedWeight tail := by
  unfold signedWeight positiveWeight negativeWeight pairDifference
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  split <;> split <;> simp <;> ring

/-- Real form of `signedWeight_cons`. -/
theorem signedWeightReal_cons {eta : ℕ} (head : Bool × Bool)
    (tail : CoinRow eta) :
    signedWeightReal (Fin.cons head tail) =
      pairDifferenceReal head + signedWeightReal tail := by
  simp [signedWeightReal, pairDifferenceReal, signedWeight_cons]

/-- One fair bit-pair difference is centered. -/
theorem expectation_pairDifferenceReal :
    expectation ($ᵗ (Bool × Bool)) pairDifferenceReal = 0 := by
  classical
  unfold expectation pairDifferenceReal pairDifference
  simp [probOutput_uniformSample, Fintype.card_prod, Fintype.card_bool,
    Fintype.sum_prod_type]

/-- One fair bit-pair difference has second moment `1/2`. -/
theorem expectation_sq_pairDifferenceReal :
    expectation ($ᵗ (Bool × Bool))
        (fun coin ↦ pairDifferenceReal coin ^ 2) = 1 / 2 := by
  classical
  unfold expectation pairDifferenceReal pairDifference
  simp [probOutput_uniformSample, Fintype.card_prod, Fintype.card_bool,
    Fintype.sum_prod_type]
  norm_num

/-- Sample all coin pairs independently. -/
def coinRowSampler (eta : ℕ) : ProbComp (CoinRow eta) :=
  ProbComp.sampleIID eta ($ᵗ (Bool × Bool))

/-- Independent fair coin pairs give a centered signed weight. -/
theorem mean_coinRowSampler_signedWeightReal (eta : ℕ) :
    mean (coinRowSampler eta) signedWeightReal = 0 := by
  induction eta with
  | zero =>
      simp [coinRowSampler, ProbComp.sampleIID, Fin.mOfFn, mean,
        signedWeightReal, signedWeight, positiveWeight, negativeWeight,
        expectation_pure]
  | succ eta inductionHypothesis =>
      rw [mean]
      unfold coinRowSampler ProbComp.sampleIID
      simp only [Fin.mOfFn]
      rw [expectation_bind]
      have hInner (head : Bool × Bool) :
          expectation
              (Fin.mOfFn eta (fun _ ↦ $ᵗ (Bool × Bool)) >>=
                fun tail ↦ pure (Fin.cons head tail))
              signedWeightReal = pairDifferenceReal head := by
        calc
          expectation
              (Fin.mOfFn eta (fun _ ↦ $ᵗ (Bool × Bool)) >>=
                fun tail ↦ pure (Fin.cons head tail))
              signedWeightReal =
            expectation (Fin.mOfFn eta fun _ ↦ $ᵗ (Bool × Bool))
              (fun tail ↦ signedWeightReal (Fin.cons head tail)) := by
                  rw [expectation_bind]
                  apply Finset.sum_congr rfl
                  intro tail _
                  rw [expectation_pure]
          _ = expectation (Fin.mOfFn eta fun _ ↦ $ᵗ (Bool × Bool))
              (fun tail ↦
                pairDifferenceReal head + signedWeightReal tail) := by
                  apply congrArg
                    (expectation (Fin.mOfFn eta fun _ ↦ $ᵗ (Bool × Bool)))
                  funext tail
                  exact signedWeightReal_cons head tail
          _ = expectation (Fin.mOfFn eta fun _ ↦ $ᵗ (Bool × Bool))
                (fun _ ↦ pairDifferenceReal head) +
              expectation (Fin.mOfFn eta fun _ ↦ $ᵗ (Bool × Bool))
                signedWeightReal :=
                  expectation_add _ _ _
          _ = pairDifferenceReal head := by
            rw [expectation_const]
            change pairDifferenceReal head +
                mean (coinRowSampler eta) signedWeightReal = _
            rw [inductionHypothesis, add_zero]
      calc
        (∑ head,
            Pr[= head | $ᵗ (Bool × Bool)].toReal *
              expectation
                (Fin.mOfFn eta (fun _ ↦ $ᵗ (Bool × Bool)) >>=
                  fun tail ↦ pure (Fin.cons head tail))
                signedWeightReal) =
          ∑ head,
            Pr[= head | $ᵗ (Bool × Bool)].toReal *
              pairDifferenceReal head := by
                apply Finset.sum_congr rfl
                intro head _
                rw [hInner]
        _ = expectation ($ᵗ (Bool × Bool)) pairDifferenceReal := rfl
        _ = 0 := expectation_pairDifferenceReal

/-- Independent fair coin pairs give second moment exactly `eta / 2`. -/
theorem secondMoment_coinRowSampler_signedWeightReal (eta : ℕ) :
    secondMoment (coinRowSampler eta) signedWeightReal = (eta : ℝ) / 2 := by
  induction eta with
  | zero =>
      simp [coinRowSampler, ProbComp.sampleIID, Fin.mOfFn, secondMoment,
        signedWeightReal, signedWeight, positiveWeight, negativeWeight,
        expectation_pure]
  | succ eta inductionHypothesis =>
      rw [secondMoment]
      unfold coinRowSampler ProbComp.sampleIID
      simp only [Fin.mOfFn]
      rw [expectation_bind]
      have hInner (head : Bool × Bool) :
          expectation
              (Fin.mOfFn eta (fun _ ↦ $ᵗ (Bool × Bool)) >>=
                fun tail ↦ pure (Fin.cons head tail))
              (fun coins ↦ signedWeightReal coins ^ 2) =
            (eta : ℝ) / 2 + pairDifferenceReal head ^ 2 := by
        calc
          expectation
              (Fin.mOfFn eta (fun _ ↦ $ᵗ (Bool × Bool)) >>=
                fun tail ↦ pure (Fin.cons head tail))
              (fun coins ↦ signedWeightReal coins ^ 2) =
            expectation (Fin.mOfFn eta fun _ ↦ $ᵗ (Bool × Bool))
              (fun tail ↦ signedWeightReal (Fin.cons head tail) ^ 2) := by
                  rw [expectation_bind]
                  apply Finset.sum_congr rfl
                  intro tail _
                  rw [expectation_pure]
          _ = expectation (Fin.mOfFn eta fun _ ↦ $ᵗ (Bool × Bool))
              (fun tail ↦
                signedWeightReal tail ^ 2 +
                  (2 * pairDifferenceReal head) * signedWeightReal tail +
                    pairDifferenceReal head ^ 2) := by
                  apply congrArg
                    (expectation (Fin.mOfFn eta fun _ ↦ $ᵗ (Bool × Bool)))
                  funext tail
                  rw [signedWeightReal_cons]
                  ring
          _ = secondMoment
                (Fin.mOfFn eta fun _ ↦ $ᵗ (Bool × Bool))
                signedWeightReal +
              (2 * pairDifferenceReal head) *
                mean (Fin.mOfFn eta fun _ ↦ $ᵗ (Bool × Bool))
                  signedWeightReal +
              pairDifferenceReal head ^ 2 :=
                expectation_quadratic _ signedWeightReal
                  (2 * pairDifferenceReal head) (pairDifferenceReal head ^ 2)
          _ = (eta : ℝ) / 2 + pairDifferenceReal head ^ 2 := by
            change secondMoment (coinRowSampler eta) signedWeightReal +
                (2 * pairDifferenceReal head) *
                  mean (coinRowSampler eta) signedWeightReal +
                pairDifferenceReal head ^ 2 = _
            rw [inductionHypothesis, mean_coinRowSampler_signedWeightReal]
            ring
      calc
        (∑ head,
            Pr[= head | $ᵗ (Bool × Bool)].toReal *
              expectation
                (Fin.mOfFn eta (fun _ ↦ $ᵗ (Bool × Bool)) >>=
                  fun tail ↦ pure (Fin.cons head tail))
                (fun coins ↦ signedWeightReal coins ^ 2)) =
          ∑ head,
            Pr[= head | $ᵗ (Bool × Bool)].toReal *
              ((eta : ℝ) / 2 + pairDifferenceReal head ^ 2) := by
                apply Finset.sum_congr rfl
                intro head _
                rw [hInner]
        _ = expectation ($ᵗ (Bool × Bool))
            (fun head ↦ (eta : ℝ) / 2 + pairDifferenceReal head ^ 2) := rfl
        _ = expectation ($ᵗ (Bool × Bool)) (fun _ ↦ (eta : ℝ) / 2) +
            expectation ($ᵗ (Bool × Bool))
              (fun head ↦ pairDifferenceReal head ^ 2) :=
                expectation_add _ _ _
        _ = (eta : ℝ) / 2 + 1 / 2 := by
          rw [expectation_const, expectation_sq_pairDifferenceReal]
        _ = ((eta + 1 : ℕ) : ℝ) / 2 := by
          push_cast
          ring

/-! ## Uniform-table and modular-coefficient forms -/

/-- The IID pair sampler is exactly the canonical uniform sampler on complete coin rows. -/
theorem coinRowSampler_evalDist_eq_uniform (eta : ℕ) :
    evalDist (coinRowSampler eta) = evalDist ($ᵗ (CoinRow eta)) := by
  exact FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
    (alpha := Bool × Bool) eta

/-- A uniformly sampled complete coin row has mean zero. -/
theorem mean_uniformCoinRow_signedWeightReal (eta : ℕ) :
    mean ($ᵗ (CoinRow eta)) signedWeightReal = 0 := by
  rw [← mean_congr_evalDist (coinRowSampler_evalDist_eq_uniform eta)
    signedWeightReal]
  exact mean_coinRowSampler_signedWeightReal eta

/-- A uniformly sampled complete coin row has second moment `eta / 2`. -/
theorem secondMoment_uniformCoinRow_signedWeightReal (eta : ℕ) :
    secondMoment ($ᵗ (CoinRow eta)) signedWeightReal = (eta : ℝ) / 2 := by
  rw [← secondMoment_congr_evalDist (coinRowSampler_evalDist_eq_uniform eta)
    signedWeightReal]
  exact secondMoment_coinRowSampler_signedWeightReal eta

/-- Centered real lift of one modular coefficient. -/
def centeredCoefficientLift (q : ℕ) [NeZero q] : ZMod q → ℝ :=
  fun value ↦ (LatticeCrypto.centeredRepr value : ℝ)

/-- Below the wrap threshold, decoding a signed centered-binomial weight through `ZMod q`
returns the original integer. -/
theorem centeredCoefficientLift_signedWeight
    {q eta : ℕ} [NeZero q] (coins : CoinRow eta)
    (hNoWrap : 2 * eta < q) :
    centeredCoefficientLift q (signedWeight coins : ZMod q) =
      signedWeightReal coins := by
  have hNatAbs : (signedWeight coins).natAbs ≤ eta := by
    rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
    exact abs_signedWeight_le coins
  unfold centeredCoefficientLift signedWeightReal
  rw [LatticeCrypto.centeredRepr_intCast_eq_of_natAbs_le
    (signedWeight coins) hNatAbs hNoWrap]

/-- The executable modular centered-binomial coefficient remains centered whenever its complete
integer support does not wrap. -/
theorem mean_coefficientSampler_centeredCoefficientLift
    (q eta : ℕ) [NeZero q] (hNoWrap : 2 * eta < q) :
    mean (coefficientSampler q eta) (centeredCoefficientLift q) = 0 := by
  rw [coefficientSampler, mean_map]
  calc
    expectation ($ᵗ (CoinRow eta))
        (fun coins ↦
          centeredCoefficientLift q (signedWeight coins : ZMod q)) =
      expectation ($ᵗ (CoinRow eta)) signedWeightReal := by
        apply congrArg (expectation ($ᵗ (CoinRow eta)))
        funext coins
        exact centeredCoefficientLift_signedWeight coins hNoWrap
    _ = 0 := mean_uniformCoinRow_signedWeightReal eta

/-- **Exact centered-binomial variance.**  With no modular wrap, one executable coefficient has
second moment exactly `eta / 2`. -/
theorem secondMoment_coefficientSampler_centeredCoefficientLift
    (q eta : ℕ) [NeZero q] (hNoWrap : 2 * eta < q) :
    secondMoment (coefficientSampler q eta) (centeredCoefficientLift q) =
      (eta : ℝ) / 2 := by
  rw [coefficientSampler, secondMoment_map]
  calc
    expectation ($ᵗ (CoinRow eta))
        (fun coins ↦
          centeredCoefficientLift q (signedWeight coins : ZMod q) ^ 2) =
      expectation ($ᵗ (CoinRow eta))
        (fun coins ↦ signedWeightReal coins ^ 2) := by
          apply congrArg (expectation ($ᵗ (CoinRow eta)))
          funext coins
          rw [centeredCoefficientLift_signedWeight coins hNoWrap]
    _ = (eta : ℝ) / 2 :=
      secondMoment_uniformCoinRow_signedWeightReal eta

/-! ## Ring-coordinate marginals -/

/-- Every coordinate of the executable ring sampler has exactly the scalar coefficient law. -/
theorem sampler_get_evalDist
    (q degree eta : ℕ) [NeZero q] (coefficient : Fin degree) :
    evalDist
        ((fun error : Rq q degree ↦ error.get coefficient) <$>
          sampler q degree eta) =
      evalDist (coefficientSampler q eta) := by
  let decode := fun coins : CoinRow eta ↦ (signedWeight coins : ZMod q)
  have hCoordinate :=
    FormalProof4FHE.FiniteProduct.evalDist_map_apply_uniformSample_fun
      (domain := Fin degree) (codomain := CoinRow eta) coefficient
  have hMapped := evalDist_map_eq_of_evalDist_eq hCoordinate decode
  simpa [sampler_eq_map_uniformCoins, coefficientSampler, decode,
    Functor.map_map, Function.comp_def, errorFromCoins_get] using hMapped

/-- Centered lift of one specified coefficient of a ring error. -/
def ringCoefficientLift
    (q : ℕ) [NeZero q] {degree : ℕ} (coefficient : Fin degree) :
    Rq q degree → ℝ :=
  fun error ↦ centeredCoefficientLift q (error.get coefficient)

/-- A no-wrap centered-binomial ring coefficient has mean zero. -/
theorem mean_sampler_ringCoefficientLift
    (q degree eta : ℕ) [NeZero q] (coefficient : Fin degree)
    (hNoWrap : 2 * eta < q) :
    mean (sampler q degree eta) (ringCoefficientLift q coefficient) = 0 := by
  calc
    mean (sampler q degree eta) (ringCoefficientLift q coefficient) =
      mean
        ((fun error : Rq q degree ↦ error.get coefficient) <$>
          sampler q degree eta)
        (centeredCoefficientLift q) := by
          rw [mean_map]
          rfl
    _ = mean (coefficientSampler q eta) (centeredCoefficientLift q) :=
      mean_congr_evalDist (sampler_get_evalDist q degree eta coefficient)
        (centeredCoefficientLift q)
    _ = 0 := mean_coefficientSampler_centeredCoefficientLift q eta hNoWrap

/-- Every no-wrap coefficient of the executable ring error has exact second moment `eta / 2`. -/
theorem secondMoment_sampler_ringCoefficientLift
    (q degree eta : ℕ) [NeZero q] (coefficient : Fin degree)
    (hNoWrap : 2 * eta < q) :
    secondMoment (sampler q degree eta) (ringCoefficientLift q coefficient) =
      (eta : ℝ) / 2 := by
  calc
    secondMoment (sampler q degree eta) (ringCoefficientLift q coefficient) =
      secondMoment
        ((fun error : Rq q degree ↦ error.get coefficient) <$>
          sampler q degree eta)
        (centeredCoefficientLift q) := by
          rw [secondMoment_map]
          rfl
    _ = secondMoment (coefficientSampler q eta) (centeredCoefficientLift q) :=
      secondMoment_congr_evalDist
        (sampler_get_evalDist q degree eta coefficient)
        (centeredCoefficientLift q)
    _ = (eta : ℝ) / 2 :=
      secondMoment_coefficientSampler_centeredCoefficientLift q eta hNoWrap

/-! ## Weighted coefficient vectors -/

/-- A real weighted sum of independent no-wrap centered-binomial coefficients is centered. -/
theorem mean_sampleIID_coefficientSampler_weightedSum
    (q eta count : ℕ) [NeZero q] (weights : Fin count → ℝ)
    (hNoWrap : 2 * eta < q) :
    mean (ProbComp.sampleIID count (coefficientSampler q eta))
        (weightedSum weights (centeredCoefficientLift q)) = 0 := by
  exact mean_sampleIID_weightedSum_eq_zero
    (coefficientSampler q eta) (centeredCoefficientLift q)
    (mean_coefficientSampler_centeredCoefficientLift q eta hNoWrap)
    count weights

/-- Exact variance of a real weighted sum of independent no-wrap centered-binomial
coefficients. -/
theorem secondMoment_sampleIID_coefficientSampler_weightedSum
    (q eta count : ℕ) [NeZero q] (weights : Fin count → ℝ)
    (hNoWrap : 2 * eta < q) :
    secondMoment (ProbComp.sampleIID count (coefficientSampler q eta))
        (weightedSum weights (centeredCoefficientLift q)) =
      ((eta : ℝ) / 2) * ∑ index, weights index ^ 2 := by
  rw [secondMoment_sampleIID_weightedSum_eq
    (coefficientSampler q eta) (centeredCoefficientLift q)
    (mean_coefficientSampler_centeredCoefficientLift q eta hNoWrap)
    count weights]
  rw [secondMoment_coefficientSampler_centeredCoefficientLift q eta hNoWrap]

/-- Coefficient-vector view of one ring error. -/
def coefficientVector {q degree : ℕ} (error : Rq q degree) :
    Fin degree → ZMod q :=
  fun coefficient ↦ error.get coefficient

/-- The complete coefficient vector of a centered-binomial ring error consists of IID scalar
centered-binomial coefficients. -/
theorem coefficientVector_sampler_evalDist
    (q degree eta : ℕ) [NeZero q] :
    evalDist (coefficientVector <$> sampler q degree eta) =
      evalDist (ProbComp.sampleIID degree (coefficientSampler q eta)) := by
  let decode := fun coins : CoinRow eta ↦ (signedWeight coins : ZMod q)
  let decodeTable := fun coins : CoinTable degree eta ↦
    fun coefficient ↦ decode (coins coefficient)
  have hUniform :=
    (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
      (alpha := CoinRow eta) degree).symm
  have hMapped := evalDist_map_eq_of_evalDist_eq hUniform decodeTable
  have hCoordinatewise := FormalProof4FHE.FiniteProduct.map_fin_mOfFn_const
    degree ($ᵗ (CoinRow eta)) decode
  calc
    evalDist (coefficientVector <$> sampler q degree eta) =
      evalDist (decodeTable <$> ($ᵗ (CoinTable degree eta))) := by
        rw [sampler_eq_map_uniformCoins]
        simp only [Functor.map_map]
        apply congrArg evalDist
        apply congrArg (fun transform ↦
          transform <$> ($ᵗ (CoinTable degree eta)))
        funext coins
        funext coefficient
        simp [coefficientVector, decodeTable, decode, errorFromCoins_get]
    _ = evalDist
        (decodeTable <$>
          Fin.mOfFn degree (fun _ ↦ $ᵗ (CoinRow eta))) := hMapped
    _ = evalDist
        (Fin.mOfFn degree
          (fun _ ↦ decode <$> ($ᵗ (CoinRow eta)))) := by
            rw [← hCoordinatewise]
    _ = evalDist
        (ProbComp.sampleIID degree (coefficientSampler q eta)) := by
          rfl

/-! ## Fixed ring multiplication -/

/-- A deterministic no-wrap coefficient identity transfers the exact IID coefficient moment to
one coefficient of a fixed-secret ring product.  The weights may encode the signed negacyclic
convolution row of the fixed secret. -/
theorem secondMoment_mul_sampler_ringCoefficientLift_eq_weighted
    (q degree eta : ℕ) [NeZero q]
    (secret : Rq q degree) (coefficient : Fin degree)
    (weights : Fin degree → ℝ) (hNoWrap : 2 * eta < q)
    (hProductLift : ∀ error,
      error ∈ support (sampler q degree eta) →
        ringCoefficientLift q coefficient (secret * error) =
          weightedSum weights (centeredCoefficientLift q)
            (coefficientVector error)) :
    secondMoment
        ((fun error : Rq q degree ↦ secret * error) <$>
          sampler q degree eta)
        (ringCoefficientLift q coefficient) =
      ((eta : ℝ) / 2) * ∑ index, weights index ^ 2 := by
  rw [secondMoment_map]
  calc
    expectation (sampler q degree eta)
        (fun error ↦ ringCoefficientLift q coefficient (secret * error) ^ 2) =
      expectation (sampler q degree eta)
        (fun error ↦
          weightedSum weights (centeredCoefficientLift q)
            (coefficientVector error) ^ 2) := by
              apply expectation_congr_on_support
              intro error hError
              rw [hProductLift error hError]
    _ = secondMoment
        (coefficientVector <$> sampler q degree eta)
        (weightedSum weights (centeredCoefficientLift q)) := by
          rw [secondMoment_map]
    _ = secondMoment
        (ProbComp.sampleIID degree (coefficientSampler q eta))
        (weightedSum weights (centeredCoefficientLift q)) :=
          secondMoment_congr_evalDist
            (coefficientVector_sampler_evalDist q degree eta)
            (weightedSum weights (centeredCoefficientLift q))
    _ = ((eta : ℝ) / 2) * ∑ index, weights index ^ 2 :=
      secondMoment_sampleIID_coefficientSampler_weightedSum
        q eta degree weights hNoWrap

end

end FormalProof4FHE.RLWE.CenteredBinomial
