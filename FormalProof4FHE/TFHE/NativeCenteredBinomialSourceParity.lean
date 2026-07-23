/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.CenteredBinomial
import FormalProof4FHE.TFHE.NativeDiagonalRetainedFiberCokernel

/-!
# Parity of Native Centered-Binomial Source Errors

The power-of-two native coefficient ring has residue field `ZMod 2`, obtained by reducing
coefficients and evaluating at `X = 1`.  For positive ring degree and positive centered-binomial
width, this residue of one sampled ring error is exactly uniform.  Consequently the probability
that every row in an independently sampled TGSW error vector lies in the maximal ideal is an
explicit inverse power of two.

This supplies the bad-event half of the distribution-weighted retained-cokernel certificate.  It
does not assert the remaining good-error cokernel estimate.
-/

open OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.Native.CenteredBinomialSourceParity

open FormalProof4FHE.RLWE.CenteredBinomial
open Native.ShiftedCandidateEvaluator.DiagonalNormalForm

noncomputable section

/-- Toggle the first positive centered-binomial coin. -/
def toggleHeadRow {eta : ℕ} (coins : CoinRow (eta + 1)) : CoinRow (eta + 1) :=
  Fin.cons (!(coins 0).1, (coins 0).2) (Fin.tail coins)

@[simp]
theorem toggleHeadRow_zero {eta : ℕ} (coins : CoinRow (eta + 1)) :
    toggleHeadRow coins 0 = (!(coins 0).1, (coins 0).2) := by
  simp [toggleHeadRow]

@[simp]
theorem toggleHeadRow_succ {eta : ℕ} (coins : CoinRow (eta + 1))
    (index : Fin eta) :
    toggleHeadRow coins index.succ = coins index.succ := by
  rfl

theorem toggleHeadRow_involutive (eta : ℕ) :
    Function.Involutive (toggleHeadRow : CoinRow (eta + 1) → CoinRow (eta + 1)) := by
  intro coins
  funext index
  refine Fin.cases ?_ (fun tailIndex ↦ ?_) index
  · simp
  · simp

theorem toggleHeadRow_bijective (eta : ℕ) :
    Function.Bijective (toggleHeadRow : CoinRow (eta + 1) → CoinRow (eta + 1)) :=
  (toggleHeadRow_involutive eta).bijective

/-- Toggle that coin in the first polynomial coefficient. -/
def toggleHeadTable {degree eta : ℕ}
    (coins : CoinTable (degree + 1) (eta + 1)) :
    CoinTable (degree + 1) (eta + 1) :=
  Fin.cons (toggleHeadRow (coins 0)) (Fin.tail coins)

@[simp]
theorem toggleHeadTable_zero {degree eta : ℕ}
    (coins : CoinTable (degree + 1) (eta + 1)) :
    toggleHeadTable coins 0 = toggleHeadRow (coins 0) := by
  simp [toggleHeadTable]

@[simp]
theorem toggleHeadTable_succ {degree eta : ℕ}
    (coins : CoinTable (degree + 1) (eta + 1)) (index : Fin degree) :
    toggleHeadTable coins index.succ = coins index.succ := by
  rfl

theorem toggleHeadTable_involutive (degree eta : ℕ) :
    Function.Involutive
      (toggleHeadTable :
        CoinTable (degree + 1) (eta + 1) → CoinTable (degree + 1) (eta + 1)) := by
  intro coins
  funext coefficient coin
  refine Fin.cases ?_ (fun tailCoefficient ↦ ?_) coefficient
  · exact congrFun (toggleHeadRow_involutive eta (coins 0)) coin
  · simp

theorem toggleHeadTable_bijective (degree eta : ℕ) :
    Function.Bijective
      (toggleHeadTable :
        CoinTable (degree + 1) (eta + 1) → CoinTable (degree + 1) (eta + 1)) :=
  (toggleHeadTable_involutive degree eta).bijective

/-- Toggling the distinguished coin flips the signed coefficient modulo two. -/
theorem signedWeight_toggleHeadRow_mod_two {eta : ℕ}
    (coins : CoinRow (eta + 1)) :
    (signedWeight (toggleHeadRow coins) : ZMod 2) =
      (signedWeight coins : ZMod 2) + 1 := by
  unfold signedWeight positiveWeight negativeWeight
  simp only [Fin.sum_univ_succ, toggleHeadRow_zero, toggleHeadRow_succ]
  cases hbit : (coins 0).1
  · simp
    ring
  · simp
    let x : ZMod 2 :=
      (Finset.univ.filter (fun index : Fin eta ↦ (coins index.succ).1 = true)).card -
        ((if (coins 0).2 = true then 1 else 0) +
          (Finset.univ.filter (fun index : Fin eta ↦
            (coins index.succ).2 = true)).card)
    change x = _
    calc
      x = x + (1 + 1) := by
        rw [show (1 : ZMod 2) + 1 = 0 by
          change (2 : ZMod 2) = 0
          exact ZMod.natCast_self 2, add_zero]
      _ = 1 +
          (Finset.univ.filter
            (fun index : Fin eta ↦ (coins index.succ).1 = true)).card -
            ((if (coins 0).2 = true then 1 else 0) +
              (Finset.univ.filter (fun index : Fin eta ↦
                (coins index.succ).2 = true)).card) + 1 := by
        dsimp [x]
        ring

/-- Toggling one coin flips the native residue-field image of the decoded ring error. -/
theorem rqParityEval_errorFromCoins_toggleHeadTable
    {q degree eta : ℕ} [NeZero q] (heven : 2 ∣ q)
    (coins : CoinTable (degree + 1) (eta + 1)) :
    rqParityEval heven (Nat.succ_pos degree)
        (errorFromCoins q (degree + 1) (eta + 1) (toggleHeadTable coins)) =
      rqParityEval heven (Nat.succ_pos degree)
          (errorFromCoins q (degree + 1) (eta + 1) coins) + 1 := by
  rw [rqParityEval_apply, rqParityEval_apply]
  change
    (∑ coefficient,
      ZMod.castHom heven (ZMod 2)
        ((errorFromCoins q (degree + 1) (eta + 1)
          (toggleHeadTable coins)).get coefficient)) =
      (∑ coefficient,
        ZMod.castHom heven (ZMod 2)
          ((errorFromCoins q (degree + 1) (eta + 1) coins).get coefficient)) + 1
  simp only [errorFromCoins_get, map_intCast]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [toggleHeadTable_zero, toggleHeadTable_succ]
  rw [signedWeight_toggleHeadRow_mod_two]
  ring

/-- Residue-field image of one positive-width, positive-degree centered-binomial ring error. -/
def paritySampler (q degree eta : ℕ) [NeZero q] (heven : 2 ∣ q) :
    ProbComp (ZMod 2) :=
  rqParityEval heven (Nat.succ_pos degree) <$>
    sampler q (degree + 1) (eta + 1)

/-- Translation by one preserves the parity output probabilities.  The proof toggles one
distinguished source coin and uses that this toggle is a permutation of the complete finite coin
space. -/
theorem paritySampler_probOutput_add_one
    (q degree eta : ℕ) [NeZero q] (heven : 2 ∣ q) (residue : ZMod 2) :
    Pr[= residue + 1 | paritySampler q degree eta heven] =
      Pr[= residue | paritySampler q degree eta heven] := by
  let Coins := CoinTable (degree + 1) (eta + 1)
  let decode := fun coins : Coins ↦
    rqParityEval heven (Nat.succ_pos degree)
      (errorFromCoins q (degree + 1) (eta + 1) coins)
  have hreindex := probOutput_bind_bijective_uniform_cross
    (α := Coins) (β := Coins)
    toggleHeadTable (toggleHeadTable_bijective degree eta)
    (fun coins ↦ pure (decode coins)) (residue + 1)
  have hsampler :
      paritySampler q degree eta heven =
        (($ᵗ Coins) >>= fun coins ↦ pure (decode coins)) := by
    unfold paritySampler sampler
    simp [Coins, decode, monad_norm]
  rw [hsampler]
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum] at hreindex ⊢
  calc
    (∑' coins : Coins,
        Pr[= coins | $ᵗ Coins] * Pr[= residue + 1 | pure (decode coins)]) =
      ∑' coins : Coins,
        Pr[= coins | $ᵗ Coins] *
          Pr[= residue + 1 | pure (decode (toggleHeadTable coins))] :=
      hreindex.symm
    _ = ∑' coins : Coins,
        Pr[= coins | $ᵗ Coins] * Pr[= residue | pure (decode coins)] := by
      refine tsum_congr fun coins ↦ ?_
      congr 1
      have hflip : decode (toggleHeadTable coins) = decode coins + 1 := by
        exact rqParityEval_errorFromCoins_toggleHeadTable heven coins
      rw [hflip]
      by_cases hresidue : residue = decode coins
      · subst residue
        rw [probOutput_pure_self, probOutput_pure_self]
      · have hshift : residue + 1 ≠ decode coins + 1 := fun heq ↦
          hresidue (add_right_cancel heq)
        rw [probOutput_pure, probOutput_pure, if_neg hshift, if_neg hresidue]
    _ = ∑' coins : Coins,
        Pr[= coins | $ᵗ Coins] * Pr[= residue | pure (decode coins)] := rfl

/-- Canonical enumeration of the two residue-field elements. -/
def finTwoEquivZModTwo : Fin 2 ≃ ZMod 2 :=
  (ZMod.finEquiv 2).toEquiv

@[simp]
theorem finTwoEquivZModTwo_zero : finTwoEquivZModTwo 0 = 0 := rfl

@[simp]
theorem finTwoEquivZModTwo_one : finTwoEquivZModTwo 1 = 1 := rfl

/-- One native centered-binomial ring error has a fair residue-field bit. -/
theorem paritySampler_probOutput_zero
    (q degree eta : ℕ) [NeZero q] (heven : 2 ∣ q) :
    Pr[= 0 | paritySampler q degree eta heven] = (2 : ENNReal)⁻¹ := by
  let Sampler := paritySampler q degree eta heven
  let mass := fun residue : ZMod 2 ↦ Pr[= residue | Sampler]
  have htranslate : mass 1 = mass 0 := by
    simpa [mass, Sampler] using
      (paritySampler_probOutput_add_one q degree eta heven 0)
  have hmass : (∑ residue : ZMod 2, mass residue) = 1 := by
    dsimp [mass]
    exact sum_probOutput_eq_one (by simp [Sampler])
  have htwoMass : mass 0 + mass 1 = 1 := by
    calc
      mass 0 + mass 1 =
          ∑ index : Fin 2, mass (finTwoEquivZModTwo index) := by
        rw [Fin.sum_univ_two]
        simp
      _ = ∑ residue : ZMod 2, mass residue := by
        exact Fintype.sum_equiv finTwoEquivZModTwo _ _ (fun _ ↦ rfl)
      _ = 1 := hmass
  apply (ENNReal.toReal_eq_toReal_iff' probOutput_ne_top
    (ENNReal.inv_ne_top.mpr (by norm_num))).mp
  have hreal := congrArg ENNReal.toReal htwoMass
  have htranslateReal := congrArg ENNReal.toReal htranslate
  change Pr[= 1 | Sampler].toReal = Pr[= 0 | Sampler].toReal at htranslateReal
  rw [ENNReal.toReal_add probOutput_ne_top probOutput_ne_top,
    htranslateReal, ENNReal.toReal_one] at hreal
  change Pr[= 0 | Sampler].toReal = _
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  norm_num at hreal ⊢
  linarith

/-- Event that one sampled ring error has zero native residue-field image. -/
theorem probEvent_rqParityEval_eq_zero_sampler
    (q degree eta : ℕ) [NeZero q] (heven : 2 ∣ q) :
    Pr[(fun error : FormalProof4FHE.RLWE.Rq q (degree + 1) ↦
          rqParityEval heven (Nat.succ_pos degree) error = 0) |
        sampler q (degree + 1) (eta + 1)] =
      (2 : ENNReal)⁻¹ := by
  rw [← probOutput_map]
  exact paritySampler_probOutput_zero q degree eta heven

/-- A source-error vector is good for the local-ring split when at least one row has nonzero
residue-field image. -/
def HasNonzeroParity {q degree count : ℕ} (heven : 2 ∣ q)
    (sourceError : Fin count → FormalProof4FHE.RLWE.Rq q (degree + 1)) : Prop :=
  ∃ row, rqParityEval heven (Nat.succ_pos degree) (sourceError row) ≠ 0

/-- Over a native local coefficient ring, the nonzero-parity event really says that at least
one source-error row is a unit.  This is the algebraic property needed to solve one digit
coordinate inside each conditioned retained-error fiber. -/
theorem hasNonzeroParity_exists_isUnit {q degree count : ℕ} [NeZero q]
    (heven : 2 ∣ q)
    (localParity : IsLocalHom (rqParityEval heven (Nat.succ_pos degree)))
    {sourceError : Fin count → FormalProof4FHE.RLWE.Rq q (degree + 1)}
    (hgood : HasNonzeroParity heven sourceError) :
    ∃ row, IsUnit (sourceError row) := by
  obtain ⟨row, hnonzero⟩ := hgood
  refine ⟨row, ?_⟩
  letI : IsLocalHom (rqParityEval heven (Nat.succ_pos degree)) := localParity
  exact IsUnit.of_map (rqParityEval heven (Nat.succ_pos degree)) _
    (isUnit_iff_ne_zero.mpr hnonzero)

/-- Exact probability that every independently sampled centered-binomial source-error row lies
in the kernel of native parity evaluation. -/
theorem probEvent_not_hasNonzeroParity_sampleIID
    (q degree eta count : ℕ) [NeZero q] (heven : 2 ∣ q) :
    Pr[(fun sourceError :
          Fin count → FormalProof4FHE.RLWE.Rq q (degree + 1) ↦
        ¬ HasNonzeroParity heven sourceError) |
      ProbComp.sampleIID count (sampler q (degree + 1) (eta + 1))] =
        ((2 : ENNReal)⁻¹) ^ count := by
  unfold ProbComp.sampleIID HasNonzeroParity
  rw [show
      (fun sourceError : Fin count →
          FormalProof4FHE.RLWE.Rq q (degree + 1) ↦
        ¬∃ row, rqParityEval heven (Nat.succ_pos degree) (sourceError row) ≠ 0) =
      (fun sourceError ↦
        ∀ row, rqParityEval heven (Nat.succ_pos degree) (sourceError row) = 0) by
    funext sourceError
    apply propext
    simp]
  calc
    Pr[(fun sourceError :
          Fin count → FormalProof4FHE.RLWE.Rq q (degree + 1) ↦
        ∀ row, rqParityEval heven (Nat.succ_pos degree) (sourceError row) = 0) |
      Fin.mOfFn count (fun _ ↦ sampler q (degree + 1) (eta + 1))] =
        ∏ row : Fin count,
          Pr[(fun error : FormalProof4FHE.RLWE.Rq q (degree + 1) ↦
              rqParityEval heven (Nat.succ_pos degree) error = 0) |
            sampler q (degree + 1) (eta + 1)] := by
      exact FormalProof4FHE.FiniteProduct.probEvent_fin_mOfFn_forall
        count (fun _ ↦ sampler q (degree + 1) (eta + 1))
          (fun _ error ↦ rqParityEval heven (Nat.succ_pos degree) error = 0)
    _ = ((2 : ENNReal)⁻¹) ^ count := by
      simp_rw [probEvent_rqParityEval_eq_zero_sampler q degree eta heven]
      simp

end

end FormalProof4FHE.TFHE.Native.CenteredBinomialSourceParity
