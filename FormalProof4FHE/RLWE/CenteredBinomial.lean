/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.Basic
import FormalProof4FHE.Probability.FiniteProduct

/-!
# Centered-Binomial Errors for Finite RLWE

This module defines an executable centered-binomial error sampler over the negacyclic ring
`FormalProof4FHE.RLWE.Rq q degree`. For every coefficient, it draws `eta` independent pairs of
uniform bits and returns the first Hamming weight minus the second, reduced modulo `q`.

The checked interface exposes the two properties used most often by scheme proofs:

- every sampled coefficient has an integer representative in `[-eta, eta]`;
- the complete polynomial distribution is invariant under coefficient-wise negation.

No ideal-Gaussian claim is made. This is a finite sampler suitable for an executable reduction.
-/

open scoped BigOperators
open OracleComp

namespace FormalProof4FHE.RLWE.CenteredBinomial

/-- The `eta` pairs of random bits used for one centered-binomial coefficient. -/
abbrev CoinRow (eta : ℕ) := Fin eta → Bool × Bool

/-- Independent centered-binomial coins for every polynomial coefficient. -/
abbrev CoinTable (degree eta : ℕ) := Fin degree → CoinRow eta

/-- Hamming weight of the first bit in every pair. -/
def positiveWeight {eta : ℕ} (coins : CoinRow eta) : ℕ :=
  ∑ i, if (coins i).1 then 1 else 0

/-- Hamming weight of the second bit in every pair. -/
def negativeWeight {eta : ℕ} (coins : CoinRow eta) : ℕ :=
  ∑ i, if (coins i).2 then 1 else 0

/-- The signed centered-binomial value before reduction modulo `q`. -/
def signedWeight {eta : ℕ} (coins : CoinRow eta) : ℤ :=
  (positiveWeight coins : ℤ) - (negativeWeight coins : ℤ)

/-- The positive Hamming weight is at most the number of pairs. -/
theorem positiveWeight_le {eta : ℕ} (coins : CoinRow eta) :
    positiveWeight coins ≤ eta := by
  calc
    positiveWeight coins ≤ ∑ _ : Fin eta, 1 := by
      apply Finset.sum_le_sum
      intro i _
      split <;> simp
    _ = eta := by simp

/-- The negative Hamming weight is at most the number of pairs. -/
theorem negativeWeight_le {eta : ℕ} (coins : CoinRow eta) :
    negativeWeight coins ≤ eta := by
  calc
    negativeWeight coins ≤ ∑ _ : Fin eta, 1 := by
      apply Finset.sum_le_sum
      intro i _
      split <;> simp
    _ = eta := by simp

/-- A centered-binomial coefficient lies in the integer interval `[-eta, eta]`. -/
theorem abs_signedWeight_le {eta : ℕ} (coins : CoinRow eta) :
    |signedWeight coins| ≤ eta := by
  have hpos := positiveWeight_le coins
  have hneg := negativeWeight_le coins
  simp only [signedWeight, abs_le]
  constructor <;> omega

/-- Swap the positive and negative bit in every pair. -/
def swapRow {eta : ℕ} (coins : CoinRow eta) : CoinRow eta :=
  fun i ↦ (coins i).swap

@[simp]
theorem positiveWeight_swapRow {eta : ℕ} (coins : CoinRow eta) :
    positiveWeight (swapRow coins) = negativeWeight coins := by
  rfl

@[simp]
theorem negativeWeight_swapRow {eta : ℕ} (coins : CoinRow eta) :
    negativeWeight (swapRow coins) = positiveWeight coins := by
  rfl

@[simp]
theorem signedWeight_swapRow {eta : ℕ} (coins : CoinRow eta) :
    signedWeight (swapRow coins) = -signedWeight coins := by
  simp [signedWeight]

/-- Swap the positive and negative coins independently at every coefficient. -/
def swapTable {degree eta : ℕ} (coins : CoinTable degree eta) : CoinTable degree eta :=
  fun i ↦ swapRow (coins i)

@[simp]
theorem swapTable_swapTable {degree eta : ℕ} (coins : CoinTable degree eta) :
    swapTable (swapTable coins) = coins := by
  funext i j
  simp [swapTable, swapRow]

/-- Swapping all coin pairs is a permutation of the finite coin space. -/
theorem swapTable_bijective (degree eta : ℕ) :
    Function.Bijective (swapTable : CoinTable degree eta → CoinTable degree eta) :=
  Function.Involutive.bijective swapTable_swapTable

/-- Deterministically convert a complete coin table into a ring error. -/
def errorFromCoins (q degree eta : ℕ) (coins : CoinTable degree eta) : Rq q degree :=
  LatticeCrypto.Poly.ofPi fun i ↦ (signedWeight (coins i) : ZMod q)

@[simp]
theorem errorFromCoins_get (q degree eta : ℕ) (coins : CoinTable degree eta)
    (i : Fin degree) :
    (errorFromCoins q degree eta coins).get i =
      (signedWeight (coins i) : ZMod q) := by
  simp [errorFromCoins, LatticeCrypto.Poly.ofPi, Vector.get]

/-- Coefficient-wise negation supplied by the bundled negacyclic ring. -/
def negError (q degree : ℕ) (error : Rq q degree) : Rq q degree :=
  (negacyclicRing q degree).neg error

/-- Bundled coefficient-wise negation is involutive. -/
theorem negError_involutive (q degree : ℕ) :
    Function.Involutive (negError q degree) := by
  intro error
  apply LatticeCrypto.NegacyclicRing.poly_ext
  intro i
  simp [negError]

/-- Bundled coefficient-wise negation is injective. -/
theorem negError_injective (q degree : ℕ) :
    Function.Injective (negError q degree) :=
  (negError_involutive q degree).injective

/-- Swapping every bit pair negates the resulting ring error. -/
theorem errorFromCoins_swapTable (q degree eta : ℕ) (coins : CoinTable degree eta) :
    errorFromCoins q degree eta (swapTable coins) =
      negError q degree (errorFromCoins q degree eta coins) := by
  apply LatticeCrypto.NegacyclicRing.poly_ext
  intro i
  calc
    (negacyclicRing q degree).backend.coeff
        (errorFromCoins q degree eta (swapTable coins)) i =
        (signedWeight (swapTable coins i) : ZMod q) := by
          simp [errorFromCoins, swapTable, LatticeCrypto.Poly.ofPi, Vector.get]
    _ = -(signedWeight (coins i) : ZMod q) := by simp [swapTable]
    _ = -(negacyclicRing q degree).backend.coeff
        (errorFromCoins q degree eta coins) i := by
          simp [errorFromCoins, LatticeCrypto.Poly.ofPi, Vector.get]
    _ = (negacyclicRing q degree).backend.coeff
        (negError q degree (errorFromCoins q degree eta coins)) i := by
          simp [negError]

/-- Every coefficient has a small signed integer representative modulo `q`. -/
def CoeffBounded {q degree : ℕ} (eta : ℕ) (error : Rq q degree) : Prop :=
  ∀ i, ∃ value : ℤ,
    |value| ≤ eta ∧ error.get i = (value : ZMod q)

/-- The deterministic error constructed from any coin table is coefficient-bounded. -/
theorem errorFromCoins_coeffBounded (q degree eta : ℕ) (coins : CoinTable degree eta) :
    CoeffBounded eta (errorFromCoins q degree eta coins) := by
  intro i
  exact ⟨signedWeight (coins i), abs_signedWeight_le (coins i),
    errorFromCoins_get q degree eta coins i⟩

/-- Sample a centered-binomial error polynomial from a uniform table of bit pairs. -/
def sampler (q degree eta : ℕ) [NeZero q] : ProbComp (Rq q degree) := do
  let coins ← $ᵗ (CoinTable degree eta)
  return errorFromCoins q degree eta coins

/-- The centered-binomial sampler is literally the deterministic image of its uniform bit-pair
table. -/
theorem sampler_eq_map_uniformCoins (q degree eta : ℕ) [NeZero q] :
    sampler q degree eta =
      errorFromCoins q degree eta <$> ($ᵗ (CoinTable degree eta)) := by
  simp [sampler, monad_norm]

/-- Uniform centered-binomial coins for a finite vector of ring errors. -/
abbrev ErrorVectorCoinTable (count degree eta : ℕ) :=
  Fin count → CoinTable degree eta

/-- Deterministically decode every ring error in a vector of centered-binomial coin tables. -/
def errorVectorFromCoins (q count degree eta : ℕ)
    (coins : ErrorVectorCoinTable count degree eta) : Fin count → Rq q degree :=
  fun row ↦ errorFromCoins q degree eta (coins row)

/-- Independent centered-binomial ring errors are exactly a deterministic image of one uniform
finite coin space. -/
theorem sampleIID_sampler_evalDist_eq_uniformCoins
    (q count degree eta : ℕ) [NeZero q] :
    evalDist (ProbComp.sampleIID count (sampler q degree eta)) =
      evalDist (errorVectorFromCoins q count degree eta <$>
        ($ᵗ (ErrorVectorCoinTable count degree eta))) := by
  let One := CoinTable degree eta
  let decode := errorFromCoins q degree eta
  rw [sampler_eq_map_uniformCoins]
  have hPointwise := FormalProof4FHE.FiniteProduct.map_fin_mOfFn count
    (fun _ ↦ ($ᵗ One : ProbComp One)) (fun _ ↦ decode)
  have hUniform := FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
    (alpha := One) count
  have hMapped := evalDist_map_eq_of_evalDist_eq hUniform
    (errorVectorFromCoins q count degree eta)
  unfold ProbComp.sampleIID
  calc
    _ = evalDist
        (errorVectorFromCoins q count degree eta <$>
          Fin.mOfFn count (fun _ ↦ ($ᵗ One : ProbComp One))) := by
      rw [← hPointwise]
      rfl
    _ = _ := hMapped

/-- Every error in the sampler's support satisfies the coefficient bound. -/
theorem coeffBounded_of_mem_support {q degree eta : ℕ} [NeZero q]
    {error : Rq q degree} (herror : error ∈ support (sampler q degree eta)) :
    CoeffBounded eta error := by
  obtain ⟨coins, _, hcoins⟩ :=
    (mem_support_bind_iff ($ᵗ (CoinTable degree eta))
      (fun coins ↦ pure (errorFromCoins q degree eta coins)) error).mp herror
  simp only [support_pure, Set.mem_singleton_iff] at hcoins
  subst error
  exact errorFromCoins_coeffBounded q degree eta coins

/-- The centered-binomial ring sampler is invariant under bundled coefficient-wise negation. -/
theorem probOutput_negError (q degree eta : ℕ) [NeZero q] (error : Rq q degree) :
    Pr[= negError q degree error | sampler q degree eta] =
      Pr[= error | sampler q degree eta] := by
  have hreindex := probOutput_bind_bijective_uniform_cross
    (α := CoinTable degree eta) (β := CoinTable degree eta)
    swapTable (swapTable_bijective degree eta)
    (fun coins ↦ pure (errorFromCoins q degree eta coins)) (negError q degree error)
  rw [show (($ᵗ (CoinTable degree eta)) >>= fun coins ↦
      pure (errorFromCoins q degree eta (swapTable coins))) =
      (($ᵗ (CoinTable degree eta)) >>= fun coins ↦
        pure (negError q degree (errorFromCoins q degree eta coins))) by
    apply bind_congr
    intro coins
    rw [errorFromCoins_swapTable]] at hreindex
  rw [show sampler q degree eta =
      (($ᵗ (CoinTable degree eta)) >>= fun coins ↦
        pure (errorFromCoins q degree eta coins)) by
    simp [sampler, monad_norm]]
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum] at hreindex ⊢
  calc
    _ = ∑' coins : CoinTable degree eta,
        Pr[= coins | $ᵗ (CoinTable degree eta)] *
          Pr[= negError q degree error |
            pure (negError q degree (errorFromCoins q degree eta coins))] := hreindex.symm
    _ = ∑' coins : CoinTable degree eta,
        Pr[= coins | $ᵗ (CoinTable degree eta)] *
          Pr[= error | pure (errorFromCoins q degree eta coins)] := by
      refine tsum_congr fun coins ↦ ?_
      congr 1
      by_cases h : error = errorFromCoins q degree eta coins
      · subst error
        rw [probOutput_pure_self, probOutput_pure_self]
      · have hn : negError q degree error ≠
            negError q degree (errorFromCoins q degree eta coins) := fun heq ↦
          h (negError_injective q degree heq)
        rw [probOutput_pure, probOutput_pure, if_neg hn, if_neg h]
    _ = _ := rfl

/-- The centered-binomial ring sampler is invariant under ring negation notation. -/
theorem probOutput_neg (q degree eta : ℕ) [NeZero q] (error : Rq q degree) :
    Pr[= -error | sampler q degree eta] = Pr[= error | sampler q degree eta] := by
  change Pr[= negError q degree error | sampler q degree eta] = _
  exact probOutput_negError q degree eta error

end FormalProof4FHE.RLWE.CenteredBinomial
