/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.CenteredBinomial

/-!
# Positive-Width Centered Binomial Noise in Characteristic Two

Modulo two, toggling one distinguished positive coin toggles a centered-binomial coefficient.
Consequently every positive-width centered-binomial coefficient is exactly uniform in `ZMod 2`.
Independence across polynomial coefficients then makes the complete native ring-error sampler
exactly uniform as well.

This identity is useful for closing characteristic-two diagnostic instances of native key
randomization.  It is not a narrow-noise statement: modulo two the positive-width error has
already filled the complete coefficient ring.
-/

open OracleComp

namespace FormalProof4FHE.RLWE.CenteredBinomial

noncomputable section

/-! ## One coefficient -/

/-- The centered-binomial sampler for one coefficient, factored out of the ring sampler. -/
def coefficientSampler (q eta : ℕ) [NeZero q] : ProbComp (ZMod q) :=
  (fun coins : CoinRow eta ↦ (signedWeight coins : ZMod q)) <$>
    ($ᵗ (CoinRow eta))

/-- Toggle the first positive coin of a positive-width coefficient sample. -/
def toggleHeadPositive {eta : ℕ} (coins : CoinRow (eta + 1)) : CoinRow (eta + 1) :=
  Fin.cons (!(coins 0).1, (coins 0).2) (Fin.tail coins)

@[simp]
theorem toggleHeadPositive_zero {eta : ℕ} (coins : CoinRow (eta + 1)) :
    toggleHeadPositive coins 0 = (!(coins 0).1, (coins 0).2) := by
  simp [toggleHeadPositive]

@[simp]
theorem toggleHeadPositive_succ {eta : ℕ} (coins : CoinRow (eta + 1))
    (index : Fin eta) :
    toggleHeadPositive coins index.succ = coins index.succ := by
  rfl

theorem toggleHeadPositive_involutive (eta : ℕ) :
    Function.Involutive
      (toggleHeadPositive : CoinRow (eta + 1) → CoinRow (eta + 1)) := by
  intro coins
  funext index
  refine Fin.cases ?_ (fun tailIndex ↦ ?_) index
  · simp
  · simp

theorem toggleHeadPositive_bijective (eta : ℕ) :
    Function.Bijective
      (toggleHeadPositive : CoinRow (eta + 1) → CoinRow (eta + 1)) :=
  (toggleHeadPositive_involutive eta).bijective

/-- Flipping the distinguished coin adds one to the decoded coefficient modulo two. -/
theorem signedWeight_toggleHeadPositive_mod_two {eta : ℕ}
    (coins : CoinRow (eta + 1)) :
    (signedWeight (toggleHeadPositive coins) : ZMod 2) =
      (signedWeight coins : ZMod 2) + 1 := by
  unfold signedWeight positiveWeight negativeWeight
  simp only [Fin.sum_univ_succ, toggleHeadPositive_zero,
    toggleHeadPositive_succ]
  cases hbit : (coins 0).1
  · simp
    ring
  · simp
    let value : ZMod 2 :=
      (Finset.univ.filter
          (fun index : Fin eta ↦ (coins index.succ).1 = true)).card -
        ((if (coins 0).2 = true then 1 else 0) +
          (Finset.univ.filter
            (fun index : Fin eta ↦ (coins index.succ).2 = true)).card)
    change value = _
    calc
      value = value + (1 + 1) := by
        rw [show (1 : ZMod 2) + 1 = 0 by
          change (2 : ZMod 2) = 0
          exact ZMod.natCast_self 2, add_zero]
      _ = 1 +
          (Finset.univ.filter
            (fun index : Fin eta ↦ (coins index.succ).1 = true)).card -
            ((if (coins 0).2 = true then 1 else 0) +
              (Finset.univ.filter
                (fun index : Fin eta ↦ (coins index.succ).2 = true)).card) + 1 := by
        dsimp [value]
        ring

/-- Translation by one preserves every output mass of the positive-width coefficient sampler. -/
theorem coefficientSampler_two_probOutput_add_one
    (eta : ℕ) (residue : ZMod 2) :
    Pr[= residue + 1 | coefficientSampler 2 (eta + 1)] =
      Pr[= residue | coefficientSampler 2 (eta + 1)] := by
  let Coins := CoinRow (eta + 1)
  let decode := fun coins : Coins ↦ (signedWeight coins : ZMod 2)
  have hreindex := probOutput_bind_bijective_uniform_cross
    (α := Coins) (β := Coins)
    toggleHeadPositive (toggleHeadPositive_bijective eta)
    (fun coins ↦ pure (decode coins)) (residue + 1)
  have hsampler :
      coefficientSampler 2 (eta + 1) =
        (($ᵗ Coins) >>= fun coins ↦ pure (decode coins)) := by
    simp [coefficientSampler, Coins, decode, monad_norm]
  rw [hsampler]
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum] at hreindex ⊢
  calc
    (∑' coins : Coins,
        Pr[= coins | $ᵗ Coins] * Pr[= residue + 1 | pure (decode coins)]) =
      ∑' coins : Coins,
        Pr[= coins | $ᵗ Coins] *
          Pr[= residue + 1 | pure (decode (toggleHeadPositive coins))] :=
      hreindex.symm
    _ = ∑' coins : Coins,
        Pr[= coins | $ᵗ Coins] * Pr[= residue | pure (decode coins)] := by
      refine tsum_congr fun coins ↦ ?_
      congr 1
      have htoggle : decode (toggleHeadPositive coins) = decode coins + 1 :=
        signedWeight_toggleHeadPositive_mod_two coins
      rw [htoggle]
      by_cases hresidue : residue = decode coins
      · subst residue
        rw [probOutput_pure_self, probOutput_pure_self]
      · have hshift : residue + 1 ≠ decode coins + 1 := fun heq ↦
          hresidue (add_right_cancel heq)
        rw [probOutput_pure, probOutput_pure, if_neg hshift, if_neg hresidue]
    _ = ∑' coins : Coins,
        Pr[= coins | $ᵗ Coins] * Pr[= residue | pure (decode coins)] := rfl

/-- Canonical enumeration of the two coefficient residues. -/
def finTwoEquivZModTwo : Fin 2 ≃ ZMod 2 :=
  (ZMod.finEquiv 2).toEquiv

@[simp]
theorem finTwoEquivZModTwo_zero : finTwoEquivZModTwo 0 = 0 := rfl

@[simp]
theorem finTwoEquivZModTwo_one : finTwoEquivZModTwo 1 = 1 := rfl

/-- Every positive-width centered-binomial coefficient modulo two is exactly uniform. -/
theorem coefficientSampler_two_evalDist_eq_uniform (eta : ℕ) :
    evalDist (coefficientSampler 2 (eta + 1)) = evalDist ($ᵗ (ZMod 2)) := by
  let Sampler := coefficientSampler 2 (eta + 1)
  let mass := fun residue : ZMod 2 ↦ Pr[= residue | Sampler]
  have htranslate : mass 1 = mass 0 := by
    simpa [mass, Sampler] using
      (coefficientSampler_two_probOutput_add_one eta 0)
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
  have hzero : mass 0 = (2 : ENNReal)⁻¹ := by
    apply (ENNReal.toReal_eq_toReal_iff' probOutput_ne_top
      (ENNReal.inv_ne_top.mpr (by norm_num))).mp
    have hreal := congrArg ENNReal.toReal htwoMass
    have htranslateReal := congrArg ENNReal.toReal htranslate
    change (mass 1).toReal = (mass 0).toReal at htranslateReal
    rw [ENNReal.toReal_add probOutput_ne_top probOutput_ne_top,
      htranslateReal, ENNReal.toReal_one] at hreal
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofNat]
    norm_num at hreal ⊢
    linarith
  apply evalDist_ext
  intro residue
  obtain ⟨index, rfl⟩ := finTwoEquivZModTwo.surjective residue
  have hindex : index = 0 ∨ index = 1 := by omega
  rcases hindex with rfl | rfl
  · simpa [Sampler, mass, probOutput_uniformSample] using hzero
  · change Pr[= (1 : ZMod 2) | Sampler] =
      Pr[= (1 : ZMod 2) | $ᵗ (ZMod 2)]
    rw [show Pr[= (1 : ZMod 2) | Sampler] = mass 1 by rfl,
      htranslate, hzero]
    simp [probOutput_uniformSample]

/-! ## Complete ring sampler -/

/-- The ring sampler is the coefficientwise IID lift of `coefficientSampler`. -/
theorem sampler_evalDist_eq_coefficientSampler
    (q degree eta : ℕ) [NeZero q] :
    evalDist (sampler q degree eta) =
      evalDist (LatticeCrypto.Poly.ofPi <$>
        ProbComp.sampleIID degree (coefficientSampler q eta)) := by
  let Coins := CoinRow eta
  let decode := fun coins : Coins ↦ (signedWeight coins : ZMod q)
  let assemble : (Fin degree → ZMod q) → Rq q degree :=
    LatticeCrypto.Poly.ofPi
  have hcoins := FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
    (alpha := Coins) degree
  have hmapped := evalDist_map_eq_of_evalDist_eq hcoins.symm
    (fun coins : CoinTable degree eta ↦ errorFromCoins q degree eta coins)
  calc
    evalDist (sampler q degree eta) =
        evalDist (errorFromCoins q degree eta <$>
          ($ᵗ (CoinTable degree eta))) := by
      rw [sampler_eq_map_uniformCoins]
    _ = evalDist (errorFromCoins q degree eta <$>
          ProbComp.sampleIID degree ($ᵗ Coins)) := hmapped
    _ = evalDist (assemble <$>
          ((fun values index ↦ decode (values index)) <$>
            ProbComp.sampleIID degree ($ᵗ Coins))) := by
      have hfunction :
          (fun coins : CoinTable degree eta ↦
            errorFromCoins q degree eta coins) =
          assemble ∘ (fun values index ↦ decode (values index)) := by
        funext coins
        apply LatticeCrypto.Poly.ext_get_eq
        intro coefficient
        simp [assemble, decode, errorFromCoins]
      change evalDist
          ((fun coins : CoinTable degree eta ↦
              errorFromCoins q degree eta coins) <$>
            ProbComp.sampleIID degree ($ᵗ Coins)) = _
      rw [hfunction, Functor.map_map]
      rfl
    _ = evalDist (assemble <$>
          ProbComp.sampleIID degree (decode <$> ($ᵗ Coins))) := by
      have hpointwise :=
        FormalProof4FHE.FiniteProduct.map_fin_mOfFn_const
          degree ($ᵗ Coins) decode
      exact congrArg evalDist (congrArg (fun distribution ↦ assemble <$> distribution)
        hpointwise)
    _ = _ := by
      rfl

/-- A positive-width centered-binomial error polynomial modulo two is exactly uniform. -/
theorem sampler_two_evalDist_eq_uniform (degree eta : ℕ) :
    evalDist (sampler 2 degree (eta + 1)) =
      evalDist ($ᵗ (Rq 2 degree)) := by
  let assemble : (Fin degree → ZMod 2) → Rq 2 degree :=
    LatticeCrypto.Poly.ofPi
  have hcoefficients :=
    FormalProof4FHE.FiniteProduct.evalDist_fin_mOfFn_congr degree
      (fun _ ↦ coefficientSampler 2 (eta + 1))
      (fun _ ↦ ($ᵗ (ZMod 2)))
      (fun _ ↦ coefficientSampler_two_evalDist_eq_uniform eta)
  have hiidUniform :=
    FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
      (alpha := ZMod 2) degree
  have hassemble : Function.Bijective assemble := by
    apply Function.bijective_iff_has_inverse.mpr
    exact ⟨LatticeCrypto.Poly.toPi, LatticeCrypto.Poly.toPi_ofPi,
      LatticeCrypto.Poly.ofPi_toPi⟩
  calc
    evalDist (sampler 2 degree (eta + 1)) =
        evalDist (assemble <$>
          ProbComp.sampleIID degree (coefficientSampler 2 (eta + 1))) :=
      sampler_evalDist_eq_coefficientSampler 2 degree (eta + 1)
    _ = evalDist (assemble <$>
          ProbComp.sampleIID degree ($ᵗ (ZMod 2))) :=
      evalDist_map_eq_of_evalDist_eq hcoefficients assemble
    _ = evalDist (assemble <$> ($ᵗ (Fin degree → ZMod 2))) :=
      evalDist_map_eq_of_evalDist_eq hiidUniform assemble
    _ = evalDist ($ᵗ (Rq 2 degree)) :=
      evalDist_map_bijective_uniform_cross
        (α := Fin degree → ZMod 2) (β := Rq 2 degree)
        assemble hassemble

end

end FormalProof4FHE.RLWE.CenteredBinomial
