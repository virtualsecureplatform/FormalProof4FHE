/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.RecursiveFeatureSecurityParameters

/-!
# An ordinary-LWE hop in the actual stored-control security layout

The quadratic compiler is connected to the same stored public-key/control type
and complete IND-CPA observer as the actual cubic generator. Replacing the real
controls by a fixed quadratic-message batch leaves an explicit replacement
advantage; the resulting quadratic game reduces to the existing ordinary-LWE
source, with the proved implementation and statistical masking losses.

No negligibility of the control replacement is assumed. This is a component of
the requested security proof, not a completed ordinary-LWE-only FHE theorem.
-/

open Matrix OracleComp AsymmEncAlg

namespace FormalProof4FHE.LWE.RecursiveFeatureControlHybrid

open RecursiveMultiplication RecursiveFeatureGSW RecursiveFeatureBootstrap
open RecursiveFeatureSecurityView

abbrev controlCount {q : ℕ} (params : Parameters q) (n : ℕ) : ℕ := n * (rows n * params.levels)

abbrev ControlPolynomial {q : ℕ} (params : Parameters q) (n : ℕ) :=
  RecursiveQuadratic.Polynomial (ZMod q) n (controlCount params n)

noncomputable local instance {q : ℕ} [NeZero q] (params : Parameters q) (n p : ℕ) :
    SampleableType (Challenge params n p) := instSampleableTypeFinFunc

def bridgeView {q n p : ℕ} (params : Parameters q)
    (view : RecursiveFeaturePublicKey.View q n 0 p (controlCount params n)) : View params n p :=
  (view.1, storeOriginal params (fun index column ↦ view.2.2 (finProdFinEquiv (index, column))))

def viewWithPolynomial {q n p : ℕ} [NeZero q] (params : Parameters q)
    (polynomial : ControlPolynomial params n) (draws : Draws params n p) : View params n p :=
  (publicTable params draws, storeOriginal params (fun index column ↦
    freshCiphertext (GSWSelfKey.binaryEmbed draws.1)
      (RecursiveQuadratic.message polynomial (GSWSelfKey.binaryEmbed draws.1) (finProdFinEquiv (index, column)))
      (maskAt params draws.2.1 (controlColumn params index column))
      (innerAt params draws.2.1 (controlColumn params index column))
      (errorsAt params draws.2.2 (controlColumn params index column))
      (bodyErrorAt params draws.2.2 (controlColumn params index column)) ))

noncomputable def keyViewWithPolynomial {q n p : ℕ} [NeZero q] (params : Parameters q)
    (polynomial : ControlPolynomial params n) (secretSampler : ProbComp (Fin n → Bool))
    (errorSampler : ProbComp (ZMod q)) : ProbComp (View params n p) :=
  viewWithPolynomial params polynomial <$> sampleDraws params secretSampler errorSampler

theorem joinedPolynomial_tail_message {q n p k : ℕ}
    (polynomial : RecursiveQuadratic.Polynomial (ZMod q) n k) (secret : Fin n → ZMod q) (index : Fin k) :
    RecursiveQuadratic.message (RecursiveFeaturePublicKey.joinedPolynomial (p := p) polynomial)
      secret (finSumFinEquiv (.inr index)) = RecursiveQuadratic.message polynomial secret index := by
  simp [RecursiveQuadratic.message, RecursiveFeaturePublicKey.joinedPolynomial]

theorem fresh_column_eq_freshCiphertext {q n k : ℕ} [NeZero q]
    (polynomial : RecursiveQuadratic.Polynomial (ZMod q) n k) (secret : Fin n → ZMod q)
    (challenge : Matrix (Fin n) (RecursiveQuadratic.Column n 0 k) (ZMod q))
    (errors : RecursiveQuadratic.Column n 0 k → ZMod q) (index : Fin k) :
    (RecursiveQuadratic.fresh polynomial secret challenge errors).2 index =
      freshCiphertext secret (RecursiveQuadratic.message polynomial secret index)
        (fun row column ↦ challenge row (.inr (index, some column)))
        (fun row ↦ challenge row (.inr (index, none)))
        (fun row ↦ errors (.inr (index, some row))) (errors (.inr (index, none))) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext row
      simp only [RecursiveQuadratic.fresh, RecursiveQuadratic.project, freshCiphertext,
        vecMul, dotProduct, Pi.add_apply, Pi.sub_apply]
      ring
    · change dotProduct secret (fun row ↦ challenge row (.inr (index, none))) +
        errors (.inr (index, none)) + RecursiveQuadratic.message polynomial secret index =
        dotProduct (fun row ↦ challenge row (.inr (index, none))) secret +
          RecursiveQuadratic.message polynomial secret index + errors (.inr (index, none))
      rw [dotProduct_comm]
      ring

theorem bridge_fresh {q n p : ℕ} [NeZero q] (params : Parameters q)
    (polynomial : ControlPolynomial params n) (draws : Draws params n p) :
    bridgeView params (RecursiveFeaturePublicKey.publish
      (RecursiveQuadratic.fresh (RecursiveFeaturePublicKey.joinedPolynomial polynomial)
        (GSWSelfKey.binaryEmbed draws.1) draws.2.1 draws.2.2)) =
      viewWithPolynomial params polynomial draws := by
  apply Prod.ext
  · funext index
    change flatten ((RecursiveQuadratic.fresh _ _ _ _).2 (finSumFinEquiv (.inl index))) = _
    rw [fresh_column_eq_freshCiphertext, RecursiveFeaturePublicKey.joinedPolynomial_zero_message]
    rfl
  · change storeOriginal params (fun index column ↦
        (RecursiveQuadratic.fresh _ _ _ _).2 (finSumFinEquiv (.inr (finProdFinEquiv (index, column))))) = _
    simp_rw [fresh_column_eq_freshCiphertext, joinedPolynomial_tail_message]
    rfl

set_option maxHeartbeats 800000 in
theorem quadratic_keyView_evalDist {q n p : ℕ} [NeZero q] (params : Parameters q)
    (polynomial : ControlPolynomial params n) (secretSampler : ProbComp (Fin n → Bool))
    (errorSampler : ProbComp (ZMod q)) :
    𝒟[keyViewWithPolynomial (p := p) params polynomial secretSampler errorSampler] =
      𝒟[bridgeView params <$> RecursiveFeaturePublicKey.freshView
        (errorColumnsEquiv params n p) polynomial (GSWSelfKey.binaryEmbed <$> secretSampler) errorSampler] := by
  have hfresh (bits : Fin n → Bool) (challenge : Challenge params n p) (errors : Errors params n p) :
      bridgeView params (RecursiveFeaturePublicKey.publish
        (RecursiveQuadratic.fresh (RecursiveFeaturePublicKey.joinedPolynomial polynomial)
          (GSWSelfKey.binaryEmbed bits) challenge errors)) =
        viewWithPolynomial params polynomial (bits, challenge, errors) :=
    bridge_fresh (n := n) (p := p) params polynomial (bits, challenge, errors)
  simp [keyViewWithPolynomial, RecursiveFeaturePublicKey.freshView, RecursiveQuadratic.freshView,
    sampleDraws, hfresh, monad_norm]
  rfl

def sourceAdversary {q n p : ℕ} [NeZero q] (params : Parameters q)
    (adversary : GSWMasking.Adversary (dimension := Dimension n) (samples := p) params (StoredOriginal params n)) :
    RecursiveFeaturePublicKey.Adversary (n := n) (r := 0) (p := p) (k := controlCount params n) params where
  State := adversary.State
  chooseMessages := fun view ↦ adversary.chooseMessages
    (view.1, storeOriginal params (fun index column ↦ view.2.2 (finProdFinEquiv (index, column))))
  distinguish := adversary.distinguish

theorem game_bridge_evalDist {q n p : ℕ} [NeZero q] (params : Parameters q)
    (sampler : ProbComp (RecursiveFeaturePublicKey.View q n 0 p (controlCount params n)))
    (adversary : GSWMasking.Adversary (dimension := Dimension n) (samples := p) params (StoredOriginal params n)) :
    𝒟[GSWMasking.game params (bridgeView params <$> sampler) adversary] =
      𝒟[GSWMasking.game params sampler (sourceAdversary params adversary)] := by
  simp [GSWMasking.game, bridgeView, sourceAdversary, monad_norm]

theorem blockBits_uniform_evalDist (n : ℕ) :
    𝒟[FormalProof4FHE.BlockBinary.bits <$> ($ᵗ FormalProof4FHE.BlockBinary.Key 1 n)] =
      𝒟[$ᵗ (Fin (n * 1) → Bool)] := by
  have hbijective : Function.Bijective (FormalProof4FHE.BlockBinary.bits (blockLength := 1) (blockCount := n)) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨FormalProof4FHE.BlockBinary.bits_injective 1 n, by simp [FormalProof4FHE.BlockBinary.Key]⟩
  exact evalDist_map_bijective_uniform_cross
    (α := FormalProof4FHE.BlockBinary.Key 1 n) (β := Fin (n * 1) → Bool)
    FormalProof4FHE.BlockBinary.bits hbijective

theorem quadratic_keyView_secret_congr {q n p : ℕ} [NeZero q] (params : Parameters q)
    (polynomial : ControlPolynomial params n) (first second : ProbComp (Fin n → Bool))
    (errorSampler : ProbComp (ZMod q)) (hsecret : 𝒟[first] = 𝒟[second]) :
    𝒟[keyViewWithPolynomial (p := p) params polynomial first errorSampler] =
      𝒟[keyViewWithPolynomial params polynomial second errorSampler] := by
  let finish := fun bits : Fin n → Bool ↦ do
    let challenge ← $ᵗ Challenge params n p
    let errors ← ProbComp.sampleIID (errorCount params n p) errorSampler
    pure (viewWithPolynomial params polynomial (bits, challenge,
      fun column ↦ errors (errorColumnsEquiv params n p column)))
  simpa [keyViewWithPolynomial, sampleDraws, finish, monad_norm] using
    FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hsecret finish

def observe {q n p : ℕ} [NeZero q] (params : Parameters q)
    (adversary : GSWMasking.Adversary (dimension := Dimension n) (samples := p) params (StoredOriginal params n))
    (view : View params n p) : ProbComp Bool := do
  let bit ← $ᵗ Bool
  let messages ← adversary.chooseMessages (GSWMasking.storeTable view.1, view.2)
  let ciphertext ← GSWMasking.encrypt params view.1 (if bit then messages.1 else messages.2.1)
  let guess ← adversary.distinguish messages.2.2 ciphertext
  pure (bit == guess)

theorem game_eq_bind {q n p : ℕ} [NeZero q] (params : Parameters q)
    (sampler : ProbComp (View params n p))
    (adversary : GSWMasking.Adversary (dimension := Dimension n) (samples := p) params (StoredOriginal params n)) :
    GSWMasking.game params sampler adversary = sampler >>= observe params adversary := rfl

open RecursiveQuadraticParameters

noncomputable def quadraticOrdinaryLoss {p : ℕ} (parameter : ℕ) (params : Parameters (modulus parameter))
    (polynomial : ControlPolynomial params (binaryDimension parameter * 1))
    (adversary : GSWMasking.Adversary (dimension := Dimension (binaryDimension parameter * 1))
      (samples := p) params (StoredOriginal params (binaryDimension parameter * 1))) : ℝ :=
  ordinaryReductionLoss parameter (errorColumnsEquiv params (binaryDimension parameter * 1) p)
    (RecursiveFeaturePublicKey.joinedPolynomial polynomial)
    (fun original ↦ RecursiveFeaturePublicKey.observe params (sourceAdversary params adversary)
      (RecursiveFeaturePublicKey.publish original))

theorem quadratic_game_abs_advantage_le {p : ℕ} (parameter : ℕ) (params : Parameters (modulus parameter))
    (polynomial : ControlPolynomial params (binaryDimension parameter * 1))
    (adversary : GSWMasking.Adversary (dimension := Dimension (binaryDimension parameter * 1))
      (samples := p) params (StoredOriginal params (binaryDimension parameter * 1))) :
    |Pr[= true | GSWMasking.game params
      (keyViewWithPolynomial params polynomial ($ᵗ (Fin (binaryDimension parameter * 1) → Bool))
        (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter))) adversary].toReal - 1 / 2| ≤
      quadraticOrdinaryLoss parameter params polynomial adversary +
        implementationLoss (errorCount params (binaryDimension parameter * 1) p) parameter +
        ((Dimension (binaryDimension parameter * 1) + 1) * params.levels) *
          (Real.sqrt ((modulus parameter : ℝ) ^ (Dimension (binaryDimension parameter * 1) + 1) / (2 : ℝ) ^ p) / 2) := by
  have hkey := (quadratic_keyView_secret_congr (p := p) params polynomial
    ($ᵗ (Fin (binaryDimension parameter * 1) → Bool))
    (FormalProof4FHE.BlockBinary.bits <$> ($ᵗ FormalProof4FHE.BlockBinary.Key 1 (binaryDimension parameter)))
    (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter))
    (blockBits_uniform_evalDist (binaryDimension parameter)).symm).trans
      (quadratic_keyView_evalDist params polynomial _ _)
  have hkey' := hkey
  simp only [Functor.map_map] at hkey'
  have hembed :
      (fun key : FormalProof4FHE.BlockBinary.Key 1 (binaryDimension parameter) ↦ GSWSelfKey.binaryEmbed (R := ZMod (modulus parameter))
        (FormalProof4FHE.BlockBinary.bits key)) = FormalProof4FHE.BlockBinary.expand (ZMod (modulus parameter)) := rfl
  rw [hembed] at hkey'
  have hgame := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hkey' (observe params adversary)
  have hbridge := game_bridge_evalDist params
    (RecursiveFeaturePublicKey.freshView (errorColumnsEquiv params (binaryDimension parameter * 1) p) polynomial
      (FormalProof4FHE.BlockBinary.expand (ZMod (modulus parameter)) <$>
        ($ᵗ FormalProof4FHE.BlockBinary.Key 1 (binaryDimension parameter)))
      (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter))) adversary
  have hbound := RecursiveFeaturePublicKey.sampled_game_abs_advantage_le parameter params
    (errorColumnsEquiv params (binaryDimension parameter * 1) p) polynomial (sourceAdversary params adversary)
  have heq : 𝒟[GSWMasking.game params
      (keyViewWithPolynomial params polynomial ($ᵗ (Fin (binaryDimension parameter * 1) → Bool))
        (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter))) adversary] =
      𝒟[GSWMasking.game params
        (RecursiveFeaturePublicKey.freshView (errorColumnsEquiv params (binaryDimension parameter * 1) p) polynomial
          (FormalProof4FHE.BlockBinary.expand (ZMod (modulus parameter)) <$>
            ($ᵗ FormalProof4FHE.BlockBinary.Key 1 (binaryDimension parameter)))
          (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter)))
        (sourceAdversary params adversary)] := by
    refine Eq.trans ?_ hbridge
    simpa only [game_eq_bind] using hgame
  rw [probOutput_congr (rfl : true = true) heq]
  exact hbound

/-- The real control replacement is an explicit experiment, not a hardness premise. -/
noncomputable def controlReplacementAdvantage {q n p : ℕ} [NeZero q] (params : Parameters q)
    (polynomial : ControlPolynomial params n) (secretSampler : ProbComp (Fin n → Bool))
    (errorSampler : ProbComp (ZMod q))
    (adversary : GSWMasking.Adversary (dimension := Dimension n) (samples := p) params (StoredOriginal params n)) : ℝ :=
  |Pr[= true | GSWMasking.game params (keyView params secretSampler errorSampler) adversary].toReal -
    Pr[= true | GSWMasking.game params (keyViewWithPolynomial params polynomial secretSampler errorSampler) adversary].toReal|

/-- The computational ordinary-LWE part covers the same complete stored-view observer;
the cubic-control replacement term remains to be proved small. -/
theorem actual_oneTime_abs_signedAdvantage_le {p : ℕ} (parameter : ℕ) (params : Parameters (modulus parameter))
    (level : Fin params.levels) (polynomial : ControlPolynomial params (binaryDimension parameter * 1))
    (adversary : IND_CPA_Adv (scheme (p := p) params level ($ᵗ (Fin (binaryDimension parameter * 1) → Bool))
      (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter)))) :
    let observer := fromINDCPA params level ($ᵗ (Fin (binaryDimension parameter * 1) → Bool))
      (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter)) adversary
    |IND_CPA_OneTime_signedAdvantageReal
      (scheme params level ($ᵗ (Fin (binaryDimension parameter * 1) → Bool))
        (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter))) adversary| ≤
      controlReplacementAdvantage params polynomial ($ᵗ (Fin (binaryDimension parameter * 1) → Bool))
        (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter)) observer +
        quadraticOrdinaryLoss parameter params polynomial observer +
        implementationLoss (errorCount params (binaryDimension parameter * 1) p) parameter +
        ((Dimension (binaryDimension parameter * 1) + 1) * params.levels) *
          (Real.sqrt ((modulus parameter : ℝ) ^ (Dimension (binaryDimension parameter * 1) + 1) / (2 : ℝ) ^ p) / 2) := by
  dsimp only
  have hgame := oneTime_game_evalDist params level ($ᵗ (Fin (binaryDimension parameter * 1) → Bool))
    (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter)) adversary
  have hbound := quadratic_game_abs_advantage_le parameter params polynomial
    (fromINDCPA params level ($ᵗ (Fin (binaryDimension parameter * 1) → Bool))
      (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter)) adversary)
  unfold IND_CPA_OneTime_signedAdvantageReal
  rw [probOutput_congr (rfl : true = true) hgame]
  have htriangle := abs_sub_le
    (Pr[= true | GSWMasking.game params
      (keyView params ($ᵗ (Fin (binaryDimension parameter * 1) → Bool))
        (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter)))
      (fromINDCPA params level ($ᵗ (Fin (binaryDimension parameter * 1) → Bool))
        (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter)) adversary)].toReal)
    (Pr[= true | GSWMasking.game params
      (keyViewWithPolynomial params polynomial ($ᵗ (Fin (binaryDimension parameter * 1) → Bool))
        (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter)))
      (fromINDCPA params level ($ᵗ (Fin (binaryDimension parameter * 1) → Bool))
        (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter)) adversary)].toReal)
    (1 / 2 : ℝ)
  unfold controlReplacementAdvantage
  linarith

end FormalProof4FHE.LWE.RecursiveFeatureControlHybrid
