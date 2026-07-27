/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.RankOneHNFLossinessRLWENTRU

/-!
# Refined Rank-One HNF Lossiness

This module formalizes the finite algebraic and probability-theoretic refinements from
`sketch/rank_one_hnf_lossiness_refined.tex`.

It proves the exact product-cancellation normal form under complete leakage, transports
conditional guessing probability through the resulting public bijection, proves the
leakage-dependent coefficient translation reduction, and develops finite-support maximal-leakage
and sequential coherent-RNS guessing bounds.

The determinant entropy lemma, subgaussian concentration, canonical-embedding diagonalization,
lattice discrete-Gaussian decomposition, and Stehlé--Steinfeld ratio theorem require analysis not
present in the finite `ProbComp` library.  Their exact conclusions and numeric hypotheses are
exposed below as proof-carrying certificates; the finite Fano arithmetic is proved natively and no
new axiom is introduced.
-/

open OracleComp

namespace FormalProof4FHE.RLWE.RankOneHNFLossinessRefined

open RankOneHNFLossinessRLWENTRU

noncomputable section

/-! ## Exact invariance of guessing probability under public side equivalences -/

/-- Apply an equivalence only to the public side of a joint secret/side sampler. -/
def mapJointSide
    {Secret Side Side' : Type} (equiv : Side ≃ Side')
    (joint : ProbComp (Secret × Side)) : ProbComp (Secret × Side') :=
  (fun value ↦ (value.1, equiv value.2)) <$> joint

/-- A side equivalence is absorbed exactly by precomposing the estimator. -/
theorem guessingSuccess_mapJointSide
    {Secret Side Side' : Type} [DecidableEq Secret]
    (equiv : Side ≃ Side') (joint : ProbComp (Secret × Side))
    (estimator : Estimator Secret Side') :
    guessingSuccess (mapJointSide equiv joint) estimator =
      guessingSuccess joint (fun side ↦ estimator (equiv side)) := by
  unfold guessingSuccess guessingGame mapJointSide
  apply probOutput_congr rfl
  simp [map_eq_bind_pure_comp, bind_assoc]

/-- Operational conditional guessing probability is invariant under any public bijection of the
complete side information. -/
theorem conditionalGuessingProbability_mapJointSide
    {Secret Side Side' : Type} [DecidableEq Secret]
    (equiv : Side ≃ Side') (joint : ProbComp (Secret × Side)) :
    conditionalGuessingProbability (mapJointSide equiv joint) =
      conditionalGuessingProbability joint := by
  apply le_antisymm
  · apply iSup_le
    intro estimator
    rw [guessingSuccess_mapJointSide]
    exact guessingSuccess_le_conditionalGuessingProbability _ _
  · apply iSup_le
    intro estimator
    have h := guessingSuccess_mapJointSide equiv joint
      (fun side' ↦ estimator (equiv.symm side'))
    have hSuccess :
        guessingSuccess joint estimator =
          guessingSuccess (mapJointSide equiv joint)
            (fun side' ↦ estimator (equiv.symm side')) := by
      simpa using h.symm
    rw [hSuccess]
    exact guessingSuccess_le_conditionalGuessingProbability _ _

/-- Conditional guessing probability depends only on the joint output distribution. -/
theorem conditionalGuessingProbability_congr
    {Secret Side : Type} [DecidableEq Secret]
    {left right : ProbComp (Secret × Side)} (h : evalDist left = evalDist right) :
    conditionalGuessingProbability left = conditionalGuessingProbability right := by
  have success_congr : ∀ estimator : Estimator Secret Side,
      guessingSuccess left estimator = guessingSuccess right estimator := by
    intro estimator
    unfold guessingSuccess guessingGame
    apply probOutput_congr rfl
    rw [evalDist_bind, h, ← evalDist_bind]
  simp only [conditionalGuessingProbability, success_congr]

/-! ## Exact product-cancellation normal form -/

/-- The entropic channel before cancellation:
`Y_j=a_j*S+sum_r F_jr*G_jr+H_j`. -/
def productCancellationChannel
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (latent : QuadraticKDM.Latent R Row Factor) (coefficient : Row → R) :
    QuadraticKDM.TargetTranscript R Row :=
  (coefficient, fun row ↦
    coefficient row * latent.secret + QuadraticKDM.terminalError latent row)

/-- Subtract the complete leakage corrections `(K,P)` from a coefficient/body channel. -/
def normalizeProductChannel
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : QuadraticKDM.Gadget R Row Factor)
    (leakage : QuadraticKDM.Leakage R Row Factor)
    (channel : QuadraticKDM.TargetTranscript R Row) :
    QuadraticKDM.TargetTranscript R Row :=
  (fun row ↦ channel.1 row - QuadraticKDM.linearCorrection gadget leakage row,
    fun row ↦ channel.2 row - QuadraticKDM.productCorrection leakage row)

/-- Inverse public affine map adding `(K,P)` back to a normalized channel. -/
def denormalizeProductChannel
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : QuadraticKDM.Gadget R Row Factor)
    (leakage : QuadraticKDM.Leakage R Row Factor)
    (channel : QuadraticKDM.TargetTranscript R Row) :
    QuadraticKDM.TargetTranscript R Row :=
  (fun row ↦ channel.1 row + QuadraticKDM.linearCorrection gadget leakage row,
    fun row ↦ channel.2 row + QuadraticKDM.productCorrection leakage row)

@[simp]
theorem denormalizeProductChannel_normalizeProductChannel
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : QuadraticKDM.Gadget R Row Factor)
    (leakage : QuadraticKDM.Leakage R Row Factor)
    (channel : QuadraticKDM.TargetTranscript R Row) :
    denormalizeProductChannel gadget leakage
      (normalizeProductChannel gadget leakage channel) = channel := by
  apply Prod.ext <;> funext row <;>
    simp [normalizeProductChannel, denormalizeProductChannel]

@[simp]
theorem normalizeProductChannel_denormalizeProductChannel
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : QuadraticKDM.Gadget R Row Factor)
    (leakage : QuadraticKDM.Leakage R Row Factor)
    (channel : QuadraticKDM.TargetTranscript R Row) :
    normalizeProductChannel gadget leakage
      (denormalizeProductChannel gadget leakage channel) = channel := by
  apply Prod.ext <;> funext row <;>
    simp [normalizeProductChannel, denormalizeProductChannel]

/-- For fixed complete leakage, subtraction of `(K,P)` is an explicit bijection. -/
def productChannelEquiv
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : QuadraticKDM.Gadget R Row Factor)
    (leakage : QuadraticKDM.Leakage R Row Factor) :
    QuadraticKDM.TargetTranscript R Row ≃ QuadraticKDM.TargetTranscript R Row where
  toFun := normalizeProductChannel gadget leakage
  invFun := denormalizeProductChannel gadget leakage
  left_inv := denormalizeProductChannel_normalizeProductChannel gadget leakage
  right_inv := normalizeProductChannel_denormalizeProductChannel gadget leakage

/-- Exact refined normal form under complete leakage:
`(a,Y) ↦ (A,B)=(a-K,Y-P)` and `B=A*S+g*S^2+H`. -/
theorem normalizeProductCancellationChannel
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : QuadraticKDM.Gadget R Row Factor)
    (latent : QuadraticKDM.Latent R Row Factor) (coefficient : Row → R) :
    normalizeProductChannel gadget (QuadraticKDM.publicLeakage gadget latent)
        (productCancellationChannel latent coefficient) =
      QuadraticKDM.kdmTranscript gadget latent
        (fun row ↦ coefficient row -
          QuadraticKDM.linearCorrection gadget
            (QuadraticKDM.publicLeakage gadget latent) row) := by
  apply Prod.ext
  · rfl
  · funext row
    simp only [normalizeProductChannel, productCancellationChannel,
      QuadraticKDM.kdmTranscript, QuadraticKDM.terminalError]
    rw [QuadraticKDM.linearCorrection_publicLeakage,
      QuadraticKDM.productCorrection_publicLeakage]
    ring

/-- Apply product cancellation to the coefficient and body fields while retaining every other
piece of public side information. -/
def normalizeProductLossySide
    {R Row Factor Descriptor : Type} [CommRing R] [Fintype Factor]
    (gadget : QuadraticKDM.Gadget R Row Factor)
    (side : LossySide R Row (QuadraticKDM.Leakage R Row Factor) Descriptor) :
    LossySide R Row (QuadraticKDM.Leakage R Row Factor) Descriptor where
  leakage := side.leakage
  descriptor := side.descriptor
  coefficient := (normalizeProductChannel gadget side.leakage
    (side.coefficient, side.sample)).1
  sample := (normalizeProductChannel gadget side.leakage
    (side.coefficient, side.sample)).2

/-- Inverse side transformation, adding the public corrections back. -/
def denormalizeProductLossySide
    {R Row Factor Descriptor : Type} [CommRing R] [Fintype Factor]
    (gadget : QuadraticKDM.Gadget R Row Factor)
    (side : LossySide R Row (QuadraticKDM.Leakage R Row Factor) Descriptor) :
    LossySide R Row (QuadraticKDM.Leakage R Row Factor) Descriptor where
  leakage := side.leakage
  descriptor := side.descriptor
  coefficient := (denormalizeProductChannel gadget side.leakage
    (side.coefficient, side.sample)).1
  sample := (denormalizeProductChannel gadget side.leakage
    (side.coefficient, side.sample)).2

@[simp]
theorem denormalizeProductLossySide_normalizeProductLossySide
    {R Row Factor Descriptor : Type} [CommRing R] [Fintype Factor]
    (gadget : QuadraticKDM.Gadget R Row Factor)
    (side : LossySide R Row (QuadraticKDM.Leakage R Row Factor) Descriptor) :
    denormalizeProductLossySide gadget (normalizeProductLossySide gadget side) = side := by
  cases side
  simp [normalizeProductLossySide, denormalizeProductLossySide,
    normalizeProductChannel, denormalizeProductChannel]

@[simp]
theorem normalizeProductLossySide_denormalizeProductLossySide
    {R Row Factor Descriptor : Type} [CommRing R] [Fintype Factor]
    (gadget : QuadraticKDM.Gadget R Row Factor)
    (side : LossySide R Row (QuadraticKDM.Leakage R Row Factor) Descriptor) :
    normalizeProductLossySide gadget (denormalizeProductLossySide gadget side) = side := by
  cases side
  simp [normalizeProductLossySide, denormalizeProductLossySide,
    normalizeProductChannel, denormalizeProductChannel]

/-- The complete public product-cancellation map is an equivalence on lossy side information. -/
def productLossySideEquiv
    {R Row Factor Descriptor : Type} [CommRing R] [Fintype Factor]
    (gadget : QuadraticKDM.Gadget R Row Factor) :
    LossySide R Row (QuadraticKDM.Leakage R Row Factor) Descriptor ≃
      LossySide R Row (QuadraticKDM.Leakage R Row Factor) Descriptor where
  toFun := normalizeProductLossySide gadget
  invFun := denormalizeProductLossySide gadget
  left_inv := denormalizeProductLossySide_normalizeProductLossySide gadget
  right_inv := normalizeProductLossySide_denormalizeProductLossySide gadget

/-- Revealing the complete leakage and applying `(a,Y) ↦ (a-K,Y-P)` preserves the exact
operational guessing probability. -/
theorem conditionalGuessingProbability_normalizeProductLossySide
    {R Row Factor Descriptor : Type} [CommRing R] [Fintype Factor] [DecidableEq R]
    (gadget : QuadraticKDM.Gadget R Row Factor)
    (joint : ProbComp
      (R × LossySide R Row (QuadraticKDM.Leakage R Row Factor) Descriptor)) :
    conditionalGuessingProbability
        (mapJointSide (productLossySideEquiv gadget) joint) =
      conditionalGuessingProbability joint :=
  conditionalGuessingProbability_mapJointSide (productLossySideEquiv gadget) joint

/-- Pointwise side-information version of the exact product-cancellation normal form. -/
theorem normalizeProductLossySide_explicit
    {R Row Factor Descriptor : Type} [CommRing R] [Fintype Factor]
    (gadget : QuadraticKDM.Gadget R Row Factor)
    (latent : QuadraticKDM.Latent R Row Factor) (descriptor : Descriptor)
    (coefficient : Row → R) :
    normalizeProductLossySide gadget
        { leakage := QuadraticKDM.publicLeakage gadget latent
          descriptor := descriptor
          coefficient := coefficient
          sample := (productCancellationChannel latent coefficient).2 } =
      { leakage := QuadraticKDM.publicLeakage gadget latent
        descriptor := descriptor
        coefficient := fun row ↦ coefficient row -
          QuadraticKDM.linearCorrection gadget
            (QuadraticKDM.publicLeakage gadget latent) row
        sample := (QuadraticKDM.kdmTranscript gadget latent
          (fun row ↦ coefficient row -
            QuadraticKDM.linearCorrection gadget
              (QuadraticKDM.publicLeakage gadget latent) row)).2 } := by
  have h := normalizeProductCancellationChannel gadget latent coefficient
  simp only [normalizeProductLossySide]
  congr 1
  simpa [productCancellationChannel] using congrArg Prod.snd h

/-! ## Leakage-dependent coefficient translation -/

/-- A coefficient game which reveals a separately sampled public context. -/
def contextualCoefficientGame
    {Context Coefficient : Type}
    (contextSampler : ProbComp Context) (coefficientSampler : ProbComp Coefficient)
    (distinguisher : Context × Coefficient → ProbComp Bool) : ProbComp Bool := do
  let context ← contextSampler
  let coefficient ← coefficientSampler
  distinguisher (context, coefficient)

/-- Translate coefficients by a public, context-dependent shift before invoking a distinguisher. -/
def shiftedContextualCoefficientGame
    {Context Coefficient Descriptor : Type} [Add Coefficient]
    (contextSampler : ProbComp Context)
    (family : ProbComp (Descriptor × Coefficient))
    (shift : Context → Coefficient)
    (distinguisher : Context × Coefficient → ProbComp Bool) : ProbComp Bool := do
  let context ← contextSampler
  let descriptorAndCoefficient ← family
  distinguisher (context, shift context + descriptorAndCoefficient.2)

/-- Reduction which adds the public shift before forwarding its input. -/
def addShiftDistinguisher
    {Context Coefficient : Type} [Add Coefficient]
    (shift : Context → Coefficient)
    (distinguisher : Context × Coefficient → ProbComp Bool) :
    Context × Coefficient → ProbComp Bool :=
  fun input ↦ distinguisher (input.1, shift input.1 + input.2)

/-- The shifted real game is definitionally the unshifted public-family game against the
translated distinguisher. -/
theorem shiftedContextualCoefficientGame_eq_reduction
    {Context Coefficient Descriptor : Type} [Add Coefficient]
    (contextSampler : ProbComp Context)
    (family : ProbComp (Descriptor × Coefficient))
    (shift : Context → Coefficient)
    (distinguisher : Context × Coefficient → ProbComp Bool) :
    shiftedContextualCoefficientGame contextSampler family shift distinguisher =
      contextualCoefficientGame contextSampler (Prod.snd <$> family)
        (addShiftDistinguisher shift distinguisher) := by
  simp [shiftedContextualCoefficientGame, contextualCoefficientGame,
    addShiftDistinguisher, map_eq_bind_pure_comp, bind_assoc]

/-- For every fixed public context, translation preserves the uniform coefficient law. -/
theorem shiftedUniformContextualCoefficientGame_evalDist
    {Context Coefficient : Type} [AddGroup Coefficient]
    [Fintype Coefficient] [SampleableType Coefficient]
    (contextSampler : ProbComp Context) (shift : Context → Coefficient)
    (distinguisher : Context × Coefficient → ProbComp Bool) :
    evalDist (contextualCoefficientGame contextSampler ($ᵗ Coefficient)
      (addShiftDistinguisher shift distinguisher)) =
    evalDist (contextualCoefficientGame contextSampler ($ᵗ Coefficient)
      distinguisher) := by
  refine evalDist_bind_congr' contextSampler fun context ↦ ?_
  change evalDist (($ᵗ Coefficient) >>= fun coefficient ↦
      distinguisher (context, shift context + coefficient)) =
    evalDist (($ᵗ Coefficient) >>= fun coefficient ↦
      distinguisher (context, coefficient))
  calc
    evalDist (($ᵗ Coefficient) >>= fun coefficient ↦
        distinguisher (context, shift context + coefficient)) =
      evalDist (((shift context + ·) <$> ($ᵗ Coefficient)) >>= fun coefficient ↦
        distinguisher (context, coefficient)) := by
          simp [map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist (($ᵗ Coefficient) >>= fun coefficient ↦
        distinguisher (context, coefficient)) := by
      rw [evalDist_bind, evalDist_add_left_uniform, ← evalDist_bind]

/-- Exact advantage preservation for the leakage-shifted family.  Thus a distinguisher for
`(Lambda,K(Lambda)+a)` gives one with the same advantage for `(Lambda,a)`. -/
theorem shiftedContextualCoefficientAdvantage_eq
    {Context Coefficient Descriptor : Type} [AddGroup Coefficient]
    [Fintype Coefficient] [SampleableType Coefficient]
    (contextSampler : ProbComp Context)
    (family : ProbComp (Descriptor × Coefficient))
    (shift : Context → Coefficient)
    (distinguisher : Context × Coefficient → ProbComp Bool) :
    (contextualCoefficientGame contextSampler ($ᵗ Coefficient) distinguisher).boolDistAdvantage
        (shiftedContextualCoefficientGame contextSampler family shift distinguisher) =
      (contextualCoefficientGame contextSampler ($ᵗ Coefficient)
          (addShiftDistinguisher shift distinguisher)).boolDistAdvantage
        (contextualCoefficientGame contextSampler (Prod.snd <$> family)
          (addShiftDistinguisher shift distinguisher)) := by
  unfold ProbComp.boolDistAdvantage
  rw [shiftedContextualCoefficientGame_eq_reduction]
  have hUniform :
      Pr[= true | contextualCoefficientGame contextSampler ($ᵗ Coefficient) distinguisher] =
        Pr[= true | contextualCoefficientGame contextSampler ($ᵗ Coefficient)
          (addShiftDistinguisher shift distinguisher)] :=
    probOutput_congr rfl
      (shiftedUniformContextualCoefficientGame_evalDist
        contextSampler shift distinguisher).symm
  rw [hUniform]

/-- After subtracting the same leakage-dependent shift, the lossy coefficient is exactly the
base coefficient selected independently of the leakage. -/
@[simp]
theorem subtract_shiftedCoefficient
    {Coefficient : Type} [AddCommGroup Coefficient] (shift base : Coefficient) :
    shift + base - shift = base := by
  abel

/-- Specializing the actual coefficient to `K(Λ)+aTilde` makes the normalized coefficient
definitionally equal to `aTilde`, as required by the shifted-family lemma. -/
theorem normalize_leakageShiftedProductChannel
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : QuadraticKDM.Gadget R Row Factor)
    (latent : QuadraticKDM.Latent R Row Factor) (baseCoefficient : Row → R) :
    normalizeProductChannel gadget (QuadraticKDM.publicLeakage gadget latent)
        (productCancellationChannel latent
          (fun row ↦ QuadraticKDM.linearCorrection gadget
            (QuadraticKDM.publicLeakage gadget latent) row + baseCoefficient row)) =
      QuadraticKDM.kdmTranscript gadget latent baseCoefficient := by
  rw [normalizeProductCancellationChannel]
  congr 1
  funext row
  simp

/-- Multiplying the normalized small-ratio row by its hidden denominator gives exactly
`z_j*S+f*g_j*S^2+f*H_j`. -/
theorem denominator_mul_quadraticChannel
    {R : Type} [CommRing R] (denominator inverse numerator secret weight finalError : R)
    (hInverse : inverse * denominator = 1) :
    denominator *
        ((inverse * numerator) * secret + weight * secret ^ 2 + finalError) =
      numerator * secret + denominator * weight * secret ^ 2 +
        denominator * finalError := by
  have hInverse' : denominator * inverse = 1 := by
    simpa [mul_comm] using hInverse
  calc
    denominator *
          ((inverse * numerator) * secret + weight * secret ^ 2 + finalError) =
        (denominator * inverse) * numerator * secret +
          denominator * weight * secret ^ 2 + denominator * finalError := by ring
    _ = numerator * secret + denominator * weight * secret ^ 2 +
          denominator * finalError := by rw [hInverse', one_mul]

/-! ## Finite-support maximal leakage -/

/-- The finite guessing mass `sum_y sup_s Pr[(s,y)]`.  The theorem below proves that this is not
merely notation: it equals the operational supremum over all randomized estimators. -/
noncomputable def finiteGuessingMass
    {Secret Side : Type} [Fintype Secret] [Fintype Side]
    (joint : ProbComp (Secret × Side)) : ENNReal :=
  ∑ side, ⨆ secret, Pr[= (secret, side) | joint]

/-- Expand the success of a randomized estimator into joint point masses. -/
theorem guessingSuccess_eq_sum_jointPointMass
    {Secret Side : Type} [Fintype Secret] [Fintype Side]
    [DecidableEq Secret] [DecidableEq Side]
    (joint : ProbComp (Secret × Side)) (estimator : Estimator Secret Side) :
    guessingSuccess joint estimator =
      ∑ value : Secret × Side,
        Pr[= value | joint] * Pr[= value.1 | estimator value.2] := by
  unfold guessingSuccess guessingGame
  simp [probOutput_bind_eq_sum_fintype, probOutput_map_eq_sum_fintype_ite]

/-- Every randomized estimator is bounded by the finite maximum-likelihood mass. -/
theorem guessingSuccess_le_finiteGuessingMass
    {Secret Side : Type} [Fintype Secret] [Fintype Side]
    [DecidableEq Secret] [DecidableEq Side]
    (joint : ProbComp (Secret × Side)) (estimator : Estimator Secret Side) :
    guessingSuccess joint estimator ≤ finiteGuessingMass joint := by
  rw [guessingSuccess_eq_sum_jointPointMass]
  unfold finiteGuessingMass
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_le_sum
  intro side _
  calc
    (∑ secret : Secret,
        Pr[= (secret, side) | joint] * Pr[= secret | estimator side]) ≤
        ∑ secret : Secret,
          (⨆ candidate, Pr[= (candidate, side) | joint]) *
            Pr[= secret | estimator side] := by
      apply Finset.sum_le_sum
      intro secret _
      exact mul_le_mul_left
        (le_iSup (fun candidate ↦ Pr[= (candidate, side) | joint]) secret) _
    _ = (⨆ candidate, Pr[= (candidate, side) | joint]) *
          ∑ secret : Secret, Pr[= secret | estimator side] := by
      rw [Finset.mul_sum]
    _ ≤ (⨆ candidate, Pr[= (candidate, side) | joint]) * 1 := by
      apply mul_le_mul_right
      simpa only [tsum_fintype] using
        (tsum_probOutput_le_one (mx := estimator side))
    _ = ⨆ candidate, Pr[= (candidate, side) | joint] := mul_one _

/-- Operational guessing is at most the finite maximum-likelihood expression. -/
theorem conditionalGuessingProbability_le_finiteGuessingMass
    {Secret Side : Type} [Fintype Secret] [Fintype Side]
    [DecidableEq Secret] [DecidableEq Side]
    (joint : ProbComp (Secret × Side)) :
    conditionalGuessingProbability joint ≤ finiteGuessingMass joint := by
  apply iSup_le
  exact guessingSuccess_le_finiteGuessingMass joint

/-- A maximum-likelihood secret exists for each public side value. -/
noncomputable def maximizingSecret
    {Secret Side : Type} [Fintype Secret] [Nonempty Secret]
    (joint : ProbComp (Secret × Side)) (side : Side) : Secret :=
  Classical.choose (Finset.exists_max_image Finset.univ
    (fun secret ↦ Pr[= (secret, side) | joint]) Finset.univ_nonempty)

theorem maximizingSecret_spec
    {Secret Side : Type} [Fintype Secret] [Nonempty Secret]
    (joint : ProbComp (Secret × Side)) (side : Side) (secret : Secret) :
    Pr[= (secret, side) | joint] ≤
      Pr[= (maximizingSecret joint side, side) | joint] := by
  exact (Classical.choose_spec (Finset.exists_max_image Finset.univ
    (fun candidate ↦ Pr[= (candidate, side) | joint])
    Finset.univ_nonempty)).2 secret (Finset.mem_univ _)

theorem maximizingSecret_eq_iSup
    {Secret Side : Type} [Fintype Secret] [Nonempty Secret]
    (joint : ProbComp (Secret × Side)) (side : Side) :
    Pr[= (maximizingSecret joint side, side) | joint] =
      ⨆ secret, Pr[= (secret, side) | joint] := by
  apply le_antisymm
  · exact le_iSup (fun secret ↦ Pr[= (secret, side) | joint]) _
  · apply iSup_le
    exact maximizingSecret_spec joint side

/-- On finite types, operational guessing probability is exactly
`sum_y max_s Pr[(s,y)]`; randomization cannot improve the maximum-likelihood estimator. -/
theorem conditionalGuessingProbability_eq_finiteGuessingMass
    {Secret Side : Type} [Fintype Secret] [Nonempty Secret] [Fintype Side]
    [DecidableEq Secret] [DecidableEq Side]
    (joint : ProbComp (Secret × Side)) :
    conditionalGuessingProbability joint = finiteGuessingMass joint := by
  apply le_antisymm
  · exact conditionalGuessingProbability_le_finiteGuessingMass joint
  · calc
      finiteGuessingMass joint =
          guessingSuccess joint (fun side ↦ pure (maximizingSecret joint side)) := by
        rw [guessingSuccess_eq_sum_jointPointMass]
        unfold finiteGuessingMass
        rw [Fintype.sum_prod_type, Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro side _
        rw [← maximizingSecret_eq_iSup joint side]
        simp [probOutput_pure]
      _ ≤ conditionalGuessingProbability joint :=
        guessingSuccess_le_conditionalGuessingProbability _ _

/-- Sample a secret from a prior and then pass it through a channel. -/
def conditionalChannelJoint
    {Secret Output : Type} (prior : ProbComp Secret)
    (channel : Secret → ProbComp Output) : ProbComp (Secret × Output) := do
  let secret ← prior
  let output ← channel secret
  return (secret, output)

/-- Largest prior point mass. -/
noncomputable def priorMaxMass
    {Secret : Type} [Fintype Secret] (prior : ProbComp Secret) : ENNReal :=
  ⨆ secret, Pr[= secret | prior]

/-- Exponential maximal-leakage mass `sum_y sup_s Pr[y|s]`.  Its base-two logarithm is the
usual maximal leakage. -/
noncomputable def channelMaximalLeakageMass
    {Secret Output : Type} [Fintype Secret] [Fintype Output]
    (channel : Secret → ProbComp Output) : ENNReal :=
  ∑ output, ⨆ secret, Pr[= output | channel secret]

theorem probOutput_conditionalChannelJoint
    {Secret Output : Type} [Fintype Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (secret : Secret) (output : Output) :
    Pr[= (secret, output) | conditionalChannelJoint prior channel] =
      Pr[= secret | prior] * Pr[= output | channel secret] := by
  simp [conditionalChannelJoint, probOutput_bind_eq_sum_fintype]

/-- Fixed-context support-aware guessing theorem. -/
theorem supportAwareGuessingBound
    {Secret Output : Type} [Fintype Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output) :
    conditionalGuessingProbability (conditionalChannelJoint prior channel) ≤
      priorMaxMass prior * channelMaximalLeakageMass channel := by
  refine (conditionalGuessingProbability_le_finiteGuessingMass _).trans ?_
  unfold finiteGuessingMass channelMaximalLeakageMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro output _
  apply iSup_le
  intro secret
  rw [probOutput_conditionalChannelJoint]
  exact mul_le_mul
    (le_iSup (fun candidate ↦ Pr[= candidate | prior]) secret)
    (le_iSup (fun candidate ↦ Pr[= output | channel candidate]) secret)
    zero_le zero_le

/-- Joint law with arbitrary public conditioning `C`: sample `c`, then `S|c`, then `Y|s,c`. -/
def contextualChannelJoint
    {Context Secret Output : Type}
    (contextSampler : ProbComp Context)
    (prior : Context → ProbComp Secret)
    (channel : Context → Secret → ProbComp Output) :
    ProbComp (Secret × (Context × Output)) := do
  let context ← contextSampler
  let secret ← prior context
  let output ← channel context secret
  return (secret, (context, output))

theorem probOutput_contextualChannelJoint
    {Context Secret Output : Type}
    [Fintype Context] [Fintype Secret] [Fintype Output]
    [DecidableEq Context] [DecidableEq Secret] [DecidableEq Output]
    (contextSampler : ProbComp Context)
    (prior : Context → ProbComp Secret)
    (channel : Context → Secret → ProbComp Output)
    (context : Context) (secret : Secret) (output : Output) :
    Pr[= (secret, (context, output)) |
        contextualChannelJoint contextSampler prior channel] =
      Pr[= context | contextSampler] * Pr[= secret | prior context] *
        Pr[= output | channel context secret] := by
  classical
  simp only [contextualChannelJoint, probOutput_bind_eq_sum_fintype]
  rw [Finset.sum_eq_single context]
  · rw [Finset.sum_eq_single secret]
    · simp [mul_assoc]
    · intro other _ hne
      simp [probOutput_pure, Ne.symm hne]
    · simp
  · intro other _ hne
    simp [probOutput_pure, Ne.symm hne]
  · simp

/-- Context-averaged support-aware guessing theorem, exactly in the form used by the refined
note.  No independence between the public context and its conditional prior/channel is assumed. -/
theorem contextualSupportAwareGuessingBound
    {Context Secret Output : Type}
    [Fintype Context] [Fintype Secret] [Fintype Output]
    [DecidableEq Context] [DecidableEq Secret] [DecidableEq Output]
    (contextSampler : ProbComp Context)
    (prior : Context → ProbComp Secret)
    (channel : Context → Secret → ProbComp Output) :
    conditionalGuessingProbability
        (contextualChannelJoint contextSampler prior channel) ≤
      ∑ context,
        Pr[= context | contextSampler] * priorMaxMass (prior context) *
          channelMaximalLeakageMass (channel context) := by
  refine (conditionalGuessingProbability_le_finiteGuessingMass _).trans ?_
  unfold finiteGuessingMass channelMaximalLeakageMass
  rw [Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro context _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro output _
  apply iSup_le
  intro secret
  rw [probOutput_contextualChannelJoint]
  exact mul_le_mul
    (mul_le_mul_right
      (le_iSup (fun candidate ↦ Pr[= candidate | prior context]) secret) _)
    (le_iSup (fun candidate ↦ Pr[= output | channel context candidate]) secret)
    zero_le zero_le

/-- Joint law before the channel, retaining only the public context. -/
def contextualPriorJoint
    {Context Secret : Type} (contextSampler : ProbComp Context)
    (prior : Context → ProbComp Secret) : ProbComp (Secret × Context) := do
  let context ← contextSampler
  let secret ← prior context
  return (secret, context)

theorem probOutput_contextualPriorJoint
    {Context Secret : Type} [Fintype Context] [Fintype Secret]
    [DecidableEq Context] [DecidableEq Secret]
    (contextSampler : ProbComp Context) (prior : Context → ProbComp Secret)
    (context : Context) (secret : Secret) :
    Pr[= (secret, context) | contextualPriorJoint contextSampler prior] =
      Pr[= context | contextSampler] * Pr[= secret | prior context] := by
  classical
  simp only [contextualPriorJoint, probOutput_bind_eq_sum_fintype]
  rw [Finset.sum_eq_single context]
  · simp
  · intro other _ hne
    simp [probOutput_pure, Ne.symm hne]
  · simp

theorem finiteGuessingMass_contextualPriorJoint
    {Context Secret : Type} [Fintype Context] [Fintype Secret]
    [DecidableEq Context] [DecidableEq Secret]
    (contextSampler : ProbComp Context) (prior : Context → ProbComp Secret) :
    finiteGuessingMass (contextualPriorJoint contextSampler prior) =
      ∑ context, Pr[= context | contextSampler] * priorMaxMass (prior context) := by
  unfold finiteGuessingMass priorMaxMass
  apply Finset.sum_congr rfl
  intro context _
  simp_rw [probOutput_contextualPriorJoint]
  exact (ENNReal.mul_iSup _ _).symm

/-- Uniform maximal-leakage corollary.  If every conditional channel has exponential leakage
mass at most `factor`, revealing the channel multiplies guessing probability by at most `factor`. -/
theorem contextualUniformMaximalLeakageBound
    {Context Secret Output : Type}
    [Fintype Context] [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Context] [DecidableEq Secret] [DecidableEq Output]
    (contextSampler : ProbComp Context)
    (prior : Context → ProbComp Secret)
    (channel : Context → Secret → ProbComp Output)
    (factor : ENNReal)
    (hFactor : ∀ context, channelMaximalLeakageMass (channel context) ≤ factor) :
    conditionalGuessingProbability
        (contextualChannelJoint contextSampler prior channel) ≤
      factor * conditionalGuessingProbability
        (contextualPriorJoint contextSampler prior) := by
  calc
    conditionalGuessingProbability
        (contextualChannelJoint contextSampler prior channel) ≤
      ∑ context,
        Pr[= context | contextSampler] * priorMaxMass (prior context) *
          channelMaximalLeakageMass (channel context) :=
      contextualSupportAwareGuessingBound contextSampler prior channel
    _ ≤ ∑ context,
        Pr[= context | contextSampler] * priorMaxMass (prior context) * factor := by
      apply Finset.sum_le_sum
      intro context _
      exact mul_le_mul_right (hFactor context) _
    _ = factor * finiteGuessingMass (contextualPriorJoint contextSampler prior) := by
      rw [finiteGuessingMass_contextualPriorJoint]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro context _
      ac_rfl
    _ = factor * conditionalGuessingProbability
        (contextualPriorJoint contextSampler prior) := by
      rw [conditionalGuessingProbability_eq_finiteGuessingMass]

/-! ## Exact finite additive-channel certificate -/

/-- Add independent noise to a secret-dependent mean. -/
def additiveChannel
    {Secret Output : Type} [Add Output]
    (noise : ProbComp Output) (mean : Secret → Output) : Secret → ProbComp Output :=
  fun secret ↦ (mean secret + ·) <$> noise

/-- The additive channel likelihood is the translated noise likelihood. -/
theorem probOutput_additiveChannel
    {Secret Output : Type} [AddCommGroup Output]
    (noise : ProbComp Output) (mean : Secret → Output)
    (secret : Secret) (output : Output) :
    Pr[= output | additiveChannel noise mean secret] =
      Pr[= output - mean secret | noise] := by
  change Pr[= output | (Equiv.addLeft (mean secret)) <$> noise] = _
  rw [probOutput_map_equiv]
  simp [sub_eq_add_neg, add_comm]

/-- Exact support-aware maximal-leakage mass for `Y=mean(S)+H`. -/
theorem channelMaximalLeakageMass_additiveChannel
    {Secret Output : Type} [Fintype Secret] [Fintype Output]
    [AddCommGroup Output]
    (noise : ProbComp Output) (mean : Secret → Output) :
    channelMaximalLeakageMass (additiveChannel noise mean) =
      ∑ output, ⨆ secret, Pr[= output - mean secret | noise] := by
  unfold channelMaximalLeakageMass
  simp_rw [probOutput_additiveChannel]

/-! ## Descriptor averaging -/

/-- The contextual guessing mass is exactly the expectation of the conditioned guessing masses. -/
theorem finiteGuessingMass_contextualChannelJoint
    {Context Secret Output : Type}
    [Fintype Context] [Fintype Secret] [Fintype Output]
    [DecidableEq Context] [DecidableEq Secret] [DecidableEq Output]
    (contextSampler : ProbComp Context)
    (prior : Context → ProbComp Secret)
    (channel : Context → Secret → ProbComp Output) :
    finiteGuessingMass (contextualChannelJoint contextSampler prior channel) =
      ∑ context, Pr[= context | contextSampler] *
        finiteGuessingMass
          (conditionalChannelJoint (prior context) (channel context)) := by
  unfold finiteGuessingMass
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro context _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro output _
  simp_rw [probOutput_contextualChannelJoint, probOutput_conditionalChannelJoint]
  simpa only [mul_assoc] using
    (ENNReal.mul_iSup (Pr[= context | contextSampler])
      (fun secret ↦ Pr[= secret | prior context] *
        Pr[= output | channel context secret])).symm

/-- Integrate descriptor-dependent pointwise bounds.  This is the elementary probability step in
the distribution-averaged Brakerski--Döttling theorem; the analytic Gaussian theorem supplies
`pointwiseBound`. -/
theorem distributionAveragedGuessingBound
    {Descriptor Secret Output : Type}
    [Fintype Descriptor] [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Descriptor] [DecidableEq Secret] [DecidableEq Output]
    (descriptorSampler : ProbComp Descriptor)
    (prior : Descriptor → ProbComp Secret)
    (channel : Descriptor → Secret → ProbComp Output)
    (bound : Descriptor → ENNReal)
    (pointwiseBound : ∀ descriptor,
      conditionalGuessingProbability
        (conditionalChannelJoint (prior descriptor) (channel descriptor)) ≤
          bound descriptor) :
    conditionalGuessingProbability
        (contextualChannelJoint descriptorSampler prior channel) ≤
      ∑ descriptor, Pr[= descriptor | descriptorSampler] * bound descriptor := by
  rw [conditionalGuessingProbability_eq_finiteGuessingMass,
    finiteGuessingMass_contextualChannelJoint]
  apply Finset.sum_le_sum
  intro descriptor _
  apply mul_le_mul_right
  rw [← conditionalGuessingProbability_eq_finiteGuessingMass]
  exact pointwiseBound descriptor

/-! ## One-step and iterated joint RNS maximal leakage -/

/-- Append a new limb observation whose law may depend on the secret and the complete preceding
history.  This models coherent errors without any limb-independence assumption. -/
def extendJointObservation
    {Secret History Output : Type}
    (joint : ProbComp (Secret × History))
    (channel : Secret → History → ProbComp Output) :
    ProbComp (Secret × (History × Output)) := do
  let value ← joint
  let output ← channel value.1 value.2
  return (value.1, (value.2, output))

theorem probOutput_extendJointObservation
    {Secret History Output : Type}
    [Fintype Secret] [Fintype History] [Fintype Output]
    [DecidableEq Secret] [DecidableEq History] [DecidableEq Output]
    (joint : ProbComp (Secret × History))
    (channel : Secret → History → ProbComp Output)
    (secret : Secret) (history : History) (output : Output) :
    Pr[= (secret, (history, output)) | extendJointObservation joint channel] =
      Pr[= (secret, history) | joint] * Pr[= output | channel secret history] := by
  classical
  simp only [extendJointObservation, probOutput_bind_eq_sum_fintype]
  rw [Finset.sum_eq_single (secret, history)]
  · simp
  · intro other _ hne
    have hpair : ¬ (secret = other.1 ∧ history = other.2) := by
      rintro ⟨hSecret, hHistory⟩
      exact hne (Prod.ext hSecret.symm hHistory.symm)
    simp [probOutput_pure]
    right
    intro hSecret hHistory
    exact (hpair ⟨hSecret, hHistory⟩).elim
  · simp

/-- One joint coherent-RNS step.  The conditional channel may depend on the entire observed
prefix, so this theorem makes no cross-limb independence assumption. -/
theorem extendJointObservation_maximalLeakage
    {Secret History Output : Type}
    [Fintype Secret] [Nonempty Secret] [Fintype History] [Fintype Output]
    [DecidableEq Secret] [DecidableEq History] [DecidableEq Output]
    (joint : ProbComp (Secret × History))
    (channel : Secret → History → ProbComp Output)
    (factor : ENNReal)
    (hFactor : ∀ history,
      channelMaximalLeakageMass (fun secret ↦ channel secret history) ≤ factor) :
    conditionalGuessingProbability (extendJointObservation joint channel) ≤
      factor * conditionalGuessingProbability joint := by
  rw [conditionalGuessingProbability_eq_finiteGuessingMass,
    conditionalGuessingProbability_eq_finiteGuessingMass]
  unfold finiteGuessingMass
  rw [Fintype.sum_prod_type]
  calc
    (∑ history, ∑ output,
        ⨆ secret,
          Pr[= (secret, (history, output)) | extendJointObservation joint channel]) ≤
      ∑ history, ∑ output,
        (⨆ secret, Pr[= (secret, history) | joint]) *
          (⨆ secret, Pr[= output | channel secret history]) := by
      apply Finset.sum_le_sum
      intro history _
      apply Finset.sum_le_sum
      intro output _
      apply iSup_le
      intro secret
      rw [probOutput_extendJointObservation]
      exact mul_le_mul
        (le_iSup (fun candidate ↦ Pr[= (candidate, history) | joint]) secret)
        (le_iSup (fun candidate ↦ Pr[= output | channel candidate history]) secret)
        zero_le zero_le
    _ = ∑ history,
        (⨆ secret, Pr[= (secret, history) | joint]) *
          (∑ output, ⨆ secret, Pr[= output | channel secret history]) := by
      apply Finset.sum_congr rfl
      intro history _
      rw [Finset.mul_sum]
    _ ≤ ∑ history,
        (⨆ secret, Pr[= (secret, history) | joint]) * factor := by
      apply Finset.sum_le_sum
      intro history _
      exact mul_le_mul_right
        (by simpa [channelMaximalLeakageMass] using hFactor history) _
    _ = factor * ∑ history,
        ⨆ secret, Pr[= (secret, history) | joint] := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro history _
      ac_rfl

/-- Iterate one-step maximal-leakage bounds.  Instantiating `guessing i` with the conditional
guessing probability after `i` RNS limbs yields the genuinely joint RNS theorem. -/
theorem jointRNSMaximalLeakageComposition
    (guessing factor : ℕ → ENNReal) (limbCount : ℕ)
    (step : ∀ index < limbCount,
      guessing (index + 1) ≤ factor index * guessing index) :
    guessing limbCount ≤
      (∏ index ∈ Finset.range limbCount, factor index) * guessing 0 := by
  induction limbCount with
  | zero => simp
  | succ count ih =>
      calc
        guessing (count + 1) ≤ factor count * guessing count :=
          step count (Nat.lt_succ_self count)
        _ ≤ factor count *
            ((∏ index ∈ Finset.range count, factor index) * guessing 0) := by
          exact mul_le_mul_right
            (ih fun index hindex ↦ step index (hindex.trans (Nat.lt_succ_self count))) _
        _ = (∏ index ∈ Finset.range (count + 1), factor index) * guessing 0 := by
          rw [Finset.prod_range_succ]
          ac_rfl

/-- A residue modulo a limb larger than twice the centered bound has at most one centered integer
lift.  This is the arithmetic content of the bounded coherent-lift corollary. -/
theorem boundedCenteredLift_unique
    (modulus bound left right : ℤ)
    (hbound : 0 ≤ bound) (hmodulus : 2 * bound < modulus)
    (hleft : |left| ≤ bound) (hright : |right| ≤ bound)
    (hresidue : left % modulus = right % modulus) : left = right := by
  have hmodulus_pos : 0 < modulus := by linarith
  have habs : |left - right| < |modulus| := by
    rw [abs_of_pos hmodulus_pos]
    calc
      |left - right| ≤ |left| + |right| := abs_sub left right
      _ ≤ bound + bound := add_le_add hleft hright
      _ = 2 * bound := by ring
      _ < modulus := hmodulus
  have hnat : (left - right).natAbs < modulus.natAbs := by
    have hcast : ((left - right).natAbs : ℤ) < (modulus.natAbs : ℤ) := by
      simpa only [Int.natCast_natAbs] using habs
    exact_mod_cast hcast
  have hdvd : modulus ∣ left - right := by
    rw [Int.dvd_iff_emod_eq_zero]
    exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hresidue
  exact sub_eq_zero.mp (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd hnat)

/-- Coordinatewise version: one sufficiently large RNS limb determines the complete bounded
coherent integer error polynomial. -/
theorem boundedCoherentLift_unique
    {Coordinate : Type} (modulus bound : ℤ)
    (left right : Coordinate → ℤ)
    (hbound : 0 ≤ bound) (hmodulus : 2 * bound < modulus)
    (hleft : ∀ coordinate, |left coordinate| ≤ bound)
    (hright : ∀ coordinate, |right coordinate| ≤ bound)
    (hresidue : ∀ coordinate,
      left coordinate % modulus = right coordinate % modulus) :
    left = right := by
  funext coordinate
  exact boundedCenteredLift_unique modulus bound (left coordinate) (right coordinate)
    hbound hmodulus (hleft coordinate) (hright coordinate) (hresidue coordinate)

/-! ## Integer entropy and finite-support Fano interface -/

/-- The determinant expression in the integer entropy lemma. -/
noncomputable def integerEntropyCovarianceBound
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (covariance : Matrix Coordinate Coordinate ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.logb 2
    (Matrix.det ((2 * Real.pi * Real.exp 1) •
      (covariance + (1 / 12 : ℝ) • (1 : Matrix Coordinate Coordinate ℝ))))

/-- Explicit analytic boundary for the integer-vector entropy lemma.  The fields name the exact
covariance and determinant conclusion; later theorems use only `entropy_le`.  This introduces no
axiom and can be replaced by a native differential-entropy development. -/
structure IntegerEntropyCovarianceCertificate
    (Coordinate : Type) [Fintype Coordinate] [DecidableEq Coordinate] where
  covariance : Matrix Coordinate Coordinate ℝ
  entropy : ℝ
  entropy_le : entropy ≤ integerEntropyCovarianceBound covariance

/-- The positive-part information bound `J(c)` from the refined note. -/
noncomputable def additiveChannelInformationBound
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (meanCovariance noiseCovariance : Matrix Coordinate Coordinate ℝ)
    (noiseEntropy : ℝ) : ℝ :=
  max 0
    (integerEntropyCovarianceBound (meanCovariance + noiseCovariance) - noiseEntropy)

/-- Purely numeric data needed for the Fano step.  `information_le` is where data processing and
the integer entropy/covariance estimate enter. -/
structure FiniteSupportFanoData where
  secretEntropy : ℝ
  information : ℝ
  informationBound : ℝ
  conditionalEntropy : ℝ
  success : ℝ
  logSupport : ℝ
  logSupport_pos : 0 < logSupport
  success_le_one : success ≤ 1
  information_le : information ≤ informationBound
  entropy_chain : conditionalEntropy = secretEntropy - information
  fano : conditionalEntropy ≤ 1 + (1 - success) * logSupport

/-- Fano's success bound after an information upper bound has been supplied. -/
theorem finiteSupportFanoBound (data : FiniteSupportFanoData) :
    data.success ≤ min 1
      (1 - (data.secretEntropy - data.informationBound - 1) / data.logSupport) := by
  apply le_min data.success_le_one
  have hcore : data.secretEntropy - data.informationBound ≤
      1 + (1 - data.success) * data.logSupport := by
    calc
      data.secretEntropy - data.informationBound ≤
          data.secretEntropy - data.information := by linarith [data.information_le]
      _ = data.conditionalEntropy := data.entropy_chain.symm
      _ ≤ _ := data.fano
  have hfrac :
      (data.secretEntropy - data.informationBound - 1) / data.logSupport ≤
        1 - data.success := by
    apply (div_le_iff₀ data.logSupport_pos).2
    linarith [hcore]
  linarith [hfrac]

/-- Uniform-support specialization `Psucc ≤ min(1,(J+1)/log₂ M)`. -/
theorem finiteSupportFanoUniformBound (data : FiniteSupportFanoData)
    (hUniform : data.secretEntropy = data.logSupport) :
    data.success ≤ min 1 ((data.informationBound + 1) / data.logSupport) := by
  have h := finiteSupportFanoBound data
  rw [hUniform] at h
  have hid :
      1 - (data.logSupport - data.informationBound - 1) / data.logSupport =
        (data.informationBound + 1) / data.logSupport := by
    field_simp [ne_of_gt data.logSupport_pos]
    ring
  simpa only [hid] using h

/-- Proof-carrying finite-support additive-channel certificate.  Its information bound is fixed
to the covariance/determinant expression from the theorem, while data processing, entropy
maximization, and covariance additivity remain explicit analytic obligations. -/
structure FiniteSupportAdditiveChannelCertificate
    (Coordinate : Type) [Fintype Coordinate] [DecidableEq Coordinate] where
  meanCovariance : Matrix Coordinate Coordinate ℝ
  noiseCovariance : Matrix Coordinate Coordinate ℝ
  noiseEntropy : ℝ
  secretEntropy : ℝ
  information : ℝ
  conditionalEntropy : ℝ
  success : ℝ
  logSupport : ℝ
  logSupport_pos : 0 < logSupport
  success_le_one : success ≤ 1
  information_le : information ≤
    additiveChannelInformationBound meanCovariance noiseCovariance noiseEntropy
  entropy_chain : conditionalEntropy = secretEntropy - information
  fano : conditionalEntropy ≤ 1 + (1 - success) * logSupport

def FiniteSupportAdditiveChannelCertificate.toFanoData
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (certificate : FiniteSupportAdditiveChannelCertificate Coordinate) :
    FiniteSupportFanoData where
  secretEntropy := certificate.secretEntropy
  information := certificate.information
  informationBound := additiveChannelInformationBound certificate.meanCovariance
    certificate.noiseCovariance certificate.noiseEntropy
  conditionalEntropy := certificate.conditionalEntropy
  success := certificate.success
  logSupport := certificate.logSupport
  logSupport_pos := certificate.logSupport_pos
  success_le_one := certificate.success_le_one
  information_le := certificate.information_le
  entropy_chain := certificate.entropy_chain
  fano := certificate.fano

/-- Finite-support additive-channel success theorem with the exact `J` expression. -/
theorem finiteSupportAdditiveChannelBound
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (certificate : FiniteSupportAdditiveChannelCertificate Coordinate) :
    certificate.success ≤ min 1
      (1 - (certificate.secretEntropy -
        additiveChannelInformationBound certificate.meanCovariance
          certificate.noiseCovariance certificate.noiseEntropy - 1) /
        certificate.logSupport) :=
  finiteSupportFanoBound certificate.toFanoData

/-- Uniform binary/ternary-support version of the additive-channel Fano certificate. -/
theorem finiteSupportAdditiveChannelUniformBound
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (certificate : FiniteSupportAdditiveChannelCertificate Coordinate)
    (hUniform : certificate.secretEntropy = certificate.logSupport) :
    certificate.success ≤ min 1
      ((additiveChannelInformationBound certificate.meanCovariance
        certificate.noiseCovariance certificate.noiseEntropy + 1) /
          certificate.logSupport) :=
  finiteSupportFanoUniformBound certificate.toFanoData hUniform

/-! ## Canonical formulas and analytic certificates -/

/-- Canonical-coordinate definition of the denominator multiplication singular value. -/
noncomputable def canonicalDenominatorSingularValue
    {Embedding Element : Type} [Fintype Embedding]
    (embedding : Embedding → Element → ℝ) (denominator : Element) : ℝ :=
  ⨆ coordinate, |embedding coordinate denominator|

/-- Squared singular value of the canonical block row of masked ratios. -/
noncomputable def canonicalRatioBlockSingularValueSquared
    {Embedding Row Element : Type} [Fintype Embedding] [Fintype Row]
    (embedding : Embedding → Element → ℝ) (ratio : Row → Element) : ℝ :=
  ⨆ coordinate, ∑ row, |embedding coordinate (ratio row)| ^ 2

/-- Exact canonical singular-value identities once multiplication has been diagonalized in the
normalized canonical basis. -/
theorem exactCanonicalSingularValueIdentities
    {Embedding Row Element : Type} [Fintype Embedding] [Fintype Row]
    (embedding : Embedding → Element → ℝ) (denominator : Element)
    (ratio : Row → Element) :
    canonicalDenominatorSingularValue embedding denominator =
        ⨆ coordinate, |embedding coordinate denominator| ∧
      canonicalRatioBlockSingularValueSquared embedding ratio =
        ⨆ coordinate, ∑ row, |embedding coordinate (ratio row)| ^ 2 :=
  ⟨rfl, rfl⟩

/-- Algebraic covariance identity underlying the continuous Gaussian decomposition. -/
theorem covarianceResidual_add
    {Left Right : Type} [Fintype Left] [Fintype Right] [DecidableEq Right]
    (sigma : ℝ) (matrix : Matrix Left Right ℝ)
    (covariance : Matrix Right Right ℝ) :
    sigma ^ 2 • (matrix.transpose * matrix) +
        (covariance - sigma ^ 2 • (matrix.transpose * matrix)) = covariance := by
  abel

/-- Explicit boundary for the remaining Gaussian existence statement.  The caller fixes the
meaning of `decompositionLaw` (normally equality in distribution of the two centered Gaussian
laws); positive semidefiniteness of the residual is represented concretely by symmetry and
nonnegativity of its quadratic form.  `covariance_eq` itself is proved from matrix algebra. -/
structure ContinuousGaussianDecompositionCertificate
    (Left Right : Type) [Fintype Left] [Fintype Right] [DecidableEq Right]
    (decompositionLaw :
      ℝ → Matrix Left Right ℝ → Matrix Right Right ℝ → Prop) where
  sigma : ℝ
  matrix : Matrix Left Right ℝ
  covariance : Matrix Right Right ℝ
  residual_symmetric :
    (covariance - sigma ^ 2 • (matrix.transpose * matrix)).transpose =
      covariance - sigma ^ 2 • (matrix.transpose * matrix)
  residual_quadratic_nonnegative : ∀ vector : Right → ℝ,
    0 ≤ dotProduct vector
      ((covariance - sigma ^ 2 • (matrix.transpose * matrix)).mulVec vector)
  decomposition_exists : decompositionLaw sigma matrix covariance

theorem ContinuousGaussianDecompositionCertificate.covariance_eq
    {Left Right : Type} [Fintype Left] [Fintype Right] [DecidableEq Right]
    {decompositionLaw :
      ℝ → Matrix Left Right ℝ → Matrix Right Right ℝ → Prop}
    (certificate : ContinuousGaussianDecompositionCertificate
      Left Right decompositionLaw) :
    certificate.sigma ^ 2 • (certificate.matrix.transpose * certificate.matrix) +
        (certificate.covariance - certificate.sigma ^ 2 •
          (certificate.matrix.transpose * certificate.matrix)) = certificate.covariance :=
  covarianceResidual_add certificate.sigma certificate.matrix certificate.covariance

/-- Numeric upper bound from the subgaussian masked-ratio proposition. -/
noncomputable def maskedRatioSubgaussianBound
    (constant maskNorm ratioNorm rowCount embeddingCount failure : ℝ) : ℝ :=
  constant * maskNorm * (1 + ratioNorm) *
    (Real.sqrt rowCount + Real.sqrt (Real.log (2 * embeddingCount / failure)))

/-- Numeric upper bound for the maximum canonical coordinate of the denominator. -/
noncomputable def denominatorSubgaussianBound
    (constant denominatorNorm width embeddingCount failure : ℝ) : ℝ :=
  constant * denominatorNorm * width *
    Real.sqrt (Real.log (2 * embeddingCount / failure))

/-- Proof-carrying interface to the two subgaussian tail estimates.  The two good events and their
probabilities are part of the statement, rather than being hidden inside unconnected numbers. -/
structure SubgaussianMaskedRatioCertificate
    (Descriptor : Type) [Fintype Descriptor] [DecidableEq Descriptor]
    (descriptorSampler : ProbComp Descriptor) where
  constant : ℝ
  maskNorm : ℝ
  ratioNorm : ℝ
  rowCount : ℝ
  embeddingCount : ℝ
  failure : ℝ
  denominatorNorm : ℝ
  denominatorWidth : ℝ
  t1 : Descriptor → ℝ
  t2 : Descriptor → ℝ
  ratioGood : Descriptor → Bool
  denominatorGood : Descriptor → Bool
  failure_pos : 0 < failure
  failure_lt_one : failure < 1
  ratio_failure_le :
    Pr[= false | ratioGood <$> descriptorSampler] ≤ ENNReal.ofReal failure
  denominator_failure_le :
    Pr[= false | denominatorGood <$> descriptorSampler] ≤ ENNReal.ofReal failure
  t1_le : ∀ descriptor, ratioGood descriptor = true →
    t1 descriptor ≤ maskedRatioSubgaussianBound constant maskNorm ratioNorm
      rowCount embeddingCount failure
  t2_le : ∀ descriptor, denominatorGood descriptor = true →
    t2 descriptor ≤ denominatorSubgaussianBound constant denominatorNorm
      denominatorWidth embeddingCount failure

/-- The certified subgaussian `t1` conclusion. -/
theorem SubgaussianMaskedRatioCertificate.ratioBound
    {Descriptor : Type} [Fintype Descriptor] [DecidableEq Descriptor]
    {descriptorSampler : ProbComp Descriptor}
    (certificate : SubgaussianMaskedRatioCertificate Descriptor descriptorSampler)
    (descriptor : Descriptor) (hGood : certificate.ratioGood descriptor = true) :
    certificate.t1 descriptor ≤ maskedRatioSubgaussianBound certificate.constant
      certificate.maskNorm certificate.ratioNorm certificate.rowCount
      certificate.embeddingCount certificate.failure :=
  certificate.t1_le descriptor hGood

/-- The certified subgaussian `t2` conclusion. -/
theorem SubgaussianMaskedRatioCertificate.denominatorBound
    {Descriptor : Type} [Fintype Descriptor] [DecidableEq Descriptor]
    {descriptorSampler : ProbComp Descriptor}
    (certificate : SubgaussianMaskedRatioCertificate Descriptor descriptorSampler)
    (descriptor : Descriptor)
    (hGood : certificate.denominatorGood descriptor = true) :
    certificate.t2 descriptor ≤ denominatorSubgaussianBound certificate.constant
      certificate.denominatorNorm certificate.denominatorWidth
      certificate.embeddingCount certificate.failure :=
  certificate.t2_le descriptor hGood

/-! ## Distribution-averaged Brakerski--Döttling certificate -/

/-- Pointwise good-descriptor bound from the refined Gaussian theorem. -/
noncomputable def averagedGaussianPointwiseBound
    (ringRank : ℕ) (t2 entropy smoothingError : ℝ) : ENNReal :=
  min 1 (ENNReal.ofReal
    (2 ^ ((ringRank : ℝ) * Real.logb 2 t2 - entropy)) +
      ENNReal.ofReal (20 * smoothingError))

/-- Use the Gaussian bound on smoothing-good descriptors and the trivial bound one elsewhere. -/
noncomputable def averagedGaussianDescriptorBound
    {Descriptor : Type} (good : Descriptor → Prop) [DecidablePred good]
    (ringRank : ℕ) (t2 entropy : Descriptor → ℝ) (smoothingError : ℝ)
    (descriptor : Descriptor) : ENNReal :=
  if good descriptor then
    averagedGaussianPointwiseBound ringRank (t2 descriptor) (entropy descriptor)
      smoothingError
  else 1

/-- Exact proof boundary for the pointwise Brakerski--Döttling Gaussian theorem.  Lean proves the
subsequent descriptor integration natively. -/
structure AveragedGaussianLossinessCertificate
    (Descriptor Secret Output : Type)
    [Fintype Descriptor] [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Descriptor] [DecidableEq Secret] [DecidableEq Output]
    (descriptorSampler : ProbComp Descriptor)
    (prior : Descriptor → ProbComp Secret)
    (channel : Descriptor → Secret → ProbComp Output) where
  ringRank : ℕ
  terminalWidth : ℝ
  smoothingError : ℝ
  t1 : Descriptor → ℝ
  t2 : Descriptor → ℝ
  sigma : Descriptor → ℝ
  conditionalEntropy : Descriptor → ℝ
  smoothingThreshold : Descriptor → ℝ
  good : Descriptor → Prop
  goodDecidable : DecidablePred good
  sigma_eq : ∀ descriptor,
    sigma descriptor = terminalWidth / (2 ^ (5 / 2 : ℝ) * t1 descriptor)
  decompositionSlack : ∀ descriptor,
    2 ^ (3 / 2 : ℝ) * t1 descriptor * sigma descriptor < terminalWidth
  good_iff : ∀ descriptor,
    good descriptor ↔ sigma descriptor > t2 descriptor * smoothingThreshold descriptor
  pointwiseGuessing : ∀ descriptor,
    conditionalGuessingProbability
      (conditionalChannelJoint (prior descriptor) (channel descriptor)) ≤
        @averagedGaussianDescriptorBound Descriptor good goodDecidable ringRank t2
          conditionalEntropy smoothingError descriptor

/-- Distribution-averaged Gaussian lossiness: no fixed good event or worst-case `(T1,T2)` is
charged after the pointwise theorem has been certified. -/
theorem averagedGaussianLossinessBound
    {Descriptor Secret Output : Type}
    [Fintype Descriptor] [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Descriptor] [DecidableEq Secret] [DecidableEq Output]
    (descriptorSampler : ProbComp Descriptor)
    (prior : Descriptor → ProbComp Secret)
    (channel : Descriptor → Secret → ProbComp Output)
    (certificate : AveragedGaussianLossinessCertificate Descriptor Secret Output
      descriptorSampler prior channel) :
    conditionalGuessingProbability
        (contextualChannelJoint descriptorSampler prior channel) ≤
      ∑ descriptor, Pr[= descriptor | descriptorSampler] *
        @averagedGaussianDescriptorBound Descriptor certificate.good
          certificate.goodDecidable certificate.ringRank certificate.t2
          certificate.conditionalEntropy certificate.smoothingError descriptor := by
  letI : DecidablePred certificate.good := certificate.goodDecidable
  exact distributionAveragedGuessingBound descriptorSampler prior channel _
    certificate.pointwiseGuessing

end

end FormalProof4FHE.RLWE.RankOneHNFLossinessRefined
