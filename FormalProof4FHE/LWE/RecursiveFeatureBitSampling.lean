/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.RecursiveFeatureSecurityParameters

/-!
# Fair-bit implementation of the complete recursive-feature key sampler

The binary secret and every full-coordinate mask are sampled with fair-bit
queries. The interval error sampler already uses bounded fair-bit rejection.
The resulting completed public key and original-bit controls have exactly the
canonical security-family distribution, including all shared-key correlations.
Its worst-case fair-bit query count is polynomial in the security parameter.

This bounds randomness queries, not deterministic bit-operation costs. It does
not prove the unresolved cubic-control security reduction or full PPT closure.
-/

open Matrix OracleComp

namespace FormalProof4FHE.LWE.RecursiveFeatureBitSampling

open RecursiveMultiplication RecursiveFeatureGSW RecursiveFeatureBootstrap
open RecursiveFeatureSecurityView RecursiveQuadraticParameters
open RecursiveFeaturePublicKeyParameters

local instance (width : ℕ) : NeZero (2 ^ width) := ⟨by positivity⟩

def residueSampler (width : ℕ) : ProbComp (ZMod (2 ^ width)) :=
  (ZMod.finEquiv (2 ^ width)) <$> BoundedUniform.drawBits width

def secretSampler (dimension : ℕ) : ProbComp (Fin dimension → Bool) :=
  ProbComp.sampleIID dimension (finTwoEquiv <$> BoundedUniform.drawBits 1)

theorem residueSampler_evalDist (width : ℕ) :
    𝒟[residueSampler width] = 𝒟[$ᵗ (ZMod (2 ^ width))] := by
  have h := evalDist_map_eq_of_evalDist_eq (BoundedUniform.evalDist_drawBits width)
    (ZMod.finEquiv (2 ^ width))
  exact h.trans (evalDist_map_bijective_uniform_cross _ _ (ZMod.finEquiv (2 ^ width)).bijective)

theorem secretSampler_evalDist (dimension : ℕ) :
    𝒟[secretSampler dimension] = 𝒟[$ᵗ (Fin dimension → Bool)] := by
  have h := evalDist_map_eq_of_evalDist_eq (BoundedUniform.evalDist_drawBits 1) finTwoEquiv
  have hbit := h.trans (evalDist_map_bijective_uniform_cross _ _ finTwoEquiv.bijective)
  exact (FormalProof4FHE.SharedRandomness.sampleIID_evalDist_congr dimension hbit).trans
    (FiniteProduct.evalDist_sampleIID_uniform dimension)

theorem coinBound_sampleIID {Alpha : Type} (count : ℕ) (sampler : ProbComp Alpha) (budget : ℕ)
    (h : BoundedUniform.CoinBound sampler budget) :
    BoundedUniform.CoinBound (ProbComp.sampleIID count sampler) (count * budget) := by
  induction count with
  | zero => exact BoundedUniform.coinBound_pure _ _
  | succ count ih =>
      have htail (head : Alpha) : BoundedUniform.CoinBound
          (ProbComp.sampleIID count sampler >>= fun tail ↦ pure (Fin.cons (α := fun _ ↦ Alpha) head tail))
          (count * budget) := by
        simpa only [map_eq_bind_pure_comp, Function.comp_def] using
          BoundedUniform.coinBound_map (fun tail : Fin count → Alpha ↦ Fin.cons (α := fun _ ↦ Alpha) head tail) ih
      simpa only [ProbComp.sampleIID, Fin.mOfFn, Nat.succ_mul, Nat.add_comm,
        map_eq_bind_pure_comp, Function.comp_def] using
        BoundedUniform.coinBound_bind h htail

theorem coinBound_residueSampler (width : ℕ) :
    BoundedUniform.CoinBound (residueSampler width) width :=
  BoundedUniform.coinBound_map _ (BoundedUniform.coinBound_drawBits width)

theorem coinBound_secretSampler (dimension : ℕ) :
    BoundedUniform.CoinBound (secretSampler dimension) dimension := by
  simpa only [secretSampler, Nat.mul_one] using coinBound_sampleIID dimension
    (finTwoEquiv <$> BoundedUniform.drawBits 1) 1
    (BoundedUniform.coinBound_map _ (BoundedUniform.coinBound_drawBits 1))

/-- Public row/column enumeration; no enumeration of all possible matrices is executed. -/
def challengeEquiv {q : ℕ} (params : Parameters q) (n samples : ℕ) :
    (Fin (n * errorCount params n samples) → ZMod q) ≃ Challenge params n samples where
  toFun values row column := values (finProdFinEquiv (row, errorColumnsEquiv params n samples column))
  invFun challenge index := challenge (finProdFinEquiv.symm index).1
    ((errorColumnsEquiv params n samples).symm (finProdFinEquiv.symm index).2)
  left_inv values := by funext index; simp only [Equiv.apply_symm_apply, Prod.mk.eta]
  right_inv challenge := by funext row column; simp

abbrev familyErrorCount (parameter : ℕ) := RecursiveFeatureSecurityParameters.scalarErrorCount parameter

noncomputable local instance (parameter : ℕ) :
    SampleableType (Challenge (params parameter) (dimension parameter) (publicSamples parameter)) :=
  instSampleableTypeFinFunc

def familyResidueSampler (parameter : ℕ) : ProbComp (ZMod (modulus parameter)) := by
  unfold modulus
  exact residueSampler (scale parameter ^ 2)

theorem familyResidueSampler_evalDist (parameter : ℕ) :
    𝒟[familyResidueSampler parameter] = 𝒟[$ᵗ (ZMod (modulus parameter))] := by
  unfold familyResidueSampler modulus
  exact residueSampler_evalDist _

theorem coinBound_familyResidueSampler (parameter : ℕ) :
    BoundedUniform.CoinBound (familyResidueSampler parameter) (scale parameter ^ 2) := by
  unfold familyResidueSampler modulus
  exact coinBound_residueSampler _

def challengeSampler (parameter : ℕ) :
    ProbComp (Challenge (params parameter) (dimension parameter) (publicSamples parameter)) :=
  challengeEquiv (params parameter) (dimension parameter) (publicSamples parameter) <$>
    ProbComp.sampleIID (dimension parameter * familyErrorCount parameter) (familyResidueSampler parameter)

theorem challengeSampler_evalDist (parameter : ℕ) :
    𝒟[challengeSampler parameter] =
      𝒟[$ᵗ (Challenge (params parameter) (dimension parameter) (publicSamples parameter))] := by
  have h := (FormalProof4FHE.SharedRandomness.sampleIID_evalDist_congr
    (dimension parameter * familyErrorCount parameter) (familyResidueSampler_evalDist parameter)).trans
    (FiniteProduct.evalDist_sampleIID_uniform _)
  have hm := evalDist_map_eq_of_evalDist_eq h
    (challengeEquiv (params parameter) (dimension parameter) (publicSamples parameter))
  exact hm.trans (evalDist_map_bijective_uniform_cross _ _
    (challengeEquiv (params parameter) (dimension parameter) (publicSamples parameter)).bijective)

theorem coinBound_challengeSampler (parameter : ℕ) :
    BoundedUniform.CoinBound (challengeSampler parameter)
      (dimension parameter * familyErrorCount parameter * scale parameter ^ 2) := by
  simpa only [challengeSampler, familyErrorCount, RecursiveFeatureSecurityParameters.scalarErrorCount]
    using BoundedUniform.coinBound_map
    (challengeEquiv (params parameter) (dimension parameter) (publicSamples parameter))
    (coinBound_sampleIID _ _ _ (coinBound_familyResidueSampler parameter))

def drawsSampler (parameter : ℕ) :
    ProbComp (Draws (params parameter) (dimension parameter) (publicSamples parameter)) := do
  let bits ← secretSampler (dimension parameter)
  let challenge ← challengeSampler parameter
  let errors ← ProbComp.sampleIID (familyErrorCount parameter)
    (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter))
  pure (bits, challenge, fun column ↦ errors (errorColumnsEquiv (params parameter)
    (dimension parameter) (publicSamples parameter) column))

theorem drawsSampler_evalDist (parameter : ℕ) :
    𝒟[drawsSampler parameter] =
      𝒟[sampleDraws (p := publicSamples parameter) (params parameter)
        ($ᵗ (Fin (dimension parameter) → Bool))
        (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter))] := by
  simp only [drawsSampler, sampleDraws, evalDist_bind, evalDist_pure,
    secretSampler_evalDist, challengeSampler_evalDist]
  rfl

def keygen (parameter : ℕ) :
    ProbComp (StoredView (params parameter) (dimension parameter) (publicSamples parameter) ×
      (Fin (dimension parameter) → Bool)) :=
  (fun draws ↦ (storeView (publicView (params parameter) draws), draws.1)) <$> drawsSampler parameter

/-- Exact complete-key law, including the original secret retained privately. -/
theorem keygen_evalDist (parameter : ℕ) :
    𝒟[keygen parameter] = 𝒟[(RecursiveFeatureSecurityParameters.family parameter).keygen] := by
  exact evalDist_map_eq_of_evalDist_eq (drawsSampler_evalDist parameter) _

def coinBudget (parameter : ℕ) : ℕ :=
  dimension parameter + (dimension parameter * familyErrorCount parameter * scale parameter ^ 2 +
    familyErrorCount parameter * (scale parameter ^ 2 * (parameter + 3)))

theorem coinBound_drawsSampler (parameter : ℕ) :
    BoundedUniform.CoinBound (drawsSampler parameter) (coinBudget parameter) := by
  apply BoundedUniform.coinBound_bind (coinBound_secretSampler (dimension parameter))
  intro bits
  apply BoundedUniform.coinBound_bind (coinBound_challengeSampler parameter)
  intro challenge
  simpa only [map_eq_bind_pure_comp, Function.comp_def, familyErrorCount,
    RecursiveFeatureSecurityParameters.scalarErrorCount] using BoundedUniform.coinBound_map
    (fun errors ↦ (bits, challenge, fun column ↦ errors (errorColumnsEquiv (params parameter)
      (dimension parameter) (publicSamples parameter) column)))
    (coinBound_sampleIID _ _ _ (RecursiveQuadraticParameters.coinBound_wide parameter))

theorem coinBound_keygen (parameter : ℕ) :
    BoundedUniform.CoinBound (keygen parameter) (coinBudget parameter) :=
  BoundedUniform.coinBound_map _ (coinBound_drawsSampler parameter)

noncomputable def coinBudgetPolynomial : Polynomial ℕ :=
  let n := 2 * (Polynomial.X + 1) ^ 5
  let errors := RecursiveFeatureSecurityParameters.scalarErrorCountPolynomial
  n + (n * errors * (Polynomial.X + 1) ^ 2 + errors * ((Polynomial.X + 1) ^ 2 * (Polynomial.X + 3)))

theorem coinBudgetPolynomial_eval (parameter : ℕ) :
    coinBudgetPolynomial.eval parameter = coinBudget parameter := by
  simp [coinBudgetPolynomial, coinBudget, RecursiveFeatureSecurityParameters.scalarErrorCountPolynomial_eval,
    dimension, binaryDimension, scale]

end FormalProof4FHE.LWE.RecursiveFeatureBitSampling
