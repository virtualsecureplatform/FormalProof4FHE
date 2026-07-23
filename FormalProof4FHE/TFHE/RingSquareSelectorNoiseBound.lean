/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.RingSquareBatchDiscreteGaussianSmudging
import FormalProof4FHE.TFHE.CenteredBinomialCorrectness

/-!
# Explicit Selector-Noise Bounds for the `RGSW_S(-S)` Compiler

The short-preimage compiler contributes the correlated shift

`S * sum_i x_i e_i`.

This file removes the abstract coefficient-bound premise from that expression.  For a native
negacyclic ring of degree `N`, `m` source rows, and coefficient bounds `B_s`, `B_x`, and `B_e`
on the secret, selector weights, and source phases, respectively, it proves the deterministic
bound

`‖S * sum_i x_i e_i‖_∞ ≤ N * (B_s * (m * (N * (B_x * B_e))))`.

No gadget-preimage success assumption is needed for this norm calculation.  Success enters only
when the compiler normal form is used.  The final theorem feeds the explicit expression into the
heterogeneous widened-discrete-Gaussian security reduction.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.SelectorNoise.Native

noncomputable section

/-- The concrete coefficient bound for the residual `S * sum_i x_i e_i`. -/
def inducedShiftBound (degree sourceCount secretBound selectorBound sourcePhaseBound : ℕ) : ℕ :=
  (degree + 1) *
    (secretBound *
      (sourceCount * ((degree + 1) * (selectorBound * sourcePhaseBound))))

/-! ## Exact support projections from the hidden source context -/

/-- The secret retained in a supported compiler context really came from the supplied secret
sampler. -/
theorem secretValue_mem_support_of_contextSampler
    {R Secret : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (context : CompilerNormalForm.Context R Secret levels sourceCount)
    (hContext : context ∈ support
      (CompilerNormalForm.contextSampler levels sourceCount secretSampler embed errorSampler)) :
    context.secretValue ∈ support secretSampler := by
  classical
  unfold CompilerNormalForm.contextSampler at hContext
  rw [mem_support_bind_iff] at hContext
  obtain ⟨challenge, _hChallenge, hContext⟩ := hContext
  rw [mem_support_bind_iff] at hContext
  obtain ⟨secretValue, hSecret, hContext⟩ := hContext
  rw [mem_support_bind_iff] at hContext
  obtain ⟨sourceError, _hSourceError, hContext⟩ := hContext
  simp only [support_pure, Set.mem_singleton_iff] at hContext
  subst context
  exact hSecret

/-- Every selected source-row phase in a supported compiler context is one actual draw from the
source-error sampler. -/
theorem sourcePhase_mem_support_of_contextSampler
    {R Secret : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (context : CompilerNormalForm.Context R Secret levels sourceCount)
    (hContext : context ∈ support
      (CompilerNormalForm.contextSampler levels sourceCount secretSampler embed errorSampler))
    (level : Fin levels) (index : Fin sourceCount) :
    TLWE.phase (embed context.secretValue)
        (Full.sourceRowsAt context.sourceBatch level index) ∈ support errorSampler := by
  classical
  unfold CompilerNormalForm.contextSampler at hContext
  rw [mem_support_bind_iff] at hContext
  obtain ⟨challenge, _hChallenge, hContext⟩ := hContext
  rw [mem_support_bind_iff] at hContext
  obtain ⟨secretValue, _hSecret, hContext⟩ := hContext
  rw [mem_support_bind_iff] at hContext
  obtain ⟨sourceError, hSourceError, hContext⟩ := hContext
  simp only [support_pure, Set.mem_singleton_iff] at hContext
  subst context
  change TLWE.phase (embed secretValue)
      (TLWE.entry (TLWE.batchAssemble (embed secretValue) challenge 0 sourceError)
        (finProdFinEquiv (level, index))) ∈ support errorSampler
  rw [TLWE.phase_entry, TLWE.batchPhase_batchAssemble]
  have hCoordinate := FormalProof4FHE.FiniteProduct.mem_support_fin_mOfFn_apply
    (levels * sourceCount) (fun _ ↦ errorSampler) sourceError
    (by simpa [ProbComp.sampleIID] using hSourceError)
    (finProdFinEquiv (level, index))
  simpa using hCoordinate

/-- Generic weighted sum, retaining one coherent commutative-ring dictionary through every
derived operation. -/
def weightedSourcePhaseGeneric {R Index : Type} [CommRing R] [Fintype Index]
    (weight phase : Index → R) : R :=
  ∑ index, weight index * phase index

/-- Native weighted source phase under the proof-facing negacyclic-ring dictionary. -/
def weightedSourcePhase
    {q degree sourceCount : ℕ}
    (weight phase : Fin sourceCount → RLWE.Rq q (degree + 1)) :
    RLWE.Rq q (degree + 1) :=
  @weightedSourcePhaseGeneric (RLWE.Rq q (degree + 1)) (Fin sourceCount)
    (NoiseBounds.positiveRqCommRing (q := q) (degree := degree)) inferInstance
    weight phase

/-- Native coefficient bound for a weighted source phase, stated with the proof-facing ring
dictionary made explicit. -/
theorem cInfNorm_weightedSourcePhase_le
    {q degree sourceCount : ℕ} [NeZero q]
    (weight : Fin sourceCount → RLWE.Rq q (degree + 1))
    (phase : Fin sourceCount → RLWE.Rq q (degree + 1))
    (selectorBound sourcePhaseBound : ℕ)
    (hWeight : ∀ index,
      LatticeCrypto.cInfNorm (weight index) ≤ selectorBound)
    (hPhase : ∀ index,
      LatticeCrypto.cInfNorm (phase index) ≤ sourcePhaseBound) :
    LatticeCrypto.cInfNorm (weightedSourcePhase weight phase) ≤
      sourceCount * ((degree + 1) * (selectorBound * sourcePhaseBound)) := by
  unfold weightedSourcePhase weightedSourcePhaseGeneric
  calc
    LatticeCrypto.cInfNorm
        (@Finset.sum (Fin sourceCount) (RLWE.Rq q (degree + 1))
          (NoiseBounds.positiveRqCommRing (q := q)
            (degree := degree)).toCommSemiring.toSemiring.toAddCommMonoid
          Finset.univ
          (fun index ↦
            @HMul.hMul (RLWE.Rq q (degree + 1)) (RLWE.Rq q (degree + 1))
              (RLWE.Rq q (degree + 1))
              (@instHMul (RLWE.Rq q (degree + 1))
                (NoiseBounds.positiveRqCommRing (q := q)
                  (degree := degree)).toCommSemiring.toSemiring.toMul)
              (weight index) (phase index))) ≤
        ∑ index : Fin sourceCount,
          LatticeCrypto.cInfNorm
            (@HMul.hMul (RLWE.Rq q (degree + 1)) (RLWE.Rq q (degree + 1))
              (RLWE.Rq q (degree + 1))
              (@instHMul (RLWE.Rq q (degree + 1))
                (NoiseBounds.positiveRqCommRing (q := q)
                  (degree := degree)).toCommSemiring.toSemiring.toMul)
              (weight index) (phase index)) := by
      simpa using NoiseBounds.cInfNorm_finset_sum_le
        (fun index : Fin sourceCount ↦
          @HMul.hMul (RLWE.Rq q (degree + 1)) (RLWE.Rq q (degree + 1))
            (RLWE.Rq q (degree + 1))
            (@instHMul (RLWE.Rq q (degree + 1))
              (NoiseBounds.positiveRqCommRing (q := q)
                (degree := degree)).toCommSemiring.toSemiring.toMul)
            (weight index) (phase index)) Finset.univ
    _ ≤ ∑ _index : Fin sourceCount,
        (degree + 1) * (selectorBound * sourcePhaseBound) := by
      apply Finset.sum_le_sum
      intro index _
      exact (SharpRotationNoise.cInfNorm_mul_le_linear
        (weight index) (phase index)).trans
          (Nat.mul_le_mul_left (degree + 1)
            (Nat.mul_le_mul (hWeight index) (hPhase index)))
    _ = sourceCount * ((degree + 1) * (selectorBound * sourcePhaseBound)) := by
      simp

/-- The explicit weighted source phase is exactly the phase of the public preimage
combination. -/
theorem phase_preimageCombination_eq_weightedSourcePhase
    {q degree sourceCount : ℕ}
    (secret : Fin 1 → RLWE.Rq q (degree + 1))
    (weight : Fin sourceCount → RLWE.Rq q (degree + 1))
    (sourceRows : Fin sourceCount → TLWE.Ciphertext (RLWE.Rq q (degree + 1)) 1) :
    @TLWE.phase (RLWE.Rq q (degree + 1))
        (NoiseBounds.positiveRqCommRing (q := q) (degree := degree)).toRing 1 secret
        (@preimageCombination (RLWE.Rq q (degree + 1)) (Fin sourceCount)
          (NoiseBounds.positiveRqCommRing (q := q)
            (degree := degree)).toCommSemiring.toSemiring
          inferInstance weight sourceRows) =
      weightedSourcePhase weight (fun index ↦
        @TLWE.phase (RLWE.Rq q (degree + 1))
          (NoiseBounds.positiveRqCommRing (q := q) (degree := degree)).toRing 1 secret
          (sourceRows index)) := by
  simpa [weightedSourcePhase, weightedSourcePhaseGeneric] using
    (@phase_preimageCombination_eq_weighted
      (RLWE.Rq q (degree + 1)) (Fin sourceCount)
      (NoiseBounds.positiveRqCommRing (q := q) (degree := degree)) inferInstance
      secret weight sourceRows)

/-- A weighted sum of `m` concrete source-row phases costs one linear
negacyclic-convolution factor per summand. -/
theorem cInfNorm_phase_preimageCombination_le
    {q degree sourceCount : ℕ} [NeZero q]
    (secret : Fin 1 → RLWE.Rq q (degree + 1))
    (weight : Fin sourceCount → RLWE.Rq q (degree + 1))
    (sourceRows : Fin sourceCount → TLWE.Ciphertext (RLWE.Rq q (degree + 1)) 1)
    (selectorBound sourcePhaseBound : ℕ)
    (hWeight : ∀ index,
      LatticeCrypto.cInfNorm (weight index) ≤ selectorBound)
    (hPhase : ∀ index,
      LatticeCrypto.cInfNorm
          (@TLWE.phase (RLWE.Rq q (degree + 1))
            (NoiseBounds.positiveRqCommRing (q := q) (degree := degree)).toRing 1
            secret (sourceRows index)) ≤ sourcePhaseBound) :
    LatticeCrypto.cInfNorm
        (@TLWE.phase (RLWE.Rq q (degree + 1))
          (NoiseBounds.positiveRqCommRing (q := q) (degree := degree)).toRing 1 secret
          (@preimageCombination (RLWE.Rq q (degree + 1)) (Fin sourceCount)
            (NoiseBounds.positiveRqCommRing (q := q)
              (degree := degree)).toCommSemiring.toSemiring
            inferInstance weight sourceRows)) ≤
      sourceCount * ((degree + 1) * (selectorBound * sourcePhaseBound)) := by
  rw [phase_preimageCombination_eq_weightedSourcePhase]
  exact cInfNorm_weightedSourcePhase_le weight
    (fun index ↦
      @TLWE.phase (RLWE.Rq q (degree + 1))
        (NoiseBounds.positiveRqCommRing (q := q) (degree := degree)).toRing 1 secret
        (sourceRows index)) selectorBound sourcePhaseBound hWeight hPhase

/-- Explicit deterministic coefficient bound for one compiler-induced square-row shift. -/
theorem cInfNorm_inducedShift_le
    {q degree sourceCount : ℕ} [NeZero q]
    (secret : Fin 1 → RLWE.Rq q (degree + 1))
    (weight : Fin sourceCount → RLWE.Rq q (degree + 1))
    (sourceRows : Fin sourceCount → TLWE.Ciphertext (RLWE.Rq q (degree + 1)) 1)
    (secretBound selectorBound sourcePhaseBound : ℕ)
    (hSecret : LatticeCrypto.cInfNorm (secret 0) ≤ secretBound)
    (hWeight : ∀ index,
      LatticeCrypto.cInfNorm (weight index) ≤ selectorBound)
    (hPhase : ∀ index,
      LatticeCrypto.cInfNorm
          (@TLWE.phase (RLWE.Rq q (degree + 1))
            (NoiseBounds.positiveRqCommRing (q := q) (degree := degree)).toRing 1
            secret (sourceRows index)) ≤ sourcePhaseBound) :
    LatticeCrypto.cInfNorm
        (@ResidualSmudging.inducedShift (RLWE.Rq q (degree + 1)) (Fin sourceCount)
          (NoiseBounds.positiveRqCommRing (q := q) (degree := degree)) inferInstance
          secret weight sourceRows) ≤
      inducedShiftBound degree sourceCount secretBound selectorBound sourcePhaseBound := by
  change LatticeCrypto.cInfNorm
      (@Mul.mul (RLWE.Rq q (degree + 1))
        (NoiseBounds.positiveRqCommRing (q := q) (degree := degree)).toMul
        (secret 0)
        (@TLWE.phase (RLWE.Rq q (degree + 1))
          (NoiseBounds.positiveRqCommRing (q := q) (degree := degree)).toRing 1 secret
          (@preimageCombination (RLWE.Rq q (degree + 1)) (Fin sourceCount)
            (NoiseBounds.positiveRqCommRing (q := q)
              (degree := degree)).toCommSemiring.toSemiring
            inferInstance weight sourceRows))) ≤ _
  unfold inducedShiftBound
  exact (SharpRotationNoise.cInfNorm_mul_le_linear
      (secret 0)
      (@TLWE.phase (RLWE.Rq q (degree + 1))
        (NoiseBounds.positiveRqCommRing (q := q) (degree := degree)).toRing 1 secret
        (@preimageCombination (RLWE.Rq q (degree + 1)) (Fin sourceCount)
          (NoiseBounds.positiveRqCommRing (q := q)
            (degree := degree)).toCommSemiring.toSemiring
          inferInstance weight sourceRows))).trans
    (Nat.mul_le_mul_left (degree + 1)
      (Nat.mul_le_mul hSecret
        (cInfNorm_phase_preimageCombination_le secret weight sourceRows
          selectorBound sourcePhaseBound hWeight hPhase)))

/-- The preceding estimate specialized to the source pool and level selector stored by the full
compiler. -/
theorem cInfNorm_contextShift_le
    {q degree levels sourceCount : ℕ} [NeZero q]
    (secret : Fin 1 → RLWE.Rq q (degree + 1))
    (selectors : Full.Selectors (RLWE.Rq q (degree + 1)) levels sourceCount)
    (sourceBatch : Full.SourceBatch (RLWE.Rq q (degree + 1)) levels sourceCount)
    (level : Fin levels) (secretBound selectorBound sourcePhaseBound : ℕ)
    (hSecret : LatticeCrypto.cInfNorm (secret 0) ≤ secretBound)
    (hWeight : ∀ index,
      LatticeCrypto.cInfNorm
          (selectors level
            (sourceMasks (Full.sourceRowsAt sourceBatch level)) index) ≤ selectorBound)
    (hPhase : ∀ index,
      LatticeCrypto.cInfNorm
          (@TLWE.phase (RLWE.Rq q (degree + 1))
            (NoiseBounds.positiveRqCommRing (q := q) (degree := degree)).toRing 1 secret
            (Full.sourceRowsAt sourceBatch level index)) ≤ sourcePhaseBound) :
    LatticeCrypto.cInfNorm
        (@CompilerNormalForm.contextShift (RLWE.Rq q (degree + 1))
          (NoiseBounds.positiveRqCommRing (q := q) (degree := degree))
          levels sourceCount secret selectors sourceBatch level) ≤
      inducedShiftBound degree sourceCount secretBound selectorBound sourcePhaseBound := by
  exact cInfNorm_inducedShift_le (q := q) (degree := degree) secret
    (selectors level (sourceMasks (Full.sourceRowsAt sourceBatch level)))
    (Full.sourceRowsAt sourceBatch level) secretBound selectorBound sourcePhaseBound
    hSecret hWeight hPhase

/-- Support-wise secret, selector, and source-phase bounds imply the exact shift premise used by
the full compiler reduction. -/
theorem cInfNorm_contextShift_le_on_successful_support
    {q degree levels sourceCount : ℕ} [NeZero q] {Secret : Type}
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → RLWE.Rq q (degree + 1))
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (selectors : Full.Selectors (RLWE.Rq q (degree + 1)) levels sourceCount)
    (secretBound selectorBound sourcePhaseBound : ℕ)
    (hSecret : ∀ context,
      context ∈ support
        (CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
          sourceErrorSampler) →
      LatticeCrypto.cInfNorm (embed context.secretValue 0) ≤ secretBound)
    (hWeight : ∀ context,
      context ∈ support
        (CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
          sourceErrorSampler) →
      CompilerNormalForm.SelectorsSucceed gadget selectors context →
      ∀ level index,
        LatticeCrypto.cInfNorm
            (selectors level
              (sourceMasks (Full.sourceRowsAt context.sourceBatch level)) index) ≤ selectorBound)
    (hPhase : ∀ context,
      context ∈ support
        (CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
          sourceErrorSampler) →
      CompilerNormalForm.SelectorsSucceed gadget selectors context →
      ∀ level index,
        LatticeCrypto.cInfNorm
            (@TLWE.phase (RLWE.Rq q (degree + 1))
              (NoiseBounds.positiveRqCommRing (q := q) (degree := degree)).toRing 1
              (embed context.secretValue)
              (Full.sourceRowsAt context.sourceBatch level index)) ≤ sourcePhaseBound) :
    ∀ context,
      context ∈ support
        (CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
          sourceErrorSampler) →
      CompilerNormalForm.SelectorsSucceed gadget selectors context →
      ∀ level,
        LatticeCrypto.cInfNorm
            (@CompilerNormalForm.contextShift (RLWE.Rq q (degree + 1))
              (NoiseBounds.positiveRqCommRing (q := q) (degree := degree))
              levels sourceCount (embed context.secretValue) selectors
              context.sourceBatch level) ≤
          inducedShiftBound degree sourceCount secretBound selectorBound sourcePhaseBound := by
  intro context hcontext hSuccess level
  exact cInfNorm_contextShift_le (q := q) (degree := degree)
    (embed context.secretValue) selectors context.sourceBatch level
    secretBound selectorBound sourcePhaseBound
    (hSecret context hcontext)
    (hWeight context hcontext hSuccess level)
    (hPhase context hcontext hSuccess level)

/-- A bounded source-error sampler supplies the source-phase premise automatically.  Thus the
only context-dependent quantitative condition left is shortness of the successful selector. -/
theorem cInfNorm_contextShift_le_on_sampler_support
    {q degree levels sourceCount : ℕ} [NeZero q] {Secret : Type}
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → RLWE.Rq q (degree + 1))
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (selectors : Full.Selectors (RLWE.Rq q (degree + 1)) levels sourceCount)
    (secretBound selectorBound sourceErrorBound : ℕ)
    (hSecret : ∀ secretValue, secretValue ∈ support secretSampler →
      LatticeCrypto.cInfNorm (embed secretValue 0) ≤ secretBound)
    (hWeight : ∀ context,
      context ∈ support
        (CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
          sourceErrorSampler) →
      CompilerNormalForm.SelectorsSucceed gadget selectors context →
      ∀ level index,
        LatticeCrypto.cInfNorm
            (selectors level
              (sourceMasks (Full.sourceRowsAt context.sourceBatch level)) index) ≤ selectorBound)
    (hSourceError : ∀ error, error ∈ support sourceErrorSampler →
      LatticeCrypto.cInfNorm error ≤ sourceErrorBound) :
    ∀ context,
      context ∈ support
        (CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
          sourceErrorSampler) →
      CompilerNormalForm.SelectorsSucceed gadget selectors context →
      ∀ level,
        LatticeCrypto.cInfNorm
            (@CompilerNormalForm.contextShift (RLWE.Rq q (degree + 1))
              (NoiseBounds.positiveRqCommRing (q := q) (degree := degree))
              levels sourceCount (embed context.secretValue) selectors
              context.sourceBatch level) ≤
          inducedShiftBound degree sourceCount secretBound selectorBound sourceErrorBound := by
  intro context hContext hSuccess level
  apply cInfNorm_contextShift_le (q := q) (degree := degree)
    (embed context.secretValue) selectors context.sourceBatch level
    secretBound selectorBound sourceErrorBound
  · exact hSecret context.secretValue
      (secretValue_mem_support_of_contextSampler levels sourceCount secretSampler embed
        sourceErrorSampler context hContext)
  · exact hWeight context hContext hSuccess level
  · intro index
    exact hSourceError _
      (sourcePhase_mem_support_of_contextSampler levels sourceCount secretSampler embed
        sourceErrorSampler context hContext level index)

/-- Fully explicit widened-noise security endpoint.  Sampler-support bounds automatically imply
the corresponding hidden-context bounds.  The only context-dependent quantitative condition is
shortness of a successful selector, and the computational term is ordinary batch-RLWE under the
narrow source-error law. -/
theorem rgswMinusSecretAdvantage_widenedDiscreteGaussian_le_failure_add_explicitNoise_add_batchLWE
    {q degree levels sourceCount : ℕ} [NeZero q] {Secret : Type}
    {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → RLWE.Rq q (degree + 1))
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (selectors : Full.Selectors (RLWE.Rq q (degree + 1)) levels sourceCount)
    (distinguisher : Full.Distinguisher (RLWE.Rq q (degree + 1)) levels)
    (secretBound selectorBound sourceErrorBound : ℕ)
    (hSecret : ∀ secretValue, secretValue ∈ support secretSampler →
      LatticeCrypto.cInfNorm (embed secretValue 0) ≤ secretBound)
    (hWeight : ∀ context,
      context ∈ support
        (CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
          sourceErrorSampler) →
      CompilerNormalForm.SelectorsSucceed gadget selectors context →
      ∀ level index,
        LatticeCrypto.cInfNorm
            (selectors level
              (sourceMasks (Full.sourceRowsAt context.sourceBatch level)) index) ≤ selectorBound)
    (hSourceError : ∀ error, error ∈ support sourceErrorSampler →
      LatticeCrypto.cInfNorm error ≤ sourceErrorBound) :
    Full.rgswMinusSecretAdvantage levels secretSampler embed
        (Heterogeneous.convolutionSampler sourceErrorSampler
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate))
        gadget distinguisher ≤
      (Pr[fun context ↦
            ¬ CompilerNormalForm.SelectorsSucceed gadget selectors context |
          CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
            sourceErrorSampler].toReal +
          (levels : ℝ) *
            (((degree + 1 : ℕ) : ℝ) *
              DiscreteGaussianSampler.scalarLinearShiftBound certificate
                (inducedShiftBound degree sourceCount secretBound selectorBound
                  sourceErrorBound))) +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.embeddedBatchProblem 1
            (levels * sourceCount + TGSW.rowCount 1 levels)
            secretSampler embed sourceErrorSampler)
          (LWE.TwoBlock.convolutionReduction
            (secondErrorSampler := Heterogeneous.convolutionSampler sourceErrorSampler
              (DiscreteGaussianSampler.ringSampler (degree + 1) certificate))
            (extraErrorSampler :=
              DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
            (Heterogeneous.reduction
              (targetErrorSampler := Heterogeneous.convolutionSampler sourceErrorSampler
                (DiscreteGaussianSampler.ringSampler (degree + 1) certificate))
              selectors (Full.restoreDistinguisher gadget distinguisher))) := by
  apply
    BatchResidualSmudging.Native.rgswMinusSecretAdvantage_widenedDiscreteGaussian_le_failure_add_shift_add_batchLWE
      certificate secretSampler embed sourceErrorSampler gadget selectors distinguisher
      (inducedShiftBound degree sourceCount secretBound selectorBound sourceErrorBound)
  exact cInfNorm_contextShift_le_on_sampler_support
    secretSampler embed sourceErrorSampler gadget selectors
    secretBound selectorBound sourceErrorBound hSecret hWeight hSourceError

/-- Centered-binomial hidden source rows give a completely concrete bounded-support instance of
the explicit-noise theorem.  Genuine RGSW rows use the exact convolution of that narrow source
law with the certified widening discrete Gaussian. -/
theorem rgswMinusSecretAdvantage_centeredBinomialSource_widenedDiscreteGaussian_le
    {q degree levels sourceCount eta : ℕ} [NeZero q] {Secret : Type}
    {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → RLWE.Rq q (degree + 1))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (selectors : Full.Selectors (RLWE.Rq q (degree + 1)) levels sourceCount)
    (distinguisher : Full.Distinguisher (RLWE.Rq q (degree + 1)) levels)
    (secretBound selectorBound : ℕ)
    (hSecret : ∀ secretValue, secretValue ∈ support secretSampler →
      LatticeCrypto.cInfNorm (embed secretValue 0) ≤ secretBound)
    (hWeight : ∀ context,
      context ∈ support
        (CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)) →
      CompilerNormalForm.SelectorsSucceed gadget selectors context →
      ∀ level index,
        LatticeCrypto.cInfNorm
            (selectors level
              (sourceMasks (Full.sourceRowsAt context.sourceBatch level)) index) ≤ selectorBound) :
    let sourceErrorSampler := RLWE.CenteredBinomial.sampler q (degree + 1) eta
    let wideningSampler := DiscreteGaussianSampler.ringSampler (degree + 1) certificate
    Full.rgswMinusSecretAdvantage levels secretSampler embed
        (Heterogeneous.convolutionSampler sourceErrorSampler wideningSampler)
        gadget distinguisher ≤
      (Pr[fun context ↦
            ¬ CompilerNormalForm.SelectorsSucceed gadget selectors context |
          CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
            sourceErrorSampler].toReal +
          (levels : ℝ) *
            (((degree + 1 : ℕ) : ℝ) *
              DiscreteGaussianSampler.scalarLinearShiftBound certificate
                (inducedShiftBound degree sourceCount secretBound selectorBound eta))) +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.embeddedBatchProblem 1
            (levels * sourceCount + TGSW.rowCount 1 levels)
            secretSampler embed sourceErrorSampler)
          (LWE.TwoBlock.convolutionReduction
            (secondErrorSampler :=
              Heterogeneous.convolutionSampler sourceErrorSampler wideningSampler)
            (extraErrorSampler := wideningSampler)
            (Heterogeneous.reduction
              (targetErrorSampler :=
                Heterogeneous.convolutionSampler sourceErrorSampler wideningSampler)
              selectors (Full.restoreDistinguisher gadget distinguisher))) := by
  dsimp only
  apply
    rgswMinusSecretAdvantage_widenedDiscreteGaussian_le_failure_add_explicitNoise_add_batchLWE
      certificate secretSampler embed
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      gadget selectors distinguisher secretBound selectorBound eta hSecret hWeight
  intro error hError
  exact CenteredBinomialCorrectness.cInfNorm_le_eta_of_mem_support hError

/-! ## Positive-degree form -/

/-- The residual bound indexed by the actual ring degree rather than by its predecessor. -/
def inducedShiftBoundForDegree
    (ringDegree sourceCount secretBound selectorBound sourcePhaseBound : ℕ) : ℕ :=
  ringDegree *
    (secretBound *
      (sourceCount * (ringDegree * (selectorBound * sourcePhaseBound))))

@[simp]
theorem inducedShiftBoundForDegree_succ
    (degree sourceCount secretBound selectorBound sourcePhaseBound : ℕ) :
    inducedShiftBoundForDegree (degree + 1) sourceCount secretBound selectorBound
        sourcePhaseBound =
      inducedShiftBound degree sourceCount secretBound selectorBound sourcePhaseBound := by
  rfl

/-- The centered-binomial endpoint for any provably positive ring degree.  This wrapper is useful
for production degrees such as `2^d`, which are positive but not syntactically successors. -/
theorem rgswMinusSecretAdvantage_centeredBinomialSource_widenedDiscreteGaussian_le_of_degree_pos
    {q ringDegree levels sourceCount eta : ℕ} [NeZero q] {Secret : Type}
    {alpha : ℝ} {halpha : 0 < alpha}
    (ringDegree_positive : 0 < ringDegree)
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → RLWE.Rq q ringDegree)
    (gadget : Fin levels → RLWE.Rq q ringDegree)
    (selectors : Full.Selectors (RLWE.Rq q ringDegree) levels sourceCount)
    (distinguisher : Full.Distinguisher (RLWE.Rq q ringDegree) levels)
    (secretBound selectorBound : ℕ)
    (hSecret : ∀ secretValue, secretValue ∈ support secretSampler →
      LatticeCrypto.cInfNorm (embed secretValue 0) ≤ secretBound)
    (hWeight : ∀ context,
      context ∈ support
        (CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
          (RLWE.CenteredBinomial.sampler q ringDegree eta)) →
      CompilerNormalForm.SelectorsSucceed gadget selectors context →
      ∀ level index,
        LatticeCrypto.cInfNorm
            (selectors level
              (sourceMasks (Full.sourceRowsAt context.sourceBatch level)) index) ≤ selectorBound) :
    let sourceErrorSampler := RLWE.CenteredBinomial.sampler q ringDegree eta
    let wideningSampler := DiscreteGaussianSampler.ringSampler ringDegree certificate
    Full.rgswMinusSecretAdvantage levels secretSampler embed
        (Heterogeneous.convolutionSampler sourceErrorSampler wideningSampler)
        gadget distinguisher ≤
      (Pr[fun context ↦
            ¬ CompilerNormalForm.SelectorsSucceed gadget selectors context |
          CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
            sourceErrorSampler].toReal +
          (levels : ℝ) *
            ((ringDegree : ℝ) *
              DiscreteGaussianSampler.scalarLinearShiftBound certificate
                (inducedShiftBoundForDegree ringDegree sourceCount secretBound selectorBound
                  eta))) +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.embeddedBatchProblem 1
            (levels * sourceCount + TGSW.rowCount 1 levels)
            secretSampler embed sourceErrorSampler)
          (LWE.TwoBlock.convolutionReduction
            (secondErrorSampler :=
              Heterogeneous.convolutionSampler sourceErrorSampler wideningSampler)
            (extraErrorSampler := wideningSampler)
            (Heterogeneous.reduction
              (targetErrorSampler :=
                Heterogeneous.convolutionSampler sourceErrorSampler wideningSampler)
              selectors (Full.restoreDistinguisher gadget distinguisher))) := by
  obtain ⟨degree, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt ringDegree_positive)
  exact rgswMinusSecretAdvantage_centeredBinomialSource_widenedDiscreteGaussian_le
    certificate secretSampler embed gadget selectors distinguisher secretBound selectorBound
      hSecret hWeight

end

end FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.SelectorNoise.Native
