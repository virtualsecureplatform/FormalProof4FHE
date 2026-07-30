/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.RankBound
import FormalProof4FHE.TFHE.DirectSubsetKeyBRK
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Prod

/-!
# Joint Subset-Key BRK/KSK Security

This module formalizes the conditional joint-constructor theorem for a subset-key
bootstrapping key accompanied by a key-switch key carrying unknown suffix messages.

The master secret is split into a prefix and suffix.  A KSK row is affine in the combined
secret, but its random mask is supported only on the prefix.  The first section proves that this
random part has zero overlap with the hidden-suffix embedding.  Thus a per-row full-overlap
subspace simulator cannot be used in the orientation where the prefix is sampled and the suffix
is the source-problem secret.

The replacement is a constrained batch factorization.  For a public source operator `A` and
gadget map `G`, a certificate supplies `L` with `L.comp A = G`.  The checked identity

`L (A z + e) = G z + L e`

shows that the resulting KSK has the exact mask and message terms; only its complete derived-error
law remains to be compared with the prescribed KSK error law.

The probabilistic section states that comparison on the full retained joint state.  A patched
target agrees with the simulator on factorization failure and with the prescribed target on
success.  Triangle inequality and an identical-until-failure TV bound give exactly
`noiseError + factorizationError` for each real branch.

Finally, the existing direct subset-key public-view constructor is specialized to obtain

`Adv jointReal jointZero ≤ 2 * Adv source + 2 * factorizationError +
  2 * noiseError + uniformError + auxiliaryError`.

The finite-field section proves existence of the factorization from full column rank and bounds
its failure probability by the exact rectangular rank experiment.  No claim is made that the
resulting left inverse is short or that its derived error is close to a correctness-compatible
KSK error; that is deliberately retained as the explicit full-joint noise premise.
-/

open Matrix OracleComp
open scoped ENNReal

namespace FormalProof4FHE.TFHE.JointSubsetKeyBRK

/-! ## The per-row hidden-suffix overlap obstruction -/

section Overlap

variable {R Prefix Suffix : Type}
  [Semiring R]
  [AddCommMonoid Prefix] [Module R Prefix]
  [AddCommMonoid Suffix] [Module R Suffix]

/-- Embed the prefix into the combined prefix/suffix secret. -/
def prefixEmbedding : Prefix →ₗ[R] Prefix × Suffix :=
  LinearMap.inl R Prefix Suffix

/-- Embed the suffix into the combined prefix/suffix secret. -/
def suffixEmbedding : Suffix →ₗ[R] Prefix × Suffix :=
  LinearMap.inr R Prefix Suffix

/-- Linear part of a KSK mask: retain the prefix coordinates and zero the suffix coordinates.
The fixed suffix gadget coefficient is an affine offset, not part of this map. -/
def prefixRandomPart : Prefix × Suffix →ₗ[R] Prefix × Suffix :=
  (prefixEmbedding (R := R)).comp (LinearMap.fst R Prefix Suffix)

@[simp]
theorem prefixRandomPart_apply (value : Prefix × Suffix) :
    prefixRandomPart (R := R) value = (value.1, 0) := by
  rfl

@[simp]
theorem prefixRandomPart_comp_suffixEmbedding :
    (prefixRandomPart (R := R) (Prefix := Prefix) (Suffix := Suffix)).comp
      (suffixEmbedding (R := R) (Prefix := Prefix) (Suffix := Suffix)) =
      (0 : Suffix →ₗ[R] Prefix × Suffix) := by
  ext suffix <;> rfl

/-- In the opposite orientation, the same KSK random part has complete overlap with the hidden
prefix embedding. -/
@[simp]
theorem prefixRandomPart_comp_prefixEmbedding :
    (prefixRandomPart (R := R) (Prefix := Prefix) (Suffix := Suffix)).comp
        (prefixEmbedding (R := R) (Prefix := Prefix) (Suffix := Suffix)) =
      prefixEmbedding (R := R) (Prefix := Prefix) (Suffix := Suffix) := by
  ext value <;> rfl

end Overlap

/-! ## Constrained batch factorization and exact KSK algebra -/

section Factorization

variable {R VZ W T : Type}
  [Semiring R]
  [AddCommMonoid VZ] [Module R VZ]
  [AddCommMonoid W] [Module R W]
  [AddCommMonoid T] [Module R T]

/-- A public solution of the constrained batch equation `L ∘ A = G`. -/
structure Factorization (source : VZ →ₗ[R] W) (gadget : VZ →ₗ[R] T) where
  postprocess : W →ₗ[R] T
  postprocess_comp : postprocess.comp source = gadget

namespace Factorization

variable {source : VZ →ₗ[R] W} {gadget : VZ →ₗ[R] T}

/-- A factorization maps every source encoding to the required gadget encoding. -/
@[simp]
theorem apply_source (certificate : Factorization source gadget) (suffix : VZ) :
    certificate.postprocess (source suffix) = gadget suffix := by
  have h := congrArg (fun map : VZ →ₗ[R] T => map suffix) certificate.postprocess_comp
  simpa using h

/-- Exact constrained-solver identity on a noisy real source body. -/
theorem apply_real (certificate : Factorization source gadget) (suffix : VZ) (error : W) :
    certificate.postprocess (source suffix + error) =
      gadget suffix + certificate.postprocess error := by
  rw [map_add, certificate.apply_source]

/-- Any factorization forces the source kernel to lie in the gadget kernel. -/
theorem ker_source_le_ker_gadget (certificate : Factorization source gadget) :
    LinearMap.ker source ≤ LinearMap.ker gadget := by
  intro suffix hsuffix
  rw [LinearMap.mem_ker] at hsuffix ⊢
  rw [← certificate.postprocess_comp]
  simp [hsuffix]

end Factorization

/-- Assemble the public mask together with its prefix, gadget-message, and error body terms. -/
def targetKSKValue {Mask : Type} (mask : Mask) (prefixTerm message error : T) : Mask × T :=
  (mask, prefixTerm + message + error)

/-- Assemble a KSK value directly from a constrained source body. -/
def simulatedKSKValue {Mask : Type} (mask : Mask) (prefixTerm : T)
    (postprocess : W →ₗ[R] T) (sourceBody : W) : Mask × T :=
  (mask, prefixTerm + postprocess sourceBody)

/-- On a real source body, constrained postprocessing gives exactly the prescribed message and
the complete derived error. -/
theorem simulatedKSKValue_real {Mask : Type} (mask : Mask) (prefixTerm : T)
    {source : VZ →ₗ[R] W} {gadget : VZ →ₗ[R] T}
    (certificate : Factorization source gadget) (suffix : VZ) (error : W) :
    simulatedKSKValue mask prefixTerm certificate.postprocess (source suffix + error) =
      targetKSKValue mask prefixTerm (gadget suffix) (certificate.postprocess error) := by
  rw [simulatedKSKValue, targetKSKValue, certificate.apply_real, add_assoc]

end Factorization

/-! ## Full-joint error replacement and factorization failure -/

section FailureAndNoise

/-- Replace the target continuation by a branch-independent fallback exactly on bad contexts. -/
def patchedTarget {Context View : Type} (bad : Context → Prop) [DecidablePred bad]
    (fallback target : Context → ProbComp View) (context : Context) : ProbComp View :=
  if bad context then fallback context else target context

/-- The patched target differs from the prescribed target by at most the bad-context
probability.  No distributional property of the fallback is required. -/
theorem tvDist_patchedTarget_target_le {Context View : Type}
    (contextSampler : ProbComp Context) (bad : Context → Prop) [DecidablePred bad]
    (fallback target : Context → ProbComp View) :
    tvDist
        (contextSampler >>= patchedTarget bad fallback target)
        (contextSampler >>= target) ≤
      Pr[bad | contextSampler].toReal := by
  apply tvDist_bind_left_event_le
  intro context hgood
  simp [patchedTarget, hgood]

/-- Full-joint KSK simulation lemma.

`simulated` may retain every public variable correlated with the derived error.  The noise premise
compares it with a patched target which uses the same fallback on factorization failure and the
prescribed target on success.  Removing the patch costs only the failure probability. -/
theorem tvDist_simulated_target_le_noise_add_failure {Context View : Type}
    (contextSampler : ProbComp Context) (bad : Context → Prop) [DecidablePred bad]
    (simulated : ProbComp View) (fallback target : Context → ProbComp View)
    (noiseError factorizationError : ℝ)
    (hnoise : tvDist simulated
        (contextSampler >>= patchedTarget bad fallback target) ≤ noiseError)
    (hfailure : Pr[bad | contextSampler].toReal ≤ factorizationError) :
    tvDist simulated (contextSampler >>= target) ≤ noiseError + factorizationError := by
  calc
    tvDist simulated (contextSampler >>= target) ≤
        tvDist simulated (contextSampler >>= patchedTarget bad fallback target) +
          tvDist (contextSampler >>= patchedTarget bad fallback target)
            (contextSampler >>= target) :=
      tvDist_triangle _ _ _
    _ ≤ noiseError + factorizationError :=
      add_le_add hnoise
        ((tvDist_patchedTarget_target_le contextSampler bad fallback target).trans hfailure)

/-- Deterministic assembly of a complete retained state and error cannot increase its joint
error-law distance.  This is the data-processing step required by the joint, rather than
coordinatewise, noise premise. -/
theorem tvDist_postprocess_jointError_le {State View : Type}
    (assemble : State → View) (derived prescribed : ProbComp State) :
    tvDist (assemble <$> derived) (assemble <$> prescribed) ≤
      tvDist derived prescribed :=
  tvDist_map_le assemble derived prescribed

end FailureAndNoise

/-! ## Defect accounting for the joint BRK/KSK constructor -/

section JointConstructor

open DirectSubsetKeyBRK

variable {Sample Secret Output Prefix View : Type} [Add Output]
  {problem : LearningWithErrors.Problem Sample Secret Output}
  {prefixSampler : ProbComp Prefix} {targetView : Bool → ProbComp View}

/-- Certificate decomposing the three public-constructor distances into factorization, complete
joint-noise, uniform-branch, and additional auxiliary-view defects. -/
structure DefectCertificate
    (constructor : PublicViewConstructor problem prefixSampler targetView) where
  factorizationError : ℝ
  noiseError : ℝ
  uniformError : ℝ
  auxiliaryRealError : Bool → ℝ
  auxiliaryUniformError : ℝ
  factorizationError_nonneg : 0 ≤ factorizationError
  noiseError_nonneg : 0 ≤ noiseError
  uniformError_nonneg : 0 ≤ uniformError
  auxiliaryRealError_nonneg : ∀ branch, 0 ≤ auxiliaryRealError branch
  auxiliaryUniformError_nonneg : 0 ≤ auxiliaryUniformError
  realError_le : ∀ branch,
    constructor.realError branch ≤
      factorizationError + noiseError + auxiliaryRealError branch
  constructorUniformError_le :
    constructor.uniformError ≤ uniformError + auxiliaryUniformError

namespace DefectCertificate

variable {constructor : PublicViewConstructor problem prefixSampler targetView}

/-- Sum of every additional real-branch and uniform-branch auxiliary defect. -/
def auxiliaryError (certificate : DefectCertificate constructor) : ℝ :=
  certificate.auxiliaryRealError true + certificate.auxiliaryRealError false +
    certificate.auxiliaryUniformError

theorem auxiliaryError_nonneg (certificate : DefectCertificate constructor) :
    0 ≤ certificate.auxiliaryError := by
  unfold auxiliaryError
  have htrue := certificate.auxiliaryRealError_nonneg true
  have hfalse := certificate.auxiliaryRealError_nonneg false
  have huniform := certificate.auxiliaryUniformError_nonneg
  linarith

/-- **Joint subset-key BRK/KSK theorem.**  A constrained batch constructor removes the intact
BRK/KSK correlation with no whole-key guessing loss.  Each real branch pays one factorization
and one full-joint noise defect; the common uniform branch is paid once. -/
theorem targetAdvantage_le_two_source_add_joint_errors
    (certificate : DefectCertificate constructor)
    (distinguisher : Distinguisher View) :
    targetAdvantage targetView distinguisher ≤
      2 * LearningWithErrors.advantage problem (constructor.reduction distinguisher) +
        2 * certificate.factorizationError + 2 * certificate.noiseError +
        certificate.uniformError + certificate.auxiliaryError := by
  have hbase := constructor.targetAdvantage_le_two_source_add_errors distinguisher
  have hrealTrue := certificate.realError_le true
  have hrealFalse := certificate.realError_le false
  have huniform := certificate.constructorUniformError_le
  unfold auxiliaryError
  linarith

end DefectCertificate

end JointConstructor

/-! ## Finite-field existence and rank-failure bounds -/

section FieldFactorization

variable {F VZ W T : Type}
  [Field F]
  [AddCommGroup VZ] [Module F VZ]
  [AddCommGroup W] [Module F W]
  [AddCommGroup T] [Module F T]

/-- Over a field, every injective source map has a linear left inverse and hence factors every
public gadget map. -/
noncomputable def factorizationOfInjective
    (source : VZ →ₗ[F] W) (gadget : VZ →ₗ[F] T)
    (hsource : Function.Injective source) : Factorization source gadget where
  postprocess := gadget.comp source.leftInverse
  postprocess_comp := by
    rw [LinearMap.comp_assoc,
      source.leftInverse_comp_of_inj (LinearMap.ker_eq_bot.mpr hsource)]
    rfl

theorem exists_factorization_of_injective
    (source : VZ →ₗ[F] W) (gadget : VZ →ₗ[F] T)
    (hsource : Function.Injective source) :
    ∃ postprocess : W →ₗ[F] T, postprocess.comp source = gadget :=
  ⟨(factorizationOfInjective source gadget hsource).postprocess,
    (factorizationOfInjective source gadget hsource).postprocess_comp⟩

/-- Full column rank makes the matrix-vector source map injective. -/
theorem mulVec_injective_of_rank_eq_width {rows columns : ℕ}
    (matrix : Matrix (Fin rows) (Fin columns) F)
    (hfull : matrix.rank = columns) :
    Function.Injective matrix.mulVecLin := by
  change Function.Injective matrix.mulVec
  rw [Matrix.mulVec_injective_iff, linearIndependent_iff_card_eq_finrank_span]
  change Fintype.card (Fin columns) =
    Module.finrank F (Submodule.span F (Set.range matrix.col))
  rw [← matrix.rank_eq_finrank_span_cols]
  simpa using hfull.symm

/-- Every gadget map factors through a full-column-rank public source matrix. -/
noncomputable def fullRankFactorization {rows columns : ℕ}
    (matrix : Matrix (Fin rows) (Fin columns) F)
    (gadget : (Fin columns → F) →ₗ[F] T)
    (hfull : matrix.rank = columns) :
    Factorization matrix.mulVecLin gadget :=
  factorizationOfInjective matrix.mulVecLin gadget
    (mulVec_injective_of_rank_eq_width matrix hfull)

theorem exists_factorization_of_rank_eq_width {rows columns : ℕ}
    (matrix : Matrix (Fin rows) (Fin columns) F)
    (gadget : (Fin columns → F) →ₗ[F] T)
    (hfull : matrix.rank = columns) :
    ∃ postprocess : (Fin rows → F) →ₗ[F] T,
      postprocess.comp matrix.mulVecLin = gadget :=
  ⟨(fullRankFactorization matrix gadget hfull).postprocess,
    (fullRankFactorization matrix gadget hfull).postprocess_comp⟩

end FieldFactorization

section FieldProbability

variable {F T : Type}
  [Field F] [SampleableType F]
  [AddCommGroup T] [Module F T]

/-- Failure of the public factorization equation is contained in rectangular rank failure. -/
theorem factorizationFailure_le_rankFailure (rows columns : ℕ)
    (gadget : (Fin columns → F) →ₗ[F] T) :
    Pr[(fun matrix : Matrix (Fin rows) (Fin columns) F ↦
        ¬∃ postprocess : (Fin rows → F) →ₗ[F] T,
          postprocess.comp matrix.mulVecLin = gadget) |
        ($ᵗ Matrix (Fin rows) (Fin columns) F)] ≤
      Pr[(fun matrix : Matrix (Fin rows) (Fin columns) F ↦
        matrix.rank < columns) |
        ($ᵗ Matrix (Fin rows) (Fin columns) F)] := by
  classical
  apply probEvent_mono
  intro matrix _ hfailure
  have hrank := Matrix.rank_le_width matrix
  by_contra hnotlt
  have hfull : matrix.rank = columns := by omega
  exact hfailure (exists_factorization_of_rank_eq_width matrix gadget hfull)

/-- Exact normalized product for the rectangular rank experiment controlling factorization
failure. -/
theorem rankFailure_toReal_eq_product [Fintype F]
    (rows columns : ℕ) (hcolumns : columns ≤ rows) :
    (Pr[(fun matrix : Matrix (Fin rows) (Fin columns) F ↦
      matrix.rank < columns) |
      ($ᵗ Matrix (Fin rows) (Fin columns) F)]).toReal =
      1 - ∏ index : Fin columns,
        (1 - (Fintype.card F : ℝ) ^ index.val /
          (Fintype.card F : ℝ) ^ rows) :=
  FormalProof4FHE.FiniteFieldRank.rankFailure_toReal_eq rows columns hcolumns

/-- Geometric-sum bound for failure of the constrained factorization over a field. -/
theorem factorizationFailure_toReal_le_sum [Fintype F] (rows columns : ℕ)
    (hcolumns : columns ≤ rows)
    (gadget : (Fin columns → F) →ₗ[F] T) :
    (Pr[(fun matrix : Matrix (Fin rows) (Fin columns) F ↦
        ¬∃ postprocess : (Fin rows → F) →ₗ[F] T,
          postprocess.comp matrix.mulVecLin = gadget) |
        ($ᵗ Matrix (Fin rows) (Fin columns) F)]).toReal ≤
      ∑ index : Fin columns,
        (Fintype.card F : ℝ) ^ index.val /
          (Fintype.card F : ℝ) ^ rows := by
  have hfactor := factorizationFailure_le_rankFailure rows columns gadget
  have hfactorReal := ENNReal.toReal_mono probEvent_ne_top hfactor
  exact hfactorReal.trans
    (FormalProof4FHE.FiniteFieldRank.rankFailure_toReal_le_sum
      rows columns hcolumns)

/-- A uniformly sampled source matrix with extra rows fails to factor the gadget map only with
the standard finite-field rectangular-rank loss. -/
theorem factorizationFailure_le [Fintype F] (dimension slack : ℕ)
    (gadget : (Fin dimension → F) →ₗ[F] T) :
    Pr[(fun matrix : Matrix (Fin (dimension + slack)) (Fin dimension) F ↦
        ¬∃ postprocess : (Fin (dimension + slack) → F) →ₗ[F] T,
          postprocess.comp matrix.mulVecLin = gadget) |
        ($ᵗ Matrix (Fin (dimension + slack)) (Fin dimension) F)] ≤
      2 / (Fintype.card F : ℝ≥0∞) ^ (slack + 1) :=
  (factorizationFailure_le_rankFailure (dimension + slack) dimension gadget).trans
    (FormalProof4FHE.FiniteFieldRank.rankFailure_le dimension slack)

end FieldProbability

end FormalProof4FHE.TFHE.JointSubsetKeyBRK
