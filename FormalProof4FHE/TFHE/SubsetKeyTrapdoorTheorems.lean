/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.FiniteProduct
import FormalProof4FHE.Probability.LeftoverHash
import FormalProof4FHE.TFHE.JointSubsetKeyBRKCenteredMixture
import FormalProof4FHE.TFHE.JointSubsetKeyBRKDelayedProjectionSolver
import FormalProof4FHE.TFHE.SubsetKeyNTRUTrapdoor
import FormalProof4FHE.TFHE.TFHEShortPreimageSecondMoment

/-!
# Trapdoor and Source-Aligned Subset-Key Theorems

This module formalizes the finite and algebraic claims in
`sketch/subset_key_trapdoor_theorems.tex`.

The existing public-view constructor theorem supplies the abstract joint-game reduction.  The
existing delayed-projection solver supplies the invertible-minor construction, its binary-rank
failure bound, and disjoint-block Gram control.  This file adds the remaining reusable claims:

* an exact reduction showing why close witness-dependent postprocessing yields an inverter;
* tagged `G`-trapdoor phase algebra and the native suffix-mask erasure barrier;
* tight statistical regularity of a fixed-weight built-in-preimage block;
* the data-processing and safe-set forms of the near-uniform derived-error barrier;
* exact factor-carrying key switching and closure under public linear operations; and
* the source-aligned branch theorem with its auxiliary defect charged once.

The concrete power-of-two primitive-orbit/counting specialization, continuous-Gaussian
existence, installation of the source-aligned public constructor, and a factor-preserving TFHE
bootstrap remain explicit certificate boundaries.  No efficient short-preimage algorithm or
hidden-witness compiler is postulated.
-/

open Matrix OracleComp
open scoped BigOperators ENNReal

namespace FormalProof4FHE.TFHE.SubsetKeyTrapdoorTheorems

noncomputable section

/-! ## Public branch-constructor reduction -/

open FormalProof4FHE.TFHE.DirectSubsetKeyBRK

/-- The abstract branch-constructor theorem from the note.  This is a named specialization of
the existing complete-view theorem; the three constructor defects are charged exactly once. -/
theorem publicBranchConstructorReduction
    {Sample Secret Output Prefix View : Type} [Add Output]
    {problem : LearningWithErrors.Problem Sample Secret Output}
    {prefixSampler : ProbComp Prefix} {targetView : Bool → ProbComp View}
    (constructor : PublicViewConstructor problem prefixSampler targetView)
    (distinguisher : Distinguisher View) :
    targetAdvantage targetView distinguisher ≤
      2 * LearningWithErrors.advantage problem (constructor.reduction distinguisher) +
        constructor.realError true + constructor.realError false + constructor.uniformError :=
  constructor.targetAdvantage_le_two_source_add_errors distinguisher

/-! ## Witness-dependent postprocessing gives an inverter -/

/-- Joint law containing a public image and its hidden generation witness. -/
def witnessJointSampler
    {Witness Public : Type} [SampleableType Witness]
    (publish : Witness → Public) : ProbComp (Public × Witness) :=
  (fun witness ↦ (publish witness, witness)) <$> ($ᵗ Witness)

/-- What a witness-independent public reconstruction algorithm can produce from a uniform
public value. -/
def publicReconstructionSampler
    {Witness Public : Type} [SampleableType Public]
    (reconstruct : Public → ProbComp Witness) : ProbComp (Public × Witness) := do
  let publicValue ← $ᵗ Public
  let witness ← reconstruct publicValue
  return (publicValue, witness)

/-- Public consistency test for a claimed preimage witness. -/
def witnessConsistencyTest
    {Witness Public : Type} [DecidableEq Public]
    (publish : Witness → Public) (input : Public × Witness) : ProbComp Bool :=
  pure (decide (publish input.2 = input.1))

/-- A bijective publication map makes the public marginal exactly uniform. -/
theorem witnessJointSampler_publicMarginal_eq_uniform
    {Witness Public : Type}
    [SampleableType Witness] [SampleableType Public]
    (publish : Witness → Public) (hpublish : Function.Bijective publish) :
    evalDist (Prod.fst <$> witnessJointSampler publish) =
      evalDist ($ᵗ Public) := by
  simpa [witnessJointSampler, Functor.map_map, Function.comp_def] using
    (evalDist_map_bijective_uniform_cross
      (α := Witness) (β := Public) publish hpublish)

/-- The genuine image/witness joint law always passes its public consistency test. -/
theorem witnessJointSampler_consistencyProbability_eq_one
    {Witness Public : Type} [SampleableType Witness] [DecidableEq Public]
    (publish : Witness → Public) :
    (Pr[= true |
      witnessJointSampler publish >>= witnessConsistencyTest publish]).toReal = 1 := by
  simp [witnessJointSampler, witnessConsistencyTest]

/-- Exact finite form of witness separation.  If a public reconstruction law is close to the
genuine image/witness law, running the public consistency test gives an inverter with success at
least one minus that distance.  An asymptotic one-way-permutation contradiction is obtained by
applying this theorem to a negligible joint-distribution defect. -/
theorem reconstructionSuccess_ge_one_sub_tvDist
    {Witness Public : Type}
    [SampleableType Witness] [SampleableType Public] [DecidableEq Public]
    (publish : Witness → Public)
    (reconstruct : Public → ProbComp Witness) :
    1 - tvDist (publicReconstructionSampler reconstruct)
          (witnessJointSampler publish) ≤
      (Pr[= true |
        publicReconstructionSampler reconstruct >>=
          witnessConsistencyTest publish]).toReal := by
  let reconstructed := publicReconstructionSampler reconstruct
  let genuine := witnessJointSampler publish
  let test := witnessConsistencyTest publish
  have hpost :
      tvDist (reconstructed >>= test) (genuine >>= test) ≤
        tvDist reconstructed genuine :=
    tvDist_bind_right_le test reconstructed genuine
  have hprob :=
    (abs_probOutput_toReal_sub_le_tvDist
      (reconstructed >>= test) (genuine >>= test)).trans hpost
  have hgenuine : (Pr[= true | genuine >>= test]).toReal = 1 := by
    exact witnessJointSampler_consistencyProbability_eq_one publish
  rw [hgenuine] at hprob
  have hbounds := abs_le.mp hprob
  linarith

/-- Quantitative corollary: an `ε`-accurate joint simulator inverts with probability at least
`1-ε`. -/
theorem reconstructionSuccess_ge_one_sub
    {Witness Public : Type}
    [SampleableType Witness] [SampleableType Public] [DecidableEq Public]
    (publish : Witness → Public)
    (reconstruct : Public → ProbComp Witness) (ε : ℝ)
    (hclose : tvDist (publicReconstructionSampler reconstruct)
      (witnessJointSampler publish) ≤ ε) :
    1 - ε ≤
      (Pr[= true |
        publicReconstructionSampler reconstruct >>=
          witnessConsistencyTest publish]).toReal := by
  calc
    1 - ε ≤ 1 - tvDist (publicReconstructionSampler reconstruct)
        (witnessJointSampler publish) := by linarith
    _ ≤ _ := reconstructionSuccess_ge_one_sub_tvDist publish reconstruct

/-! ## Exact affine native-KSK barrier -/

/-- The affine necessity theorem in direct implication form.  Exact correctness on every
noiseless source body forces equality of offsets and the public factorization equation
`postprocess ∘ source = gadget`. -/
theorem affineFactorizationNecessity
    {R V W T : Type} [Semiring R]
    [AddCommMonoid V] [Module R V]
    [AddCommMonoid W] [Module R W]
    [AddCommGroup T] [Module R T]
    (source : V →ₗ[R] W) (gadget : V →ₗ[R] T)
    (postprocess : W →ₗ[R] T) (sourceOffset targetOffset : T)
    (hcorrect : ∀ secret, sourceOffset + postprocess (source secret) =
      targetOffset + gadget secret) :
    sourceOffset = targetOffset ∧ postprocess.comp source = gadget :=
  (SubsetKeyNTRUTrapdoor.affineNoiselessCorrect_iff_offsets_eq_and_factorization
    source gadget postprocess sourceOffset targetOffset).mp hcorrect

/-- Once the forced factorization equation holds, reintroducing a source error shows that the
compiler's derived error is exactly its public linear image. -/
theorem affineCompilerDerivedError
    {R V W T : Type} [Semiring R]
    [AddCommMonoid V] [Module R V]
    [AddCommMonoid W] [Module R W]
    [AddCommGroup T] [Module R T]
    (source : V →ₗ[R] W) (gadget : V →ₗ[R] T)
    (postprocess : W →ₗ[R] T)
    (secret : V) (sourceError : W)
    (hfactor : postprocess.comp source = gadget) :
    postprocess (source secret + sourceError) - gadget secret =
      postprocess sourceError := by
  have hvalue := DFunLike.congr_fun hfactor secret
  simp only [LinearMap.comp_apply] at hvalue
  rw [map_add, ← hvalue]
  abel

/-! ## Tagged `G`-trapdoor algebra -/

section TaggedTrapdoor

variable {R V W T : Type} [CommRing R]
  [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]
  [AddCommGroup T] [Module R T]

/-- Abstract transpose-oriented form of `B_H = H G - A R`.  Here `source` maps the suffix
secret to the ordinary source-body space and `trapdoor` maps source bodies to target rows. -/
def taggedMask
    (source : V →ₗ[R] W) (gadget : V →ₗ[R] T)
    (trapdoor : W →ₗ[R] T) (tag : T →ₗ[R] T) : V →ₗ[R] T :=
  tag.comp gadget - trapdoor.comp source

/-- The tagged public body `-Rᵀ b + ξ` in abstract linear-map orientation. -/
def taggedBody (trapdoor : W →ₗ[R] T) (sourceBody : W) (correction : T) : T :=
  -trapdoor sourceBody + correction

/-- Exact tagged preimage identity `B_H + R A = H G`. -/
theorem taggedMask_add_trapdoor_comp_source
    (source : V →ₗ[R] W) (gadget : V →ₗ[R] T)
    (trapdoor : W →ₗ[R] T) (tag : T →ₗ[R] T) :
    taggedMask source gadget trapdoor tag + trapdoor.comp source =
      tag.comp gadget := by
  simp [taggedMask]

/-- Exact tagged phase

`(-R(Az+e)+ξ) - (HG-RA)z = -HGz + ξ - Re`.
-/
theorem taggedPhase
    (source : V →ₗ[R] W) (gadget : V →ₗ[R] T)
    (trapdoor : W →ₗ[R] T) (tag : T →ₗ[R] T)
    (suffix : V) (sourceError : W) (correction : T) :
    taggedBody trapdoor (source suffix + sourceError) correction -
        taggedMask source gadget trapdoor tag suffix =
      -tag (gadget suffix) + correction - trapdoor sourceError := by
  simp only [taggedBody, taggedMask, LinearMap.sub_apply, LinearMap.comp_apply, map_add]
  abel

/-- The all-but-one tag `H=-I` yields a KSK row with suffix mask `B`, gadget message `Gz`, and
error `ξ-Re`. -/
theorem taggedMinusIdBody
    (source : V →ₗ[R] W) (gadget : V →ₗ[R] T)
    (trapdoor : W →ₗ[R] T)
    (suffix : V) (sourceError : W) (correction : T) :
    taggedBody trapdoor (source suffix + sourceError) correction =
      taggedMask source gadget trapdoor (-LinearMap.id) suffix +
        gadget suffix + (correction - trapdoor sourceError) := by
  simp only [taggedBody, taggedMask, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.neg_apply, LinearMap.id_apply, map_add]
  abel

/-- Adding an independently sampled known prefix term preserves the exact tagged KSK message
identity. -/
theorem taggedFullKeyBody
    (source : V →ₗ[R] W) (gadget : V →ₗ[R] T)
    (trapdoor : W →ₗ[R] T)
    (prefixTerm : T) (suffix : V) (sourceError : W) (correction : T) :
    prefixTerm + taggedBody trapdoor (source suffix + sourceError) correction =
      prefixTerm + taggedMask source gadget trapdoor (-LinearMap.id) suffix +
        gadget suffix + (correction - trapdoor sourceError) := by
  rw [taggedMinusIdBody source gadget trapdoor suffix sourceError correction]
  abel

/-! ### Native suffix-mask erasure -/

/-- Any exact affine erasure of the tagged suffix mask produces a new public preimage of the
gadget: `(X-R) A = G`. -/
theorem nativeSuffixMaskErasureNecessity
    (source : V →ₗ[R] W) (gadget : V →ₗ[R] T)
    (trapdoor eraser : W →ₗ[R] T)
    (herase : taggedMask source gadget trapdoor (-LinearMap.id) +
      eraser.comp source = 0) :
    (eraser - trapdoor).comp source = gadget := by
  apply LinearMap.ext
  intro suffix
  have hsuffix := DFunLike.congr_fun herase suffix
  simp only [taggedMask, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.id_apply,
    LinearMap.zero_apply] at hsuffix ⊢
  calc
    eraser (source suffix) - trapdoor (source suffix) =
        (-gadget suffix - trapdoor (source suffix) + eraser (source suffix)) +
          gadget suffix := by abel
    _ = 0 + gadget suffix := by rw [hsuffix]
    _ = gadget suffix := zero_add _

/-- Exact error formula after native suffix-mask erasure.  The original tagged error `ξ-Re`
and the erasure contribution `Xe` combine to `ξ+(X-R)e`. -/
theorem nativeSuffixMaskErasedBody
    (source : V →ₗ[R] W) (gadget : V →ₗ[R] T)
    (trapdoor eraser : W →ₗ[R] T)
    (herase : taggedMask source gadget trapdoor (-LinearMap.id) +
      eraser.comp source = 0)
    (suffix : V) (sourceError : W) (correction : T) :
    taggedBody trapdoor (source suffix + sourceError) correction +
        eraser (source suffix + sourceError) =
      gadget suffix + correction + (eraser - trapdoor) sourceError := by
  have hsuffix := DFunLike.congr_fun herase suffix
  simp only [taggedMask, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.id_apply,
    LinearMap.zero_apply] at hsuffix
  have heraser :
      eraser (source suffix) = gadget suffix + trapdoor (source suffix) := by
    calc
      eraser (source suffix) =
          (-gadget suffix - trapdoor (source suffix) + eraser (source suffix)) +
            gadget suffix + trapdoor (source suffix) := by abel
      _ = 0 + gadget suffix + trapdoor (source suffix) := by rw [hsuffix]
      _ = gadget suffix + trapdoor (source suffix) := by abel
  simp only [taggedBody, map_add, LinearMap.sub_apply]
  rw [heraser]
  abel

end TaggedTrapdoor

/-! ## Covariance-completion boundary -/

open FormalProof4FHE.TFHE.JointSubsetKeyBRKRefined

/-- Matrix bookkeeping for the tagged correction Gaussian.  Analytic existence of a sampler
with this covariance remains the explicit `exactCorrection` field of the existing certificate. -/
theorem taggedTransformed_add_correctionCovariance
    {SourceCoordinate TargetCoordinate : Type} [Fintype SourceCoordinate]
    (trapdoor : Matrix TargetCoordinate SourceCoordinate ℝ)
    (sourceCovariance : Matrix SourceCoordinate SourceCoordinate ℝ)
    (targetCovariance : Matrix TargetCoordinate TargetCoordinate ℝ) :
    trapdoor * sourceCovariance * trapdoor.transpose +
        correctionCovariance trapdoor sourceCovariance targetCovariance =
      targetCovariance :=
  transformed_add_correctionCovariance trapdoor sourceCovariance targetCovariance

/-- An exact correction certificate proves the complete joint law, including independence from
the retained trapdoor state, rather than only equality of error marginals. -/
theorem taggedExactCorrection_jointLaw
    {State Error : Type} [Add Error]
    {stateSampler : ProbComp State} {derived : State → Error}
    {prescribed : ProbComp Error}
    (certificate : ExactCorrectionNoiseCertificate stateSampler derived prescribed) :
    evalDist (correctedJointError stateSampler derived certificate.correction) =
      evalDist (prescribedJointError stateSampler prescribed) :=
  certificate.corrected_joint_law

/-- Complete tagged-view loss accounting.  A regularity and finite-noise defect in each real
branch is charged twice overall, while the common-uniform auxiliary defect is charged once. -/
theorem taggedJointSecurity
    {Sample Secret Output Prefix View : Type} [Add Output]
    {problem : LearningWithErrors.Problem Sample Secret Output}
    {prefixSampler : ProbComp Prefix} {targetView : Bool → ProbComp View}
    (constructor : PublicViewConstructor problem prefixSampler targetView)
    (distinguisher : Distinguisher View)
    (regularityError noiseError auxiliaryError : ℝ)
    (hreal : ∀ branch,
      constructor.realError branch ≤ regularityError + noiseError)
    (huniform : constructor.uniformError ≤ auxiliaryError) :
    targetAdvantage targetView distinguisher ≤
      2 * LearningWithErrors.advantage problem (constructor.reduction distinguisher) +
        2 * regularityError + 2 * noiseError + auxiliaryError := by
  have h := constructor.targetAdvantage_le_two_source_add_errors distinguisher
  have htrue := hreal true
  have hfalse := hreal false
  linarith

/-! ## Near-uniform derived-error and correctness barrier -/

/-- If the primitive-vector law is `δ`-close to the full uniform vector law and the full uniform
inner product maps exactly to the appropriate ideal-uniform law, the primitive inner product is
also `δ`-close.  This is the data-processing core of the invertible-minor theorem. -/
theorem primitiveDerivedError_close_to_idealUniform
    {Coefficient Ideal : Type}
    [SampleableType Coefficient] [SampleableType Ideal]
    (primitiveSampler : ProbComp Coefficient)
    (innerProduct : Coefficient → Ideal) (δ : ℝ)
    (hprimitive : tvDist primitiveSampler ($ᵗ Coefficient) ≤ δ)
    (huniform : evalDist (innerProduct <$> ($ᵗ Coefficient)) =
      evalDist ($ᵗ Ideal)) :
    tvDist (innerProduct <$> primitiveSampler) ($ᵗ Ideal) ≤ δ := by
  calc
    tvDist (innerProduct <$> primitiveSampler) ($ᵗ Ideal) =
        tvDist (innerProduct <$> primitiveSampler)
          (innerProduct <$> ($ᵗ Coefficient)) := by
      unfold tvDist
      rw [huniform]
    _ ≤ tvDist primitiveSampler ($ᵗ Coefficient) :=
      tvDist_map_le innerProduct primitiveSampler ($ᵗ Coefficient)
    _ ≤ δ := hprimitive

/-- Test a finite safe set by a Boolean public postprocessing. -/
def safeSetTest {Output : Type} [DecidableEq Output]
    (safe : Finset Output) (value : Output) : ProbComp Bool :=
  pure (decide (value ∈ safe))

/-- A distribution `ε`-close to uniform can land in a safe set with probability at most its
uniform density plus `ε`. -/
theorem safeSetProbability_le_uniformDensity_add
    {Output : Type} [Fintype Output] [SampleableType Output] [DecidableEq Output]
    (sampler : ProbComp Output) (safe : Finset Output) (ε : ℝ)
    (hclose : tvDist sampler ($ᵗ Output) ≤ ε) :
    (Pr[(fun value ↦ value ∈ safe) | sampler]).toReal ≤
      (safe.card : ℝ) / Fintype.card Output + ε := by
  have hpost :
      tvDist (sampler >>= safeSetTest safe)
          (($ᵗ Output) >>= safeSetTest safe) ≤ ε :=
    (tvDist_bind_right_le (safeSetTest safe) sampler ($ᵗ Output)).trans hclose
  have hprob :=
    (abs_probOutput_toReal_sub_le_tvDist
      (sampler >>= safeSetTest safe)
      (($ᵗ Output) >>= safeSetTest safe)).trans hpost
  have htest (source : ProbComp Output) :
      Pr[= true | source >>= safeSetTest safe] =
        Pr[(fun value ↦ value ∈ safe) | source] := by
    rw [probOutput_bind_eq_tsum, probEvent_eq_tsum_ite]
    apply tsum_congr
    intro value
    by_cases hvalue : value ∈ safe <;> simp [safeSetTest, hvalue]
  have hsampler :
      (Pr[= true | sampler >>= safeSetTest safe]).toReal =
        (Pr[(fun value ↦ value ∈ safe) | sampler]).toReal := by
    exact congrArg ENNReal.toReal (htest sampler)
  have huniform :
      (Pr[= true | ($ᵗ Output) >>= safeSetTest safe]).toReal =
        (safe.card : ℝ) / Fintype.card Output := by
    rw [congrArg ENNReal.toReal (htest ($ᵗ Output))]
    rw [probEvent_uniformSample, ENNReal.toReal_div]
    simp only [ENNReal.toReal_natCast]
    rw [show (Finset.univ.filter fun value : Output ↦ value ∈ safe) = safe by
      ext value
      simp]
  rw [hsampler, huniform] at hprob
  have hbounds := abs_le.mp hprob
  linarith

/-- Correctness barrier in the form used by the note.  Substitute the primitive-vector defect
`2⁻ⁿ` and the probability of a non-unit source error into `ε`. -/
theorem projectedSolverCorrectness_le
    {Output : Type} [Fintype Output] [SampleableType Output] [DecidableEq Output]
    (derivedError : ProbComp Output) (safe : Finset Output)
    (nonunitErrorProbability primitiveDefect : ℝ)
    (hclose : tvDist derivedError ($ᵗ Output) ≤
      nonunitErrorProbability + primitiveDefect) :
    (Pr[(fun value ↦ value ∈ safe) | derivedError]).toReal ≤
      (safe.card : ℝ) / Fintype.card Output +
        nonunitErrorProbability + primitiveDefect := by
  have h := safeSetProbability_le_uniformDensity_add derivedError safe
    (nonunitErrorProbability + primitiveDefect) hclose
  linarith

/-! ## Statistically regular matrices with built-in short preimages -/

namespace BuiltInPreimage

open FormalProof4FHE.LeftoverHash
open FormalProof4FHE.TFHE.JointSubsetKeyBRKCenteredMixture

/-- Boolean incidence vector of an exact-weight support. -/
def supportBits {dimension weight : ℕ}
    (support : FixedWeightSupport dimension weight) : Fin dimension → Bool :=
  fun index ↦ decide (index ∈ support.1)

/-- Distinct exact-weight supports remain distinct after Boolean incidence encoding. -/
theorem supportBits_injective {dimension weight : ℕ} :
    Function.Injective
      (supportBits : FixedWeightSupport dimension weight → Fin dimension → Bool) := by
  intro left right heq
  apply Subtype.ext
  ext index
  have hindex := congrFun heq index
  by_cases hleft : index ∈ left.1 <;>
    by_cases hright : index ∈ right.1 <;>
      simp [supportBits, hleft, hright] at hindex ⊢

/-- Restricting the binary subset-sum input to an exact-weight support family preserves
two-universality. -/
theorem fixedWeightSubsetSum_isTwoUniversal
    {dimension weight : ℕ} {G : Type}
    [Fintype G] [DecidableEq G] [AddCommGroup G] :
    IsTwoUniversal (Fin dimension → G) (FixedWeightSupport dimension weight) G
      (fun table support ↦ binarySubsetSum table (supportBits support)) := by
  intro left right hne
  exact binarySubsetSum_isTwoUniversal
    (supportBits left) (supportBits right)
    (fun heq ↦ hne (supportBits_injective heq))

/-- The programmed final column `b = g - A r`. -/
def lastColumn {dimension weight : ℕ} {G : Type} [AddCommGroup G]
    (target : G) (table : Fin dimension → G)
    (support : FixedWeightSupport dimension weight) : G :=
  target - binarySubsetSum table (supportBits support)

/-- Exact built-in-preimage identity `A r + b = g`. -/
theorem subsetSum_add_lastColumn
    {dimension weight : ℕ} {G : Type} [AddCommGroup G]
    (target : G) (table : Fin dimension → G)
    (support : FixedWeightSupport dimension weight) :
    binarySubsetSum table (supportBits support) +
        lastColumn target table support = target := by
  simp [lastColumn]

/-- The target-translated built-in-preimage hash family. -/
def hash {dimension weight : ℕ} {G : Type} [AddCommGroup G]
    (target : G) (table : Fin dimension → G)
    (support : FixedWeightSupport dimension weight) : G :=
  lastColumn target table support

/-- Translation by the target preserves the exact two-universal collision bound. -/
theorem hash_isTwoUniversal
    {dimension weight : ℕ} {G : Type}
    [Fintype G] [DecidableEq G] [AddCommGroup G]
    (target : G) :
    IsTwoUniversal (Fin dimension → G) (FixedWeightSupport dimension weight) G
      (hash target) := by
  intro left right hne
  have hbase := fixedWeightSubsetSum_isTwoUniversal
    (G := G) left right hne
  have hfilter :
      (Finset.univ.filter fun table : Fin dimension → G =>
          hash target table left = hash target table right) =
        Finset.univ.filter fun table : Fin dimension → G =>
          binarySubsetSum table (supportBits left) =
            binarySubsetSum table (supportBits right) := by
    ext table
    simp [hash, lastColumn]
  rw [hfilter]
  exact hbase

theorem card_fixedWeightSupport
    (dimension weight : ℕ) :
    Fintype.card (FixedWeightSupport dimension weight) =
      Nat.choose dimension weight := by
  simp [FixedWeightSupport]

/-- Joint public matrix/programmed-column sampler. -/
def sampler
    {G : Type} [SampleableType G] [AddCommGroup G]
    (dimension weight : ℕ) (weight_le : weight ≤ dimension) (target : G) :
    ProbComp ((Fin dimension → G) × G) := do
  let table ← $ᵗ (Fin dimension → G)
  let support ← fixedWeightSupportSampler dimension weight weight_le
  return (table, lastColumn target table support)

/-- Ideal law retaining the same uniform matrix and replacing the programmed column by an
independent uniform value. -/
def idealSampler
    {G : Type} [SampleableType G]
    (dimension : ℕ) : ProbComp ((Fin dimension → G) × G) :=
  $ᵗ ((Fin dimension → G) × G)

/-- Tight statistical regularity theorem

`Δ((A,g-Ar),(A,U)) ≤ 1/2 sqrt((|G|-1)/choose(d,w))`.
-/
theorem sampler_tvDist_ideal_le
    {G : Type} [Fintype G] [DecidableEq G] [SampleableType G] [AddCommGroup G]
    (dimension weight : ℕ) (weight_le : weight ≤ dimension) (target : G) :
    tvDist (sampler dimension weight weight_le target)
        (idealSampler dimension) ≤
      Real.sqrt
          (((Fintype.card G : ℝ) - 1) /
            (Nat.choose dimension weight : ℝ)) / 2 := by
  letI : Nonempty (FixedWeightSupport dimension weight) :=
    fixedWeightSupport_nonempty dimension weight weight_le
  letI : SampleableType (FixedWeightSupport dimension weight) :=
    fixedWeightSupportSampleable dimension weight weight_le
  have hleft :
      evalDist (sampler dimension weight weight_le target) =
        evalDist (hashed
          (hash (dimension := dimension) (weight := weight) target)) := by
    change evalDist (do
        let table ← $ᵗ (Fin dimension → G)
        let support ←
          @uniformSample (FixedWeightSupport dimension weight)
            (fixedWeightSupportSampleable dimension weight weight_le)
        return (table, lastColumn target table support)) =
      evalDist (do
        let table ← $ᵗ (Fin dimension → G)
        let support ← $ᵗ (FixedWeightSupport dimension weight)
        return (table, lastColumn target table support))
    rfl
  have hright :
      evalDist (idealSampler (G := G) dimension) =
        evalDist (ideal (Seed := Fin dimension → G) (Output := G)) := by
    rfl
  have h := leftover_hash_lemma_tight
    (hash (dimension := dimension) (weight := weight) target)
    (hash_isTwoUniversal (dimension := dimension) (weight := weight) target)
  rw [card_fixedWeightSupport dimension weight] at h
  unfold tvDist at h ⊢
  rw [hleft, hright]
  exact h

/-- Independent, possibly different target blocks cost at most the sum of their one-block
regularity defects. -/
theorem samplerBlocks_tvDist_ideal_le
    {G : Type} [Fintype G] [DecidableEq G] [SampleableType G] [AddCommGroup G]
    (blocks dimension weight : ℕ) (weight_le : weight ≤ dimension)
    (target : Fin blocks → G) :
    tvDist
        (Fin.mOfFn blocks
          (fun block ↦ sampler dimension weight weight_le (target block)))
        (Fin.mOfFn blocks (fun _ ↦ idealSampler (G := G) dimension)) ≤
      (blocks : ℝ) *
        (Real.sqrt
          (((Fintype.card G : ℝ) - 1) /
            (Nat.choose dimension weight : ℝ)) / 2) := by
  calc
    _ ≤ ∑ block, tvDist
          (sampler dimension weight weight_le (target block))
          (idealSampler dimension) :=
      FormalProof4FHE.FiniteProduct.tvDist_fin_mOfFn_le_sum blocks
        (fun block ↦ sampler dimension weight weight_le (target block))
        (fun _ ↦ idealSampler (G := G) dimension)
    _ ≤ ∑ _block : Fin blocks,
          Real.sqrt
            (((Fintype.card G : ℝ) - 1) /
              (Nat.choose dimension weight : ℝ)) / 2 := by
      apply Finset.sum_le_sum
      intro block _
      exact sampler_tvDist_ideal_le dimension weight weight_le (target block)
    _ = _ := by simp [nsmul_eq_mul]

/-- IID specialization of the independent-target regularity theorem. -/
theorem samplerIID_tvDist_ideal_le
    {G : Type} [Fintype G] [DecidableEq G] [SampleableType G] [AddCommGroup G]
    (blocks dimension weight : ℕ) (weight_le : weight ≤ dimension) (target : G) :
    tvDist
        (ProbComp.sampleIID blocks (sampler dimension weight weight_le target))
        (ProbComp.sampleIID blocks (idealSampler dimension)) ≤
      (blocks : ℝ) *
        (Real.sqrt
          (((Fintype.card G : ℝ) - 1) /
            (Nat.choose dimension weight : ℝ)) / 2) := by
  simpa only [ProbComp.sampleIID] using
    (samplerBlocks_tvDist_ideal_le blocks dimension weight weight_le
      (fun _ ↦ target))

/-- Real coefficient vector of the built-in preimage `(r,1)`. -/
def realPreimage {dimension weight : ℕ}
    (support : FixedWeightSupport dimension weight) : Sum (Fin dimension) Unit → ℝ
  | Sum.inl index => if index ∈ support.1 then 1 else 0
  | Sum.inr _ => 1

/-- The first block of the built-in preimage has squared norm exactly `weight`. -/
theorem realPreimage_left_sqNorm
    {dimension weight : ℕ}
    (support : FixedWeightSupport dimension weight) :
    (∑ index : Fin dimension,
      (realPreimage support (Sum.inl index)) ^ 2) = weight := by
  simp only [realPreimage]
  rw [show (∑ index : Fin dimension,
      (if index ∈ support.1 then (1 : ℝ) else 0) ^ 2) =
      ∑ index ∈ support.1, (1 : ℝ) by
    rw [← show
      Finset.univ.filter (fun index : Fin dimension ↦ index ∈ support.1) = support.1 by
        ext index
        simp]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro index _
    by_cases hmem : index ∈ support.1 <;> simp [hmem]]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard := (Finset.mem_powersetCard.mp support.property).2
  exact_mod_cast hcard

/-- Its squared Euclidean norm is exactly `weight+1`. -/
theorem realPreimage_sqNorm
    {dimension weight : ℕ}
    (support : FixedWeightSupport dimension weight) :
    (∑ index, (realPreimage support index) ^ 2) = weight + 1 := by
  rw [Fintype.sum_sum_type]
  simp only [realPreimage]
  simp only [Fintype.sum_unique, one_pow]
  rw [show (∑ index : Fin dimension,
      (if index ∈ support.1 then (1 : ℝ) else 0) ^ 2) =
      ∑ index ∈ support.1, (1 : ℝ) by
    rw [← show
      Finset.univ.filter (fun index : Fin dimension ↦ index ∈ support.1) = support.1 by
        ext index
        simp]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro index _
    by_cases hmem : index ∈ support.1 <;> simp [hmem]]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard := (Finset.mem_powersetCard.mp support.property).2
  norm_num [hcard]

/-- Coordinatewise variance profile used by the note's two-variance Gaussian calculation. -/
def coordinateVariance {dimension : ℕ} (firstVariance lastVariance : ℝ) :
    Sum (Fin dimension) Unit → ℝ
  | Sum.inl _ => firstVariance
  | Sum.inr _ => lastVariance

/-- The variance-weighted squared norm is exactly
`firstVariance * weight + lastVariance`.  For independent centered Gaussian coordinates this
is the variance of the derived preimage error. -/
theorem realPreimage_weightedEnergy
    {dimension weight : ℕ}
    (support : FixedWeightSupport dimension weight)
    (firstVariance lastVariance : ℝ) :
    (∑ index,
      coordinateVariance firstVariance lastVariance index *
        (realPreimage support index) ^ 2) =
      firstVariance * weight + lastVariance := by
  rw [Fintype.sum_sum_type]
  simp only [coordinateVariance]
  rw [show (∑ index : Fin dimension,
      firstVariance * realPreimage support (Sum.inl index) ^ 2) =
      firstVariance * weight by
    rw [← Finset.mul_sum, realPreimage_left_sqNorm support]]
  simp [realPreimage]

/-- Put each built-in preimage in its own source block.  This is the row-oriented version of
the note's complete preimage matrix. -/
def blockPreimage {Output : Type} [DecidableEq Output]
    {dimension weight : ℕ}
    (supports : Output → FixedWeightSupport dimension weight) :
    Matrix Output (Output × Sum (Fin dimension) Unit) ℝ :=
  fun output source ↦
    if source.1 = output then realPreimage (supports output) source.2 else 0

open FormalProof4FHE.TFHE.TFHEShortPreimageSecondMoment

/-- Distinct built-in-preimage rows have disjoint source support. -/
theorem blockPreimage_pairwiseDisjoint
    {Output : Type} [DecidableEq Output]
    {dimension weight : ℕ}
    (supports : Output → FixedWeightSupport dimension weight) :
    DisjointGram.PairwiseDisjointRows (blockPreimage supports) := by
  intro first second hne source
  by_cases hfirst : source.1 = first
  · right
    have hsecond : source.1 ≠ second := by
      intro heq
      exact hne (hfirst.symm.trans heq)
    simp [blockPreimage, hsecond]
  · left
    simp [blockPreimage, hfirst]

/-- Every block row has the exact energy `weight + 1`. -/
theorem blockPreimage_rowEnergy
    {Output : Type} [Fintype Output] [DecidableEq Output]
    {dimension weight : ℕ}
    (supports : Output → FixedWeightSupport dimension weight) (output : Output) :
    DisjointGram.rowEnergy (blockPreimage supports) output = weight + 1 := by
  classical
  unfold DisjointGram.rowEnergy blockPreimage
  rw [Fintype.sum_prod_type]
  simp
  have henergy := realPreimage_sqNorm (supports output)
  rw [Fintype.sum_sum_type] at henergy
  simpa using henergy

/-- The complete built-in-preimage Gram matrix is exactly `(weight+1) I`. -/
theorem blockPreimage_mul_transpose_eq
    {Output : Type} [Fintype Output] [DecidableEq Output]
    {dimension weight : ℕ}
    (supports : Output → FixedWeightSupport dimension weight) :
    blockPreimage supports * (blockPreimage supports).transpose =
      (weight + 1 : ℝ) • (1 : Matrix Output Output ℝ) := by
  rw [DisjointGram.mul_transpose_eq_diagonal
    (blockPreimage supports) (blockPreimage_pairwiseDisjoint supports)]
  ext first second
  by_cases heq : first = second
  · subst second
    simp [Matrix.diagonal, blockPreimage_rowEnergy]
  · simp [Matrix.diagonal, heq]

end BuiltInPreimage

/-! ## Source-aligned random gadgets and factor-carrying ciphertexts -/

namespace SourceAligned

/-- Ciphertext carrying a public factor vector `d`; its implicit suffix mask is `G d`. -/
structure FactorCiphertext
    (R Prefix Suffix Factor : Type) where
  prefixMask : Prefix → R
  factor : Factor → R
  body : R

section Algebra

variable {R Prefix Suffix Factor : Type} [CommRing R]
  [Fintype Prefix] [Fintype Suffix] [Fintype Factor]

/-- Implicit suffix mask represented by the public factor vector. -/
def FactorCiphertext.suffixMask
    (gadget : Matrix Suffix Factor R)
    (ciphertext : FactorCiphertext R Prefix Suffix Factor) : Suffix → R :=
  gadget.mulVec ciphertext.factor

/-- Split-key phase of a factor-carrying ciphertext. -/
def FactorCiphertext.phase
    (gadget : Matrix Suffix Factor R)
    (prefixSecret : Prefix → R) (suffixSecret : Suffix → R)
    (ciphertext : FactorCiphertext R Prefix Suffix Factor) : R :=
  ciphertext.body - dotProduct prefixSecret ciphertext.prefixMask -
    dotProduct suffixSecret (ciphertext.suffixMask gadget)

/-- Public factor-aligned KSK body `UᵀP+GᵀZ+η`. -/
def randomGadgetKSKBody
    (prefixMask : Matrix Prefix Factor R)
    (gadget : Matrix Suffix Factor R)
    (prefixSecret : Prefix → R) (suffixSecret : Suffix → R)
    (error : Factor → R) : Factor → R :=
  prefixMask.transpose.mulVec prefixSecret +
    gadget.transpose.mulVec suffixSecret + error

/-- Key switching consumes the carried factor directly; it performs no preimage search. -/
def FactorCiphertext.keySwitch
    (prefixMask : Matrix Prefix Factor R)
    (kskBody : Factor → R)
    (ciphertext : FactorCiphertext R Prefix Suffix Factor) :
    (Prefix → R) × R :=
  (ciphertext.prefixMask - prefixMask.mulVec ciphertext.factor,
    ciphertext.body - dotProduct ciphertext.factor kskBody)

/-- Exact factor-carrying key-switch identity. -/
theorem FactorCiphertext.keySwitch_phase
    (prefixMask : Matrix Prefix Factor R)
    (gadget : Matrix Suffix Factor R)
    (prefixSecret : Prefix → R) (suffixSecret : Suffix → R)
    (error : Factor → R)
    (ciphertext : FactorCiphertext R Prefix Suffix Factor) :
    (ciphertext.keySwitch prefixMask
        (randomGadgetKSKBody prefixMask gadget prefixSecret suffixSecret error)).2 -
      dotProduct prefixSecret
        (ciphertext.keySwitch prefixMask
          (randomGadgetKSKBody prefixMask gadget prefixSecret suffixSecret error)).1 =
      ciphertext.phase gadget prefixSecret suffixSecret -
        dotProduct ciphertext.factor error := by
  classical
  simp only [FactorCiphertext.keySwitch, randomGadgetKSKBody,
    FactorCiphertext.phase, FactorCiphertext.suffixMask,
    dotProduct_add, dotProduct_sub]
  have hprefix :
      dotProduct ciphertext.factor (prefixMask.transpose.mulVec prefixSecret) =
        dotProduct prefixSecret (prefixMask.mulVec ciphertext.factor) := by
    exact Matrix.dotProduct_transpose_mulVec prefixMask ciphertext.factor prefixSecret
  have hsuffix :
      dotProduct ciphertext.factor (gadget.transpose.mulVec suffixSecret) =
        dotProduct suffixSecret (gadget.mulVec ciphertext.factor) := by
    exact Matrix.dotProduct_transpose_mulVec gadget ciphertext.factor suffixSecret
  rw [hprefix, hsuffix]
  abel

/-- Addition of factor-carrying ciphertexts. -/
def FactorCiphertext.add
    (left right : FactorCiphertext R Prefix Suffix Factor) :
    FactorCiphertext R Prefix Suffix Factor where
  prefixMask := left.prefixMask + right.prefixMask
  factor := left.factor + right.factor
  body := left.body + right.body

/-- Public scalar multiplication of a factor-carrying ciphertext. -/
def FactorCiphertext.scale
    (scalar : R) (ciphertext : FactorCiphertext R Prefix Suffix Factor) :
    FactorCiphertext R Prefix Suffix Factor where
  prefixMask := scalar • ciphertext.prefixMask
  factor := scalar • ciphertext.factor
  body := scalar * ciphertext.body

omit [Fintype Prefix] [Fintype Suffix] in
theorem FactorCiphertext.suffixMask_add
    (gadget : Matrix Suffix Factor R)
    (left right : FactorCiphertext R Prefix Suffix Factor) :
    (left.add right).suffixMask gadget =
      left.suffixMask gadget + right.suffixMask gadget := by
  simp [FactorCiphertext.add, FactorCiphertext.suffixMask, Matrix.mulVec_add]

theorem FactorCiphertext.phase_add
    (gadget : Matrix Suffix Factor R)
    (prefixSecret : Prefix → R) (suffixSecret : Suffix → R)
    (left right : FactorCiphertext R Prefix Suffix Factor) :
    (left.add right).phase gadget prefixSecret suffixSecret =
      left.phase gadget prefixSecret suffixSecret +
        right.phase gadget prefixSecret suffixSecret := by
  classical
  simp [FactorCiphertext.add, FactorCiphertext.phase,
    FactorCiphertext.suffixMask, Matrix.mulVec_add, dotProduct_add]
  ring

omit [Fintype Prefix] [Fintype Suffix] in
theorem FactorCiphertext.suffixMask_scale
    (gadget : Matrix Suffix Factor R) (scalar : R)
    (ciphertext : FactorCiphertext R Prefix Suffix Factor) :
    (ciphertext.scale scalar).suffixMask gadget =
      scalar • ciphertext.suffixMask gadget := by
  classical
  ext suffix
  simp [FactorCiphertext.scale, FactorCiphertext.suffixMask, Matrix.mulVec]

theorem FactorCiphertext.phase_scale
    (gadget : Matrix Suffix Factor R)
    (prefixSecret : Prefix → R) (suffixSecret : Suffix → R)
    (scalar : R) (ciphertext : FactorCiphertext R Prefix Suffix Factor) :
    (ciphertext.scale scalar).phase gadget prefixSecret suffixSecret =
      scalar * ciphertext.phase gadget prefixSecret suffixSecret := by
  classical
  unfold FactorCiphertext.phase
  rw [FactorCiphertext.suffixMask_scale]
  simp only [FactorCiphertext.scale, dotProduct_smul, smul_eq_mul]
  ring

end Algebra

/-! ### Source-aligned game composition -/

/-- Once the random-gadget KSK block and every retained auxiliary object have been installed in
one public constructor, exact real branches and an `ε_aux` common-uniform defect give the direct
ordinary-source bound from the note. -/
theorem randomGadgetJointSecurity
    {Sample Secret Output Prefix View : Type} [Add Output]
    {problem : LearningWithErrors.Problem Sample Secret Output}
    {prefixSampler : ProbComp Prefix} {targetView : Bool → ProbComp View}
    (constructor : PublicViewConstructor problem prefixSampler targetView)
    (distinguisher : Distinguisher View) (auxiliaryError : ℝ)
    (hreal : ∀ branch, constructor.realError branch = 0)
    (huniform : constructor.uniformError ≤ auxiliaryError) :
    targetAdvantage targetView distinguisher ≤
      2 * LearningWithErrors.advantage problem (constructor.reduction distinguisher) +
        auxiliaryError := by
  have h := constructor.targetAdvantage_le_two_source_add_errors distinguisher
  rw [hreal true, hreal false] at h
  linarith

/-- Explicit remaining implementation boundary.  A bootstrap certificate must expose the
publicly propagated output factor, a caller-selected factor cost, and the two correctness facts
needed by the random-gadget KSK theorem. -/
structure FactorPreservingBootstrapCertificate
    (R Prefix Suffix Factor Input Randomness : Type)
    (bootstrap : Input → Randomness →
      FactorCiphertext R Prefix Suffix Factor)
    (factorCost : (Factor → R) → ℝ) (bound : ℝ)
    (messageCorrect noiseCorrect : Input → Randomness → Prop) where
  factorBound : ∀ input randomness,
    factorCost (bootstrap input randomness).factor ≤ bound
  message_correct : ∀ input randomness, messageCorrect input randomness
  noise_correct : ∀ input randomness, noiseCorrect input randomness

end SourceAligned

end

end FormalProof4FHE.TFHE.SubsetKeyTrapdoorTheorems
