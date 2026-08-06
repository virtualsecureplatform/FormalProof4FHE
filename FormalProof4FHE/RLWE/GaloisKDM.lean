/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.AffineCircular

/-!
# Joint Galois Evaluation-Key Security Boundary

This file formalizes the direct BFV/BGV Galois-key batch.  A row indexed by `j` contains

`(A_j, A_j*S + g_j*sigma_j(S) + E_j)`,

where `sigma_j` is a public ring automorphism and `g_j` is a public gadget weight.  All rows use
one common secret and independent errors, exactly as in an evaluation-key batch.

The checked results are:

* the row phase and the complete automorphism/key-switch correctness identity;
* an exact triangle through the common uniform endpoint;
* identification of the zero-message endpoint with ordinary rank-one batch RLWE;
* a conditional security theorem containing one joint automorphism-KDM term and one ordinary
  RLWE term; and
* a generic obstruction showing that a nontrivial automorphism cannot be absorbed by the usual
  rank-one RLWE challenge translation on any secret set containing `1` and a moved element.

The last item is why this file does not claim that ordinary RLWE alone proves Galois-key
security.  It also explains the limitation of a scalar affine-KDM argument: coefficientwise the
message is affine, but a ring row shares one structured mask across all coefficients.
-/

open Matrix OracleComp

namespace FormalProof4FHE.RLWE.GaloisKDM

noncomputable section

/-! ## Joint direct Galois-key problem -/

/-- One public automorphism and gadget weight for every evaluation-key row.  Repeated rows may
carry the same automorphism at different gadget levels. -/
structure Spec (R : Type) [CommRing R] (rows : ℕ) where
  automorphism : Fin rows → R ≃+* R
  weight : Fin rows → R

/-- Canonical complete batch with one row for every `(automorphism, gadget level)` pair. -/
def cartesianSpec {R : Type} [CommRing R]
    (automorphismCount levels : ℕ)
    (automorphism : Fin automorphismCount → R ≃+* R)
    (weight : Fin levels → R) : Spec R (automorphismCount * levels) where
  automorphism row := automorphism (finProdFinEquiv.symm row).1
  weight row := weight (finProdFinEquiv.symm row).2

@[simp]
theorem cartesianSpec_automorphism {R : Type} [CommRing R]
    (automorphismCount levels : ℕ)
    (automorphism : Fin automorphismCount → R ≃+* R)
    (weight : Fin levels → R)
    (index : Fin automorphismCount) (level : Fin levels) :
    (cartesianSpec automorphismCount levels automorphism weight).automorphism
        (finProdFinEquiv (index, level)) = automorphism index := by
  change automorphism
      (finProdFinEquiv.symm (finProdFinEquiv (index, level))).1 = automorphism index
  rw [Equiv.symm_apply_apply]

@[simp]
theorem cartesianSpec_weight {R : Type} [CommRing R]
    (automorphismCount levels : ℕ)
    (automorphism : Fin automorphismCount → R ≃+* R)
    (weight : Fin levels → R)
    (index : Fin automorphismCount) (level : Fin levels) :
    (cartesianSpec automorphismCount levels automorphism weight).weight
        (finProdFinEquiv (index, level)) = weight level := by
  change weight
      (finProdFinEquiv.symm (finProdFinEquiv (index, level))).2 = weight level
  rw [Equiv.symm_apply_apply]

/-- The rank-one RLWE secret representation used by the generic matrix-LWE game. -/
abbrev Secret (R : Type) := Fin 1 → R

/-- Public masks for a complete Galois evaluation-key batch. -/
abbrev Challenge (R : Type) (rows : ℕ) := Matrix (Fin 1) (Fin rows) R

/-- Bodies of a complete Galois evaluation-key batch. -/
abbrev Output (R : Type) (rows : ℕ) := Fin rows → R

/-- The public batch transcript. -/
abbrev Transcript (R : Type) (rows : ℕ) :=
  Challenge R rows × Output R rows

/-- Gadget-scaled automorphed-secret messages for all rows. -/
def message {R : Type} [CommRing R] {rows : ℕ}
    (spec : Spec R rows) (secret : Secret R) : Output R rows :=
  fun row ↦ spec.weight row * spec.automorphism row (secret 0)

/-- Direct Galois evaluation-key problem: every row encrypts
`g_j * sigma_j(S)` under the common key `S`. -/
def problem {R : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    (rows : ℕ) (spec : Spec R rows)
    (secretSampler : ProbComp (Secret R)) (errorSampler : ProbComp R) :
    LearningWithErrors.Problem (Challenge R rows) (Secret R) (Output R rows) where
  sampleChallenge := $ᵗ (Challenge R rows)
  sampleSecret := secretSampler
  sampleError := ProbComp.sampleIID rows errorSampler
  noiseless := fun secret challenge ↦ vecMul secret challenge + message spec secret
  sampleUniform := $ᵗ (Output R rows)

/-- Ordinary zero-message rank-one batch RLWE with the identical secret and error laws. -/
abbrev ordinaryProblem {R : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    (rows : ℕ) (secretSampler : ProbComp (Secret R)) (errorSampler : ProbComp R) :=
  FormalProof4FHE.LWE.batchProblem 1 rows secretSampler errorSampler

/-- Real Galois evaluation-key sampler. -/
def realSampler {R : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    (rows : ℕ) (spec : Spec R rows)
    (secretSampler : ProbComp (Secret R)) (errorSampler : ProbComp R) :
    ProbComp (Transcript R rows) :=
  LearningWithErrors.distr (problem rows spec secretSampler errorSampler)

/-- Zero-message evaluation-key sampler under the same secret. -/
def zeroSampler {R : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    (rows : ℕ) (secretSampler : ProbComp (Secret R)) (errorSampler : ProbComp R) :
    ProbComp (Transcript R rows) :=
  LearningWithErrors.distr (ordinaryProblem rows secretSampler errorSampler)

/-- Common uniform endpoint. -/
def uniformSampler {R : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    (rows : ℕ) (spec : Spec R rows)
    (secretSampler : ProbComp (Secret R)) (errorSampler : ProbComp R) :
    ProbComp (Transcript R rows) :=
  LearningWithErrors.uniformDistr (problem rows spec secretSampler errorSampler)

/-- A public distinguisher for the complete batch. -/
abbrev Distinguisher (R : Type) (rows : ℕ) := Transcript R rows → ProbComp Bool

/-- Real Galois keys versus the zero-message evaluation-key hybrid. -/
noncomputable def kdmAdvantage
    {R : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    (rows : ℕ) (spec : Spec R rows)
    (secretSampler : ProbComp (Secret R)) (errorSampler : ProbComp R)
    (distinguisher : Distinguisher R rows) : ℝ :=
  (realSampler rows spec secretSampler errorSampler >>= distinguisher).boolDistAdvantage
    (zeroSampler rows secretSampler errorSampler >>= distinguisher)

/-- Joint automorphism-KDM versus uniform advantage. -/
noncomputable def automorphismUniformAdvantage
    {R : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    (rows : ℕ) (spec : Spec R rows)
    (secretSampler : ProbComp (Secret R)) (errorSampler : ProbComp R)
    (distinguisher : Distinguisher R rows) : ℝ :=
  (realSampler rows spec secretSampler errorSampler >>= distinguisher).boolDistAdvantage
    (uniformSampler rows spec secretSampler errorSampler >>= distinguisher)

/-- Ordinary zero-message RLWE versus the same uniform endpoint. -/
noncomputable def zeroUniformAdvantage
    {R : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    (rows : ℕ) (spec : Spec R rows)
    (secretSampler : ProbComp (Secret R)) (errorSampler : ProbComp R)
    (distinguisher : Distinguisher R rows) : ℝ :=
  (zeroSampler rows secretSampler errorSampler >>= distinguisher).boolDistAdvantage
    (uniformSampler rows spec secretSampler errorSampler >>= distinguisher)

/-- The Galois problem and the ordinary problem have literally the same uniform branch. -/
theorem uniformDistr_problem_eq_ordinary
    {R : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    (rows : ℕ) (spec : Spec R rows)
    (secretSampler : ProbComp (Secret R)) (errorSampler : ProbComp R) :
    LearningWithErrors.uniformDistr (problem rows spec secretSampler errorSampler) =
      LearningWithErrors.uniformDistr
        (ordinaryProblem rows secretSampler errorSampler) := rfl

/-- The named automorphism-KDM term is exactly the decisional advantage of `problem`. -/
theorem automorphismUniformAdvantage_eq_problemAdvantage
    {R : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    (rows : ℕ) (spec : Spec R rows)
    (secretSampler : ProbComp (Secret R)) (errorSampler : ProbComp R)
    (distinguisher : Distinguisher R rows) :
    automorphismUniformAdvantage rows spec secretSampler errorSampler distinguisher =
      LearningWithErrors.advantage
        (problem rows spec secretSampler errorSampler) distinguisher := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  rfl

/-- The zero endpoint is exactly ordinary rank-one batch RLWE, with no sampler or row loss. -/
theorem zeroUniformAdvantage_eq_ordinaryAdvantage
    {R : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    (rows : ℕ) (spec : Spec R rows)
    (secretSampler : ProbComp (Secret R)) (errorSampler : ProbComp R)
    (distinguisher : Distinguisher R rows) :
    zeroUniformAdvantage rows spec secretSampler errorSampler distinguisher =
      LearningWithErrors.advantage
        (ordinaryProblem rows secretSampler errorSampler) distinguisher := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  rfl

/-- Exact hybrid decomposition through one common uniform transcript.  There is no per-row or
per-automorphism hybrid. -/
theorem kdmAdvantage_le_automorphismUniform_add_zeroUniform
    {R : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    (rows : ℕ) (spec : Spec R rows)
    (secretSampler : ProbComp (Secret R)) (errorSampler : ProbComp R)
    (distinguisher : Distinguisher R rows) :
    kdmAdvantage rows spec secretSampler errorSampler distinguisher ≤
      automorphismUniformAdvantage rows spec secretSampler errorSampler distinguisher +
        zeroUniformAdvantage rows spec secretSampler errorSampler distinguisher := by
  have h := ProbComp.boolDistAdvantage_triangle
    (realSampler rows spec secretSampler errorSampler >>= distinguisher)
    (uniformSampler rows spec secretSampler errorSampler >>= distinguisher)
    (zeroSampler rows secretSampler errorSampler >>= distinguisher)
  unfold kdmAdvantage automorphismUniformAdvantage zeroUniformAdvantage
  rw [show (uniformSampler rows spec secretSampler errorSampler >>=
        distinguisher).boolDistAdvantage
      (zeroSampler rows secretSampler errorSampler >>= distinguisher) =
      (zeroSampler rows secretSampler errorSampler >>= distinguisher).boolDistAdvantage
        (uniformSampler rows spec secretSampler errorSampler >>= distinguisher) by
    unfold ProbComp.boolDistAdvantage
    rw [abs_sub_comm]] at h
  exact h

/-- Minimal sound conditional security theorem for the complete joint Galois-key batch. -/
theorem kdmAdvantage_le_of_automorphismKDM_and_rlwe
    {R : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    (rows : ℕ) (spec : Spec R rows)
    (secretSampler : ProbComp (Secret R)) (errorSampler : ProbComp R)
    (distinguisher : Distinguisher R rows)
    (automorphismBound rlweBound : ℝ)
    (hAutomorphism : LearningWithErrors.advantage
      (problem rows spec secretSampler errorSampler) distinguisher ≤ automorphismBound)
    (hRLWE : LearningWithErrors.advantage
      (ordinaryProblem rows secretSampler errorSampler) distinguisher ≤ rlweBound) :
    kdmAdvantage rows spec secretSampler errorSampler distinguisher ≤
      automorphismBound + rlweBound := by
  apply (kdmAdvantage_le_automorphismUniform_add_zeroUniform
    rows spec secretSampler errorSampler distinguisher).trans
  rw [automorphismUniformAdvantage_eq_problemAdvantage,
    zeroUniformAdvantage_eq_ordinaryAdvantage]
  exact add_le_add hAutomorphism hRLWE

/-! ### Identity action closes under ordinary affine KDM -/

/-- The degenerate Galois specification in which every public action is the identity. -/
def identitySpec {R : Type} [CommRing R] {rows : ℕ}
    (weight : Fin rows → R) : Spec R rows where
  automorphism := fun _ ↦ RingEquiv.refl R
  weight := weight

/-- Rank-one affine coefficients corresponding to the gadget weights. -/
def identityCoefficients {R : Type} {rows : ℕ}
    (weight : Fin rows → R) :
    FormalProof4FHE.LWE.AffineCircular.Coefficients R 1 rows :=
  fun _ row ↦ weight row

/-- For the identity action, the Galois message is exactly the ring-affine message consumed by
the ordinary direct affine-KDM theorem. -/
theorem message_identitySpec_eq_affineMessage
    {R : Type} [CommRing R] {rows : ℕ}
    (weight : Fin rows → R) (secret : Secret R) :
    message (identitySpec weight) secret =
      FormalProof4FHE.LWE.AffineCircular.affineMessage
        (fun value : Secret R ↦ value) (identityCoefficients weight) 0 secret := by
  funext row
  simp [message, identitySpec, FormalProof4FHE.LWE.AffineCircular.affineMessage,
    identityCoefficients, Matrix.vecMul, dotProduct, mul_comm]

/-- The identity-action problem is literally the previously proved direct affine-KDM problem. -/
theorem problem_identitySpec_eq_affineCircular
    {R : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    (rows : ℕ) (weight : Fin rows → R)
    (secretSampler : ProbComp (Secret R)) (errorSampler : ProbComp R) :
    problem rows (identitySpec weight) secretSampler errorSampler =
      FormalProof4FHE.LWE.AffineCircular.problem 1 rows secretSampler
        (fun value : Secret R ↦ value) (identityCoefficients weight) 0 errorSampler := by
  unfold problem FormalProof4FHE.LWE.AffineCircular.problem
  congr 1
  funext secret challenge
  rw [message_identitySpec_eq_affineMessage]

/-- The existing affine-KDM transcript translation specialized to identity Galois rows. -/
def identityReduction
    {R : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    {rows : ℕ} {weight : Fin rows → R}
    {secretSampler : ProbComp (Secret R)} {errorSampler : ProbComp R}
    (distinguisher : Distinguisher R rows) :
    LearningWithErrors.Adversary
      (ordinaryProblem rows secretSampler errorSampler) :=
  @FormalProof4FHE.LWE.AffineCircular.reduction
    R (Secret R) _ _ _ 1 rows secretSampler
    (fun value : Secret R ↦ value) (identityCoefficients weight)
    (0 : FormalProof4FHE.LWE.AffineCircular.Offset R rows)
    errorSampler distinguisher

/-- Exact ordinary-RLWE reduction for the identity action.  This theorem deliberately stops at
identity: the non-absorbability result below rules out extending the same rank-one translation to
a nontrivial automorphism on the usual binary or ternary support. -/
theorem identity_problem_advantage_eq_ordinary
    {R : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    (rows : ℕ) (weight : Fin rows → R)
    (secretSampler : ProbComp (Secret R)) (errorSampler : ProbComp R)
    (distinguisher : Distinguisher R rows) :
    LearningWithErrors.advantage
        (problem rows (identitySpec weight) secretSampler errorSampler) distinguisher =
      LearningWithErrors.advantage
        (ordinaryProblem rows secretSampler errorSampler)
        (identityReduction (weight := weight) distinguisher) := by
  rw [problem_identitySpec_eq_affineCircular]
  exact FormalProof4FHE.LWE.AffineCircular.advantage_eq_lwe
    1 rows secretSampler (fun value : Secret R ↦ value)
    (identityCoefficients weight) 0 errorSampler distinguisher

/-! ## Exact row and key-switch correctness -/

/-- Body of one direct Galois evaluation-key row. -/
def evaluationKeyBody {R : Type} [CommRing R]
    (automorphism : R ≃+* R) (weight secret mask error : R) : R :=
  mask * secret + weight * automorphism secret + error

/-- Removing the mask phase leaves exactly the gadget-scaled automorphed secret and error. -/
theorem evaluationKeyBody_sub_mask_mul_secret
    {R : Type} [CommRing R]
    (automorphism : R ≃+* R) (weight secret mask error : R) :
    evaluationKeyBody automorphism weight secret mask error - mask * secret =
      weight * automorphism secret + error := by
  simp only [evaluationKeyBody]
  ring_nf

/-- Exact phase after applying an automorphism and switching back to the original secret.
The decomposition is of `sigma(c1)` in the public gadget weights. -/
theorem galoisKeySwitch_phase
    {R Level : Type} [CommRing R] [Fintype Level]
    (automorphism : R ≃+* R) (weight digit : Level → R)
    (secret c0 c1 : R) (mask error : Level → R)
    (hDecomposition : automorphism c1 = ∑ level, digit level * weight level) :
    (automorphism c0 + ∑ level, digit level *
        evaluationKeyBody automorphism (weight level) secret
          (mask level) (error level)) +
      (-(∑ level, digit level * mask level)) * secret =
        automorphism (c0 + c1 * secret) +
          ∑ level, digit level * error level := by
  simp only [evaluationKeyBody, map_add, map_mul]
  rw [hDecomposition]
  simp_rw [mul_add, Finset.sum_add_distrib]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  ring

/-! ## Why ordinary rank-one RLWE challenge translation is insufficient -/

/-- An automorphed-secret message is absorbable by the usual rank-one RLWE challenge shift on a
secret set only if it agrees there with multiplication by one fixed public ring element. -/
def RingMultiplicationOn
    {R : Type} [CommRing R] (secrets : Set R) (automorphism : R ≃+* R) : Prop :=
  ∃ multiplier : R, ∀ secret ∈ secrets,
    automorphism secret = secret * multiplier

/-- Any secret set containing the ring unit and one element moved by an automorphism rejects such
a rank-one challenge-shift representation.  Binary and centered-ternary polynomial secret sets
contain these witnesses for every nontrivial coefficient permutation/sign automorphism. -/
theorem not_ringMultiplicationOn_of_one_mem_and_moved
    {R : Type} [CommRing R] (secrets : Set R) (automorphism : R ≃+* R)
    (hone : (1 : R) ∈ secrets) (witness : R) (hwitness : witness ∈ secrets)
    (hmoved : automorphism witness ≠ witness) :
    ¬ RingMultiplicationOn secrets automorphism := by
  rintro ⟨multiplier, hrepresentation⟩
  have honeRepresentation := hrepresentation 1 hone
  have hmultiplier : multiplier = 1 := by
    simpa using honeRepresentation.symm
  have hwitnessRepresentation := hrepresentation witness hwitness
  rw [hmultiplier, mul_one] at hwitnessRepresentation
  exact hmoved hwitnessRepresentation

/-- Support-aware obstruction requiring no unit secret.  Two allowed secrets rule out one common
rank-one multiplier whenever their automorphism images fail the displayed cross relation.  This
is the appropriate interface for fixed-Hamming-weight secret supports, which need not contain
the ring unit. -/
theorem not_ringMultiplicationOn_of_cross_mismatch
    {R : Type} [CommRing R] (secrets : Set R) (automorphism : R ≃+* R)
    (left right : R) (hleft : left ∈ secrets) (hright : right ∈ secrets)
    (hmismatch : left * automorphism right ≠ right * automorphism left) :
    ¬ RingMultiplicationOn secrets automorphism := by
  rintro ⟨multiplier, hrepresentation⟩
  have hleftRepresentation := hrepresentation left hleft
  have hrightRepresentation := hrepresentation right hright
  apply hmismatch
  rw [hrightRepresentation, hleftRepresentation]
  ring

/-- Global version: a ring automorphism representable as right multiplication everywhere is the
identity. -/
theorem ringMultiplicationOn_univ_iff_identity
    {R : Type} [CommRing R] (automorphism : R ≃+* R) :
    RingMultiplicationOn Set.univ automorphism ↔ automorphism = RingEquiv.refl R := by
  constructor
  · rintro ⟨multiplier, hrepresentation⟩
    have hone := hrepresentation 1 (Set.mem_univ 1)
    have hmultiplier : multiplier = 1 := by simpa using hone.symm
    ext value
    simpa [hmultiplier] using hrepresentation value (Set.mem_univ value)
  · intro hidentity
    subst automorphism
    exact ⟨1, by simp⟩

end

end FormalProof4FHE.RLWE.GaloisKDM
