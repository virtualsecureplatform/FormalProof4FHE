/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.GSWSelfKey
import FormalProof4FHE.LWE.MultiKeyAffine
import FormalProof4FHE.LWE.AuxiliaryInputSearchToDecision

/-!
# Public binary-secret randomization of quadratic GSW rows

Flipping secret bits is an affine map over any coefficient ring.  Each degree-at-most-two
monomial changes by a sign, a known linear correction, and a known constant.  These corrections
give a public permutation of the complete mask/body transcript.  Its error changes only by
coordinate signs; symmetric IID error laws are therefore preserved without flooding.

This randomizes a view that already contains the quadratic hints.  It does not simulate such
hints from an ordinary-LWE challenge and does not assume or prove their computational hardness.
Unmodeled secret-dependent auxiliary information cannot simply be left unchanged by a key flip.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.LWE.GSWBinaryRandomization

/-- Each public row has no hint, a linear hint, or one quadratic coordinate product. -/
inductive Monomial (dimension : ℕ) where
  | zero
  | linear (coordinate : Fin dimension)
  | quadratic (first second : Fin dimension)

abbrev Shape (dimension samples : ℕ) := Fin samples → Monomial dimension

/-- Scalar monomial evaluated on a ring-valued secret. -/
def monomialValue {R : Type} [Mul R] [Zero R] {dimension : ℕ}
    (monomial : Monomial dimension) (secret : Fin dimension → R) : R :=
  match monomial with
  | .zero => 0
  | .linear row => secret row
  | .quadratic first second => secret first * secret second

def signal {R : Type} [Mul R] [Zero R] {dimension samples : ℕ}
    (shape : Shape dimension samples) (weight : Fin samples → R)
    (secret : Fin dimension → R) : Fin samples → R :=
  fun column ↦ weight column * monomialValue (shape column) secret

def maskEmbed {R : Type} [Zero R] [One R] {dimension : ℕ}
    (mask : Fin dimension → Bool) : Fin dimension → R :=
  fun row ↦ MultiKeyAffine.embedBit (mask row)

def signedSecret {R : Type} [Ring R] {dimension : ℕ}
    (mask : Fin dimension → Bool) (secret : Fin dimension → R) : Fin dimension → R :=
  fun row ↦ MultiKeyAffine.maskSign (mask row) * secret row

def affineSecret {R : Type} [Ring R] {dimension : ℕ}
    (mask : Fin dimension → Bool) (secret : Fin dimension → R) : Fin dimension → R :=
  signedSecret mask secret + maskEmbed mask

def flip {dimension : ℕ} (mask secret : Fin dimension → Bool) : Fin dimension → Bool :=
  fun row ↦ MultiKeyAffine.maskedBit (secret row) (mask row)

theorem binaryEmbed_flip {R : Type} [Ring R] {dimension : ℕ}
    (mask secret : Fin dimension → Bool) :
    GSWSelfKey.binaryEmbed (R := R) (flip mask secret) =
      affineSecret mask (GSWSelfKey.binaryEmbed secret) := by
  funext row
  exact MultiKeyAffine.embed_maskedBit (secret row) (mask row)

/-- A monomial's sign under the bit flip. -/
def rowSign {R : Type} [Ring R] {dimension : ℕ}
    (monomial : Monomial dimension) (mask : Fin dimension → Bool) : R :=
  match monomial with
  | .zero => 1
  | .linear row => MultiKeyAffine.maskSign (mask row)
  | .quadratic first second =>
      MultiKeyAffine.maskSign (mask first) * MultiKeyAffine.maskSign (mask second)

theorem rowSign_sq {R : Type} [CommRing R] {dimension : ℕ}
    (monomial : Monomial dimension) (mask : Fin dimension → Bool) :
    rowSign (R := R) monomial mask * rowSign monomial mask = 1 := by
  cases monomial with
  | zero => simp [rowSign]
  | linear row => exact MultiKeyAffine.maskSign_sq (mask row)
  | quadratic first second =>
    cases hfirst : mask first <;> cases hsecond : mask second <;>
      simp [rowSign, MultiKeyAffine.maskSign, hfirst, hsecond]

/-- Public mask correction, nonzero only for quadratic rows. -/
def correction {R : Type} [Ring R] {dimension samples : ℕ}
    (shape : Shape dimension samples) (weight : Fin samples → R)
    (mask : Fin dimension → Bool) : Matrix (Fin dimension) (Fin samples) R :=
  fun row column ↦ match shape column with
  | .quadratic first second =>
      weight column *
        ((if row = first then MultiKeyAffine.embedBit (mask second) else 0) +
          (if row = second then MultiKeyAffine.embedBit (mask first) else 0))
  | _ => 0

theorem vecMul_correction {R : Type} [CommRing R] {dimension samples : ℕ}
    (shape : Shape dimension samples) (weight : Fin samples → R)
    (mask : Fin dimension → Bool) (secret : Fin dimension → R) (column : Fin samples) :
    vecMul secret (correction shape weight mask) column =
      match shape column with
      | .quadratic first second => weight column *
          (secret first * MultiKeyAffine.embedBit (mask second) +
            secret second * MultiKeyAffine.embedBit (mask first))
      | _ => 0 := by
  cases hshape : shape column with
  | zero => simp [vecMul, dotProduct, correction, hshape]
  | linear row => simp [vecMul, dotProduct, correction, hshape]
  | quadratic first second =>
    simp only [vecMul, dotProduct, correction, hshape]
    simp_rw [mul_add, mul_ite]
    rw [Finset.sum_add_distrib]
    simp
    ring

/-- Exact expansion of the shifted hint, including its public derivative and constant. -/
theorem signal_affineSecret {R : Type} [CommRing R] {dimension samples : ℕ}
    (shape : Shape dimension samples) (weight : Fin samples → R)
    (mask : Fin dimension → Bool) (secret : Fin dimension → R) (column : Fin samples) :
    signal shape weight (affineSecret mask secret) column =
      rowSign (shape column) mask * signal shape weight secret column +
        vecMul (signedSecret mask secret) (correction shape weight mask) column +
        signal shape weight (maskEmbed mask) column := by
  rw [vecMul_correction]
  cases hshape : shape column <;>
    simp [signal, monomialValue, affineSecret, signedSecret, maskEmbed, rowSign, hshape]
  all_goals ring

def challengeMultiplier {R : Type} [Ring R] {dimension samples : ℕ}
    (shape : Shape dimension samples) (mask : Fin dimension → Bool)
    (row : Fin dimension) (column : Fin samples) : R :=
  rowSign (shape column) mask * MultiKeyAffine.maskSign (mask row)

theorem challengeMultiplier_sq {R : Type} [CommRing R] {dimension samples : ℕ}
    (shape : Shape dimension samples) (mask : Fin dimension → Bool)
    (row : Fin dimension) (column : Fin samples) :
    challengeMultiplier (R := R) shape mask row column *
      challengeMultiplier shape mask row column = 1 := by
  calc
    _ = (rowSign (R := R) (shape column) mask * rowSign (shape column) mask) *
        (MultiKeyAffine.maskSign (mask row) * MultiKeyAffine.maskSign (mask row)) := by
      simp only [challengeMultiplier]
      ring
    _ = 1 := by rw [rowSign_sq, MultiKeyAffine.maskSign_sq, mul_one]

/-- Transform all public masks, using only the chosen flip and the public monomial layout. -/
def transformChallenge {R : Type} [Ring R] {dimension samples : ℕ}
    (shape : Shape dimension samples) (weight : Fin samples → R)
    (mask : Fin dimension → Bool) (challenge : Matrix (Fin dimension) (Fin samples) R) :
    Matrix (Fin dimension) (Fin samples) R :=
  fun row column ↦ challengeMultiplier shape mask row column * challenge row column -
    correction shape weight mask row column

def untransformChallenge {R : Type} [Ring R] {dimension samples : ℕ}
    (shape : Shape dimension samples) (weight : Fin samples → R)
    (mask : Fin dimension → Bool) (challenge : Matrix (Fin dimension) (Fin samples) R) :
    Matrix (Fin dimension) (Fin samples) R :=
  fun row column ↦ challengeMultiplier shape mask row column *
    (challenge row column + correction shape weight mask row column)

@[simp]
theorem untransformChallenge_transformChallenge {R : Type} [CommRing R]
    {dimension samples : ℕ} (shape : Shape dimension samples) (weight : Fin samples → R)
    (mask : Fin dimension → Bool) (challenge : Matrix (Fin dimension) (Fin samples) R) :
    untransformChallenge shape weight mask (transformChallenge shape weight mask challenge) =
      challenge := by
  funext row column
  simp only [untransformChallenge, transformChallenge, sub_add_cancel, ← mul_assoc,
    challengeMultiplier_sq, one_mul]

@[simp]
theorem transformChallenge_untransformChallenge {R : Type} [CommRing R]
    {dimension samples : ℕ} (shape : Shape dimension samples) (weight : Fin samples → R)
    (mask : Fin dimension → Bool) (challenge : Matrix (Fin dimension) (Fin samples) R) :
    transformChallenge shape weight mask (untransformChallenge shape weight mask challenge) =
      challenge := by
  funext row column
  simp only [untransformChallenge, transformChallenge, ← mul_assoc,
    challengeMultiplier_sq, one_mul, add_sub_cancel_right]

theorem transformChallenge_bijective {R : Type} [CommRing R]
    {dimension samples : ℕ} (shape : Shape dimension samples) (weight : Fin samples → R)
    (mask : Fin dimension → Bool) : Function.Bijective (transformChallenge shape weight mask) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨untransformChallenge shape weight mask,
      untransformChallenge_transformChallenge shape weight mask,
      transformChallenge_untransformChallenge shape weight mask⟩

theorem vecMul_signedSecret_transformChallenge {R : Type} [CommRing R]
    {dimension samples : ℕ} (shape : Shape dimension samples) (weight : Fin samples → R)
    (mask : Fin dimension → Bool) (secret : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin samples) R) (column : Fin samples) :
    vecMul (signedSecret mask secret) (transformChallenge shape weight mask challenge) column =
      rowSign (shape column) mask * vecMul secret challenge column -
        vecMul (signedSecret mask secret) (correction shape weight mask) column := by
  simp only [vecMul, dotProduct, transformChallenge, signedSecret, challengeMultiplier]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro row _
  cases mask row <;> simp [MultiKeyAffine.maskSign] <;> ring

/-- Flip only the signs of the error coordinates. -/
def transformError {R : Type} [Ring R] {dimension samples : ℕ}
    (shape : Shape dimension samples) (mask : Fin dimension → Bool)
    (error : Fin samples → R) : Fin samples → R :=
  fun column ↦ rowSign (shape column) mask * error column

def transformTranscript {R : Type} [Ring R] {dimension samples : ℕ}
    (shape : Shape dimension samples) (weight : Fin samples → R)
    (mask : Fin dimension → Bool) (transcript : BatchTranscript R dimension samples) :
    BatchTranscript R dimension samples :=
  let challenge := transformChallenge shape weight mask transcript.1
  (challenge, fun column ↦ rowSign (shape column) mask * transcript.2 column +
    vecMul (maskEmbed mask) challenge column + signal shape weight (maskEmbed mask) column)

def untransformTranscript {R : Type} [Ring R] {dimension samples : ℕ}
    (shape : Shape dimension samples) (weight : Fin samples → R)
    (mask : Fin dimension → Bool) (transcript : BatchTranscript R dimension samples) :
    BatchTranscript R dimension samples :=
  (untransformChallenge shape weight mask transcript.1,
    fun column ↦ rowSign (shape column) mask *
      (transcript.2 column - vecMul (maskEmbed mask) transcript.1 column -
        signal shape weight (maskEmbed mask) column))

/-- All hint rows and ordinary zero-hint rows retarget to the same flipped secret. -/
theorem transformTranscript_real {R : Type} [CommRing R] {dimension samples : ℕ}
    (shape : Shape dimension samples) (weight : Fin samples → R)
    (mask : Fin dimension → Bool) (secret : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin samples) R) (error : Fin samples → R) :
    transformTranscript shape weight mask
        (challenge, (vecMul secret challenge + signal shape weight secret) + error) =
      (transformChallenge shape weight mask challenge,
        (vecMul (affineSecret mask secret) (transformChallenge shape weight mask challenge) +
          signal shape weight (affineSecret mask secret)) + transformError shape mask error) := by
  apply Prod.ext
  · rfl
  · funext column
    simp only [transformTranscript, transformError, Pi.add_apply]
    rw [signal_affineSecret]
    simp only [affineSecret, add_vecMul, Pi.add_apply]
    rw [vecMul_signedSecret_transformChallenge]
    ring

@[simp]
theorem untransformTranscript_transformTranscript {R : Type} [CommRing R]
    {dimension samples : ℕ} (shape : Shape dimension samples) (weight : Fin samples → R)
    (mask : Fin dimension → Bool) (transcript : BatchTranscript R dimension samples) :
    untransformTranscript shape weight mask (transformTranscript shape weight mask transcript) =
      transcript := by
  apply Prod.ext
  · exact untransformChallenge_transformChallenge shape weight mask transcript.1
  · funext column
    simp only [untransformTranscript, transformTranscript, untransformChallenge_transformChallenge]
    change rowSign (shape column) mask *
      (rowSign (shape column) mask * transcript.2 column +
        vecMul (maskEmbed mask) (transformChallenge shape weight mask transcript.1) column +
        signal shape weight (maskEmbed mask) column -
        vecMul (maskEmbed mask) (transformChallenge shape weight mask transcript.1) column -
        signal shape weight (maskEmbed mask) column) = transcript.2 column
    ring_nf
    rw [pow_two, rowSign_sq, one_mul]

@[simp]
theorem transformTranscript_untransformTranscript {R : Type} [CommRing R]
    {dimension samples : ℕ} (shape : Shape dimension samples) (weight : Fin samples → R)
    (mask : Fin dimension → Bool) (transcript : BatchTranscript R dimension samples) :
    transformTranscript shape weight mask (untransformTranscript shape weight mask transcript) =
      transcript := by
  apply Prod.ext
  · exact transformChallenge_untransformChallenge shape weight mask transcript.1
  · funext column
    simp only [transformTranscript, untransformTranscript, transformChallenge_untransformChallenge]
    change rowSign (shape column) mask *
      (rowSign (shape column) mask *
        (transcript.2 column - vecMul (maskEmbed mask) transcript.1 column -
          signal shape weight (maskEmbed mask) column)) +
      vecMul (maskEmbed mask) transcript.1 column + signal shape weight (maskEmbed mask) column =
      transcript.2 column
    rw [← mul_assoc, rowSign_sq, one_mul]
    abel

theorem transformTranscript_bijective {R : Type} [CommRing R] {dimension samples : ℕ}
    (shape : Shape dimension samples) (weight : Fin samples → R)
    (mask : Fin dimension → Bool) : Function.Bijective (transformTranscript shape weight mask) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨untransformTranscript shape weight mask,
      untransformTranscript_transformTranscript shape weight mask,
      transformTranscript_untransformTranscript shape weight mask⟩

/-- A sign is always one of the two scalar error symmetries. -/
theorem rowSign_eq_one_or_negOne {R : Type} [CommRing R] {dimension : ℕ}
    (monomial : Monomial dimension) (mask : Fin dimension → Bool) :
    rowSign (R := R) monomial mask = 1 ∨ rowSign (R := R) monomial mask = -1 := by
  cases monomial with
  | zero => simp [rowSign]
  | linear row => cases h : mask row <;> simp [rowSign, MultiKeyAffine.maskSign, h]
  | quadratic first second =>
    cases hfirst : mask first <;> cases hsecond : mask second <;>
      simp [rowSign, MultiKeyAffine.maskSign, hfirst, hsecond]

/-- Scalar negation symmetry lifts to the complete independent error tape. -/
theorem transformError_sampleIID_evalDist {R : Type} [CommRing R] [Finite R]
    {dimension samples : ℕ} (shape : Shape dimension samples)
    (mask : Fin dimension → Bool) (errorSampler : ProbComp R)
    (symmetric : evalDist ((fun value : R ↦ -value) <$> errorSampler) = evalDist errorSampler) :
    evalDist (transformError shape mask <$> ProbComp.sampleIID samples errorSampler) =
      evalDist (ProbComp.sampleIID samples errorSampler) := by
  unfold transformError ProbComp.sampleIID
  rw [FormalProof4FHE.FiniteProduct.map_fin_mOfFn]
  apply FormalProof4FHE.FiniteProduct.evalDist_fin_mOfFn_congr
  intro column
  rcases rowSign_eq_one_or_negOne (R := R) (shape column) mask with hsign | hsign
  · have hfunction : (HMul.hMul (rowSign (shape column) mask) : R → R) = id := by
      funext value
      rw [hsign, one_mul]
      rfl
    rw [hfunction]
    simp
  · have hfunction : (HMul.hMul (rowSign (shape column) mask) : R → R) =
        (fun value : R ↦ -value) := by
      funext value
      rw [hsign, neg_one_mul]
    rw [hfunction]
    exact symmetric

/-- Complete normalized view for a fixed binary secret, with an arbitrary joint error law. -/
def realView {R : Type} [CommRing R] [SampleableType R] {dimension samples : ℕ}
    (shape : Shape dimension samples) (weight : Fin samples → R)
    (errorSampler : ProbComp (Fin samples → R)) (secret : Fin dimension → Bool) :
    ProbComp (BatchTranscript R dimension samples) := do
  let challenge ← $ᵗ Matrix (Fin dimension) (Fin samples) R
  let error ← errorSampler
  return (challenge, (vecMul (GSWSelfKey.binaryEmbed secret) challenge +
    signal shape weight (GSWSelfKey.binaryEmbed secret)) + error)

/-- Exact per-secret, per-flip joint law.  The hypothesis concerns the full error tape;
scalar symmetry suffices when the coordinates are independently sampled. -/
theorem transformTranscript_realView_evalDist {R : Type}
    [CommRing R] [Fintype R] [SampleableType R] {dimension samples : ℕ}
    (shape : Shape dimension samples) (weight : Fin samples → R)
    (mask : Fin dimension → Bool) (errorSampler : ProbComp (Fin samples → R))
    (secret : Fin dimension → Bool)
    (symmetric : evalDist (transformError shape mask <$> errorSampler) = evalDist errorSampler) :
    evalDist (transformTranscript shape weight mask <$> realView shape weight errorSampler secret) =
      evalDist (realView shape weight errorSampler (flip mask secret)) := by
  let finish := fun challenge : Matrix (Fin dimension) (Fin samples) R ↦ do
    let error ← errorSampler
    return (challenge, (vecMul (GSWSelfKey.binaryEmbed (flip mask secret)) challenge +
      signal shape weight (GSWSelfKey.binaryEmbed (flip mask secret))) + error)
  calc
    _ = evalDist (do
        let challenge ← $ᵗ Matrix (Fin dimension) (Fin samples) R
        let error ← transformError shape mask <$> errorSampler
        return (transformChallenge shape weight mask challenge,
          (vecMul (GSWSelfKey.binaryEmbed (flip mask secret))
              (transformChallenge shape weight mask challenge) +
            signal shape weight (GSWSelfKey.binaryEmbed (flip mask secret))) + error)) := by
      simp only [realView, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
      simp_rw [transformTranscript_real, binaryEmbed_flip]
    _ = evalDist (($ᵗ Matrix (Fin dimension) (Fin samples) R) >>= fun challenge ↦
        finish (transformChallenge shape weight mask challenge)) := by
      simp only [finish, evalDist_bind, symmetric]
    _ = _ := by
      apply evalDist_ext
      intro output
      exact probOutput_bind_bijective_uniform_cross
        (α := Matrix (Fin dimension) (Fin samples) R)
        (β := Matrix (Fin dimension) (Fin samples) R)
        (transformChallenge shape weight mask) (transformChallenge_bijective shape weight mask)
        finish output

/-- The same public transformation preserves the complete uniform transcript. -/
theorem transformTranscript_uniform_evalDist {R : Type}
    [CommRing R] [Fintype R] [SampleableType R] {dimension samples : ℕ}
    (shape : Shape dimension samples) (weight : Fin samples → R)
    (mask : Fin dimension → Bool) :
    evalDist (transformTranscript shape weight mask <$>
      ($ᵗ BatchTranscript R dimension samples)) =
      evalDist ($ᵗ BatchTranscript R dimension samples) :=
  evalDist_map_bijective_uniform_cross
    (α := BatchTranscript R dimension samples) (β := BatchTranscript R dimension samples)
    (transformTranscript shape weight mask) (transformTranscript_bijective shape weight mask)

/-- For fixed secret, uniformly chosen flips produce a fresh uniform binary secret. -/
theorem flip_uniform_evalDist {dimension : ℕ} (secret : Fin dimension → Bool) :
    evalDist ((fun mask ↦ flip mask secret) <$> ($ᵗ (Fin dimension → Bool))) =
      evalDist ($ᵗ (Fin dimension → Bool)) := by
  apply evalDist_map_bijective_uniform_cross
  apply Function.bijective_iff_has_inverse.mpr
  refine ⟨(fun mask ↦ flip mask secret), ?_, ?_⟩ <;>
    intro mask <;> funext row <;>
    change MultiKeyAffine.maskedBit (secret row)
      (MultiKeyAffine.maskedBit (secret row) (mask row)) = mask row
  all_goals cases secret row <;> cases mask row <;> rfl

/-- Instantiation of the existing search-to-decision view-randomization interface.
The input view already contains the quadratic hints.  This definition supplies exact public
randomization, not an ordinary-LWE simulator or a search-hardness certificate. -/
def viewRandomization {R : Type} [CommRing R] [Fintype R] [SampleableType R]
    {dimension samples : ℕ} (shape : Shape dimension samples) (weight : Fin samples → R)
    (errorSampler : ProbComp R)
    (symmetric : evalDist ((fun value : R ↦ -value) <$> errorSampler) = evalDist errorSampler) :
    AuxiliaryInput.SearchToDecision.ViewRandomization
      (Fin dimension → Bool) (Fin dimension → Bool) (BatchTranscript R dimension samples) :=
  AuxiliaryInput.SearchToDecision.ViewRandomization.ofExact
    ($ᵗ (Fin dimension → Bool)) (fun secret mask ↦ flip mask secret)
    ($ᵗ (Fin dimension → Bool))
    (realView shape weight (ProbComp.sampleIID samples errorSampler))
    (fun mask transcript ↦ pure (transformTranscript shape weight mask transcript))
    flip_uniform_evalDist (fun secret mask ↦ by
      simpa only [map_eq_bind_pure_comp, Function.comp_def] using
        transformTranscript_realView_evalDist shape weight mask
          (ProbComp.sampleIID samples errorSampler) secret
          (transformError_sampleIID_evalDist shape mask errorSampler symmetric))

/-- Monomials of the actual full self-key GSW tape, in its original flattened order. -/
def selfKeyShape (dimension digits : ℕ) :
    Shape dimension (dimension * ((dimension + 1) * digits)) :=
  fun column ↦
    let position := GSWSelfKey.selfKeyPosition dimension digits column
    Fin.cases (.linear position.1) (fun row ↦ .quadratic position.1 row) position.2.1

/-- Actual gadget weights; mask-phase products carry the negative gadget weight. -/
def selfKeyWeight {R : Type} [Neg R] (dimension digits : ℕ) (gadget : Fin digits → R) :
    Fin (dimension * ((dimension + 1) * digits)) → R :=
  fun column ↦
    let position := GSWSelfKey.selfKeyPosition dimension digits column
    Fin.cases (gadget position.2.2) (fun _ ↦ -gadget position.2.2) position.2.1

/-- This is the complete GSW self-key phase, rather than a different quadratic-hint layout. -/
theorem signal_selfKey_eq_phaseMessage {R : Type} [CommRing R] {dimension digits : ℕ}
    (gadget : Fin digits → R) (secret : Fin dimension → R) :
    signal (selfKeyShape dimension digits) (selfKeyWeight dimension digits gadget) secret =
      GSWSelfKey.phaseMessage (GSWSelfKey.selfKeyLayout dimension digits gadget) secret
        (GSWSelfKey.selfKeyMessages digits secret) := by
  funext column
  obtain ⟨⟨encrypted, inner⟩, rfl⟩ := finProdFinEquiv.surjective column
  obtain ⟨⟨coordinate, digit⟩, rfl⟩ := finProdFinEquiv.surjective inner
  change signal _ _ secret (GSWSelfKey.selfKeyColumn encrypted coordinate digit) = _
  refine Fin.cases ?_ (fun row ↦ ?_) coordinate
  · change _ = GSWSelfKey.phaseMessage (GSWSelfKey.selfKeyLayout dimension digits gadget)
      secret (GSWSelfKey.selfKeyMessages digits secret) (GSWSelfKey.selfKeyColumn encrypted 0 digit)
    rw [GSWSelfKey.selfKey_body_phase]
    simp [signal, selfKeyShape, selfKeyWeight, monomialValue, mul_comm]
  · change _ = GSWSelfKey.phaseMessage (GSWSelfKey.selfKeyLayout dimension digits gadget)
      secret (GSWSelfKey.selfKeyMessages digits secret)
      (GSWSelfKey.selfKeyColumn encrypted row.succ digit)
    rw [GSWSelfKey.selfKey_mask_phase]
    simp [signal, selfKeyShape, selfKeyWeight, monomialValue]
    ring

end FormalProof4FHE.LWE.GSWBinaryRandomization
