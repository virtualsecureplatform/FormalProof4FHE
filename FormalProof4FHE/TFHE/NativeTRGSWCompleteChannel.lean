/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeTRGSWBarrierAndSpectralBoundary
import FormalProof4FHE.TFHE.SharedRandomnessOneCycle
import FormalProof4FHE.Probability.BoundedMoment

/-!
# Complete native TRGSW channel

This module connects the abstract complete-channel Fourier theorem to the concrete native
shared-prefix/suffix TFHE cloud-key sampler.  Conditional on a binary prefix `p` and an arbitrary
binary BRK message vector `m`, it samples the independent suffix, generates the complete native
BRK encrypting `m`, and retains the real suffix KSK under `p`.  Consequently the native circular
view is the diagonal `m = p`, while the randomized-message view uses independent uniform `p,m`.

The module also records the exact support-restriction leakage cardinality and a posterior-spectral
sanity check: any decoder of a diagonal parity gives a lower bound on the corresponding posterior
spectral radius.  Thus an information-theoretically recoverable parity cannot satisfy a negligible
statistical spectral-tail premise.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.NativeTRGSWCompleteChannel

noncomputable section

open NativeTRGSWBarrierAndSpectralBoundary
open Native.SharedRandomnessOneCycle

/-- The negation operation selected canonically by a commutative-ring structure. -/
abbrev commRingNeg (R : Type) [CommRing R] : Neg R :=
  SubNegMonoid.toNeg

/-! ## Turning a total finite sampler kernel into a complete channel -/

/-- Conditional point mass of a finite sampler kernel, represented as a real-valued complete
channel. -/
def channelOfSampler
    {Index View : Type} [Fintype View]
    (sampler : BitVector Index → BitVector Index → ProbComp View) :
    CompleteChannel Index View :=
  fun view secret message ↦ Pr[= view | sampler secret message].toReal

theorem channelOfSampler_nonneg
    {Index View : Type} [Fintype View]
    (sampler : BitVector Index → BitVector Index → ProbComp View)
    (view : View) (secret message : BitVector Index) :
    0 ≤ channelOfSampler sampler view secret message :=
  ENNReal.toReal_nonneg

/-- A total conditional sampler gives a normalized complete channel. -/
theorem channelOfSampler_normalized
    {Index View : Type} [Fintype View]
    (sampler : BitVector Index → BitVector Index → ProbComp View)
    (htotal : ∀ secret message, probFailure (sampler secret message) = 0)
    (secret message : BitVector Index) :
    ∑ view, channelOfSampler sampler view secret message = 1 := by
  unfold channelOfSampler
  rw [← ENNReal.toReal_sum (fun _ _ ↦ probOutput_ne_top),
    sum_probOutput_eq_one (htotal secret message), ENNReal.toReal_one]

/-- The response induced by a sampler channel is exactly finite expectation under its
conditional sampler. -/
theorem completeChannelResponse_channelOfSampler_eq_expectation
    {Index View : Type} [Fintype View]
    (sampler : BitVector Index → BitVector Index → ProbComp View)
    (response : View → ℝ) (secret message : BitVector Index) :
    completeChannelResponse (channelOfSampler sampler) response secret message =
      FormalProof4FHE.BoundedMoment.expectation (sampler secret message) response := by
  rfl

/-- Acceptance probability of a randomized adversary is the expectation of its pointwise
acceptance response. -/
def adversaryResponse {View : Type} (adversary : View → ProbComp Bool) (view : View) : ℝ :=
  Pr[= true | adversary view].toReal

theorem expectation_adversaryResponse_eq_probOutput
    {View : Type} [Fintype View]
    (sampler : ProbComp View) (adversary : View → ProbComp Bool) :
    FormalProof4FHE.BoundedMoment.expectation sampler (adversaryResponse adversary) =
      Pr[= true | sampler >>= adversary].toReal := by
  classical
  unfold FormalProof4FHE.BoundedMoment.expectation adversaryResponse
  rw [probOutput_bind_eq_sum_fintype,
    ENNReal.toReal_sum (fun _ _ ↦
      ENNReal.mul_ne_top probOutput_ne_top probOutput_ne_top)]
  simp_rw [ENNReal.toReal_mul]

theorem adversaryResponse_abs_le_one
    {View : Type} (adversary : View → ProbComp Bool) (view : View) :
    |adversaryResponse adversary view| ≤ 1 := by
  unfold adversaryResponse
  rw [abs_of_nonneg ENNReal.toReal_nonneg, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono ENNReal.one_ne_top probOutput_le_one

/-- The diagonal mean of a sampler channel is the expectation under its diagonal sampler. -/
theorem diagonalMean_channelOfSampler_eq_expectation
    {Index View : Type} [Fintype Index] [DecidableEq Index]
    [Fintype View] [SampleableType (BitVector Index)]
    (sampler : BitVector Index → BitVector Index → ProbComp View)
    (response : View → ℝ) :
    diagonalMean (completeChannelResponse (channelOfSampler sampler) response) =
      FormalProof4FHE.BoundedMoment.expectation
        (($ᵗ (BitVector Index)) >>= fun secret ↦ sampler secret secret) response := by
  classical
  rw [FormalProof4FHE.BoundedMoment.expectation_bind]
  simp_rw [← completeChannelResponse_channelOfSampler_eq_expectation]
  unfold diagonalMean
  have hcard : (Fintype.card (BitVector Index) : ℝ) = cubeSize Index := by
    simp [cubeSize]
  simp_rw [probOutput_uniformSample, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [← Finset.mul_sum, hcard]
  field_simp [cubeSize_ne_zero Index]

/-- The independent mean is the expectation under independently sampled secret and message. -/
theorem independentMean_channelOfSampler_eq_expectation
    {Index View : Type} [Fintype Index] [DecidableEq Index]
    [Fintype View] [SampleableType (BitVector Index)]
    (sampler : BitVector Index → BitVector Index → ProbComp View)
    (response : View → ℝ) :
    independentMean (completeChannelResponse (channelOfSampler sampler) response) =
      FormalProof4FHE.BoundedMoment.expectation
        (($ᵗ (BitVector Index)) >>= fun secret ↦
          ($ᵗ (BitVector Index)) >>= fun message ↦ sampler secret message) response := by
  classical
  rw [FormalProof4FHE.BoundedMoment.expectation_bind]
  simp_rw [FormalProof4FHE.BoundedMoment.expectation_bind]
  simp_rw [← completeChannelResponse_channelOfSampler_eq_expectation]
  unfold independentMean
  have hcard : (Fintype.card (BitVector Index) : ℝ) = cubeSize Index := by
    simp [cubeSize]
  simp_rw [probOutput_uniformSample, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [← Finset.mul_sum]
  simp_rw [← Finset.mul_sum]
  rw [hcard]
  field_simp [cubeSize_ne_zero Index]

/-! ## Exact bounded-support leakage -/

/-- Restriction of a binary word to the support of one Walsh frequency. -/
abbrev SupportLeakage
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (frequency : BitVector Index) :=
  {coordinate : Index // coordinate ∈ frequencySupport frequency} → Bool

def supportLeakage
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (frequency : BitVector Index) (secret : BitVector Index) :
    SupportLeakage frequency :=
  fun coordinate ↦ secret coordinate.1

/-- Revealing precisely the frequency support has exactly `2^|S|` possible values. -/
theorem card_supportLeakage
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (frequency : BitVector Index) :
    Fintype.card (SupportLeakage frequency) =
      2 ^ supportSize frequency := by
  classical
  simp [SupportLeakage, supportSize]

/-- A degree-`d` frequency leaks at most `2^d` possible binary strings. -/
theorem card_supportLeakage_le
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (frequency : BitVector Index) (degree : ℕ)
    (hdegree : supportSize frequency ≤ degree) :
    Fintype.card (SupportLeakage frequency) ≤ 2 ^ degree := by
  rw [card_supportLeakage]
  exact Nat.pow_le_pow_right (by norm_num) hdegree

/-- Revealing exactly the coordinates in a Walsh support incurs the finite-range leakage loss
`sqrt (2^(degree+1) * delta)`.  In particular, the leakage carrier is derived from the frequency;
its size is not an independently chosen proof constant. -/
theorem supportLeakageRemoval_binaryBound
    {Index : Type} [Fintype Index] [DecidableEq Index]
    [SampleableType (BitVector Index)]
    (frequency : BitVector Index) (degree : ℕ)
    (real ideal : SupportLeakage frequency → BitVector Index → ProbComp Bool)
    (delta : ℝ) (hdegree : supportSize frequency ≤ degree)
    (hremoval :
      RGSWCoefficientCircularSecurity.leakageRemovalAdvantage
        ($ᵗ (BitVector Index)) ($ᵗ (SupportLeakage frequency)) real ideal ≤ delta) :
    RGSWCoefficientCircularSecurity.leakedAdvantage
        ($ᵗ (BitVector Index)) (supportLeakage frequency) real ideal ≤
      Real.sqrt ((2 : ℝ) ^ (degree + 1) * delta) := by
  exact finiteRangeLeakageRemoval_binaryBound
    ($ᵗ (BitVector Index)) (supportLeakage frequency) real ideal degree delta
    (card_supportLeakage_le frequency degree hdegree) hremoval

/-! ## Known-message affine normal form -/

/-- Once the TGSW message is known, the direct-row body is affine in the encryption secret:
the public gadget-mask term can be absorbed into the public challenge, while the gadget-body
term becomes a public offset.  The bilinear obstruction from the circular experiment is therefore
absent in every conditioned known-message game. -/
theorem vecMul_add_gadgetPhase_add_error_eq_knownMessageAffine
    {R : Type} [Ring R] {dimension levels : ℕ}
    (secret : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R)
    (error : Fin (TGSW.rowCount dimension levels) → R)
    (gadget : Fin levels → R) (message : R) :
    Matrix.vecMul secret challenge + TGSW.gadgetPhase secret gadget message + error =
      Matrix.vecMul secret (challenge - TGSW.gadgetMaskShift gadget message) +
        TGSW.gadgetBodyShift gadget message + error := by
  funext row
  simp only [TGSW.gadgetPhase, Matrix.vecMul, dotProduct, Pi.add_apply,
    Pi.sub_apply, Matrix.sub_apply]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  abel

/-- Publicly absorb the known-message gadget-mask shift into the displayed challenge while
leaving the body unchanged. -/
def normalizeKnownMessageDirectCiphertext
    {R : Type} [Ring R] {dimension levels : ℕ}
    (gadget : Fin levels → R) (message : R)
    (ciphertext : TGSW.Ciphertext R dimension levels) :
    TGSW.Ciphertext R dimension levels :=
  (TGSW.unshiftChallenge gadget message ciphertext.1, ciphertext.2)

/-- The pointwise normalized direct ciphertext is an ordinary affine batch-LWE assembly with a
public message vector. -/
@[simp]
theorem normalizeKnownMessageDirectCiphertext_batchAssemble
    {R : Type} [Ring R] {dimension levels : ℕ}
    (secret : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R)
    (error : Fin (TGSW.rowCount dimension levels) → R)
    (gadget : Fin levels → R) (message : R) :
    normalizeKnownMessageDirectCiphertext gadget message
        (TLWE.batchAssemble secret challenge
          (TGSW.gadgetPhase secret gadget message) error) =
      TLWE.batchAssemble secret (TGSW.unshiftChallenge gadget message challenge)
        (TGSW.gadgetBodyShift gadget message) error := by
  apply Prod.ext
  · rfl
  · exact vecMul_add_gadgetPhase_add_error_eq_knownMessageAffine
      secret challenge error gadget message

/-- Subtracting the fixed known-message mask shift is a bijection of the complete challenge
matrix. -/
theorem unshiftChallenge_bijective
    {R : Type} [Ring R] {dimension levels : ℕ}
    (gadget : Fin levels → R) (message : R) :
    Function.Bijective (TGSW.unshiftChallenge (dimension := dimension) gadget message) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨TGSW.shiftChallenge gadget message,
      TGSW.shiftChallenge_unshiftChallenge gadget message,
      TGSW.unshiftChallenge_shiftChallenge gadget message⟩

/-- Exact distributional affine-source normal form for a fixed known TGSW message. After the
public mask normalization, native direct encryption is ordinary batch LWE/RLWE with the public
message vector `gadgetBodyShift gadget message`. -/
theorem normalizeKnownMessageDirectCiphertext_directEncrypt_evalDist
    {R : Type} [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (dimension levels : ℕ) (errorSampler : ProbComp R)
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R) :
    evalDist (normalizeKnownMessageDirectCiphertext gadget message <$>
        TGSW.directEncrypt dimension levels errorSampler secret gadget message) =
      evalDist (TLWE.batchEncrypt dimension (TGSW.rowCount dimension levels)
        errorSampler secret (TGSW.gadgetBodyShift gadget message)) := by
  let challenges :
      ProbComp (Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R) :=
    $ᵗ Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R
  let errors : ProbComp (Fin (TGSW.rowCount dimension levels) → R) :=
    ProbComp.sampleIID (TGSW.rowCount dimension levels) errorSampler
  let finish := fun challenge :
      Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R ↦
    errors >>= fun error ↦ pure (TLWE.batchAssemble secret challenge
      (TGSW.gadgetBodyShift gadget message) error)
  have hchallenge :
    evalDist (TGSW.unshiftChallenge gadget message <$> challenges) =
        evalDist challenges :=
    evalDist_map_bijective_uniform_cross
      (α := Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R)
      (β := Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R)
      (TGSW.unshiftChallenge (dimension := dimension) gadget message)
      (unshiftChallenge_bijective gadget message)
  calc
    _ = evalDist ((TGSW.unshiftChallenge gadget message <$> challenges) >>= finish) := by
      simp [TGSW.directEncrypt, TLWE.batchEncrypt, challenges, errors, finish,
        map_eq_bind_pure_comp, bind_assoc, monad_norm]
    _ = evalDist (challenges >>= finish) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hchallenge finish
    _ = _ := by
      simp [TLWE.batchEncrypt, challenges, errors, finish, monad_norm]

/-- The same affine-source normal form for the native structured TGSW sampler. The native-to-direct
reparameterization and the known-message mask normalization both have exact distributional loss
zero. -/
theorem normalizeKnownMessageDirectCiphertext_encrypt_evalDist
    {R : Type} [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (dimension levels : ℕ) (errorSampler : ProbComp R)
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R) :
    evalDist (normalizeKnownMessageDirectCiphertext gadget message <$>
        TGSW.encrypt dimension levels errorSampler secret gadget message) =
      evalDist (TLWE.batchEncrypt dimension (TGSW.rowCount dimension levels)
        errorSampler secret (TGSW.gadgetBodyShift gadget message)) := by
  calc
    _ = evalDist (normalizeKnownMessageDirectCiphertext gadget message <$>
        TGSW.directEncrypt dimension levels errorSampler secret gadget message) :=
      evalDist_map_eq_of_evalDist_eq
        (TGSW.encrypt_evalDist_eq_directEncrypt dimension levels errorSampler
          secret gadget message)
        (normalizeKnownMessageDirectCiphertext gadget message)
    _ = _ := normalizeKnownMessageDirectCiphertext_directEncrypt_evalDist
      dimension levels errorSampler secret gadget message

/-! ## Low-degree affine-source certificate -/

/-- Data still required from a concrete affine-source reduction for every low Walsh frequency.
The certificate separates the cryptographic game identification (`coefficient_le`) from the
ordinary leakage-removal bound (`removal_le`).  The support cardinality and square-root loss are
then derived automatically. -/
structure LowDegreeAffineSourceCertificate
    {Index View : Type} [Fintype Index] [DecidableEq Index]
    [SampleableType (BitVector Index)] [Fintype View]
    (channel : CompleteChannel Index View) (response : View → ℝ)
    (degree : ℕ) (delta : ℝ) where
  real : (frequency : BitVector Index) →
    SupportLeakage frequency → BitVector Index → ProbComp Bool
  ideal : (frequency : BitVector Index) →
    SupportLeakage frequency → BitVector Index → ProbComp Bool
  coefficient_le : ∀ frequency ∈ lowFrequencies Index degree,
    |fourierCoefficient (completeChannelResponse channel response) frequency frequency| ≤
      RGSWCoefficientCircularSecurity.leakedAdvantage
        ($ᵗ (BitVector Index)) (supportLeakage frequency)
          (real frequency) (ideal frequency)
  removal_le : ∀ frequency ∈ lowFrequencies Index degree,
    RGSWCoefficientCircularSecurity.leakageRemovalAdvantage
      ($ᵗ (BitVector Index)) ($ᵗ (SupportLeakage frequency))
        (real frequency) (ideal frequency) ≤ delta

/-- A low-degree affine-source certificate discharges the complete low-frequency premise of the
native spectral theorem. -/
theorem LowDegreeAffineSourceCertificate.lowFrequencyBound
    {Index View : Type} [Fintype Index] [DecidableEq Index]
    [SampleableType (BitVector Index)] [Fintype View]
    {channel : CompleteChannel Index View} {response : View → ℝ}
    {degree : ℕ} {delta : ℝ}
    (certificate : LowDegreeAffineSourceCertificate channel response degree delta)
    (frequency : BitVector Index) (hfrequency : frequency ∈ lowFrequencies Index degree) :
    |fourierCoefficient (completeChannelResponse channel response) frequency frequency| ≤
      Real.sqrt ((2 : ℝ) ^ (degree + 1) * delta) := by
  have hdegree : supportSize frequency ≤ degree :=
    (Finset.mem_filter.mp hfrequency).2
  exact (certificate.coefficient_le frequency hfrequency).trans
    (supportLeakageRemoval_binaryBound frequency degree
      (certificate.real frequency) (certificate.ideal frequency) delta hdegree
      (certificate.removal_le frequency hfrequency))

/-! ## Decoder lower bounds for posterior spectral radius -/

/-- Signed response of a deterministic Boolean parity predictor. -/
def decoderSign {View : Type} (predictor : View → Bool) (view : View) : ℝ :=
  bitSign (predictor view)

@[simp]
theorem abs_decoderSign {View : Type} (predictor : View → Bool) (view : View) :
    |decoderSign predictor view| = 1 := by
  cases hprediction : predictor view <;> simp [decoderSign, bitSign, hprediction]

/-- Uniform-input success probability for predicting the diagonal Walsh parity
`χ_S(secret) χ_S(message)` from the complete view. -/
def completeChannelDecoderSuccess
    {Index View : Type} [Fintype Index] [DecidableEq Index] [Fintype View]
    (channel : CompleteChannel Index View) (frequency : BitVector Index)
    (predictor : View → Bool) : ℝ :=
  (∑ secret : BitVector Index, ∑ message : BitVector Index, ∑ view : View,
      channel view secret message *
        if decoderSign predictor view =
            walsh frequency secret * walsh frequency message
        then 1 else 0) / cubeSize Index ^ 2

/-- The product of the predicted sign and true Walsh parity is `+1` on success and `-1` on
failure. -/
theorem decoderSign_mul_walsh_eq_indicator
    {Index View : Type} [Fintype Index] [DecidableEq Index]
    (frequency : BitVector Index) (secret message : BitVector Index)
    (predictor : View → Bool) (view : View) :
    decoderSign predictor view *
        (walsh frequency secret * walsh frequency message) =
      2 * (if decoderSign predictor view =
          walsh frequency secret * walsh frequency message
        then (1 : ℝ) else 0) - 1 := by
  have hsecret := (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp
    (abs_walsh frequency secret)
  have hmessage := (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp
    (abs_walsh frequency message)
  rcases hsecret with hsecret | hsecret <;>
    rcases hmessage with hmessage | hmessage <;>
    cases hprediction : predictor view <;>
    norm_num [decoderSign, bitSign, hprediction, hsecret, hmessage]

/-- For a normalized complete channel, decoder correlation is exactly `2 success - 1`. -/
theorem fourierCoefficient_decoderSign_eq_two_success_sub_one
    {Index View : Type} [Fintype Index] [DecidableEq Index] [Fintype View]
    (channel : CompleteChannel Index View)
    (hnormalized : ∀ secret message, ∑ view, channel view secret message = 1)
    (frequency : BitVector Index) (predictor : View → Bool) :
    fourierCoefficient (completeChannelResponse channel (decoderSign predictor))
        frequency frequency =
      2 * completeChannelDecoderSuccess channel frequency predictor - 1 := by
  classical
  let successIndicator := fun (secret message : BitVector Index) (view : View) ↦
    if decoderSign predictor view = walsh frequency secret * walsh frequency message
    then (1 : ℝ) else 0
  have htotal :
      (∑ secret : BitVector Index, ∑ message : BitVector Index, ∑ view : View,
        channel view secret message) = cubeSize Index ^ 2 := by
    simp_rw [hnormalized]
    simp [cubeSize, pow_two]
  have hexpand :
      (∑ secret : BitVector Index, ∑ message : BitVector Index,
          (∑ view : View, channel view secret message * decoderSign predictor view) *
            walsh frequency secret * walsh frequency message) =
        ∑ secret : BitVector Index, ∑ message : BitVector Index, ∑ view : View,
          channel view secret message *
            (decoderSign predictor view *
              (walsh frequency secret * walsh frequency message)) := by
    apply Finset.sum_congr rfl
    intro secret _
    apply Finset.sum_congr rfl
    intro message _
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro view _
    ring
  have hpointwise :
      (∑ secret : BitVector Index, ∑ message : BitVector Index, ∑ view : View,
          channel view secret message *
            (decoderSign predictor view *
              (walsh frequency secret * walsh frequency message))) =
        ∑ secret : BitVector Index, ∑ message : BitVector Index, ∑ view : View,
          channel view secret message * (2 * successIndicator secret message view - 1) := by
    apply Finset.sum_congr rfl
    intro secret _
    apply Finset.sum_congr rfl
    intro message _
    apply Finset.sum_congr rfl
    intro view _
    rw [decoderSign_mul_walsh_eq_indicator]
  have hsplit :
      (∑ secret : BitVector Index, ∑ message : BitVector Index, ∑ view : View,
          channel view secret message * (2 * successIndicator secret message view - 1)) =
        2 * (∑ secret : BitVector Index, ∑ message : BitVector Index, ∑ view : View,
          channel view secret message * successIndicator secret message view) -
        (∑ secret : BitVector Index, ∑ message : BitVector Index, ∑ view : View,
          channel view secret message) := by
    have hterm (secret message : BitVector Index) (view : View) :
        channel view secret message * (2 * successIndicator secret message view - 1) =
          2 * (channel view secret message * successIndicator secret message view) -
            channel view secret message := by ring
    simp_rw [hterm, Finset.sum_sub_distrib]
    simp_rw [← Finset.mul_sum]
  unfold fourierCoefficient completeChannelResponse completeChannelDecoderSuccess
  rw [hexpand, hpointwise, hsplit, htotal]
  dsimp only [successIndicator]
  field_simp [cubeSize_ne_zero Index]

/-- Any deterministic diagonal-parity decoder is bounded by the exact posterior spectral radius
of the complete channel. -/
theorem decoderCorrelation_le_posteriorSpectralRadius
    {Index View : Type} [Fintype Index] [DecidableEq Index] [Fintype View]
    (channel : CompleteChannel Index View)
    (hchannel : ∀ view secret message, 0 ≤ channel view secret message)
    (hnormalized : ∀ secret message, ∑ view, channel view secret message = 1)
    (frequency : BitVector Index) (predictor : View → Bool) :
    |fourierCoefficient (completeChannelResponse channel (decoderSign predictor))
        frequency frequency| ≤
      posteriorSpectralRadius (completeChannelViewMass channel)
        (completeChannelPosteriorParity channel frequency) := by
  apply completeChannel_fourier_le_posteriorSpectralRadius
    channel hchannel hnormalized (decoderSign predictor)
  intro view
  rw [abs_decoderSign]

/-- If a decoder succeeds with probability at least `1 - ε`, then the posterior spectral radius
is at least `1 - 2ε`.  This is the promised information-theoretic viability test. -/
theorem one_sub_two_mul_le_posteriorSpectralRadius_of_decoder
    {Index View : Type} [Fintype Index] [DecidableEq Index] [Fintype View]
    (channel : CompleteChannel Index View)
    (hchannel : ∀ view secret message, 0 ≤ channel view secret message)
    (hnormalized : ∀ secret message, ∑ view, channel view secret message = 1)
    (frequency : BitVector Index) (predictor : View → Bool) (ε : ℝ)
    (hsuccess : 1 - ε ≤ completeChannelDecoderSuccess channel frequency predictor) :
    1 - 2 * ε ≤
      posteriorSpectralRadius (completeChannelViewMass channel)
        (completeChannelPosteriorParity channel frequency) := by
  let correlation := fourierCoefficient
    (completeChannelResponse channel (decoderSign predictor)) frequency frequency
  have hcorrelation : correlation =
      2 * completeChannelDecoderSuccess channel frequency predictor - 1 :=
    fourierCoefficient_decoderSign_eq_two_success_sub_one
      channel hnormalized frequency predictor
  have hlower : 1 - 2 * ε ≤ correlation := by
    rw [hcorrelation]
    linarith
  calc
    1 - 2 * ε ≤ correlation := hlower
    _ ≤ |correlation| := le_abs_self correlation
    _ ≤ _ := decoderCorrelation_le_posteriorSpectralRadius
      channel hchannel hnormalized frequency predictor

/-- Exact parity recovery forces the corresponding posterior radius to be at least one. -/
theorem one_le_posteriorSpectralRadius_of_exactDecoder
    {Index View : Type} [Fintype Index] [DecidableEq Index] [Fintype View]
    (channel : CompleteChannel Index View)
    (hchannel : ∀ view secret message, 0 ≤ channel view secret message)
    (hnormalized : ∀ secret message, ∑ view, channel view secret message = 1)
    (frequency : BitVector Index) (predictor : View → Bool)
    (hsuccess : completeChannelDecoderSuccess channel frequency predictor = 1) :
    1 ≤ posteriorSpectralRadius (completeChannelViewMass channel)
      (completeChannelPosteriorParity channel frequency) := by
  simpa using
    (one_sub_two_mul_le_posteriorSpectralRadius_of_decoder
      channel hchannel hnormalized frequency predictor 0 (by rw [hsuccess]; norm_num))

/-! ## The concrete shared-prefix/suffix native channel -/

/-- The native cloud-key structure is equivalent to the product of its two finite fields. -/
def cloudKeyEquiv
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) :
    (SharedBootstrappingKey q prefixDimension suffixDimension tgswLevels ×
      SharedKeySwitchKey q prefixDimension suffixDimension keySwitchLevels) ≃
      CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels where
  toFun value := ⟨value.1, value.2⟩
  invFun value := (value.bootstrappingKey, value.keySwitchKey)
  left_inv value := by cases value; rfl
  right_inv value := by cases value; rfl

noncomputable instance instFintypeCloudKey
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q] :
    Fintype (CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels) :=
  Fintype.ofEquiv
    (SharedBootstrappingKey q prefixDimension suffixDimension tgswLevels ×
      SharedKeySwitchKey q prefixDimension suffixDimension keySwitchLevels)
    (cloudKeyEquiv q prefixDimension suffixDimension tgswLevels keySwitchLevels)

/-- Generate a native BRK for an arbitrary known binary message vector under one fixed nested
ring key.  The native real BRK is the specialization `message = prefixSecret ringSecret`. -/
noncomputable def generateKnownMessageBootstrappingKey
    (q prefixDimension suffixDimension tgswLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (message : BinarySecret prefixDimension)
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    ProbComp (SharedBootstrappingKey
      q prefixDimension suffixDimension tgswLevels) :=
  Native.generateBootstrappingKey q (prefixDimension + suffixDimension) 1 tgswLevels
    prefixDimension ringErrorSampler tgswGadget message ringSecret

/-- Coordinatewise public affine normalization of a fixed known-message native BRK. -/
def affineNormalizeKnownMessageBootstrappingKey
    (q prefixDimension suffixDimension tgswLevels : ℕ) [NeZero q]
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (message : BinarySecret prefixDimension)
    (bootstrappingKey :
      SharedBootstrappingKey q prefixDimension suffixDimension tgswLevels) :
    SharedBootstrappingKey q prefixDimension suffixDimension tgswLevels :=
  fun coordinate ↦ normalizeKnownMessageDirectCiphertext tgswGadget
    (embedConstantBit q (prefixDimension + suffixDimension) (message coordinate))
    (bootstrappingKey coordinate)

/-- Independently generated ordinary affine batch-RLWE rows corresponding to a fixed
known-message native BRK. Every row message is the public gadget-body shift. -/
noncomputable def generateKnownMessageAffineBootstrappingKey
    (q prefixDimension suffixDimension tgswLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (message : BinarySecret prefixDimension)
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    ProbComp (SharedBootstrappingKey
      q prefixDimension suffixDimension tgswLevels) :=
  Fin.mOfFn prefixDimension fun coordinate ↦
    TLWE.batchEncrypt 1 (TGSW.rowCount 1 tgswLevels) ringErrorSampler
      (embedRingSecret q ringSecret)
      (@TGSW.gadgetBodyShift (RLWE.Rq q (prefixDimension + suffixDimension))
        MulZeroClass.toZero Distrib.toMul 1 tgswLevels tgswGadget
        (embedConstantBit q (prefixDimension + suffixDimension) (message coordinate)))

/-- The complete independently generated native BRK, after its public known-message
normalization, has exactly the ordinary affine batch-RLWE product law. -/
theorem affineNormalize_generateKnownMessageBootstrappingKey_evalDist
    (q prefixDimension suffixDimension tgswLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (message : BinarySecret prefixDimension)
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    evalDist (affineNormalizeKnownMessageBootstrappingKey q prefixDimension suffixDimension
        tgswLevels tgswGadget message <$>
      generateKnownMessageBootstrappingKey q prefixDimension suffixDimension tgswLevels
        ringErrorSampler tgswGadget message ringSecret) =
      evalDist (generateKnownMessageAffineBootstrappingKey q prefixDimension suffixDimension
        tgswLevels ringErrorSampler tgswGadget message ringSecret) := by
  unfold affineNormalizeKnownMessageBootstrappingKey
    generateKnownMessageBootstrappingKey Native.generateBootstrappingKey
    generateKnownMessageAffineBootstrappingKey
  apply Native.ScalarSecretRandomization.mOfFn_map_evalDist_congr
  intro coordinate
  exact normalizeKnownMessageDirectCiphertext_encrypt_evalDist
    1 tgswLevels ringErrorSampler (embedRingSecret q ringSecret) tgswGadget
      (embedConstantBit q (prefixDimension + suffixDimension) (message coordinate))

/-- Complete known-message view: the arbitrary-message BRK and the real suffix KSK are sampled
under the same nested ring key. -/
noncomputable def generateKnownMessageCloudKey
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (message : BinarySecret prefixDimension)
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    ProbComp (CloudKey
      q prefixDimension suffixDimension tgswLevels keySwitchLevels) := do
  let bootstrappingKey ← generateKnownMessageBootstrappingKey q prefixDimension
    suffixDimension tgswLevels ringErrorSampler tgswGadget message ringSecret
  let keySwitchKey ← generateKeySwitchKey q prefixDimension suffixDimension
    keySwitchLevels keySwitchErrorSampler keySwitchGadget ringSecret
  return ⟨bootstrappingKey, keySwitchKey⟩

/-- Public known-message affine normalization of only the BRK field of a complete cloud key. The
real correlated suffix KSK is retained literally. -/
def affineNormalizeKnownMessageCloudKey
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (message : BinarySecret prefixDimension)
    (view : CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels :=
  ⟨affineNormalizeKnownMessageBootstrappingKey q prefixDimension suffixDimension
      tgswLevels tgswGadget message view.bootstrappingKey,
    view.keySwitchKey⟩

/-- Complete conditioned affine-source cloud-key sampler: public-message affine RLWE rows and the
real suffix KSK share the same fixed prefix/suffix ring key. -/
noncomputable def generateKnownMessageAffineCloudKey
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (message : BinarySecret prefixDimension)
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    ProbComp (CloudKey
      q prefixDimension suffixDimension tgswLevels keySwitchLevels) := do
  let bootstrappingKey ← generateKnownMessageAffineBootstrappingKey q prefixDimension
    suffixDimension tgswLevels ringErrorSampler tgswGadget message ringSecret
  let keySwitchKey ← generateKeySwitchKey q prefixDimension suffixDimension
    keySwitchLevels keySwitchErrorSampler keySwitchGadget ringSecret
  return ⟨bootstrappingKey, keySwitchKey⟩

/-- Exact complete-view conditioned affine-source law. Normalizing the BRK preserves the retained
KSK and all shared-key correlation, while replacing the native TGSW entries by ordinary affine
batch-RLWE rows. -/
theorem affineNormalize_generateKnownMessageCloudKey_evalDist
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (message : BinarySecret prefixDimension)
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    evalDist (affineNormalizeKnownMessageCloudKey q prefixDimension suffixDimension
        tgswLevels keySwitchLevels tgswGadget message <$>
      generateKnownMessageCloudKey q prefixDimension suffixDimension tgswLevels
        keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        message ringSecret) =
      evalDist (generateKnownMessageAffineCloudKey q prefixDimension suffixDimension tgswLevels
        keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        message ringSecret) := by
  let leftBRK := generateKnownMessageBootstrappingKey q prefixDimension suffixDimension
    tgswLevels ringErrorSampler tgswGadget message ringSecret
  let rightBRK := generateKnownMessageAffineBootstrappingKey q prefixDimension suffixDimension
    tgswLevels ringErrorSampler tgswGadget message ringSecret
  let retainedKSK := generateKeySwitchKey q prefixDimension suffixDimension keySwitchLevels
    keySwitchErrorSampler keySwitchGadget ringSecret
  let finish : SharedBootstrappingKey q prefixDimension suffixDimension tgswLevels →
      ProbComp (CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels) :=
    fun bootstrappingKey ↦ retainedKSK >>= fun keySwitchKey ↦
      pure (CloudKey.mk bootstrappingKey keySwitchKey)
  have hBRK :
      evalDist (affineNormalizeKnownMessageBootstrappingKey q prefixDimension suffixDimension
          tgswLevels tgswGadget message <$> leftBRK) =
        evalDist rightBRK :=
    affineNormalize_generateKnownMessageBootstrappingKey_evalDist q prefixDimension
      suffixDimension tgswLevels ringErrorSampler tgswGadget message ringSecret
  calc
    _ = evalDist ((affineNormalizeKnownMessageBootstrappingKey q prefixDimension
          suffixDimension tgswLevels tgswGadget message <$> leftBRK) >>= finish) := by
      simp [generateKnownMessageCloudKey, affineNormalizeKnownMessageCloudKey,
        leftBRK, retainedKSK, finish, map_eq_bind_pure_comp, bind_assoc, monad_norm]
    _ = evalDist (rightBRK >>= finish) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hBRK finish
    _ = _ := by
      simp [generateKnownMessageAffineCloudKey, rightBRK, retainedKSK, finish, monad_norm]

/-- The ordinary real fixed-key cloud sampler is exactly the diagonal known-message sampler. -/
theorem generateKnownMessageCloudKey_prefix_eq_real
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    generateKnownMessageCloudKey q prefixDimension suffixDimension tgswLevels
        keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        (prefixSecret ringSecret) ringSecret =
      generateCloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget ringSecret := by
  rfl

/-- Positive-degree native constant-bit embedding agrees with the ring's ordinary bit scalar. -/
theorem embedConstantBit_eq_embedBit_of_pos
    {q degree : ℕ} [NeZero q] (hdegree : 0 < degree) (bit : Bool) :
    embedConstantBit q degree bit = (embedBit bit : RLWE.Rq q degree) := by
  obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdegree)
  exact BlindRotation.embedConstantBit_eq_embedBit bit

/-- At positive degree the zero/one operations selected through the commutative-ring dictionary
agree with the executable negacyclic-ring dictionary. -/
theorem commRingEmbedBit_eq_embedBit_of_pos
    {q degree : ℕ} [NeZero q] (hdegree : 0 < degree) (bit : Bool) :
    (@embedBit (RLWE.Rq q degree) MulZeroClass.toZero AddMonoidWithOne.toOne bit) =
      (embedBit bit : RLWE.Rq q degree) := by
  obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdegree)
  cases bit <;> rfl

/-- Public xor transport of every complete native BRK entry. -/
def transformKnownMessageBootstrappingKey
    {q prefixDimension suffixDimension tgswLevels : ℕ}
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (mask : BinarySecret prefixDimension)
    (bootstrappingKey :
      SharedBootstrappingKey q prefixDimension suffixDimension tgswLevels) :
    SharedBootstrappingKey q prefixDimension suffixDimension tgswLevels :=
  Native.ScalarSecretRandomization.transformBootstrappingKey
    tgswGadget mask bootstrappingKey

/-- The complete arbitrary-message BRK obeys the exact public xor-normalization law. -/
theorem transform_generateKnownMessageBootstrappingKey_evalDist
    (q prefixDimension suffixDimension tgswLevels : ℕ) [NeZero q]
    (hdegree : 0 < prefixDimension + suffixDimension)
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (hsymmetric : @Native.ScalarSecretRandomization.NegationSymmetric
      (RLWE.Rq q (prefixDimension + suffixDimension))
      (commRingNeg (RLWE.Rq q (prefixDimension + suffixDimension))) ringErrorSampler)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (message mask : BinarySecret prefixDimension)
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    evalDist (transformKnownMessageBootstrappingKey tgswGadget mask <$>
        generateKnownMessageBootstrappingKey q prefixDimension suffixDimension
          tgswLevels ringErrorSampler tgswGadget message ringSecret) =
      evalDist (generateKnownMessageBootstrappingKey q prefixDimension suffixDimension
        tgswLevels ringErrorSampler tgswGadget
        (Native.ScalarSecretRandomization.maskedSecret message mask) ringSecret) := by
  unfold generateKnownMessageBootstrappingKey Native.generateBootstrappingKey
    transformKnownMessageBootstrappingKey
  rw [show Native.ScalarSecretRandomization.transformBootstrappingKey tgswGadget mask =
      (fun bootstrappingKey coordinate ↦
        Native.ScalarSecretRandomization.toggleTGSW tgswGadget (mask coordinate)
          (bootstrappingKey coordinate)) by rfl]
  simpa only [Native.ScalarSecretRandomization.maskedSecret,
    embedConstantBit_eq_embedBit_of_pos hdegree,
    commRingEmbedBit_eq_embedBit_of_pos hdegree] using
    (NativeTRGSWBarrierAndSpectralBoundary.nativeBRKNormalization
      ringErrorSampler hsymmetric (embedRingSecret q ringSecret) tgswGadget message mask)

/-- Xor-normalize only the BRK component of a complete cloud-key view; the correlated suffix KSK
is retained literally. -/
def transformKnownMessageCloudKey
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ}
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (mask : BinarySecret prefixDimension)
    (view : CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels :=
  ⟨transformKnownMessageBootstrappingKey tgswGadget mask view.bootstrappingKey,
    view.keySwitchKey⟩

/-- Complete fixed-key normalization keeps the real suffix KSK and all BRK/KSK correlation in
the same view. -/
theorem transform_generateKnownMessageCloudKey_evalDist
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (hdegree : 0 < prefixDimension + suffixDimension)
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (hsymmetric : @Native.ScalarSecretRandomization.NegationSymmetric
      (RLWE.Rq q (prefixDimension + suffixDimension))
      (commRingNeg (RLWE.Rq q (prefixDimension + suffixDimension))) ringErrorSampler)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (message mask : BinarySecret prefixDimension)
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    evalDist (transformKnownMessageCloudKey tgswGadget mask <$>
        generateKnownMessageCloudKey q prefixDimension suffixDimension tgswLevels
          keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
          message ringSecret) =
      evalDist (generateKnownMessageCloudKey q prefixDimension suffixDimension tgswLevels
        keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        (Native.ScalarSecretRandomization.maskedSecret message mask) ringSecret) := by
  let leftBRK := generateKnownMessageBootstrappingKey q prefixDimension suffixDimension
    tgswLevels ringErrorSampler tgswGadget message ringSecret
  let rightBRK := generateKnownMessageBootstrappingKey q prefixDimension suffixDimension
    tgswLevels ringErrorSampler tgswGadget
      (Native.ScalarSecretRandomization.maskedSecret message mask) ringSecret
  let retainedKSK := generateKeySwitchKey q prefixDimension suffixDimension keySwitchLevels
    keySwitchErrorSampler keySwitchGadget ringSecret
  let finish : SharedBootstrappingKey q prefixDimension suffixDimension tgswLevels →
      ProbComp (CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels) :=
    fun bootstrappingKey ↦ retainedKSK >>= fun keySwitchKey ↦
      pure (CloudKey.mk bootstrappingKey keySwitchKey)
  have hBRK :
      evalDist (transformKnownMessageBootstrappingKey tgswGadget mask <$> leftBRK) =
        evalDist rightBRK :=
    transform_generateKnownMessageBootstrappingKey_evalDist q prefixDimension
      suffixDimension tgswLevels hdegree ringErrorSampler hsymmetric tgswGadget
      message mask ringSecret
  calc
    _ = evalDist ((transformKnownMessageBootstrappingKey tgswGadget mask <$> leftBRK) >>=
        finish) := by
      simp [generateKnownMessageCloudKey, transformKnownMessageCloudKey,
        leftBRK, retainedKSK, finish, map_eq_bind_pure_comp, bind_assoc, monad_norm]
    _ = evalDist (rightBRK >>= finish) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hBRK finish
    _ = _ := by
      simp [generateKnownMessageCloudKey, rightBRK, retainedKSK, finish,
        monad_norm]

/-- Conditional complete native view for fixed prefix and BRK message.  Only the independent
suffix and encryption randomness are hidden in this kernel. -/
noncomputable def fixedPrefixMessageView
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (prefixKey message : BinarySecret prefixDimension) :
    ProbComp (CloudKey
      q prefixDimension suffixDimension tgswLevels keySwitchLevels) := do
  let suffix ← Native.sampleLweSecret suffixDimension
  generateKnownMessageCloudKey q prefixDimension suffixDimension tgswLevels
    keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
    message (nestedRingSecret prefixKey suffix)

/-- Conditional ordinary affine BRK plus real KSK view, including the independently sampled
suffix. -/
noncomputable def fixedPrefixMessageAffineView
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (prefixKey message : BinarySecret prefixDimension) :
    ProbComp (CloudKey
      q prefixDimension suffixDimension tgswLevels keySwitchLevels) := do
  let suffix ← Native.sampleLweSecret suffixDimension
  generateKnownMessageAffineCloudKey q prefixDimension suffixDimension tgswLevels
    keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
    message (nestedRingSecret prefixKey suffix)

/-- Exact conditional-channel affine-source law after suffix sampling. This is a whole-view law,
not a statement about separate BRK and KSK marginals. -/
theorem affineNormalize_fixedPrefixMessageView_evalDist
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (prefixKey message : BinarySecret prefixDimension) :
    evalDist (affineNormalizeKnownMessageCloudKey q prefixDimension suffixDimension
        tgswLevels keySwitchLevels tgswGadget message <$>
      fixedPrefixMessageView q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget prefixKey message) =
      evalDist (fixedPrefixMessageAffineView q prefixDimension suffixDimension tgswLevels
        keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        prefixKey message) := by
  simp only [fixedPrefixMessageView, fixedPrefixMessageAffineView,
    map_eq_bind_pure_comp, bind_assoc]
  refine evalDist_bind_congr' (Native.sampleLweSecret suffixDimension) fun suffixKey ↦ ?_
  simpa only [map_eq_bind_pure_comp] using
    (affineNormalize_generateKnownMessageCloudKey_evalDist q prefixDimension suffixDimension
      tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget
      keySwitchGadget message (nestedRingSecret prefixKey suffixKey))

/-- Concrete point-mass channel of the complete native BRK plus retained real suffix KSK. -/
noncomputable def nativeCompleteChannel
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    CompleteChannel (Fin prefixDimension)
      (CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels) :=
  channelOfSampler (fixedPrefixMessageView q prefixDimension suffixDimension
    tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget)

theorem nativeCompleteChannel_nonneg
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (view : CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels)
    (prefixKey message : BinarySecret prefixDimension) :
    0 ≤ nativeCompleteChannel q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
      view prefixKey message := by
  unfold nativeCompleteChannel
  exact channelOfSampler_nonneg _ _ _ _

/-- Every conditional native channel row is total. -/
theorem fixedPrefixMessageView_probFailure_eq_zero
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (prefixKey message : BinarySecret prefixDimension) :
    probFailure
        (fixedPrefixMessageView q prefixDimension suffixDimension tgswLevels keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
          prefixKey message) = 0 := by
  simp [fixedPrefixMessageView, generateKnownMessageCloudKey,
    generateKnownMessageBootstrappingKey, Native.generateBootstrappingKey,
    generateKeySwitchKey, Native.generateKeySwitchKey, TLWE.batchEncrypt,
    Native.sampleLweSecret]

/-- The concrete channel is normalized. -/
theorem nativeCompleteChannel_normalized
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (prefixKey message : BinarySecret prefixDimension) :
    ∑ view, nativeCompleteChannel q prefixDimension suffixDimension tgswLevels
      keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
      view prefixKey message = 1 := by
  apply channelOfSampler_normalized
  intro secret knownMessage
  exact fixedPrefixMessageView_probFailure_eq_zero q prefixDimension suffixDimension
    tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget secret knownMessage

/-- Exact xor normalization of the conditional complete channel sampler.  The suffix is sampled
inside the kernel, and its real KSK remains correlated with the same prefix/suffix key. -/
theorem transform_fixedPrefixMessageView_evalDist
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (hdegree : 0 < prefixDimension + suffixDimension)
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (hsymmetric : @Native.ScalarSecretRandomization.NegationSymmetric
      (RLWE.Rq q (prefixDimension + suffixDimension))
      (commRingNeg (RLWE.Rq q (prefixDimension + suffixDimension))) ringErrorSampler)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (prefixKey message mask : BinarySecret prefixDimension) :
    evalDist (transformKnownMessageCloudKey tgswGadget mask <$>
        fixedPrefixMessageView q prefixDimension suffixDimension tgswLevels keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
          prefixKey message) =
      evalDist (fixedPrefixMessageView q prefixDimension suffixDimension tgswLevels
        keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        prefixKey (Native.ScalarSecretRandomization.maskedSecret message mask)) := by
  simp only [fixedPrefixMessageView, map_eq_bind_pure_comp, bind_assoc]
  refine evalDist_bind_congr' (Native.sampleLweSecret suffixDimension) fun suffixKey ↦ ?_
  simpa only [map_eq_bind_pure_comp] using
    (transform_generateKnownMessageCloudKey_evalDist q prefixDimension suffixDimension
      tgswLevels keySwitchLevels hdegree ringErrorSampler keySwitchErrorSampler hsymmetric
      tgswGadget keySwitchGadget message mask
      (nestedRingSecret prefixKey suffixKey))

/-- Diagonal and independent-message samplers associated with the concrete native channel. -/
noncomputable def diagonalNativeView
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    ProbComp (CloudKey
      q prefixDimension suffixDimension tgswLevels keySwitchLevels) := do
  let prefixKey ← Native.sampleLweSecret prefixDimension
  fixedPrefixMessageView q prefixDimension suffixDimension tgswLevels keySwitchLevels
    ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget prefixKey prefixKey

noncomputable def independentMessageNativeView
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    ProbComp (CloudKey
      q prefixDimension suffixDimension tgswLevels keySwitchLevels) := do
  let prefixKey ← Native.sampleLweSecret prefixDimension
  let message ← Native.sampleLweSecret prefixDimension
  fixedPrefixMessageView q prefixDimension suffixDimension tgswLevels keySwitchLevels
    ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget prefixKey message

/-- Averaging the diagonal channel over its uniform prefix gives exactly the existing native
shared-randomness real cloud-key distribution. -/
theorem diagonalNativeView_evalDist_eq_realCloudKeyView
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    evalDist (diagonalNativeView q prefixDimension suffixDimension tgswLevels
        keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget) =
      evalDist (Native.SharedRandomnessOneCycle.realCloudKeyView q prefixDimension
        suffixDimension tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget) := by
  let splitSampler : ProbComp
      (BinarySecret prefixDimension × BinarySecret suffixDimension) := do
    let ringSecret ← Native.sampleRingSecret 1 (prefixDimension + suffixDimension)
    return splitNestedSecret ringSecret
  let independentSampler : ProbComp
      (BinarySecret prefixDimension × BinarySecret suffixDimension) := do
    let prefixKey ← Native.sampleLweSecret prefixDimension
    let suffixKey ← Native.sampleLweSecret suffixDimension
    return (prefixKey, suffixKey)
  let finish := fun keys :
      BinarySecret prefixDimension × BinarySecret suffixDimension ↦
    generateKnownMessageCloudKey q prefixDimension suffixDimension tgswLevels
      keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
      keys.1 (nestedRingSecret keys.1 keys.2)
  have hsampler : evalDist splitSampler = evalDist independentSampler :=
    sampleRingSecret_prefix_suffix_evalDist prefixDimension suffixDimension
  have hbind := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    hsampler finish
  simpa [diagonalNativeView, fixedPrefixMessageView,
    Native.SharedRandomnessOneCycle.realCloudKeyView,
    generateKnownMessageCloudKey_prefix_eq_real, splitSampler, independentSampler,
    finish, splitNestedSecret, bind_assoc, monad_norm] using hbind.symm

/-- The generic diagonal mean is exactly acceptance in the concrete diagonal native sampler. -/
theorem diagonalNativeAcceptance_eq_diagonalMean
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels →
      ProbComp Bool) :
    Pr[= true | diagonalNativeView q prefixDimension suffixDimension tgswLevels
        keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget >>=
          adversary].toReal =
      diagonalMean (completeChannelResponse
        (nativeCompleteChannel q prefixDimension suffixDimension tgswLevels keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        (adversaryResponse adversary)) := by
  calc
    _ = FormalProof4FHE.BoundedMoment.expectation
        (diagonalNativeView q prefixDimension suffixDimension tgswLevels keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        (adversaryResponse adversary) :=
      (expectation_adversaryResponse_eq_probOutput _ adversary).symm
    _ = _ := by
      simpa [diagonalNativeView, nativeCompleteChannel, Native.sampleLweSecret] using
        (diagonalMean_channelOfSampler_eq_expectation
          (fixedPrefixMessageView q prefixDimension suffixDimension tgswLevels
            keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
          (adversaryResponse adversary)).symm

/-- The independent mean is exactly acceptance in the native random-message sampler. -/
theorem independentMessageNativeAcceptance_eq_independentMean
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels →
      ProbComp Bool) :
    Pr[= true | independentMessageNativeView q prefixDimension suffixDimension tgswLevels
        keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget >>=
          adversary].toReal =
      independentMean (completeChannelResponse
        (nativeCompleteChannel q prefixDimension suffixDimension tgswLevels keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        (adversaryResponse adversary)) := by
  calc
    _ = FormalProof4FHE.BoundedMoment.expectation
        (independentMessageNativeView q prefixDimension suffixDimension tgswLevels keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        (adversaryResponse adversary) :=
      (expectation_adversaryResponse_eq_probOutput _ adversary).symm
    _ = _ := by
      simpa [independentMessageNativeView, nativeCompleteChannel,
        Native.sampleLweSecret] using
        (independentMean_channelOfSampler_eq_expectation
          (fixedPrefixMessageView q prefixDimension suffixDimension tgswLevels
            keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
          (adversaryResponse adversary)).symm

/-- Existing native real-cloud acceptance is the same diagonal mean, not merely a related
experiment. -/
theorem realCloudKeyAcceptance_eq_diagonalMean
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels →
      ProbComp Bool) :
    Pr[= true | Native.SharedRandomnessOneCycle.realCloudKeyView q prefixDimension
        suffixDimension tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget >>= adversary].toReal =
      diagonalMean (completeChannelResponse
        (nativeCompleteChannel q prefixDimension suffixDimension tgswLevels keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        (adversaryResponse adversary)) := by
  have hbind := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (diagonalNativeView_evalDist_eq_realCloudKeyView q prefixDimension suffixDimension
      tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget) adversary
  rw [← diagonalNativeAcceptance_eq_diagonalMean q prefixDimension suffixDimension
    tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget adversary]
  exact congrArg ENNReal.toReal (evalDist_ext_iff.mp hbind true).symm

/-! ## Concrete conditional native security theorem -/

/-- Conditional security statement for the actual native shared-prefix/suffix cloud-key sampler.

The real term is literally adversarial acceptance on `realCloudKeyView`; the comparison term is
acceptance after independently resampling the BRK message while retaining the real suffix KSK.
The low-frequency premise is supplied as an affine-source certificate, whose support leakage loss
is discharged internally.  What remains explicit is the summed high-frequency posterior decay
and the independently specified random-message/zero-message endpoint. -/
theorem realCloudKey_conditionalNativeCircularSecurity
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels →
      ProbComp Bool)
    (degree : ℕ) (delta spectralBound randomZeroBound randomZeroAdvantage : ℝ)
    (certificate : LowDegreeAffineSourceCertificate
      (nativeCompleteChannel q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
      (adversaryResponse adversary) degree delta)
    (hdecay : NativeDiagonalSpectralDecay
      (fun frequency ↦ posteriorSpectralRadius
        (completeChannelViewMass
          (nativeCompleteChannel q prefixDimension suffixDimension tgswLevels keySwitchLevels
            ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget))
        (completeChannelPosteriorParity
          (nativeCompleteChannel q prefixDimension suffixDimension tgswLevels keySwitchLevels
            ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
          frequency))
      degree spectralBound)
    (hendpoint : randomZeroAdvantage ≤ randomZeroBound) :
    |Pr[= true | Native.SharedRandomnessOneCycle.realCloudKeyView q prefixDimension
        suffixDimension tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget >>= adversary].toReal -
      Pr[= true | independentMessageNativeView q prefixDimension suffixDimension tgswLevels
        keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget >>=
          adversary].toReal| + randomZeroAdvantage ≤
      binomialLowFrequencyCount (Fin prefixDimension) degree *
        Real.sqrt ((2 : ℝ) ^ (degree + 1) * delta) +
          spectralBound + randomZeroBound := by
  rw [realCloudKeyAcceptance_eq_diagonalMean q prefixDimension suffixDimension
    tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget adversary]
  rw [independentMessageNativeAcceptance_eq_independentMean q prefixDimension suffixDimension
    tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget adversary]
  exact completeChannel_conditionalNativeCircularSecurity
    (nativeCompleteChannel q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    (nativeCompleteChannel_nonneg q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    (nativeCompleteChannel_normalized q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    (adversaryResponse adversary) (adversaryResponse_abs_le_one adversary)
    degree delta spectralBound randomZeroBound randomZeroAdvantage
    certificate.lowFrequencyBound hdecay hendpoint

end

end FormalProof4FHE.TFHE.NativeTRGSWCompleteChannel
