/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.BinaryNTTRegularQH
import FormalProof4FHE.Probability.SquaredBias

/-!
# Binary-NTT automorphism KDM for one transposition

This module formalizes the valid finite core of `sketch/automorphism_kdm_transposition_proof.tex`.
It checks:

* the split-NTT transposition decomposition;
* the impossibility of absorbing a moved coordinate by an ordinary diagonal/ring mask;
* the one-bit insertion identity;
* the two-parity decomposition showing that a second bit remains hidden after one insertion;
* a quantitative two-insertion theorem with explicit base-view and parity-correlation bounds.

The manuscript's parity-hiding lemma uses the exact Binary-NTT XOR rerandomization and a two-copy
squared-bias decision reduction.  The displayed proof contains one duplicated factor in an
expectation; the theorem below formalizes the intended unsquared correlation identity.

Efficiency is represented by an abstract predicate `allowed` on real response functions.  The
theorem requires closure only for the concrete mean and Fourier responses constructed by the
reduction.  It therefore does not turn a computational assumption into a statistical one.
-/

open OracleComp

namespace FormalProof4FHE.RLWE.BinaryNTTSecurity.AutomorphismTransposition

noncomputable section

/-! ## Split-coordinate transposition algebra -/

/-- Embed one Boolean NTT coordinate into the field. -/
def bitValue {K : Type} [Zero K] [One K] (bit : Bool) : K :=
  if bit then 1 else 0

theorem bitValue_xor {K : Type} [CommRing K] (left right : Bool) :
    bitValue (K := K) (xor left right) =
      BinaryNTTSecurity.idempotentXor (bitValue (K := K) left) (bitValue (K := K) right) := by
  cases left <;> cases right <;> norm_num [bitValue, BinaryNTTSecurity.idempotentXor]

/-- Swap two selected coordinates and fix every other coordinate. -/
def transposeCoordinates {Slot Value : Type} [DecidableEq Slot]
    (left right : Slot) (values : Slot → Value) : Slot → Value :=
  fun slot ↦ if slot = left then values right else if slot = right then values left else values slot

/-- Weighted NTT contribution of the transposed secret. -/
def weightedTransposition {Slot K : Type} [CommRing K] [DecidableEq Slot]
    (left right : Slot) (gadget secret : Slot → K) : Slot → K :=
  gadget * transposeCoordinates left right secret

/-- The fixed-coordinate multiplier obtained by deleting the moved coordinates. -/
def fixedMultiplier {Slot K : Type} [Zero K] [DecidableEq Slot]
    (left right : Slot) (gadget : Slot → K) : Slot → K :=
  fun slot ↦ if slot = left ∨ slot = right then 0 else gadget slot

/-- Public rank-one contribution supported at one NTT coordinate. -/
def coordinateContribution {Slot K : Type} [Zero K] [DecidableEq Slot]
    (target : Slot) (coefficient : K) : Slot → K :=
  fun slot ↦ if slot = target then coefficient else 0

/-- The transposition message is a public self-linear part plus two one-bit insertions. -/
theorem weightedTransposition_decomposition
    {Slot K : Type} [CommRing K] [DecidableEq Slot]
    (left right : Slot) (hne : left ≠ right) (gadget : Slot → K)
    (bits : Slot → Bool) :
    weightedTransposition left right gadget (fun slot ↦ bitValue (K := K) (bits slot)) =
      fixedMultiplier left right gadget * (fun slot ↦ bitValue (K := K) (bits slot)) +
        coordinateContribution left (gadget left) *
          (fun _ ↦ bitValue (K := K) (bits right)) +
        coordinateContribution right (gadget right) *
          (fun _ ↦ bitValue (K := K) (bits left)) := by
  funext slot
  by_cases hleft : slot = left
  · subst slot
    simp [weightedTransposition, transposeCoordinates, fixedMultiplier,
      coordinateContribution, hne]
  · by_cases hright : slot = right
    · subst slot
      simp [weightedTransposition, transposeCoordinates, fixedMultiplier,
        coordinateContribution, hne.symm]
    · simp [weightedTransposition, transposeCoordinates, fixedMultiplier,
        coordinateContribution, hleft, hright]

/-- Boolean vector supported at one selected coordinate. -/
def basisBits {Slot : Type} [DecidableEq Slot] (selected : Slot) : Slot → Bool :=
  fun slot ↦ decide (slot = selected)

/-- A nontrivial weighted transposition cannot be multiplication by one fixed diagonal/ring
element on every Binary-NTT secret. -/
theorem no_diagonal_translation
    {Slot K : Type} [Field K] [DecidableEq Slot]
    (left right : Slot) (hne : left ≠ right) (gadget : Slot → K)
    (hgadget : gadget left ≠ 0) :
    ¬ ∃ multiplier : Slot → K, ∀ bits : Slot → Bool,
      multiplier * (fun slot ↦ bitValue (K := K) (bits slot)) =
        weightedTransposition left right gadget
          (fun slot ↦ bitValue (K := K) (bits slot)) := by
  rintro ⟨multiplier, hmultiplier⟩
  have hcoordinate := congrFun (hmultiplier (basisBits right)) left
  simp [basisBits, bitValue, weightedTransposition, transposeCoordinates, hne] at hcoordinate
  exact hgadget hcoordinate.symm

/-- Exact phase identity for one automorphism-key row. -/
theorem phase_identity {R : Type} [Ring R]
    (mask secret error message : R) :
    (mask * secret + error + message) - mask * secret = message + error := by
  abel

/-! ## Concrete Binary-NTT XOR transport -/

/-- Split NTT product ring. -/
abbrev SplitRing (Slot K : Type) := Slot → K

/-- Embed a binary NTT vector into the split ring. -/
def embedBits {Slot K : Type} [Zero K] [One K] (bits : Slot → Bool) : SplitRing Slot K :=
  fun slot ↦ bitValue (K := K) (bits slot)

/-- Public XOR rerandomization applied to a complete RLWE row batch. -/
def xorView {Slot K Row : Type} [CommRing K]
    (coins : Slot → Bool)
    (view : BinaryNTTSecurity.RLWEView (SplitRing Slot K) Row) :
    BinaryNTTSecurity.RLWEView (SplitRing Slot K) Row where
  mask := fun row slot ↦
    view.mask row slot * (1 - 2 * bitValue (K := K) (coins slot))
  body := fun row slot ↦
    view.body row slot - view.mask row slot * bitValue (K := K) (coins slot)

/-- XORing a Binary-NTT secret preserves a real RLWE row and leaves its error coordinate
unchanged. -/
theorem xorView_real {Slot K Row : Type} [CommRing K]
    (coins secret : Slot → Bool) (mask error : Row → SplitRing Slot K) :
    xorView coins (BinaryNTTSecurity.realView mask (embedBits secret) error) =
      BinaryNTTSecurity.realView (xorView coins
        ⟨mask, fun _ ↦ 0⟩).mask
        (embedBits (BinaryNTTSecurity.binaryVectorXor secret coins)) error := by
  apply BinaryNTTSecurity.RLWEView.ext
  · rfl
  · funext row slot
    change mask row slot * bitValue (secret slot) + error row slot -
        mask row slot * bitValue (coins slot) =
      (mask row slot * (1 - 2 * bitValue (coins slot))) *
          bitValue (xor (secret slot) (coins slot)) + error row slot
    rw [bitValue_xor]
    simpa only [BinaryNTTSecurity.xorMaskMultiplier] using
      (BinaryNTTSecurity.xor_rerandomize_sample
        (mask row slot) (bitValue (K := K) (secret slot)) (error row slot)
        (bitValue (K := K) (coins slot))
        (by cases secret slot <;> norm_num [bitValue])
        (by cases coins slot <;> norm_num [bitValue]))

/-- The batch XOR map is an involution. -/
@[simp]
theorem xorView_xorView {Slot K Row : Type} [CommRing K]
    (coins : Slot → Bool)
    (view : BinaryNTTSecurity.RLWEView (SplitRing Slot K) Row) :
    xorView coins (xorView coins view) = view := by
  apply BinaryNTTSecurity.RLWEView.ext <;> funext row slot
  · cases hcoin : coins slot
    · simp [xorView, bitValue, hcoin]
    · simp [xorView, bitValue, hcoin]
      ring
  · cases hcoin : coins slot
    · simp [xorView, bitValue, hcoin]
    · simp [xorView, bitValue, hcoin]
      ring

theorem xorView_bijective {Slot K Row : Type} [CommRing K]
    (coins : Slot → Bool) :
    Function.Bijective
      (xorView (K := K) (Row := Row) coins) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨xorView coins, xorView_xorView coins, xorView_xorView coins⟩

/-- A fully uniform RLWE batch remains exactly uniform after fixed XOR rerandomization. -/
theorem xorView_uniform_evalDist {Slot K Row : Type}
    [CommRing K] [Finite K] [DecidableEq K] [SampleableType K]
    [Fintype Slot] [DecidableEq Slot]
    [Finite Row] [DecidableEq Row]
    [SampleableType (BinaryNTTSecurity.RLWEView (SplitRing Slot K) Row)]
    (coins : Slot → Bool) :
    evalDist (($ᵗ (BinaryNTTSecurity.RLWEView (SplitRing Slot K) Row)) >>= fun view ↦
        pure (xorView coins view)) =
      evalDist ($ᵗ (BinaryNTTSecurity.RLWEView (SplitRing Slot K) Row)) := by
  apply evalDist_ext
  intro output
  simpa [monad_norm] using
    (probOutput_bind_bijective_uniform_cross
      (α := BinaryNTTSecurity.RLWEView (SplitRing Slot K) Row)
      (β := BinaryNTTSecurity.RLWEView (SplitRing Slot K) Row)
      (xorView coins) (xorView_bijective coins)
      (fun value ↦ pure value) output)

/-- Mask component of the public XOR transform. -/
def xorMask {Slot K Row : Type} [CommRing K]
    (coins : Slot → Bool) (mask : Row → SplitRing Slot K) : Row → SplitRing Slot K :=
  (xorView coins ⟨mask, fun _ ↦ 0⟩).mask

@[simp]
theorem xorMask_xorMask {Slot K Row : Type} [CommRing K]
    (coins : Slot → Bool) (mask : Row → SplitRing Slot K) :
    xorMask coins (xorMask coins mask) = mask := by
  funext row slot
  cases hcoin : coins slot
  · simp [xorMask, xorView, bitValue, hcoin]
  · simp [xorMask, xorView, bitValue, hcoin]
    ring

theorem xorMask_bijective {Slot K Row : Type} [CommRing K]
    (coins : Slot → Bool) : Function.Bijective (xorMask (K := K) (Row := Row) coins) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨xorMask coins, xorMask_xorMask coins, xorMask_xorMask coins⟩

/-- Honest Binary-NTT RLWE channel conditioned on the hidden binary coordinate vector. -/
def splitChannel {Slot K Row : Type} [CommRing K]
    [SampleableType (Row → SplitRing Slot K)]
    (errorSampler : ProbComp (Row → SplitRing Slot K))
    (secret : Slot → Bool) :
    ProbComp (BinaryNTTSecurity.RLWEView (SplitRing Slot K) Row) := do
  let error ← errorSampler
  let mask ← $ᵗ (Row → SplitRing Slot K)
  return BinaryNTTSecurity.realView mask (embedBits secret) error

/-- Complete conditional-channel equivariance under Binary-NTT XOR randomization. -/
theorem xorView_splitChannel_evalDist
    {Slot K Row : Type}
    [CommRing K] [Finite K] [DecidableEq K] [SampleableType K]
    [Fintype Slot] [DecidableEq Slot]
    [Fintype Row] [DecidableEq Row]
    (errorSampler : ProbComp (Row → SplitRing Slot K))
    (secret coins : Slot → Bool) :
    evalDist (splitChannel errorSampler secret >>= fun view ↦ pure (xorView coins view)) =
      evalDist (splitChannel errorSampler
        (BinaryNTTSecurity.binaryVectorXor secret coins)) := by
  simp only [splitChannel, bind_assoc, pure_bind]
  refine evalDist_bind_congr' errorSampler fun error ↦ ?_
  apply evalDist_ext
  intro output
  simpa only [xorView_real, xorMask] using
    (probOutput_bind_bijective_uniform_cross
      (α := Row → SplitRing Slot K) (β := Row → SplitRing Slot K)
      (xorMask coins) (xorMask_bijective coins)
      (fun mask ↦ pure (BinaryNTTSecurity.realView mask
        (embedBits (BinaryNTTSecurity.binaryVectorXor secret coins)) error)) output)

/-! ## Finite signed-response framework -/

/-- Boolean character with values `+1` for zero and `-1` for one. -/
def bitCharacter (bit : Bool) : ℝ := if bit then -1 else 1

@[simp]
theorem bitIndicator_eq (bit : Bool) :
    (if bit then (1 : ℝ) else 0) = (1 - bitCharacter bit) / 2 := by
  cases bit <;> norm_num [bitCharacter]

/-- Shift a public view only when the selected secret bit is one. -/
def bitShift {View Shift : Type} (act : View → Shift → View)
    (view : View) (shift : Shift) (bit : Bool) : View :=
  if bit then act view shift else view

/-- Expectation of a response on the public marginal of a joint secret/view sampler. -/
def viewExpectation {Secret View : Type} [Fintype Secret] [Fintype View]
    (joint : ProbComp (Secret × View)) (response : View → ℝ) : ℝ :=
  FormalProof4FHE.BoundedMoment.expectation joint (fun value ↦ response value.2)

/-- Correlation of a real response with a secret character. -/
def correlation {Secret View : Type} [Fintype Secret] [Fintype View]
    (joint : ProbComp (Secret × View)) (character : Secret → ℝ)
    (response : View → ℝ) : ℝ :=
  FormalProof4FHE.BoundedMoment.expectation joint
    (fun value ↦ character value.1 * response value.2)

/-- Signed response gap caused by inserting one hidden bit. -/
def insertionGap {Secret View Shift : Type} [Fintype Secret] [Fintype View]
    (joint : ProbComp (Secret × View)) (bit : Secret → Bool)
    (act : View → Shift → View) (shift : Shift) (response : View → ℝ) : ℝ :=
  FormalProof4FHE.BoundedMoment.expectation joint
      (fun value ↦ response (bitShift act value.2 shift (bit value.1))) -
    viewExpectation joint response

/-- The signed algorithm used by the insertion proof has conditional mean half the shifted
response difference. -/
def meanResponse {View Shift : Type}
    (act : View → Shift → View) (shift : Shift) (response : View → ℝ) : View → ℝ :=
  fun view ↦ (response (act view shift) - response view) / 2

/-- Exact identity behind the secret-bit insertion lemma. -/
theorem insertionGap_eq_mean_sub_correlation
    {Secret View Shift : Type} [Fintype Secret] [Fintype View]
    (joint : ProbComp (Secret × View)) (bit : Secret → Bool)
    (act : View → Shift → View) (shift : Shift) (response : View → ℝ) :
    insertionGap joint bit act shift response =
      viewExpectation joint (meanResponse act shift response) -
        correlation joint (fun secret ↦ bitCharacter (bit secret))
          (meanResponse act shift response) := by
  unfold insertionGap viewExpectation correlation meanResponse bitShift
  rw [← FormalProof4FHE.SquaredBias.expectation_sub]
  rw [← FormalProof4FHE.SquaredBias.expectation_sub]
  apply congrArg (FormalProof4FHE.BoundedMoment.expectation joint)
  funext value
  rw [show response (if bit value.1 then act value.2 shift else value.2) - response value.2 =
      (response (act value.2 shift) - response value.2) / 2 -
        bitCharacter (bit value.1) *
          ((response (act value.2 shift) - response value.2) / 2) by
    cases bit value.1 <;> norm_num [bitCharacter]]

/-- Quantitative one-bit insertion bound. -/
theorem abs_insertionGap_le
    {Secret View Shift : Type} [Fintype Secret] [Fintype View]
    (joint : ProbComp (Secret × View)) (bit : Secret → Bool)
    (act : View → Shift → View) (shift : Shift) (response : View → ℝ) :
    |insertionGap joint bit act shift response| ≤
      |viewExpectation joint (meanResponse act shift response)| +
        |correlation joint (fun secret ↦ bitCharacter (bit secret))
          (meanResponse act shift response)| := by
  rw [insertionGap_eq_mean_sub_correlation]
  simpa [sub_eq_add_neg] using
    (abs_add_le
      (viewExpectation joint (meanResponse act shift response))
      (-correlation joint (fun secret ↦ bitCharacter (bit secret))
        (meanResponse act shift response)))

/-! ## The second-bit Fourier decomposition -/

/-- Even part of a response under one public shift. -/
def evenResponse {View Shift : Type}
    (act : View → Shift → View) (shift : Shift) (response : View → ℝ) : View → ℝ :=
  fun view ↦ (response view + response (act view shift)) / 2

/-- Odd part of a response under one public shift. -/
def oddResponse {View Shift : Type}
    (act : View → Shift → View) (shift : Shift) (response : View → ℝ) : View → ℝ :=
  fun view ↦ (response view - response (act view shift)) / 2

/-- One-bit Walsh decomposition evaluated at the hidden bit. -/
theorem response_bitShift_eq_even_add_character_mul_odd
    {View Shift : Type} (act : View → Shift → View)
    (view : View) (shift : Shift) (bit : Bool) (response : View → ℝ) :
    response (bitShift act view shift bit) =
      evenResponse act shift response view +
        bitCharacter bit * oddResponse act shift response view := by
  cases bit <;> simp [bitShift, evenResponse, oddResponse, bitCharacter] <;> ring

/-- Correlation of the next bit after one insertion is the sum of two ordinary-view parity
correlations. -/
theorem insertedCorrelation_eq_two_parities
    {Secret View Shift : Type} [Fintype Secret] [Fintype View]
    (joint : ProbComp (Secret × View)) (first second : Secret → Bool)
    (act : View → Shift → View) (shift : Shift) (response : View → ℝ) :
    FormalProof4FHE.BoundedMoment.expectation joint
        (fun value ↦ bitCharacter (second value.1) *
          response (bitShift act value.2 shift (first value.1))) =
      correlation joint (fun secret ↦ bitCharacter (second secret))
          (evenResponse act shift response) +
        correlation joint
          (fun secret ↦ bitCharacter (first secret) * bitCharacter (second secret))
          (oddResponse act shift response) := by
  unfold correlation
  rw [← FormalProof4FHE.BoundedMoment.expectation_add]
  apply congrArg (FormalProof4FHE.BoundedMoment.expectation joint)
  funext value
  rw [response_bitShift_eq_even_add_character_mul_odd
    act value.2 shift (first value.1) response]
  ring

/-- Quantitative version of "the second bit remains hidden". -/
theorem abs_insertedCorrelation_le_two_parities
    {Secret View Shift : Type} [Fintype Secret] [Fintype View]
    (joint : ProbComp (Secret × View)) (first second : Secret → Bool)
    (act : View → Shift → View) (shift : Shift) (response : View → ℝ) :
    |FormalProof4FHE.BoundedMoment.expectation joint
        (fun value ↦ bitCharacter (second value.1) *
          response (bitShift act value.2 shift (first value.1)))| ≤
      |correlation joint (fun secret ↦ bitCharacter (second secret))
          (evenResponse act shift response)| +
        |correlation joint
          (fun secret ↦ bitCharacter (first secret) * bitCharacter (second secret))
          (oddResponse act shift response)| := by
  rw [insertedCorrelation_eq_two_parities]
  exact abs_add_le _ _

/-! ## Two-copy parity-hiding arithmetic -/

/-- If the manuscript's two-copy decision experiment has advantage `correlation^2/2` bounded by
`ordinaryBound`, then the predictor correlation is at most `sqrt(2*ordinaryBound)`. -/
theorem abs_correlation_le_sqrt_two_mul
    (correlationValue ordinaryBound : ℝ)
    (hBound : correlationValue ^ 2 / 2 ≤ ordinaryBound)
    (hOrdinaryNonneg : 0 ≤ ordinaryBound) :
    |correlationValue| ≤ Real.sqrt (2 * ordinaryBound) := by
  have hsqrt : (Real.sqrt (2 * ordinaryBound)) ^ 2 = 2 * ordinaryBound := by
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) hOrdinaryNonneg)]
  have habsSq : |correlationValue| ^ 2 = correlationValue ^ 2 := sq_abs correlationValue
  have hnonneg : 0 ≤ Real.sqrt (2 * ordinaryBound) := Real.sqrt_nonneg _
  nlinarith [abs_nonneg correlationValue]

/-- Abstract certificate supplied by the exact doubled-row XOR decision reduction in the
manuscript.  It records no hardness assumption: `advantage_eq` is a finite-game identity to be
proved for the concrete Binary-NTT samplers. -/
structure ParityHidingCertificate where
  correlation : ℝ
  ordinaryDecisionAdvantage : ℝ
  ordinaryDecisionAdvantage_nonneg : 0 ≤ ordinaryDecisionAdvantage
  advantage_eq : ordinaryDecisionAdvantage = correlation ^ 2 / 2

theorem ParityHidingCertificate.abs_correlation_le
    (certificate : ParityHidingCertificate) (ordinaryBound : ℝ)
    (hBound : certificate.ordinaryDecisionAdvantage ≤ ordinaryBound)
    (hOrdinaryNonneg : 0 ≤ ordinaryBound) :
    |certificate.correlation| ≤ Real.sqrt (2 * ordinaryBound) := by
  apply abs_correlation_le_sqrt_two_mul certificate.correlation ordinaryBound
  · rw [← certificate.advantage_eq]
    exact hBound
  · exact hOrdinaryNonneg

/-- Walsh parity character of a binary NTT vector. -/
def parityCharacter {Slot : Type} [Fintype Slot]
    (frequency bits : Slot → Bool) : ℝ :=
  ∏ slot, if frequency slot then bitCharacter (bits slot) else 1

theorem bitCharacter_xor (left right : Bool) :
    bitCharacter (xor left right) = bitCharacter left * bitCharacter right := by
  cases left <;> cases right <;> norm_num [bitCharacter]

theorem parityCharacter_xor {Slot : Type} [Fintype Slot]
    (frequency left right : Slot → Bool) :
    parityCharacter frequency (BinaryNTTSecurity.binaryVectorXor left right) =
      parityCharacter frequency left * parityCharacter frequency right := by
  unfold parityCharacter
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro slot _
  by_cases hfrequency : frequency slot
  · simp [hfrequency, BinaryNTTSecurity.binaryVectorXor, bitCharacter_xor]
  · simp [hfrequency]

theorem parityCharacter_sq {Slot : Type} [Fintype Slot]
    (frequency bits : Slot → Bool) : parityCharacter frequency bits ^ 2 = 1 := by
  unfold parityCharacter
  rw [pow_two, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro slot _
  by_cases hfrequency : frequency slot
  · cases hbit : bits slot <;> norm_num [hfrequency, bitCharacter, hbit]
  · simp [hfrequency]

theorem parityCharacter_basisBits
    {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (frequency : Slot → Bool) (selected : Slot) (hselected : frequency selected = true) :
    parityCharacter frequency (basisBits selected) = -1 := by
  classical
  unfold parityCharacter
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ selected)]
  have hrest :
      (∏ x ∈ Finset.univ \ {selected},
        if frequency x then bitCharacter (basisBits selected x) else 1) = 1 := by
    apply Finset.prod_eq_one
    intro slot hslot
    have hne : slot ≠ selected := by
      simpa using (Finset.mem_sdiff.mp hslot).2
    simp [basisBits, hne, bitCharacter]
  rw [hrest]
  simp [hselected, basisBits, bitCharacter]

/-- Every nonzero Walsh parity is balanced under a uniform binary vector. -/
theorem parityCharacter_uniform_expectation_eq_zero
    {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (frequency : Slot → Bool) (selected : Slot) (hselected : frequency selected = true) :
    FormalProof4FHE.BoundedMoment.expectation ($ᵗ (Slot → Bool))
      (parityCharacter frequency) = 0 := by
  let flip := basisBits selected
  have hdist := BinaryNTTSecurity.binaryVectorXor_uniform_evalDist flip
  have hexpect := FormalProof4FHE.BoundedMoment.expectation_congr_evalDist
    hdist (parityCharacter frequency)
  have hleft :
      FormalProof4FHE.BoundedMoment.expectation
          (($ᵗ (Slot → Bool)) >>= fun bits ↦
            pure (BinaryNTTSecurity.binaryVectorXor flip bits))
          (parityCharacter frequency) =
        -FormalProof4FHE.BoundedMoment.expectation ($ᵗ (Slot → Bool))
          (parityCharacter frequency) := by
    have hmap :
        BinaryNTTSecurity.binaryVectorXor flip <$> ($ᵗ (Slot → Bool)) =
          (($ᵗ (Slot → Bool)) >>= fun bits ↦
            pure (BinaryNTTSecurity.binaryVectorXor flip bits)) := by
      rw [map_eq_bind_pure_comp]
      rfl
    rw [← hmap]
    rw [FormalProof4FHE.BoundedMoment.expectation_map]
    rw [show (fun bits ↦ parityCharacter frequency
        (BinaryNTTSecurity.binaryVectorXor flip bits)) =
      (fun bits ↦ (-1 : ℝ) * parityCharacter frequency bits) by
        funext bits
        rw [parityCharacter_xor, parityCharacter_basisBits frequency selected hselected]]
    rw [FormalProof4FHE.BoundedMoment.expectation_const_mul]
    ring
  rw [hleft] at hexpect
  linarith

/-- Signed mean of a predictor on the real channel for one fixed secret. -/
def predictorMean {Secret View : Type} [Fintype View]
    (channel : Secret → ProbComp View) (predictor : View → ProbComp Bool)
    (secret : Secret) : ℝ :=
  FormalProof4FHE.BoundedMoment.expectation (channel secret >>= predictor) bitCharacter

/-- Correlation of the predictor with one Walsh parity under a uniform Binary-NTT secret. -/
def predictorParityCorrelation
    {Slot View : Type} [Fintype Slot] [DecidableEq Slot] [Fintype View]
    (channel : (Slot → Bool) → ProbComp View) (predictor : View → ProbComp Bool)
    (frequency : Slot → Bool) : ℝ :=
  FormalProof4FHE.BoundedMoment.expectation ($ᵗ (Slot → Bool))
    (fun secret ↦ parityCharacter frequency secret * predictorMean channel predictor secret)

/-- Mean of one XOR-rerandomized, parity-twisted predictor block, conditioned on the original
secret.  The concrete public XOR channel is distributionally equal to this ideal expression by
`xorView_splitChannel_evalDist`. -/
def rerandomizedParityMean
    {Slot View : Type} [Fintype Slot] [DecidableEq Slot] [Fintype View]
    (channel : (Slot → Bool) → ProbComp View) (predictor : View → ProbComp Bool)
    (frequency originalSecret : Slot → Bool) : ℝ :=
  FormalProof4FHE.BoundedMoment.expectation ($ᵗ (Slot → Bool))
    (fun coins ↦ parityCharacter frequency coins *
      predictorMean channel predictor
        (BinaryNTTSecurity.binaryVectorXor originalSecret coins))

/-- Corrected expectation identity from the manuscript: there is one predictor/character factor,
not the duplicated product appearing in the TeX typo. -/
theorem rerandomizedParityMean_eq
    {Slot View : Type} [Fintype Slot] [DecidableEq Slot] [Fintype View]
    (channel : (Slot → Bool) → ProbComp View) (predictor : View → ProbComp Bool)
    (frequency originalSecret : Slot → Bool) :
    rerandomizedParityMean channel predictor frequency originalSecret =
      parityCharacter frequency originalSecret *
        predictorParityCorrelation channel predictor frequency := by
  let observable := fun coins : Slot → Bool ↦
    parityCharacter frequency coins *
      predictorMean channel predictor
        (BinaryNTTSecurity.binaryVectorXor originalSecret coins)
  have hdist := BinaryNTTSecurity.binaryVectorXor_uniform_evalDist originalSecret
  have hreindex := FormalProof4FHE.BoundedMoment.expectation_congr_evalDist
    hdist observable
  unfold rerandomizedParityMean predictorParityCorrelation
  calc
    FormalProof4FHE.BoundedMoment.expectation ($ᵗ (Slot → Bool)) observable =
        FormalProof4FHE.BoundedMoment.expectation
          (($ᵗ (Slot → Bool)) >>= fun bits ↦
            pure (BinaryNTTSecurity.binaryVectorXor originalSecret bits)) observable :=
      hreindex.symm
    _ = FormalProof4FHE.BoundedMoment.expectation ($ᵗ (Slot → Bool))
        (fun coins ↦ observable
          (BinaryNTTSecurity.binaryVectorXor originalSecret coins)) := by
      rw [show (($ᵗ (Slot → Bool)) >>= fun bits ↦
          pure (BinaryNTTSecurity.binaryVectorXor originalSecret bits)) =
        BinaryNTTSecurity.binaryVectorXor originalSecret <$> ($ᵗ (Slot → Bool)) by
          rw [map_eq_bind_pure_comp]
          rfl]
      rw [FormalProof4FHE.BoundedMoment.expectation_map]
    _ = FormalProof4FHE.BoundedMoment.expectation ($ᵗ (Slot → Bool))
        (fun coins ↦ parityCharacter frequency originalSecret *
          (parityCharacter frequency coins * predictorMean channel predictor coins)) := by
      apply congrArg (FormalProof4FHE.BoundedMoment.expectation ($ᵗ (Slot → Bool)))
      funext coins
      simp only [observable, parityCharacter_xor,
        BinaryNTTSecurity.binaryVectorXor_self_left]
      ring
    _ = parityCharacter frequency originalSecret *
        FormalProof4FHE.BoundedMoment.expectation ($ᵗ (Slot → Bool))
          (fun coins ↦ parityCharacter frequency coins *
            predictorMean channel predictor coins) := by
      rw [FormalProof4FHE.BoundedMoment.expectation_const_mul]

/-- The two conditionally independent real blocks have product-sign mean exactly `rho^2`. -/
theorem real_twoBlock_product_mean_eq_sq
    {Slot View : Type} [Fintype Slot] [DecidableEq Slot] [Fintype View]
    (channel : (Slot → Bool) → ProbComp View) (predictor : View → ProbComp Bool)
    (frequency : Slot → Bool) :
    FormalProof4FHE.BoundedMoment.expectation ($ᵗ (Slot → Bool))
        (fun originalSecret ↦
          rerandomizedParityMean channel predictor frequency originalSecret ^ 2) =
      predictorParityCorrelation channel predictor frequency ^ 2 := by
  rw [show (fun originalSecret ↦
      rerandomizedParityMean channel predictor frequency originalSecret ^ 2) =
    (fun _ ↦ predictorParityCorrelation channel predictor frequency ^ 2) by
      funext originalSecret
      rw [rerandomizedParityMean_eq, mul_pow, parityCharacter_sq, one_mul]]
  exact FormalProof4FHE.BoundedMoment.expectation_const _ _

/-- In the uniform branch, a balanced nonzero parity makes each twisted block have mean zero,
independently of the predictor's behavior on a uniform view. -/
theorem uniform_twistedBlock_mean_eq_zero
    {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (frequency : Slot → Bool) (selected : Slot) (hselected : frequency selected = true)
    (uniformPredictorMean : ℝ) :
    FormalProof4FHE.BoundedMoment.expectation ($ᵗ (Slot → Bool))
        (fun coins ↦ parityCharacter frequency coins * uniformPredictorMean) = 0 := by
  rw [show (fun coins ↦ parityCharacter frequency coins * uniformPredictorMean) =
      (fun coins ↦ uniformPredictorMean * parityCharacter frequency coins) by
    funext coins
    ring]
  rw [FormalProof4FHE.BoundedMoment.expectation_const_mul,
    parityCharacter_uniform_expectation_eq_zero frequency selected hselected, mul_zero]

/-! ### Boolean realization of the doubled-row product-sign test -/

/-- Boolean parity bit corresponding to the real Walsh character. -/
def parityBit {Slot : Type} [Fintype Slot]
    (frequency bits : Slot → Bool) : Bool :=
  decide (parityCharacter frequency bits = -1)

theorem bitCharacter_parityBit {Slot : Type} [Fintype Slot]
    (frequency bits : Slot → Bool) :
    bitCharacter (parityBit frequency bits) = parityCharacter frequency bits := by
  have hsquare := parityCharacter_sq frequency bits
  have hcases : parityCharacter frequency bits = 1 ∨
      parityCharacter frequency bits = -1 := by
    exact sq_eq_one_iff.mp hsquare
  rcases hcases with hone | hneg
  · have hnneg : parityCharacter frequency bits ≠ -1 := by linarith
    unfold parityBit
    have hdecide : decide (parityCharacter frequency bits = -1) = false := by
      simp [hnneg]
    rw [hdecide]
    simp [bitCharacter, hone]
  · unfold parityBit
    have hdecide : decide (parityCharacter frequency bits = -1) = true := by
      simp [hneg]
    rw [hdecide]
    simp [bitCharacter, hneg]

/-- One idealized XOR-rerandomized predictor block.  The concrete public transformation has this
distribution by `xorView_splitChannel_evalDist`. -/
def twistedBlock
    {Slot View : Type} [Fintype Slot] [DecidableEq Slot]
    (channel : (Slot → Bool) → ProbComp View) (predictor : View → ProbComp Bool)
    (frequency originalSecret : Slot → Bool) : ProbComp Bool := do
  let coins ← $ᵗ (Slot → Bool)
  let view ← channel (BinaryNTTSecurity.binaryVectorXor originalSecret coins)
  let output ← predictor view
  return xor output (parityBit frequency coins)

/-- Signed mean of a Boolean sampler. -/
def signedMean (sampler : ProbComp Bool) : ℝ :=
  FormalProof4FHE.BoundedMoment.expectation sampler bitCharacter

theorem signedMean_twistedBlock
    {Slot View : Type} [Fintype Slot] [DecidableEq Slot] [Fintype View]
    (channel : (Slot → Bool) → ProbComp View) (predictor : View → ProbComp Bool)
    (frequency originalSecret : Slot → Bool) :
    signedMean (twistedBlock channel predictor frequency originalSecret) =
      rerandomizedParityMean channel predictor frequency originalSecret := by
  unfold signedMean twistedBlock rerandomizedParityMean predictorMean
  rw [FormalProof4FHE.SquaredBias.expectation_bind_nested]
  apply congrArg (FormalProof4FHE.BoundedMoment.expectation ($ᵗ (Slot → Bool)))
  funext coins
  rw [FormalProof4FHE.SquaredBias.expectation_bind_nested]
  rw [FormalProof4FHE.SquaredBias.expectation_bind_nested]
  rw [← FormalProof4FHE.BoundedMoment.expectation_const_mul]
  apply congrArg
    (FormalProof4FHE.BoundedMoment.expectation
      (channel (BinaryNTTSecurity.binaryVectorXor originalSecret coins)))
  funext view
  rw [FormalProof4FHE.SquaredBias.expectation_bind_nested]
  simp only [FormalProof4FHE.BoundedMoment.expectation_pure, bitCharacter_xor,
    bitCharacter_parityBit]
  rw [show FormalProof4FHE.BoundedMoment.expectation (predictor view)
      (fun output ↦ bitCharacter output * parityCharacter frequency coins) =
    parityCharacter frequency coins *
      FormalProof4FHE.BoundedMoment.expectation (predictor view) bitCharacter by
        rw [show (fun output ↦ bitCharacter output * parityCharacter frequency coins) =
          (fun output ↦ parityCharacter frequency coins * bitCharacter output) by
            funext output
            ring]
        rw [FormalProof4FHE.BoundedMoment.expectation_const_mul]]

/-- The actual public block transform applied to a challenge sampled under the original secret. -/
def actualTwistedBlock
    {Secret View : Type} [Fintype Secret] [SampleableType Secret]
    (transform : Secret → View → View)
    (channel : Secret → ProbComp View) (predictor : View → ProbComp Bool)
    (parity : Secret → Bool) (originalSecret : Secret) : ProbComp Bool := do
  let coins ← $ᵗ Secret
  let view ← channel originalSecret
  let output ← predictor (transform coins view)
  return xor output (parity coins)

/-- Channel equivariance identifies the actual public block with the ideal rerandomized block. -/
theorem actualTwistedBlock_evalDist
    {Secret View : Type} [Fintype Secret] [SampleableType Secret]
    (xorSecret : Secret → Secret → Secret)
    (transform : Secret → View → View)
    (channel : Secret → ProbComp View) (predictor : View → ProbComp Bool)
    (parity : Secret → Bool) (originalSecret : Secret)
    (hChannel : ∀ coins,
      evalDist (channel originalSecret >>= fun view ↦ pure (transform coins view)) =
        evalDist (channel (xorSecret originalSecret coins))) :
    evalDist (actualTwistedBlock transform channel predictor parity originalSecret) =
      evalDist (do
        let coins ← $ᵗ Secret
        let view ← channel (xorSecret originalSecret coins)
        let output ← predictor view
        return xor output (parity coins)) := by
  unfold actualTwistedBlock
  refine evalDist_bind_congr' ($ᵗ Secret) fun coins ↦ ?_
  let finish := fun view : View ↦ do
    let output ← predictor view
    return xor output (parity coins)
  have hpost := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (hChannel coins) finish
  simpa only [finish, bind_assoc, pure_bind] using hpost

/-- Uniform block before the equality/product-sign test. -/
def uniformTwistedBlock
    {Secret View : Type} [Fintype Secret] [SampleableType Secret]
    (uniformView : ProbComp View) (predictor : View → ProbComp Bool)
    (parity : Secret → Bool) : ProbComp Bool := do
  let coins ← $ᵗ Secret
  let view ← uniformView
  let output ← predictor view
  return xor output (parity coins)

/-- A balanced parity makes the uniform twisted block a signed-mean-zero Boolean sampler. -/
theorem signedMean_uniformTwistedBlock_eq_zero
    {Secret View : Type} [Fintype Secret] [SampleableType Secret] [Fintype View]
    (uniformView : ProbComp View) (predictor : View → ProbComp Bool)
    (parity : Secret → Bool)
    (hParityBalanced : FormalProof4FHE.BoundedMoment.expectation ($ᵗ Secret)
      (fun secret ↦ bitCharacter (parity secret)) = 0) :
    signedMean (uniformTwistedBlock uniformView predictor parity) = 0 := by
  unfold signedMean uniformTwistedBlock
  rw [FormalProof4FHE.SquaredBias.expectation_bind_nested]
  rw [show (fun coins ↦
      FormalProof4FHE.BoundedMoment.expectation
        (uniformView >>= fun view ↦
          predictor view >>= fun output ↦ pure (xor output (parity coins))) bitCharacter) =
    (fun coins ↦ bitCharacter (parity coins) *
      FormalProof4FHE.BoundedMoment.expectation (uniformView >>= predictor) bitCharacter) by
        funext coins
        rw [FormalProof4FHE.SquaredBias.expectation_bind_nested]
        rw [FormalProof4FHE.SquaredBias.expectation_bind_nested]
        rw [← FormalProof4FHE.BoundedMoment.expectation_const_mul]
        apply congrArg (FormalProof4FHE.BoundedMoment.expectation uniformView)
        funext view
        rw [FormalProof4FHE.SquaredBias.expectation_bind_nested]
        simp_rw [FormalProof4FHE.BoundedMoment.expectation_pure, bitCharacter_xor]
        rw [← FormalProof4FHE.BoundedMoment.expectation_const_mul]
        apply congrArg (FormalProof4FHE.BoundedMoment.expectation (predictor view))
        funext output
        ring]
  let predictorValue :=
    FormalProof4FHE.BoundedMoment.expectation (uniformView >>= predictor) bitCharacter
  rw [show (fun coins ↦ bitCharacter (parity coins) * predictorValue) =
      (fun coins ↦ predictorValue * bitCharacter (parity coins)) by
    funext coins
    ring]
  rw [FormalProof4FHE.BoundedMoment.expectation_const_mul, hParityBalanced, mul_zero]

/-- The actual uniform challenge block is equal to `uniformTwistedBlock` whenever the public
transform preserves the uniform challenge distribution. -/
theorem actualUniformTwistedBlock_evalDist
    {Secret View : Type} [Fintype Secret] [SampleableType Secret]
    (transform : Secret → View → View) (uniformView : ProbComp View)
    (predictor : View → ProbComp Bool) (parity : Secret → Bool)
    (hUniform : ∀ coins,
      evalDist (uniformView >>= fun view ↦ pure (transform coins view)) = evalDist uniformView) :
    evalDist (do
      let coins ← $ᵗ Secret
      let view ← uniformView
      let output ← predictor (transform coins view)
      return xor output (parity coins)) =
      evalDist (uniformTwistedBlock uniformView predictor parity) := by
  unfold uniformTwistedBlock
  refine evalDist_bind_congr' ($ᵗ Secret) fun coins ↦ ?_
  let finish := fun view : View ↦ do
    let output ← predictor view
    return xor output (parity coins)
  have hpost := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (hUniform coins) finish
  simpa only [finish, bind_assoc, pure_bind] using hpost

/-- Equality test on two independent Boolean samplers. -/
def equalityGame (first second : ProbComp Bool) : ProbComp Bool := do
  let left ← first
  let right ← second
  return decide (left = right)

theorem bitReal_decide_eq (left right : Bool) :
    FormalProof4FHE.SquaredBias.bitReal (decide (left = right)) =
      (1 + bitCharacter left * bitCharacter right) / 2 := by
  cases left <;> cases right <;>
    norm_num [FormalProof4FHE.SquaredBias.bitReal, bitCharacter]

theorem probOutput_equalityGame_true (first second : ProbComp Bool) :
    Pr[= true | equalityGame first second].toReal =
      (1 + signedMean first * signedMean second) / 2 := by
  rw [← FormalProof4FHE.SquaredBias.expectation_bitReal]
  unfold equalityGame signedMean
  rw [FormalProof4FHE.SquaredBias.expectation_bind_nested]
  have hinner (left : Bool) :
      FormalProof4FHE.BoundedMoment.expectation
          (second >>= fun right ↦ pure (decide (left = right)))
          FormalProof4FHE.SquaredBias.bitReal =
        (1 + bitCharacter left *
          FormalProof4FHE.BoundedMoment.expectation second bitCharacter) / 2 := by
    rw [FormalProof4FHE.SquaredBias.expectation_bind_nested]
    simp_rw [FormalProof4FHE.BoundedMoment.expectation_pure, bitReal_decide_eq]
    have h := FormalProof4FHE.SquaredBias.expectation_affine second
      (1 / 2) (bitCharacter left / 2) bitCharacter
    calc
      FormalProof4FHE.BoundedMoment.expectation second
          (fun right ↦ (1 + bitCharacter left * bitCharacter right) / 2) =
        FormalProof4FHE.BoundedMoment.expectation second
          (fun right ↦ 1 / 2 + (bitCharacter left / 2) * bitCharacter right) := by
            apply congrArg (FormalProof4FHE.BoundedMoment.expectation second)
            funext right
            ring
      _ = 1 / 2 + (bitCharacter left / 2) *
          FormalProof4FHE.BoundedMoment.expectation second bitCharacter := h
      _ = (1 + bitCharacter left *
          FormalProof4FHE.BoundedMoment.expectation second bitCharacter) / 2 := by ring
  simp_rw [hinner]
  let secondMean := FormalProof4FHE.BoundedMoment.expectation second bitCharacter
  have houter := FormalProof4FHE.SquaredBias.expectation_affine first
    (1 / 2)
    (secondMean / 2)
    bitCharacter
  calc
    FormalProof4FHE.BoundedMoment.expectation first
        (fun value ↦ (1 + bitCharacter value * secondMean) / 2) =
      FormalProof4FHE.BoundedMoment.expectation first
        (fun value ↦ 1 / 2 + (secondMean / 2) * bitCharacter value) := by
          apply congrArg (FormalProof4FHE.BoundedMoment.expectation first)
          funext value
          ring
    _ = 1 / 2 + (secondMean / 2) *
        FormalProof4FHE.BoundedMoment.expectation first bitCharacter := houter
    _ = (1 + FormalProof4FHE.BoundedMoment.expectation first bitCharacter *
        FormalProof4FHE.BoundedMoment.expectation second bitCharacter) / 2 := by
          dsimp only [secondMean]
          ring

/-- Distinguisher used in the real doubled-row branch. -/
def realParityDecisionGame
    {Slot View : Type} [Fintype Slot] [DecidableEq Slot]
    (channel : (Slot → Bool) → ProbComp View) (predictor : View → ProbComp Bool)
    (frequency : Slot → Bool) : ProbComp Bool := do
  let originalSecret ← $ᵗ (Slot → Bool)
  equalityGame
    (twistedBlock channel predictor frequency originalSecret)
    (twistedBlock channel predictor frequency originalSecret)

theorem probOutput_realParityDecisionGame_true
    {Slot View : Type} [Fintype Slot] [DecidableEq Slot] [Fintype View]
    (channel : (Slot → Bool) → ProbComp View) (predictor : View → ProbComp Bool)
    (frequency : Slot → Bool) :
    Pr[= true | realParityDecisionGame channel predictor frequency].toReal =
      (1 + predictorParityCorrelation channel predictor frequency ^ 2) / 2 := by
  rw [← FormalProof4FHE.SquaredBias.expectation_bitReal]
  unfold realParityDecisionGame
  rw [FormalProof4FHE.SquaredBias.expectation_bind_nested]
  simp_rw [FormalProof4FHE.SquaredBias.expectation_bitReal,
    probOutput_equalityGame_true, signedMean_twistedBlock]
  have h := FormalProof4FHE.SquaredBias.expectation_affine
    ($ᵗ (Slot → Bool)) (1 / 2) (1 / 2)
    (fun originalSecret ↦
      rerandomizedParityMean channel predictor frequency originalSecret ^ 2)
  rw [real_twoBlock_product_mean_eq_sq] at h
  calc
    FormalProof4FHE.BoundedMoment.expectation ($ᵗ (Slot → Bool))
        (fun value ↦
          (1 + rerandomizedParityMean channel predictor frequency value *
            rerandomizedParityMean channel predictor frequency value) / 2) =
      FormalProof4FHE.BoundedMoment.expectation ($ᵗ (Slot → Bool))
        (fun value ↦ 1 / 2 + 1 / 2 *
          rerandomizedParityMean channel predictor frequency value ^ 2) := by
            apply congrArg
              (FormalProof4FHE.BoundedMoment.expectation ($ᵗ (Slot → Bool)))
            funext value
            ring
    _ = 1 / 2 + 1 / 2 * predictorParityCorrelation channel predictor frequency ^ 2 := h
    _ = (1 + predictorParityCorrelation channel predictor frequency ^ 2) / 2 := by ring

/-- The ideal uniform endpoint is a fair coin in the doubled product-sign test. -/
def uniformParityDecisionGame : ProbComp Bool := $ᵗ Bool

theorem parityHiding_advantage_eq_sq_div_two
    {Slot View : Type} [Fintype Slot] [DecidableEq Slot] [Fintype View]
    (channel : (Slot → Bool) → ProbComp View) (predictor : View → ProbComp Bool)
    (frequency : Slot → Bool) :
    (realParityDecisionGame channel predictor frequency).boolDistAdvantage
        uniformParityDecisionGame =
      predictorParityCorrelation channel predictor frequency ^ 2 / 2 := by
  unfold ProbComp.boolDistAdvantage uniformParityDecisionGame
  rw [probOutput_realParityDecisionGame_true]
  simp [probOutput_uniformSample]
  have hsquare := sq_nonneg (predictorParityCorrelation channel predictor frequency)
  rw [abs_of_nonneg]
  · ring
  · linarith

/-- The concrete doubled-row construction discharges `ParityHidingCertificate.advantage_eq`. -/
def concreteParityHidingCertificate
    {Slot View : Type} [Fintype Slot] [DecidableEq Slot] [Fintype View]
    (channel : (Slot → Bool) → ProbComp View) (predictor : View → ProbComp Bool)
    (frequency : Slot → Bool) : ParityHidingCertificate where
  correlation := predictorParityCorrelation channel predictor frequency
  ordinaryDecisionAdvantage :=
    (realParityDecisionGame channel predictor frequency).boolDistAdvantage
      uniformParityDecisionGame
  ordinaryDecisionAdvantage_nonneg := abs_nonneg _
  advantage_eq := parityHiding_advantage_eq_sq_div_two channel predictor frequency

/-! ### Exact ordinary-challenge realization -/

theorem equalityGame_evalDist_congr
    {first first' second second' : ProbComp Bool}
    (hFirst : evalDist first = evalDist first')
    (hSecond : evalDist second = evalDist second') :
    evalDist (equalityGame first second) = evalDist (equalityGame first' second') := by
  unfold equalityGame
  calc
    evalDist (first >>= fun left ↦
        second >>= fun right ↦ pure (decide (left = right))) =
      evalDist (first' >>= fun left ↦
        second >>= fun right ↦ pure (decide (left = right))) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hFirst _
    _ = _ := by
      refine evalDist_bind_congr' first' fun left ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hSecond _

/-- Actual reduction game on two ordinary real blocks sharing one Binary-NTT secret. -/
def actualRealParityDecisionGame
    {Secret View : Type} [Fintype Secret] [SampleableType Secret]
    (transform : Secret → View → View)
    (channel : Secret → ProbComp View) (predictor : View → ProbComp Bool)
    (parity : Secret → Bool) : ProbComp Bool := do
  let originalSecret ← $ᵗ Secret
  equalityGame
    (actualTwistedBlock transform channel predictor parity originalSecret)
    (actualTwistedBlock transform channel predictor parity originalSecret)

/-- Actual reduction block on an ordinary uniform challenge. -/
def actualUniformTwistedBlock
    {Secret View : Type} [Fintype Secret] [SampleableType Secret]
    (transform : Secret → View → View) (uniformView : ProbComp View)
    (predictor : View → ProbComp Bool) (parity : Secret → Bool) : ProbComp Bool := do
  let coins ← $ᵗ Secret
  let view ← uniformView
  let output ← predictor (transform coins view)
  return xor output (parity coins)

/-- Actual reduction game on two independent ordinary uniform blocks. -/
def actualUniformParityDecisionGame
    {Secret View : Type} [Fintype Secret] [SampleableType Secret]
    (transform : Secret → View → View) (uniformView : ProbComp View)
    (predictor : View → ProbComp Bool) (parity : Secret → Bool) : ProbComp Bool :=
  equalityGame
    (actualUniformTwistedBlock transform uniformView predictor parity)
    (actualUniformTwistedBlock transform uniformView predictor parity)

/-- The actual real reduction game is exactly the ideal real parity game. -/
theorem actualRealParityDecisionGame_evalDist
    {Slot View : Type} [Fintype Slot] [DecidableEq Slot] [Fintype View]
    (transform : (Slot → Bool) → View → View)
    (channel : (Slot → Bool) → ProbComp View) (predictor : View → ProbComp Bool)
    (frequency : Slot → Bool)
    (hChannel : ∀ secret coins,
      evalDist (channel secret >>= fun view ↦ pure (transform coins view)) =
        evalDist (channel (BinaryNTTSecurity.binaryVectorXor secret coins))) :
    evalDist (actualRealParityDecisionGame transform channel predictor
      (parityBit frequency)) =
      evalDist (realParityDecisionGame channel predictor frequency) := by
  unfold actualRealParityDecisionGame realParityDecisionGame
  refine evalDist_bind_congr' ($ᵗ (Slot → Bool)) fun secret ↦ ?_
  apply equalityGame_evalDist_congr
  · exact actualTwistedBlock_evalDist
      BinaryNTTSecurity.binaryVectorXor transform channel predictor
      (parityBit frequency) secret (hChannel secret)
  · exact actualTwistedBlock_evalDist
      BinaryNTTSecurity.binaryVectorXor transform channel predictor
      (parityBit frequency) secret (hChannel secret)

/-- Each actual uniform block is exactly the ideal uniform twisted block. -/
theorem actualUniformTwistedBlock_evalDist_eq
    {Secret View : Type} [Fintype Secret] [SampleableType Secret]
    (transform : Secret → View → View) (uniformView : ProbComp View)
    (predictor : View → ProbComp Bool) (parity : Secret → Bool)
    (hUniform : ∀ coins,
      evalDist (uniformView >>= fun view ↦ pure (transform coins view)) = evalDist uniformView) :
    evalDist (actualUniformTwistedBlock transform uniformView predictor parity) =
      evalDist (uniformTwistedBlock uniformView predictor parity) :=
  actualUniformTwistedBlock_evalDist transform uniformView predictor parity hUniform

/-- The actual uniform two-block game accepts with probability exactly one half. -/
theorem probOutput_actualUniformParityDecisionGame_true
    {Secret View : Type} [Fintype Secret] [SampleableType Secret] [Fintype View]
    (transform : Secret → View → View) (uniformView : ProbComp View)
    (predictor : View → ProbComp Bool) (parity : Secret → Bool)
    (hUniform : ∀ coins,
      evalDist (uniformView >>= fun view ↦ pure (transform coins view)) = evalDist uniformView)
    (hParityBalanced : FormalProof4FHE.BoundedMoment.expectation ($ᵗ Secret)
      (fun secret ↦ bitCharacter (parity secret)) = 0) :
    Pr[= true | actualUniformParityDecisionGame transform uniformView predictor parity].toReal =
      1 / 2 := by
  unfold actualUniformParityDecisionGame
  rw [probOutput_congr rfl (equalityGame_evalDist_congr
    (actualUniformTwistedBlock_evalDist_eq transform uniformView predictor parity hUniform)
    (actualUniformTwistedBlock_evalDist_eq transform uniformView predictor parity hUniform))]
  rw [probOutput_equalityGame_true,
    signedMean_uniformTwistedBlock_eq_zero uniformView predictor parity hParityBalanced]
  ring

/-- **Closed two-copy parity reduction.**  The same public algorithm on ordinary real and
uniform two-block challenges has advantage exactly `rho^2/2`. -/
theorem actualParityHiding_advantage_eq_sq_div_two
    {Slot View : Type} [Fintype Slot] [DecidableEq Slot] [Fintype View]
    (transform : (Slot → Bool) → View → View)
    (channel : (Slot → Bool) → ProbComp View) (uniformView : ProbComp View)
    (predictor : View → ProbComp Bool) (frequency : Slot → Bool)
    (selected : Slot) (hselected : frequency selected = true)
    (hChannel : ∀ secret coins,
      evalDist (channel secret >>= fun view ↦ pure (transform coins view)) =
        evalDist (channel (BinaryNTTSecurity.binaryVectorXor secret coins)))
    (hUniform : ∀ coins,
      evalDist (uniformView >>= fun view ↦ pure (transform coins view)) = evalDist uniformView) :
    (actualRealParityDecisionGame transform channel predictor (parityBit frequency)).boolDistAdvantage
        (actualUniformParityDecisionGame transform uniformView predictor (parityBit frequency)) =
      predictorParityCorrelation channel predictor frequency ^ 2 / 2 := by
  unfold ProbComp.boolDistAdvantage
  rw [probOutput_congr rfl
      (actualRealParityDecisionGame_evalDist transform channel predictor frequency hChannel),
    probOutput_realParityDecisionGame_true,
    probOutput_actualUniformParityDecisionGame_true transform uniformView predictor
      (parityBit frequency) hUniform]
  · have hsquare := sq_nonneg (predictorParityCorrelation channel predictor frequency)
    rw [abs_of_nonneg]
    · ring
    · linarith
  · simpa only [bitCharacter_parityBit] using
      parityCharacter_uniform_expectation_eq_zero frequency selected hselected

/-- Concrete certificate backed by the actual ordinary real/uniform reduction games. -/
def actualParityHidingCertificate
    {Slot View : Type} [Fintype Slot] [DecidableEq Slot] [Fintype View]
    (transform : (Slot → Bool) → View → View)
    (channel : (Slot → Bool) → ProbComp View) (uniformView : ProbComp View)
    (predictor : View → ProbComp Bool) (frequency : Slot → Bool)
    (selected : Slot) (hselected : frequency selected = true)
    (hChannel : ∀ secret coins,
      evalDist (channel secret >>= fun view ↦ pure (transform coins view)) =
        evalDist (channel (BinaryNTTSecurity.binaryVectorXor secret coins)))
    (hUniform : ∀ coins,
      evalDist (uniformView >>= fun view ↦ pure (transform coins view)) = evalDist uniformView) :
    ParityHidingCertificate where
  correlation := predictorParityCorrelation channel predictor frequency
  ordinaryDecisionAdvantage :=
    (actualRealParityDecisionGame transform channel predictor (parityBit frequency)).boolDistAdvantage
      (actualUniformParityDecisionGame transform uniformView predictor (parityBit frequency))
  ordinaryDecisionAdvantage_nonneg := abs_nonneg _
  advantage_eq := actualParityHiding_advantage_eq_sq_div_two
    transform channel uniformView predictor frequency selected hselected hChannel hUniform

/-- **Concrete split-ring parity-hiding reduction.**  This is the final instantiation used by the
transposition proof: the doubled ordinary Binary-NTT RLWE decision advantage is exactly half the
squared predictor correlation. -/
theorem splitParityHiding_advantage_eq_sq_div_two
    {Slot K Row : Type}
    [Fintype Slot] [DecidableEq Slot]
    [Field K] [Fintype K] [DecidableEq K] [SampleableType K]
    [Fintype Row] [DecidableEq Row]
    [Fintype (BinaryNTTSecurity.RLWEView (SplitRing Slot K) Row)]
    (errorSampler : ProbComp (Row → SplitRing Slot K))
    (predictor : BinaryNTTSecurity.RLWEView (SplitRing Slot K) Row → ProbComp Bool)
    (frequency : Slot → Bool) (selected : Slot) (hselected : frequency selected = true) :
    (actualRealParityDecisionGame
        (xorView (K := K) (Row := Row)) (splitChannel errorSampler) predictor
        (parityBit frequency)).boolDistAdvantage
      (actualUniformParityDecisionGame
        (xorView (K := K) (Row := Row))
        ($ᵗ (BinaryNTTSecurity.RLWEView (SplitRing Slot K) Row)) predictor
        (parityBit frequency)) =
      predictorParityCorrelation (splitChannel errorSampler) predictor frequency ^ 2 / 2 := by
  apply actualParityHiding_advantage_eq_sq_div_two
    (xorView (K := K) (Row := Row)) (splitChannel errorSampler)
    ($ᵗ (BinaryNTTSecurity.RLWEView (SplitRing Slot K) Row)) predictor
    frequency selected hselected
  · intro secret coins
    exact xorView_splitChannel_evalDist errorSampler secret coins
  · intro coins
    exact xorView_uniform_evalDist coins

/-! ## Quantitative transposition composition -/

/-- Two successive hidden-bit insertions have at most the sum of their individual signed gaps. -/
theorem twoInsertion_gap_le
    {Secret View Shift : Type} [Fintype Secret] [Fintype View]
    (joint : ProbComp (Secret × View)) (first second : Secret → Bool)
    (act : View → Shift → View) (firstShift secondShift : Shift)
    (response : View → ℝ) :
    let firstView := fun value : Secret × View ↦
      bitShift act value.2 firstShift (first value.1)
    let secondView := fun value : Secret × View ↦
      bitShift act (firstView value) secondShift (second value.1)
    |FormalProof4FHE.BoundedMoment.expectation joint (fun value ↦ response (secondView value)) -
        viewExpectation joint response| ≤
      |insertionGap joint first act firstShift response| +
        |FormalProof4FHE.BoundedMoment.expectation joint
            (fun value ↦ response (secondView value)) -
          FormalProof4FHE.BoundedMoment.expectation joint
            (fun value ↦ response (firstView value))| := by
  dsimp only
  have h := abs_sub_le
    (FormalProof4FHE.BoundedMoment.expectation joint
      (fun value ↦ response
        (bitShift act (bitShift act value.2 firstShift (first value.1))
          secondShift (second value.1))))
    (FormalProof4FHE.BoundedMoment.expectation joint
      (fun value ↦ response (bitShift act value.2 firstShift (first value.1))))
    (viewExpectation joint response)
  simpa [insertionGap, viewExpectation, add_comm] using h

/-- Retain the hidden secret while inserting one secret-dependent public shift. -/
def insertJoint {Secret View Shift : Type}
    (joint : ProbComp (Secret × View)) (bit : Secret → Bool)
    (act : View → Shift → View) (shift : Shift) : ProbComp (Secret × View) :=
  (fun value ↦ (value.1, bitShift act value.2 shift (bit value.1))) <$> joint

theorem expectation_insertJoint
    {Secret View Shift : Type} [Fintype Secret] [Fintype View]
    (joint : ProbComp (Secret × View)) (bit : Secret → Bool)
    (act : View → Shift → View) (shift : Shift)
    (observable : Secret × View → ℝ) :
    FormalProof4FHE.BoundedMoment.expectation (insertJoint joint bit act shift) observable =
      FormalProof4FHE.BoundedMoment.expectation joint
        (fun value ↦ observable
          (value.1, bitShift act value.2 shift (bit value.1))) := by
  unfold insertJoint
  rw [FormalProof4FHE.BoundedMoment.expectation_map]

theorem viewExpectation_insertJoint
    {Secret View Shift : Type} [Fintype Secret] [Fintype View]
    (joint : ProbComp (Secret × View)) (bit : Secret → Bool)
    (act : View → Shift → View) (shift : Shift) (response : View → ℝ) :
    viewExpectation (insertJoint joint bit act shift) response =
      FormalProof4FHE.BoundedMoment.expectation joint
        (fun value ↦ response (bitShift act value.2 shift (bit value.1))) := by
  unfold viewExpectation insertJoint
  rw [FormalProof4FHE.BoundedMoment.expectation_map]

theorem correlation_insertJoint
    {Secret View Shift : Type} [Fintype Secret] [Fintype View]
    (joint : ProbComp (Secret × View)) (insertedBit : Secret → Bool)
    (character : Secret → ℝ)
    (act : View → Shift → View) (shift : Shift) (response : View → ℝ) :
    correlation (insertJoint joint insertedBit act shift) character response =
      FormalProof4FHE.BoundedMoment.expectation joint
        (fun value ↦ character value.1 *
          response (bitShift act value.2 shift (insertedBit value.1))) := by
  unfold correlation insertJoint
  rw [FormalProof4FHE.BoundedMoment.expectation_map]

/-- **Quantitative transposition theorem.**  The seven premises are exactly the ordinary-view
tests and parity predictors constructed by two applications of the insertion argument.  If each
ordinary test is bounded by `epsilon` and each nonzero parity correlation by `delta`, inserting
both transposed secret coordinates changes every selected response by at most
`3*epsilon + 4*delta`. -/
theorem transposition_gap_le
    {Secret View Shift : Type} [Fintype Secret] [Fintype View]
    (joint : ProbComp (Secret × View)) (first second : Secret → Bool)
    (act : View → Shift → View) (firstShift secondShift : Shift)
    (response : View → ℝ) (epsilon delta : ℝ)
    (hBaseFirst :
      |viewExpectation joint (meanResponse act firstShift response)| ≤ epsilon)
    (hParityFirst :
      |correlation joint (fun secret ↦ bitCharacter (first secret))
        (meanResponse act firstShift response)| ≤ delta)
    (hBaseSecond :
      |viewExpectation joint (meanResponse act secondShift response)| ≤ epsilon)
    (hBaseNested :
      |viewExpectation joint
        (meanResponse act firstShift (meanResponse act secondShift response))| ≤ epsilon)
    (hParityNested :
      |correlation joint (fun secret ↦ bitCharacter (first secret))
        (meanResponse act firstShift (meanResponse act secondShift response))| ≤ delta)
    (hParitySecondEven :
      |correlation joint (fun secret ↦ bitCharacter (second secret))
        (evenResponse act firstShift (meanResponse act secondShift response))| ≤ delta)
    (hParityProductOdd :
      |correlation joint
        (fun secret ↦ bitCharacter (first secret) * bitCharacter (second secret))
        (oddResponse act firstShift (meanResponse act secondShift response))| ≤ delta) :
    let firstView := fun value : Secret × View ↦
      bitShift act value.2 firstShift (first value.1)
    let secondView := fun value : Secret × View ↦
      bitShift act (firstView value) secondShift (second value.1)
    |FormalProof4FHE.BoundedMoment.expectation joint (fun value ↦ response (secondView value)) -
        viewExpectation joint response| ≤ 3 * epsilon + 4 * delta := by
  dsimp only
  let jointFirst := insertJoint joint first act firstShift
  let secondMean := meanResponse act secondShift response
  have hFirstGap : |insertionGap joint first act firstShift response| ≤ epsilon + delta :=
    (abs_insertionGap_le joint first act firstShift response).trans
      (add_le_add hBaseFirst hParityFirst)
  have hNestedGap : |insertionGap joint first act firstShift secondMean| ≤ epsilon + delta :=
    (abs_insertionGap_le joint first act firstShift secondMean).trans
      (add_le_add hBaseNested hParityNested)
  have hFirstSecondMean :
      |viewExpectation jointFirst secondMean| ≤ 2 * epsilon + delta := by
    have htriangle :
        |viewExpectation jointFirst secondMean| ≤
          |viewExpectation jointFirst secondMean - viewExpectation joint secondMean| +
            |viewExpectation joint secondMean| := by
      have h := abs_add_le
        (viewExpectation jointFirst secondMean - viewExpectation joint secondMean)
        (viewExpectation joint secondMean)
      simpa using h
    have hdifference :
        viewExpectation jointFirst secondMean - viewExpectation joint secondMean =
          insertionGap joint first act firstShift secondMean := by
      simp [jointFirst, insertionGap, viewExpectation_insertJoint]
    rw [hdifference] at htriangle
    exact htriangle.trans (by linarith)
  have hSecondCorrelation :
      |correlation jointFirst (fun secret ↦ bitCharacter (second secret)) secondMean| ≤
        2 * delta := by
    rw [correlation_insertJoint]
    exact (abs_insertedCorrelation_le_two_parities
      joint first second act firstShift secondMean).trans (by linarith)
  have hSecondGap :
      |insertionGap jointFirst second act secondShift response| ≤
        2 * epsilon + 3 * delta :=
    (abs_insertionGap_le jointFirst second act secondShift response).trans (by
      change |viewExpectation jointFirst secondMean| +
        |correlation jointFirst (fun secret ↦ bitCharacter (second secret)) secondMean| ≤ _
      linarith)
  have htotal := twoInsertion_gap_le
    joint first second act firstShift secondShift response
  have hSecondEq :
      FormalProof4FHE.BoundedMoment.expectation joint
          (fun value ↦ response
            (bitShift act (bitShift act value.2 firstShift (first value.1))
              secondShift (second value.1))) -
        FormalProof4FHE.BoundedMoment.expectation joint
          (fun value ↦ response (bitShift act value.2 firstShift (first value.1))) =
        insertionGap jointFirst second act secondShift response := by
    unfold insertionGap viewExpectation
    rw [show FormalProof4FHE.BoundedMoment.expectation jointFirst
        (fun value ↦ response (bitShift act value.2 secondShift (second value.1))) =
      FormalProof4FHE.BoundedMoment.expectation joint
        (fun value ↦ response
          (bitShift act (bitShift act value.2 firstShift (first value.1))
            secondShift (second value.1))) by
      exact expectation_insertJoint joint first act firstShift _]
    rw [show FormalProof4FHE.BoundedMoment.expectation jointFirst
        (fun value ↦ response value.2) =
      FormalProof4FHE.BoundedMoment.expectation joint
        (fun value ↦ response (bitShift act value.2 firstShift (first value.1))) by
      exact expectation_insertJoint joint first act firstShift _]
  dsimp only at htotal
  rw [hSecondEq] at htotal
  exact htotal.trans (by linarith)

end

end FormalProof4FHE.RLWE.BinaryNTTSecurity.AutomorphismTransposition
