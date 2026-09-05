/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.CompactCoverBGV65536Instantiation
import FormalProof4FHE.RLWE.BinaryNTTAutomorphismFixedSubringBoundary
import FormalProof4FHE.RLWE.RegularCoverBGVInstantiation

/-!
# Consolidated Binary-NTT BGV theorem boundary

This module formalizes the previously uncovered exact algebra and finite
certificates from `sketch/binary_ntt_bgv_consolidated.tex`.  It deliberately
does not postulate the manuscript's missing chosen-mask automorphism synthesis
(CMAS) implication.  The unchanged scalar joint-automorphism theorem remains
a cryptographic research target; the imported staged-descent and full regular-
cover modules contain the two proved redesign frontiers.
-/

open OracleComp

namespace FormalProof4FHE.RLWE.BinaryNTTSecurity.BGVConsolidated

noncomputable section

/-! ## Concrete split-coordinate index-two assembly -/

/-- Two functions on the orbit set are exactly one function on paired
coordinates. -/
def pairFunctionsEquiv (Slot Value : Type) :
    ((Slot → Value) × (Slot → Value)) ≃ (Slot × Bool → Value) where
  toFun pair coordinate := if coordinate.2 then pair.2 coordinate.1 else pair.1 coordinate.1
  invFun value :=
    (fun slot => value (slot, false), fun slot => value (slot, true))
  left_inv pair := by
    rcases pair with ⟨left, right⟩
    apply Prod.ext <;> funext slot <;> rfl
  right_inv value := by
    funext coordinate
    rcases coordinate with ⟨slot, side⟩
    cases side <;> rfl

/-- Concrete NTT-coordinate assembly for an index-two tower.  The embedded
lower secret is constant on each two-point orbit. -/
def pairedIndexTwoAssembly (Slot K : Type) [CommRing K] :
    FixedPointFreeAutomorphism.IndexTwoAssembly
      (Slot → K) (Slot × Bool → K) where
  assemble := pairFunctionsEquiv Slot K
  embed secret coordinate := secret coordinate.1
  mul_fixed left right secret := by
    funext coordinate
    rcases coordinate with ⟨slot, side⟩
    cases side <;> rfl

/-- The concrete assembly also preserves addition exactly. -/
def pairedAdditiveIndexTwoAssembly (Slot K : Type) [CommRing K] :
    FixedPointFreeAutomorphism.AdditiveIndexTwoAssembly
      (Slot → K) (Slot × Bool → K) where
  toIndexTwoAssembly := pairedIndexTwoAssembly Slot K
  map_add left right := by
    funext coordinate
    rcases coordinate with ⟨slot, side⟩
    cases side <;> rfl

theorem pairedAssembly_real_equation
    {Slot K : Type} [CommRing K]
    (maskLeft maskRight errorLeft errorRight secret : Slot → K) :
    (pairedAdditiveIndexTwoAssembly Slot K).assemble
        (maskLeft * secret + errorLeft, maskRight * secret + errorRight) =
      (pairedAdditiveIndexTwoAssembly Slot K).assemble
          (maskLeft, maskRight) *
        (pairedAdditiveIndexTwoAssembly Slot K).embed secret +
      (pairedAdditiveIndexTwoAssembly Slot K).assemble
          (errorLeft, errorRight) :=
  FixedPointFreeAutomorphism.AdditiveIndexTwoAssembly.assemble_real_equation
    (pairedAdditiveIndexTwoAssembly Slot K)
    maskLeft maskRight errorLeft errorRight secret

theorem pairedAssembly_uniform_evalDist
    (Slot K : Type) [Fintype Slot] [DecidableEq Slot]
    [CommRing K] [Fintype K] [SampleableType K]
    [SampleableType (Slot → K)]
    [SampleableType ((Slot → K) × (Slot → K))]
    [SampleableType (Slot × Bool → K)] :
    evalDist
        (FixedPointFreeAutomorphism.assembleUniformSampler
          (pairedIndexTwoAssembly Slot K)) =
      evalDist ($ᵗ (Slot × Bool → K)) :=
  FixedPointFreeAutomorphism.assemble_uniform_evalDist
    (pairedIndexTwoAssembly Slot K)

/-! ## Exact scalar reduction frontier -/

/-- Small operational secret exposed by the public affine context. -/
def operationalSecret {R : Type} [CommRing R]
    (pivot : Rˣ) (offset witness : R) : R :=
  offset - (pivot : R) * witness

/-- Binary-witness diagonal-plus-automorphism row at the exact scalar
reduction frontier. -/
def witnessAutomorphismBody {R : Type} [CommRing R]
    (automorphism : R ≃+* R) (pivot : Rˣ)
    (gadget sourceMask witness error : R) : R :=
  sourceMask * witness +
    gadget * automorphism (pivot : R) * automorphism witness + error

/-- Public output mask used by the scalar affine transport. -/
def scalarTransportMask {R : Type} [CommRing R]
    (pivot : Rˣ) (sourceMask : R) : R :=
  -sourceMask * (pivot⁻¹ : Rˣ)

/-- Public output body used by the scalar affine transport. -/
def scalarAutomorphismBody {R : Type} [CommRing R]
    (automorphism : R ≃+* R) (pivot : Rˣ) (offset gadget : R)
    (sourceMask sourceBody : R) : R :=
  let targetMask := scalarTransportMask pivot sourceMask
  sourceBody + targetMask * offset - gadget * automorphism offset

/-- The exact affine transport exposes the implemented automorphism-key
phase.  It reduces the problem to pseudorandomness of the structured witness
row; it does not prove that structured row pseudorandom from ordinary
Binary-NTT RLWE. -/
theorem scalarAutomorphism_phase
    {R : Type} [CommRing R]
    (automorphism : R ≃+* R) (pivot : Rˣ)
    (offset gadget sourceMask witness error : R) :
    scalarAutomorphismBody automorphism pivot offset gadget sourceMask
        (witnessAutomorphismBody automorphism pivot gadget sourceMask
          witness error) -
      scalarTransportMask pivot sourceMask *
        operationalSecret pivot offset witness =
      -gadget * automorphism (operationalSecret pivot offset witness) + error := by
  simp only [scalarAutomorphismBody, scalarTransportMask,
    witnessAutomorphismBody, operationalSecret, map_sub, map_mul]
  have unit_cancel : (↑(pivot⁻¹) : R) * (pivot : R) = 1 := by simp
  change
    sourceMask * witness +
        gadget * automorphism (pivot : R) * automorphism witness + error +
        (-sourceMask * (pivot⁻¹ : Rˣ)) * offset -
        gadget * (automorphism offset) -
        (-sourceMask * (pivot⁻¹ : Rˣ)) *
          (offset - (pivot : R) * witness) =
      -gadget * (automorphism offset -
        automorphism (pivot : R) * automorphism witness) + error
  calc
    _ = sourceMask * witness -
          sourceMask * ((↑(pivot⁻¹) : R) * (pivot : R)) * witness -
          gadget * automorphism offset +
          gadget * automorphism (pivot : R) * automorphism witness + error := by
        ring
    _ = _ := by rw [unit_cancel]; ring

/-- Ordinary diagonal witness row used for the zero-message endpoint. -/
def witnessZeroBody {R : Type} [Ring R]
    (sourceMask witness error : R) : R :=
  sourceMask * witness + error

/-- Public body transport for the zero-message endpoint. -/
def scalarZeroBody {R : Type} [CommRing R]
    (pivot : Rˣ) (offset sourceMask sourceBody : R) : R :=
  sourceBody + scalarTransportMask pivot sourceMask * offset

theorem scalarZero_phase
    {R : Type} [CommRing R]
    (pivot : Rˣ) (offset sourceMask witness error : R) :
    scalarZeroBody pivot offset sourceMask
        (witnessZeroBody sourceMask witness error) -
      scalarTransportMask pivot sourceMask *
        operationalSecret pivot offset witness = error := by
  simp only [scalarZeroBody, scalarTransportMask, witnessZeroBody,
    operationalSecret]
  have unit_cancel : (↑(pivot⁻¹) : R) * (pivot : R) = 1 := by simp
  calc
    _ = sourceMask * witness -
          sourceMask * ((↑(pivot⁻¹) : R) * (pivot : R)) * witness + error := by
        ring
    _ = error := by rw [unit_cancel]; ring

/-! ## Exact uniform endpoint of the affine transport -/

/-- Common affine shape of both real and zero scalar transports.  The
automorphism-dependent public constant is supplied as `constant`. -/
def affineTransport {R : Type} [CommRing R]
    (pivot : Rˣ) (offset constant : R) : R × R → R × R
  | (sourceMask, sourceBody) =>
      let targetMask := scalarTransportMask pivot sourceMask
      (targetMask, sourceBody + targetMask * offset + constant)

def affineTransportInv {R : Type} [CommRing R]
    (pivot : Rˣ) (offset constant : R) : R × R → R × R
  | (targetMask, targetBody) =>
      (-targetMask * (pivot : R),
        targetBody - targetMask * offset - constant)

@[simp]
theorem affineTransportInv_affineTransport
    {R : Type} [CommRing R]
    (pivot : Rˣ) (offset constant : R) (source : R × R) :
    affineTransportInv pivot offset constant
      (affineTransport pivot offset constant source) = source := by
  rcases source with ⟨sourceMask, sourceBody⟩
  simp only [affineTransport, affineTransportInv, scalarTransportMask]
  have unit_cancel : (↑(pivot⁻¹) : R) * (pivot : R) = 1 := by simp
  apply Prod.ext
  · change -(-sourceMask * (↑(pivot⁻¹) : R)) * (pivot : R) = sourceMask
    calc
      _ = sourceMask * ((↑(pivot⁻¹) : R) * (pivot : R)) := by ring
      _ = sourceMask := by rw [unit_cancel, mul_one]
  · change sourceBody +
        (-sourceMask * (↑(pivot⁻¹) : R)) * offset + constant -
        (-sourceMask * (↑(pivot⁻¹) : R)) * offset - constant = sourceBody
    ring

@[simp]
theorem affineTransport_affineTransportInv
    {R : Type} [CommRing R]
    (pivot : Rˣ) (offset constant : R) (target : R × R) :
    affineTransport pivot offset constant
      (affineTransportInv pivot offset constant target) = target := by
  rcases target with ⟨targetMask, targetBody⟩
  simp only [affineTransport, affineTransportInv, scalarTransportMask]
  have unit_cancel : (pivot : R) * (↑(pivot⁻¹) : R) = 1 := by simp
  apply Prod.ext
  · change -(-targetMask * (pivot : R)) * (↑(pivot⁻¹) : R) = targetMask
    calc
      _ = targetMask * ((pivot : R) * (↑(pivot⁻¹) : R)) := by ring
      _ = targetMask := by rw [unit_cancel, mul_one]
  · change targetBody - targetMask * offset - constant +
        (-(-targetMask * (pivot : R)) * (↑(pivot⁻¹) : R)) * offset +
        constant = targetBody
    rw [show -(-targetMask * (pivot : R)) * (↑(pivot⁻¹) : R) = targetMask by
      calc
        _ = targetMask * ((pivot : R) * (↑(pivot⁻¹) : R)) := by ring
        _ = targetMask := by rw [unit_cancel, mul_one]]
    ring

theorem affineTransport_bijective
    {R : Type} [CommRing R]
    (pivot : Rˣ) (offset constant : R) :
    Function.Bijective (affineTransport pivot offset constant) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨affineTransportInv pivot offset constant,
      affineTransportInv_affineTransport pivot offset constant,
      affineTransport_affineTransportInv pivot offset constant⟩

theorem affineTransport_uniform_evalDist
    {R : Type} [CommRing R] [Fintype R]
    [SampleableType R] [SampleableType (R × R)]
    (pivot : Rˣ) (offset constant : R) :
    evalDist (affineTransport pivot offset constant <$> ($ᵗ (R × R))) =
      evalDist ($ᵗ (R × R)) :=
  evalDist_map_bijective_uniform_cross
    (α := R × R) (β := R × R)
    (affineTransport pivot offset constant)
    (affineTransport_bijective pivot offset constant)

/-- Product of the affine transport over a complete finite row family. -/
def affineTransportBatch {Row R : Type} [CommRing R]
    (pivot : Rˣ) (offset : R) (constant : Row → R)
    (source : Row → R × R) : Row → R × R :=
  fun row => affineTransport pivot offset (constant row) (source row)

def affineTransportBatchInv {Row R : Type} [CommRing R]
    (pivot : Rˣ) (offset : R) (constant : Row → R)
    (target : Row → R × R) : Row → R × R :=
  fun row => affineTransportInv pivot offset (constant row) (target row)

theorem affineTransportBatch_bijective
    {Row R : Type} [CommRing R]
    (pivot : Rˣ) (offset : R) (constant : Row → R) :
    Function.Bijective (affineTransportBatch pivot offset constant) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨affineTransportBatchInv pivot offset constant, ?_, ?_⟩
  · intro source
    funext row
    simp [affineTransportBatch, affineTransportBatchInv]
  · intro target
    funext row
    simp [affineTransportBatch, affineTransportBatchInv]

theorem affineTransportBatch_uniform_evalDist
    {Row R : Type} [Finite Row] [DecidableEq Row]
    [CommRing R] [Fintype R] [SampleableType R]
    [SampleableType (Row → R × R)]
    (pivot : Rˣ) (offset : R) (constant : Row → R) :
    evalDist (affineTransportBatch pivot offset constant <$>
        ($ᵗ (Row → R × R))) =
      evalDist ($ᵗ (Row → R × R)) :=
  evalDist_map_bijective_uniform_cross
    (α := Row → R × R) (β := Row → R × R)
    (affineTransportBatch pivot offset constant)
    (affineTransportBatch_bijective pivot offset constant)

/-- Exact public constant used to transport a structured witness row into an
automorphism-key row under the small operational secret. -/
def automorphismTransportConstant {Row R : Type} [CommRing R]
    (automorphism : Row → R ≃+* R) (gadget : Row → R) (offset : R) :
    Row → R :=
  fun row => -gadget row * automorphism row offset

theorem affineTransportBatch_automorphism_phase
    {Row R : Type} [CommRing R]
    (automorphism : Row → R ≃+* R) (pivot : Rˣ)
    (offset : R) (gadget sourceMask error : Row → R) (witness : R)
    (row : Row) :
    let source := fun index =>
      (sourceMask index,
        witnessAutomorphismBody (automorphism index) pivot (gadget index)
          (sourceMask index) witness (error index))
    let target := affineTransportBatch pivot offset
      (automorphismTransportConstant automorphism gadget offset) source
    (target row).2 - (target row).1 *
        operationalSecret pivot offset witness =
      -gadget row * automorphism row
        (operationalSecret pivot offset witness) + error row := by
  simpa [affineTransportBatch, affineTransport,
    automorphismTransportConstant, scalarAutomorphismBody, sub_eq_add_neg]
    using scalarAutomorphism_phase (automorphism row) pivot offset
      (gadget row) (sourceMask row) witness (error row)

/-- Source problem at the exact CMAS frontier. -/
def structuredWitnessProblem
    {Row R : Type} [Fintype R] [SampleableType (Row → R × R)]
    (realSource : ProbComp (Row → R × R)) :
    DecisionProblem (Row → R × R) where
  real := realSource
  random := $ᵗ (Row → R × R)

/-- Scalar automorphism-key problem obtained by exact affine transport from a
structured witness source. -/
def transportedScalarProblem
    {Row R : Type} [CommRing R] [Fintype R]
    [SampleableType (Row → R × R)]
    (pivot : Rˣ) (offset : R) (constant : Row → R)
    (realSource : ProbComp (Row → R × R)) :
    DecisionProblem (Row → R × R) where
  real := affineTransportBatch pivot offset constant <$> realSource
  random := $ᵗ (Row → R × R)

/-- **Exact scalar reduction frontier.**  The implemented scalar
automorphism rows are an exact public image of the structured CMAS source, and
the source-uniform endpoint maps to the canonical joint-uniform table.  This
theorem isolates, rather than assumes, the missing computational implication
from ordinary Binary-NTT RLWE to the structured source. -/
def exactScalarFrontierReduction
    {Row R : Type} [Finite Row] [DecidableEq Row]
    [CommRing R] [Fintype R] [SampleableType R]
    [SampleableType (Row → R × R)]
    (pivot : Rˣ) (offset : R) (constant : Row → R)
    (realSource : ProbComp (Row → R × R)) :
    ExactMapReduction (structuredWitnessProblem realSource)
      (transportedScalarProblem pivot offset constant realSource) where
  transform := affineTransportBatch pivot offset constant
  realLaw := by simp [structuredWitnessProblem, transportedScalarProblem]
  randomLaw := by
    simpa [structuredWitnessProblem, transportedScalarProblem] using
      affineTransportBatch_uniform_evalDist pivot offset constant

/-! ## Exact completion of one arbitrary finite orbit -/

/-- One anchor bit and one completion bit for each remaining point of an orbit
of length `orbitTail + 1`. -/
abbrev OrbitCompletionSource (orbitTail : ℕ) :=
  Bool × (Fin orbitTail → Bool)

def completeOrbit {orbitTail : ℕ}
    (source : OrbitCompletionSource orbitTail) : Fin (orbitTail + 1) → Bool :=
  Fin.cases source.1 (fun index => xor source.1 (source.2 index))

def recoverOrbit {orbitTail : ℕ}
    (completed : Fin (orbitTail + 1) → Bool) :
    OrbitCompletionSource orbitTail :=
  (completed 0, fun index => xor (completed 0) (completed index.succ))

@[simp]
theorem recoverOrbit_completeOrbit {orbitTail : ℕ}
    (source : OrbitCompletionSource orbitTail) :
    recoverOrbit (completeOrbit source) = source := by
  rcases source with ⟨anchor, coins⟩
  apply Prod.ext
  · rfl
  · funext index
    simp [recoverOrbit, completeOrbit]

@[simp]
theorem completeOrbit_recoverOrbit {orbitTail : ℕ}
    (completed : Fin (orbitTail + 1) → Bool) :
    completeOrbit (recoverOrbit completed) = completed := by
  funext coordinate
  refine Fin.cases ?_ (fun index => ?_) coordinate
  · rfl
  · simp [completeOrbit, recoverOrbit]

/-- Long-orbit completion is a literal equivalence, not an entropy estimate. -/
def orbitCompletionEquiv (orbitTail : ℕ) :
    OrbitCompletionSource orbitTail ≃ (Fin (orbitTail + 1) → Bool) where
  toFun := completeOrbit
  invFun := recoverOrbit
  left_inv := recoverOrbit_completeOrbit
  right_inv := completeOrbit_recoverOrbit

theorem completeOrbit_uniform_evalDist
    (orbitTail : ℕ)
    [SampleableType (OrbitCompletionSource orbitTail)]
    [SampleableType (Fin (orbitTail + 1) → Bool)] :
    evalDist (orbitCompletionEquiv orbitTail <$>
        ($ᵗ (OrbitCompletionSource orbitTail))) =
      evalDist ($ᵗ (Fin (orbitTail + 1) → Bool)) :=
  evalDist_map_bijective_uniform_cross
    (α := OrbitCompletionSource orbitTail)
    (β := Fin (orbitTail + 1) → Bool)
    (orbitCompletionEquiv orbitTail)
    (orbitCompletionEquiv orbitTail).bijective

/-! ## Generic Fourier counterexample -/

/-- Delta response concentrated at the hidden point. -/
def deltaResponse {Secret : Type} [DecidableEq Secret]
    (hidden candidate : Secret) : ℝ :=
  if candidate = hidden then 1 else 0

/-- Normalized finite Fourier coefficient of a real response. -/
def normalizedCoefficient {Secret : Type} [Fintype Secret]
    (response character : Secret → ℝ) : ℝ :=
  (∑ candidate, response candidate * character candidate) /
    Fintype.card Secret

/-- A delta response has maximal value at the hidden point while each
normalized character coefficient has magnitude only `1 / |Secret|`. -/
theorem delta_normalizedCoefficient
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (hidden : Secret) (character : Secret → ℝ) :
    normalizedCoefficient (deltaResponse hidden) character =
      character hidden / Fintype.card Secret := by
  simp [normalizedCoefficient, deltaResponse]

theorem abs_delta_normalizedCoefficient
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (hidden : Secret) (character : Secret → ℝ)
    (hcharacter : |character hidden| = 1) :
    |normalizedCoefficient (deltaResponse hidden) character| =
      1 / Fintype.card Secret := by
  rw [delta_normalizedCoefficient, abs_div, hcharacter]
  norm_num

theorem boolVector_card (dimension : ℕ) :
    Fintype.card (Fin dimension → Bool) = 2 ^ dimension := by
  simp

/-- Specialization of the delta counterexample to an `N`-bit secret space. -/
theorem abs_delta_boolVector_coefficient
    (dimension : ℕ) (hidden : Fin dimension → Bool)
    (character : (Fin dimension → Bool) → ℝ)
    (hcharacter : |character hidden| = 1) :
    |normalizedCoefficient (deltaResponse hidden) character| =
      1 / (2 ^ dimension : ℕ) := by
  rw [abs_delta_normalizedCoefficient hidden character hcharacter,
    boolVector_card]

/-! ## Finite core of the narrow-noise affine barrier -/

def integerSupport {Index : Type} [Fintype Index] [DecidableEq Index]
    (coefficients : Index → ℤ) : Finset Index :=
  Finset.univ.filter (fun index => coefficients index ≠ 0)

/-- An integral coefficient tuple with squared energy at most `budget` has at
most `budget` nonzero coefficient positions.  This is the deterministic
sparsity step used by the manuscript's chosen-mask counting barrier. -/
theorem integerSupport_card_le_energy
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (coefficients : Index → ℤ) (budget : ℕ)
    (henergy : ∑ index, (coefficients index).natAbs ^ 2 ≤ budget) :
    (integerSupport coefficients).card ≤ budget := by
  let support := integerSupport coefficients
  calc
    support.card = ∑ _index ∈ support, 1 := by simp
    _ ≤ ∑ index ∈ support, (coefficients index).natAbs ^ 2 := by
      apply Finset.sum_le_sum
      intro index hindex
      have nonzero : coefficients index ≠ 0 :=
        (Finset.mem_filter.mp hindex).2
      have positive : 0 < (coefficients index).natAbs := Int.natAbs_pos.mpr nonzero
      nlinarith
    _ ≤ ∑ index, (coefficients index).natAbs ^ 2 := by
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ ≤ budget := henergy

/-- Every individual squared coefficient is bounded by the total energy. -/
theorem coefficient_square_le_energy
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (coefficients : Index → ℤ) (budget : ℕ)
    (henergy : ∑ index, (coefficients index).natAbs ^ 2 ≤ budget)
    (index : Index) :
    (coefficients index).natAbs ^ 2 ≤ budget := by
  calc
    (coefficients index).natAbs ^ 2 ≤
        ∑ candidate, (coefficients candidate).natAbs ^ 2 := by
      exact Finset.single_le_sum
        (s := Finset.univ)
        (f := fun candidate => (coefficients candidate).natAbs ^ 2)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ index)
    _ ≤ budget := henergy

/-! ## Concrete trace-order certificates -/

def traceCyclotomicModulus : ℕ := 131072

def traceExponents : List ℕ :=
  [5, 25, 625, 128481, 28609, 61313, 7937, 81409,
   31745, 63489, 126977, 122881, 114689, 98305, 65537, 131071]

def traceDyadicOrderExponents : List ℕ :=
  [15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 1]

@[simp] theorem traceExponents_length : traceExponents.length = 16 := by decide

@[simp] theorem traceDyadicOrderExponents_length :
    traceDyadicOrderExponents.length = 16 := by decide

/-- Executable exact-order certificate for a positive power-of-two order.
The first conjunct gives an order dividing `2^power`; the second excludes all
proper divisors because every divisor of a power of two divides its half. -/
def exactDyadicOrderCheck (value power : ℕ) : Bool :=
  decide (0 < power ∧
    (value : ZMod traceCyclotomicModulus) ^ (2 ^ power) = 1 ∧
    (value : ZMod traceCyclotomicModulus) ^ (2 ^ (power - 1)) ≠ 1)

theorem traceDyadicOrders_checked :
    (traceExponents.zip traceDyadicOrderExponents).all
      (fun pair => exactDyadicOrderCheck pair.1 pair.2) = true := by
  native_decide

def traceCycleLengths : List ℕ :=
  traceDyadicOrderExponents.map (fun power => 2 ^ power)

def traceCycleCounts : List ℕ :=
  traceCycleLengths.map (fun length => 65536 / length)

theorem traceCycleLengths_eq :
    traceCycleLengths =
      [32768, 16384, 8192, 4096, 2048, 1024, 512, 256,
       128, 64, 32, 16, 8, 4, 2, 2] := by
  decide

theorem traceCycleCounts_eq :
    traceCycleCounts =
      [2, 4, 8, 16, 32, 64, 128, 256,
       512, 1024, 2048, 4096, 8192, 16384, 32768, 32768] := by
  decide

/-- Natural NTT coordinate `slot` is the odd residue `2*slot+1`. -/
def naturalOddLabel (slot : Fin 65536) : ZMod traceCyclotomicModulus :=
  2 * slot.val + 1

/-- No selected trace exponent fixes a natural NTT coordinate. -/
theorem traceExponents_no_fixed_coordinate :
    ∀ exponent ∈ traceExponents, ∀ slot : Fin 65536,
      (exponent : ZMod traceCyclotomicModulus) * naturalOddLabel slot ≠
        naturalOddLabel slot := by
  native_decide

/-- The consolidation uses exactly the executable trace list. -/
theorem traceExponents_eq_implementation :
    traceExponents =
      CompactCoverBGV65536.concreteTraceExponents := by
  rfl

/-! ## Explicit research boundary -/

/-- The diagonal-plus-permutation source family named CMAS in the manuscript.
This is a data definition, not a hardness axiom. -/
def chosenMaskAutomorphismRow
    {Row R : Type} [CommRing R]
    (automorphism : Row → R ≃+* R)
    (weight mask : Row → R) (witness : R) (error : Row → R) :
    Row → R × R :=
  fun row =>
    (mask row,
      mask row * witness +
        weight row * automorphism row witness + error row)

/-- Removing the automorphism term gives an ordinary diagonal common-secret
row family. -/
def chosenMaskZeroRow
    {Row R : Type} [Ring R]
    (mask : Row → R) (witness : R) (error : Row → R) :
    Row → R × R :=
  fun row => (mask row, mask row * witness + error row)

/-- Any claimed proof for the unchanged scalar implementation must bound this
exact gap.  Keeping it as a proposition prevents the consolidation layer from
silently manufacturing a CMAS reduction. -/
def ChosenMaskAutomorphismSecure
    {Row R : Type} [CommRing R] [Fintype R]
    [SampleableType (Row → R × R)]
    (real zero : ProbComp (Row → R × R))
    (allowed : Distinguisher (Row → R × R) → Prop)
    (bound : ℝ) : Prop :=
  HardAgainst ⟨real, zero⟩ allowed bound

end

end FormalProof4FHE.RLWE.BinaryNTTSecurity.BGVConsolidated
