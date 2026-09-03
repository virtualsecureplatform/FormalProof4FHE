/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import Mathlib
import FormalProof4FHE.NumberTheory.LucasCertificate

/-!
# Exact noise recurrence for the N=65536 scalar compact-cover BGV cycle

This file is the integer counterpart of the executable parameter certificate.
It deliberately contains no floating-point logarithms and no claimed security
bits.  Every selected correctness bound is computed from the concrete RNS
primes, gadget dimensions, bounded secret, and CBD support.
-/

namespace FormalProof4FHE.RLWE.BinaryNTTSecurity.CompactCoverBGVExactNoise

def degree : ℕ := 65536
def plaintextPrime : ℕ := 65537
def plaintextSquare : ℕ := plaintextPrime ^ 2
def secretWeight : ℕ := 32
def cbdEta : ℕ := 20
def phaseLiftDigits : ℕ := 2
def traceDigits : ℕ := 23
def digitErrorBound : ℕ := 23

/-- The available ordered RNS primes certified for the TFHEpp backend. -/
def availableRNSPrimes : List ℕ :=
  [2301972608560791553, 2295217002959732737, 2291839200159203329,
   2280016890357350401, 2274950186156556289, 2271009416222605313,
   2265942712021811201, 2252994467953115137, 2244549960951791617,
   2230475782616252417, 2227097979815723009, 2217527538547556353,
   2203453360212017153, 2179808740608311297, 2156164121004605441,
   2152786318204076033, 2124637961532997633, 2114504553131409409,
   2109437848930615297, 2102682243329556481, 2078474656592429057,
   2065526412523732993, 2057081905522409473]

structure RNSPrimeData where
  value : ℕ
  generator : ℕ
  factors : List ℕ

def rnsPrimeData : List RNSPrimeData :=
  [{ value := 2301972608560791553, generator := 5,
     factors := List.replicate 17 2 ++ [3, 29, 47, 65537, 65537] },
   { value := 2295217002959732737, generator := 5,
     factors := List.replicate 17 2 ++ [3, 3, 3, 151, 65537, 65537] },
   { value := 2291839200159203329, generator := 7,
     factors := List.replicate 17 2 ++ [3, 23, 59, 65537, 65537] },
   { value := 2280016890357350401, generator := 7,
     factors := List.replicate 18 2 ++ [3, 3, 3, 3, 5, 5, 65537, 65537] },
   { value := 2274950186156556289, generator := 7,
     factors := List.replicate 17 2 ++ [3, 3, 449, 65537, 65537] },
   { value := 2271009416222605313, generator := 3,
     factors := List.replicate 18 2 ++ [2017, 65537, 65537] },
   { value := 2265942712021811201, generator := 3,
     factors := List.replicate 17 2 ++ [5, 5, 7, 23, 65537, 65537] },
   { value := 2252994467953115137, generator := 7,
     factors := List.replicate 18 2 ++ [3, 23, 29, 65537, 65537] },
   { value := 2244549960951791617, generator := 7,
     factors := List.replicate 17 2 ++ [3, 3, 443, 65537, 65537] },
   { value := 2230475782616252417, generator := 3,
     factors := List.replicate 18 2 ++ [7, 283, 65537, 65537] },
   { value := 2227097979815723009, generator := 3,
     factors := List.replicate 19 2 ++ [23, 43, 65537, 65537] },
   { value := 2217527538547556353, generator := 5,
     factors := List.replicate 17 2 ++ [3, 13, 101, 65537, 65537] },
   { value := 2203453360212017153, generator := 3,
     factors := List.replicate 18 2 ++ [19, 103, 65537, 65537] },
   { value := 2179808740608311297, generator := 5,
     factors := List.replicate 22 2 ++ [11, 11, 65537, 65537] },
   { value := 2156164121004605441, generator := 3,
     factors := List.replicate 18 2 ++ [5, 383, 65537, 65537] },
   { value := 2152786318204076033, generator := 3,
     factors := List.replicate 21 2 ++ [239, 65537, 65537] },
   { value := 2124637961532997633, generator := 11,
     factors := List.replicate 18 2 ++ [3, 17, 37, 65537, 65537] },
   { value := 2114504553131409409, generator := 14,
     factors := List.replicate 19 2 ++ [3, 313, 65537, 65537] },
   { value := 2109437848930615297, generator := 5,
     factors := List.replicate 17 2 ++ [3, 1249, 65537, 65537] },
   { value := 2102682243329556481, generator := 13,
     factors := List.replicate 17 2 ++ [3, 3, 5, 83, 65537, 65537] },
   { value := 2078474656592429057, generator := 3,
     factors := List.replicate 19 2 ++ [13, 71, 65537, 65537] },
   { value := 2065526412523732993, generator := 11,
     factors := List.replicate 17 2 ++ [3, 1223, 65537, 65537] },
   { value := 2057081905522409473, generator := 5,
     factors := List.replicate 18 2 ++ [3, 3, 7, 29, 65537, 65537] }]

theorem plaintextPrime_prime : Nat.Prime plaintextPrime := by
  norm_num [plaintextPrime]

theorem rnsPrimeData_values :
    rnsPrimeData.map RNSPrimeData.value = availableRNSPrimes := by
  native_decide

theorem rnsPrimeData_checked :
    rnsPrimeData.all (fun data =>
      FormalProof4FHE.NumberTheory.LucasCertificate.check
        data.value data.generator data.factors) = true := by
  native_decide

theorem availableRNSPrimes_prime {prime : ℕ}
    (member : prime ∈ availableRNSPrimes) :
    Nat.Prime prime := by
  rw [← rnsPrimeData_values] at member
  obtain ⟨data, dataMember, rfl⟩ := List.mem_map.mp member
  have all := List.all_eq_true.mp rnsPrimeData_checked
  exact FormalProof4FHE.NumberTheory.LucasCertificate.prime_of_check
    (all data dataMember)

/-- The selected 1219-bit bootstrap chain uses the first twenty certified
primes; the three trailing backend primes are deliberately inactive. -/
def rnsPrimes : List ℕ := availableRNSPrimes.take 20

theorem rnsPrimes_prime {prime : ℕ} (member : prime ∈ rnsPrimes) :
    Nat.Prime prime :=
  availableRNSPrimes_prime (List.mem_of_mem_take member)

def RNSPrimeData.negacyclicRootCheck (data : RNSPrimeData) : Bool :=
  decide ((((data.generator : ZMod data.value) ^
    ((data.value - 1) / (2 * degree))) ^ degree) = -1)

theorem rnsPrimeData_negacyclicRoots_checked :
    rnsPrimeData.all RNSPrimeData.negacyclicRootCheck = true := by
  native_decide

theorem rnsPrimeCongruences_checked :
    rnsPrimes.all (fun prime =>
      (prime - 1) % (2 * degree * plaintextSquare) = 0) = true := by
  native_decide

theorem rnsPrime_congruent {prime : ℕ} (member : prime ∈ rnsPrimes) :
    (prime - 1) % (2 * degree * plaintextSquare) = 0 := by
  have all := List.all_eq_true.mp rnsPrimeCongruences_checked
  exact of_decide_eq_true (all prime member)

/-- Coefficients of the concrete odd digit-removal polynomial modulo `p²`. -/
def digitRemovalCoefficients : List ℕ :=
  [0, 3014703, 0, 3238870490, 0, 260547141, 0, 3852544443,
   0, 2026537897, 0, 171292757, 0, 2299505656, 0, 2807800136,
   0, 2729394369, 0, 3420676537, 0, 2310160525, 0, 1557412513,
   0, 1505867716, 0, 2804512912, 0, 1980057043, 0, 3719467179,
   0, 215909847, 0, 2015916591, 0, 1507214369, 0, 3371949771,
   0, 2412504583, 0, 3638586939, 0, 2132554192, 0, 2971959138,
   0, 2127803462, 0, 2375152868, 0, 2601708476, 0, 3154282838,
   0, 1616683414, 0, 2905606412, 0, 313867077, 0, 3801553684,
   0, 321425772, 0, 3116444645, 0, 2385654620, 0, 2629295321,
   0, 2712500045, 0, 3077573173, 0, 303006977, 0, 3601109967,
   0, 965236460, 0, 2224409375, 0, 212541920, 0, 4104818155,
   0, 2393009638, 0, 1896907154, 0, 1287511956]

/-! ## Exact digit-removal semantics -/

/-- Executable Horner interpretation of a low-to-high natural coefficient list. -/
def coefficientEval {R : Type} [Semiring R] : List ℕ → R → R
  | [], _ => 0
  | coefficient :: rest, value => coefficient + value * coefficientEval rest value

/-- Executable derivative evaluation, defined without constructing a sparse polynomial. -/
def coefficientDerivativeEval {R : Type} [Semiring R] : List ℕ → R → R
  | [], _ => 0
  | _ :: rest, value =>
      coefficientEval rest value + value * coefficientDerivativeEval rest value

/-- First-order Taylor evaluation is exact whenever the shift squares to zero. -/
theorem coefficientEval_add_of_sq_eq_zero {R : Type} [CommRing R]
    (coefficients : List ℕ) (value shift : R) (hshift : shift ^ 2 = 0) :
    coefficientEval coefficients (value + shift) =
      coefficientEval coefficients value +
        coefficientDerivativeEval coefficients value * shift := by
  induction coefficients with
  | nil => simp [coefficientEval, coefficientDerivativeEval]
  | cons coefficient rest ih =>
      simp only [coefficientEval, coefficientDerivativeEval]
      rw [ih]
      have hzero : shift * shift = 0 := by simpa [pow_two] using hshift
      calc
        _ = coefficient + value * coefficientEval rest value +
              (coefficientEval rest value +
                value * coefficientDerivativeEval rest value) * shift +
              coefficientDerivativeEval rest value * (shift * shift) := by ring
        _ = _ := by rw [hzero]; simp

/-- The two finite conditions needed at every permitted centered carry: the
polynomial vanishes there, and its derivative is one modulo `p`.  They are
checked on exactly the 47 implementation-supported carry values. -/
theorem digitRemoval_centered_conditions (carry : ℤ)
    (lower : -(digitErrorBound : ℤ) ≤ carry)
    (upper : carry ≤ digitErrorBound) :
    coefficientEval digitRemovalCoefficients
        (carry : ZMod plaintextSquare) = 0 ∧
      (coefficientDerivativeEval digitRemovalCoefficients
        (carry : ZMod plaintextSquare) - 1) * plaintextPrime = 0 := by
  norm_num [digitErrorBound] at lower upper
  interval_cases carry <;>
    native_decide

/-- A multiple of `p` squares to zero modulo `p²`. -/
theorem plaintextPrime_mul_sq_zero (message : ZMod plaintextSquare) :
    ((plaintextPrime : ZMod plaintextSquare) * message) ^ 2 = 0 := by
  have hp : ((plaintextPrime : ZMod plaintextSquare)) ^ 2 = 0 := by
    native_decide
  rw [mul_pow, hp, zero_mul]

/-- Concrete bounded low-digit removal, proved for every scalar message rather
than checked by enumerating all 65537 messages. -/
theorem digitRemovalPolynomial_correct (message : ZMod plaintextSquare)
    (carry : ℤ) (lower : -(digitErrorBound : ℤ) ≤ carry)
    (upper : carry ≤ digitErrorBound) :
    coefficientEval digitRemovalCoefficients
        ((plaintextPrime : ZMod plaintextSquare) * message + carry) =
      (plaintextPrime : ZMod plaintextSquare) * message := by
  let shift : ZMod plaintextSquare := plaintextPrime * message
  have hshift : shift ^ 2 = 0 := plaintextPrime_mul_sq_zero message
  have conditions := digitRemoval_centered_conditions carry lower upper
  rw [add_comm, coefficientEval_add_of_sq_eq_zero _ _ shift hshift,
    conditions.1, zero_add]
  change coefficientDerivativeEval digitRemovalCoefficients
      (carry : ZMod plaintextSquare) *
        ((plaintextPrime : ZMod plaintextSquare) * message) = _
  calc
    _ = ((coefficientDerivativeEval digitRemovalCoefficients
          (carry : ZMod plaintextSquare) - 1) * plaintextPrime) * message +
        plaintextPrime * message := by ring
    _ = _ := by rw [conditions.2]; simp

structure ErrorState where
  limbs : ℕ
  bound : ℕ
  deriving DecidableEq, Repr

def modulus (limbs : ℕ) : ℕ := (rnsPrimes.take limbs).prod

def centeredAbs (value : ℕ) : ℕ :=
  let reduced := value % plaintextSquare
  min reduced (plaintextSquare - reduced)

def dropOnce (state : ErrorState) : ErrorState :=
  if state.limbs = 0 then state else
    let dropped := rnsPrimes.getD (state.limbs - 1) 1
    { limbs := state.limbs - 1
      bound := (state.bound + dropped - 1) / dropped + (secretWeight + 2) / 2 }

def modulusDrop (state : ErrorState) (targetLimbs : ℕ) : ErrorState :=
  Nat.iterate dropOnce (state.limbs - targetLimbs) state

def keySwitchError (limbs rows : ℕ) (gadgetBits : ℕ := 0) : ℕ :=
  let bits := if gadgetBits = 0 then (Nat.log2 (modulus limbs) + rows) / rows
    else gadgetBits
  rows * degree * 2 ^ (bits - 1) * cbdEta

def add (left right : ErrorState) : ErrorState :=
  let limbs := min left.limbs right.limbs
  { limbs := limbs
    bound := (modulusDrop left limbs).bound + (modulusDrop right limbs).bound }

def scale (state : ErrorState) (scalar : ℕ) : ErrorState :=
  { state with bound := centeredAbs scalar * state.bound }

def multiplyAndDrop (left right : ErrorState) : ErrorState :=
  let limbs := min left.limbs right.limbs
  let leftError := (modulusDrop left limbs).bound
  let rightError := (modulusDrop right limbs).bound
  let messageBound := plaintextSquare / 2
  let raw := messageBound * (leftError + rightError) +
    plaintextSquare * leftError * rightError +
    (messageBound * messageBound + plaintextSquare - 1) / plaintextSquare + 1
  modulusDrop { limbs := limbs, bound := raw } (limbs - 1)

private def babyPowers (value : ErrorState) : List ErrorState :=
  let square := multiplyAndDrop value value
  [{ limbs := value.limbs, bound := 0 }, value, square,
    multiplyAndDrop square value]

private def giantPowers (value : ErrorState) : List ErrorState :=
  let first := (babyPowers value).getD 3 value
  List.iterate (fun state => multiplyAndDrop state state) first 6

private def levelZeroEval (coefficients : List ℕ) (value : ErrorState) : ErrorState :=
  let powers := babyPowers value
  (List.range (min (coefficients.length - 1) 3)).foldl
    (fun accumulator index =>
      add accumulator (scale (powers.getD (index + 1) value)
        (coefficients.getD (index + 1) 0)))
    { limbs := value.limbs, bound := 0 }

private def genericBSGSEval (value : ErrorState) : List ℕ → ℕ → ErrorState
  | coefficients, 0 => levelZeroEval coefficients value
  | coefficients, level + 1 =>
      let split := min coefficients.length (3 * 2 ^ level)
      let lower := genericBSGSEval value (coefficients.take split) level
      if split = coefficients.length then lower else
        let upper := genericBSGSEval value (coefficients.drop split) level
        add lower (multiplyAndDrop upper ((giantPowers value).getD level value))

def digitPolynomialError (value : ErrorState) : ErrorState :=
  let square := multiplyAndDrop value value
  let rec oddCoefficients : List ℕ → List ℕ
    | _even :: odd :: rest => odd :: oddCoefficients rest
    | _ => []
  let oddCoefficients := oddCoefficients digitRemovalCoefficients
  let inner := genericBSGSEval square oddCoefficients 6
  multiplyAndDrop inner value

def acceptedInputError : ℕ :=
  6 * (rnsPrimes.getD 0 1) / plaintextSquare

def quotientFactor : ℕ :=
  (rnsPrimes.getD 0 1 - 1) / plaintextSquare

def phaseLiftState : ErrorState :=
  { limbs := 20
    bound := acceptedInputError + quotientFactor * digitErrorBound +
      keySwitchError 20 phaseLiftDigits 31 }

def traceStep (state : ErrorState) : ErrorState :=
  { state with bound := 2 * state.bound + keySwitchError state.limbs traceDigits }

def traceState : ErrorState :=
  let firstEight := Nat.iterate traceStep 8 phaseLiftState
  let afterFirstDrop := modulusDrop firstEight 19
  let secondEight := Nat.iterate traceStep 8 afterFirstDrop
  modulusDrop secondEight 18

def projectedState : ErrorState :=
  scale traceState (plaintextSquare - 65538)

def outputState : ErrorState := digitPolynomialError projectedState
def outputCapacity : ℕ := modulus outputState.limbs / (2 * plaintextPrime)
def oneLimbAdditionState : ErrorState :=
  add (modulusDrop outputState 1) (modulusDrop outputState 1)
def twoLimbInputState : ErrorState := modulusDrop outputState 2
def multiplicationState : ErrorState := multiplyAndDrop twoLimbInputState twoLimbInputState
def bootstrapInputCapacity : ℕ := (rnsPrimes.getD 0 1) / (2 * plaintextPrime)

structure ExactCycleCertificate : Prop where
  primeCount : rnsPrimes.length = 20
  polynomialDegree : digitRemovalCoefficients.length - 1 = 93
  carryStrict : secretWeight + 1 + 12 < 2 * digitErrorBound
  outputLevel : outputState.limbs = 10
  outputFits : outputState.bound < outputCapacity
  additionLevel : oneLimbAdditionState.limbs = 1
  additionCloses : oneLimbAdditionState.bound ≤ acceptedInputError
  multiplicationLevel : multiplicationState.limbs = 1
  multiplicationCloses : multiplicationState.bound ≤ acceptedInputError
  multiplicationFits : multiplicationState.bound < bootstrapInputCapacity

/-- The exact, machine-computed correctness certificate. -/
theorem selectedExactCycleCertificate : ExactCycleCertificate := by
  constructor <;> native_decide

@[simp] theorem acceptedInputError_eq : acceptedInputError = 3215720448 := by
  native_decide

@[simp] theorem projectedState_eq :
    projectedState = { limbs := 18, bound := 268909426566 } := by
  native_decide

@[simp] theorem multiplicationState_eq :
    multiplicationState = { limbs := 1, bound := 18 } := by
  native_decide

@[simp] theorem oneLimbAdditionState_eq :
    oneLimbAdditionState = { limbs := 1, bound := 36 } := by
  native_decide

/-! ## Unlimited normalized gate schedule -/

inductive BinaryGate where
  | add
  | multiply
  deriving DecidableEq, Fintype

def BinaryGate.preBootstrapState : BinaryGate → ErrorState
  | .add => oneLimbAdditionState
  | .multiply => multiplicationState

theorem everyBinaryGate_accepted (gate : BinaryGate) :
    gate.preBootstrapState.limbs = 1 ∧
      gate.preBootstrapState.bound ≤ acceptedInputError := by
  cases gate
  · exact ⟨selectedExactCycleCertificate.additionLevel,
      selectedExactCycleCertificate.additionCloses⟩
  · exact ⟨selectedExactCycleCertificate.multiplicationLevel,
      selectedExactCycleCertificate.multiplicationCloses⟩

/-- A circuit whose every internal binary gate is immediately followed by the
scalar bootstrap. -/
inductive NormalizedScalarCircuit (inputs : ℕ) where
  | input : Fin inputs → NormalizedScalarCircuit inputs
  | gate : BinaryGate → NormalizedScalarCircuit inputs →
      NormalizedScalarCircuit inputs → NormalizedScalarCircuit inputs

def NormalizedScalarCircuit.Refreshable {inputs : ℕ} :
    NormalizedScalarCircuit inputs → Prop
  | .input _ => True
  | .gate kind left right =>
      left.Refreshable ∧ right.Refreshable ∧
        kind.preBootstrapState.limbs = 1 ∧
        kind.preBootstrapState.bound ≤ acceptedInputError

/-- Addition/multiplication circuits of arbitrary depth remain refreshable; no
fixed multiplicative-depth parameter appears in the theorem. -/
theorem normalizedScalarCircuit_refreshable {inputs : ℕ}
    (circuit : NormalizedScalarCircuit inputs) : circuit.Refreshable := by
  induction circuit with
  | input index => simp [NormalizedScalarCircuit.Refreshable]
  | gate kind left right leftIH rightIH =>
      exact ⟨leftIH, rightIH, everyBinaryGate_accepted kind⟩

end FormalProof4FHE.RLWE.BinaryNTTSecurity.CompactCoverBGVExactNoise
