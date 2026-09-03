/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.CompactCoverBGVAdaptiveSecurity
import FormalProof4FHE.RLWE.CompactCoverBGVExactNoise
import FormalProof4FHE.RLWE.CompactCoverBGVScalarSecurity
import FormalProof4FHE.RLWE.CenteredBinomial
import FormalProof4FHE.TFHE.JointSubsetKeyBRKCenteredMixture

/-!
# Concrete mixed-error source for scalar Binary-NTT BGV

This module fixes the source distributions left abstract by the joint security
theorem. Every evaluation row receives an independent `p²*CBD(20)` coefficient
error, every online encryption row receives `p*CBD(20)`, and the operational
secret is sampled from the exact-weight-32 signed-ternary law. A backend records
the public coefficient-to-NTT embedding and the binary split-slot embedding.
Thus CRT residues of one error remain coherent instead of being resampled per
limb.
-/

open OracleComp

namespace FormalProof4FHE.RLWE.BinaryNTTSecurity.CompactCoverBGVMixedSource

open FormalProof4FHE.RLWE.BinaryNTTSecurity.CompactCoverBGVExactNoise
open FormalProof4FHE.RLWE.BinaryNTTSecurity.CompactCoverBGVScalarSecurity

set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

/-- Public representation boundary. `coefficientNTT` is applied once to a
single integer coefficient vector, so all RNS limbs see the same CBD error. -/
structure Backend (R : Type) [CommRing R] where
  binaryNTT : (Fin degree → Bool) → R
  coefficientNTT : (Fin degree → ℤ) → R
  binary_idempotent : ∀ bits, binaryNTT bits ^ 2 = binaryNTT bits

/-- The selected modulus at an RNS limb. -/
def rnsModulus (limb : Fin 20) : ℕ :=
  rnsPrimes.get ⟨limb, by
    rw [selectedExactCycleCertificate.primeCount]
    exact limb.isLt⟩

theorem rnsModulus_mem (limb : Fin 20) : rnsModulus limb ∈ rnsPrimes := by
  unfold rnsModulus
  exact List.get_mem rnsPrimes _

instance instNeZeroRNSModulus (limb : Fin 20) : NeZero (rnsModulus limb) :=
  ⟨(rnsPrimes_prime (rnsModulus_mem limb)).ne_zero⟩

/-- Exact heterogeneous split RNS/NTT carrier used by the implementation. -/
abbrev ConcreteSplitRNS :=
  (limb : Fin 20) → Fin degree → ZMod (rnsModulus limb)

noncomputable instance instSampleableConcreteSplitRNS :
    SampleableType ConcreteSplitRNS := SampleableType.ofFintype _

noncomputable instance instSampleableConcreteSplitRNSTable (queries : ℕ) :
    SampleableType (ScalarRow queries → ConcreteSplitRNS) :=
  SampleableType.ofFintype _

def binarySplitEncoding (bits : Fin degree → Bool) : ConcreteSplitRNS :=
  fun _limb slot => if bits slot then 1 else 0

theorem binarySplitEncoding_idempotent (bits : Fin degree → Bool) :
    binarySplitEncoding bits ^ 2 = binarySplitEncoding bits := by
  funext limb slot
  by_cases value : bits slot <;> simp [binarySplitEncoding, value]

/-- Concrete split-RNS backend. Only the public coefficient-to-NTT transform
is supplied; the binary NTT representation and all moduli are now fixed. -/
def concreteRNSBackend
    (coefficientNTT : (Fin degree → ℤ) → ConcreteSplitRNS) :
    Backend ConcreteSplitRNS where
  binaryNTT := binarySplitEncoding
  coefficientNTT := coefficientNTT
  binary_idempotent := binarySplitEncoding_idempotent

theorem rnsPrimeData_length : rnsPrimeData.length = 23 := by native_decide

def rnsDatum (limb : Fin 20) : RNSPrimeData :=
  rnsPrimeData.get ⟨limb, by rw [rnsPrimeData_length]; omega⟩

def rnsGenerator (limb : Fin 20) : ℕ := (rnsDatum limb).generator

/-- Canonical mathematical negacyclic NTT: evaluation at the odd powers of a
primitive `2N`-th root. Concrete backend ordering may differ by a public slot
permutation. -/
def mathematicalCoefficientNTT
    (coefficients : Fin degree → ℤ) : ConcreteSplitRNS :=
  fun limb slot =>
    let modulus := rnsModulus limb
    let root : ZMod modulus :=
      (rnsGenerator limb) ^ ((modulus - 1) / (2 * degree))
    ∑ coefficient : Fin degree,
      (coefficients coefficient : ZMod modulus) *
        root ^ ((2 * slot.val + 1) * coefficient.val)

def mathematicalRNSBackend : Backend ConcreteSplitRNS :=
  concreteRNSBackend mathematicalCoefficientNTT

noncomputable def concreteUnitSampler : ProbComp ConcreteSplitRNSˣ := by
  letI : Fintype ConcreteSplitRNSˣ := Fintype.ofFinite _
  letI : SampleableType ConcreteSplitRNSˣ := SampleableType.ofFintype _
  exact $ᵗ ConcreteSplitRNSˣ

theorem concreteUnitSampler_neverFails : NeverFail concreteUnitSampler := by
  unfold concreteUnitSampler
  infer_instance

abbrev RowCoins (queries : ℕ) :=
  ScalarRow queries → CenteredBinomial.CoinTable degree cbdEta

def errorScale {queries : ℕ} : ScalarRow queries → ℤ
  | .evaluation _ => plaintextSquare
  | .encryption _ => plaintextPrime

def errorCoefficients {queries : ℕ} (coins : RowCoins queries)
    (row : ScalarRow queries) : Fin degree → ℤ :=
  fun coefficient => errorScale row *
    CenteredBinomial.signedWeight (coins row coefficient)

def errorTableFromCoins {queries : ℕ} {R : Type} [CommRing R]
    (backend : Backend R) (coins : RowCoins queries) : ScalarRow queries → R :=
  fun row => backend.coefficientNTT (errorCoefficients coins row)

/-- Exact mixed `p²*CBD(20)` / `p*CBD(20)` row sampler. -/
noncomputable def mixedErrorSampler (queries : ℕ) (R : Type)
    [CommRing R] [Fintype R] [SampleableType R]
    (backend : Backend R) : ProbComp (ScalarRow queries → R) :=
  errorTableFromCoins backend <$> ($ᵗ (RowCoins queries))

theorem mixedErrorSampler_neverFails (queries : ℕ) (R : Type)
    [CommRing R] [Fintype R] [SampleableType R]
    (backend : Backend R) : NeverFail (mixedErrorSampler queries R backend) := by
  simp [mixedErrorSampler]

/-- Every sampled coefficient obeys the exact implementation support bound. -/
theorem errorCoefficients_natAbs_le {queries : ℕ} (coins : RowCoins queries)
    (row : ScalarRow queries) (coefficient : Fin degree) :
    (errorCoefficients coins row coefficient).natAbs ≤
      (errorScale row).natAbs * cbdEta := by
  simp only [errorCoefficients, Int.natAbs_mul]
  exact Nat.mul_le_mul_left _ (by
    rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
    exact CenteredBinomial.abs_signedWeight_le (coins row coefficient))

abbrev OperationalSecret :=
  FormalProof4FHE.TFHE.JointSubsetKeyBRKCenteredMixture.FixedWeightTernarySecret
    degree secretWeight

def ternaryCoefficient (secret : OperationalSecret) (index : Fin degree) : ℤ :=
  if member : index ∈ secret.1.1 then
    if secret.2 ⟨index, member⟩ = 0 then -1 else 1
  else 0

theorem ternaryCoefficient_support_card (secret : OperationalSecret) :
    (Finset.univ.filter fun index => ternaryCoefficient secret index ≠ 0).card =
      secretWeight := by
  have supportEq :
      (Finset.univ.filter fun index => ternaryCoefficient secret index ≠ 0) =
        secret.1.1 := by
    ext index
    by_cases member : index ∈ secret.1.1
    · by_cases sign : secret.2 ⟨index, member⟩ = 0
      · simp [ternaryCoefficient, member, sign]
      · simp [ternaryCoefficient, member, sign]
    · simp [ternaryCoefficient, member]
  rw [supportEq]
  exact (Finset.mem_powersetCard.mp secret.1.property).2

noncomputable def operationalSecretSampler : ProbComp OperationalSecret :=
  FormalProof4FHE.TFHE.JointSubsetKeyBRKCenteredMixture.fixedWeightTernarySampler
    degree secretWeight (by native_decide)

theorem operationalSecretSampler_neverFails : NeverFail operationalSecretSampler := by
  constructor
  simp [operationalSecretSampler,
    FormalProof4FHE.TFHE.JointSubsetKeyBRKCenteredMixture.fixedWeightTernarySampler,
    FormalProof4FHE.TFHE.JointSubsetKeyBRKCenteredMixture.fixedWeightTernarySeedSampler,
    FormalProof4FHE.TFHE.JointSubsetKeyBRKCenteredMixture.fixedWeightSupportSampler]

structure ContextInputs (R : Type) [CommRing R] where
  unitSampler : ProbComp Rˣ
  unitSampler_neverFails : NeverFail unitSampler

noncomputable def concreteContextInputs : ContextInputs ConcreteSplitRNS where
  unitSampler := concreteUnitSampler
  unitSampler_neverFails := concreteUnitSampler_neverFails

/-- Actual key-generation normal form: `offset = pivot*witness + secret`, so
the advertised operational secret is `offset-pivot*witness`. -/
noncomputable def contextWitnessSampler (R : Type)
    [CommRing R] [Fintype R] [SampleableType R]
    (backend : Backend R) (inputs : ContextInputs R) :
    ProbComp (CompilerContext R × R) := do
  let bits ← $ᵗ (Fin degree → Bool)
  let pivot ← inputs.unitSampler
  let operational ← operationalSecretSampler
  let witness := backend.binaryNTT bits
  let secret := backend.coefficientNTT (ternaryCoefficient operational)
  return (⟨pivot, pivot * witness + secret⟩, witness)

theorem contextWitnessSampler_idempotent
    (R : Type) [CommRing R] [Fintype R] [SampleableType R]
    (backend : Backend R) (inputs : ContextInputs R)
    (sample : CompilerContext R × R)
    (member : sample ∈ support (contextWitnessSampler R backend inputs)) :
    sample.2 ^ 2 = sample.2 := by
  rw [contextWitnessSampler, mem_support_bind_iff] at member
  obtain ⟨bits, _, member⟩ := member
  rw [mem_support_bind_iff] at member
  obtain ⟨pivot, _, member⟩ := member
  rw [mem_support_bind_iff] at member
  obtain ⟨operational, _, member⟩ := member
  obtain rfl := eq_of_mem_support_pure member
  exact backend.binary_idempotent bits

theorem contextWitnessSampler_neverFails
    (R : Type) [CommRing R] [Fintype R] [SampleableType R]
    (backend : Backend R) (inputs : ContextInputs R) :
    NeverFail (contextWitnessSampler R backend inputs) := by
  unfold contextWitnessSampler
  apply NeverFail.bind_of_forall

/-- Fully instantiated source specification, up to the public representation
backend and a total product-unit sampler. -/
noncomputable def sourceSpec (queries : ℕ) (R : Type)
    [CommRing R] [Fintype R] [SampleableType R]
    [SampleableType (ScalarRow queries → R)]
    (backend : Backend R) (inputs : ContextInputs R) :
    BinaryNTTSourceSpec queries R where
  contextWitnessSampler := contextWitnessSampler R backend inputs
  errorSampler := mixedErrorSampler queries R backend
  witness_idempotent := contextWitnessSampler_idempotent R backend inputs
  source_neverFails := by
    unfold commonSecretSource
    apply NeverFail.bind_of_forall
      (hx := contextWitnessSampler_neverFails R backend inputs)

/-- Fully concrete 20-limb source problem used by the selected N=65536
instantiation. -/
noncomputable def concreteSourceSpec (queries : ℕ) :
    BinaryNTTSourceSpec queries ConcreteSplitRNS :=
  sourceSpec queries ConcreteSplitRNS mathematicalRNSBackend
    concreteContextInputs

/-! ## Removing the conditional-context formulation -/

def publicContextSampler {queries : ℕ} {R : Type}
    [CommRing R] [Fintype R] [SampleableType R]
    [SampleableType (ScalarRow queries → R)]
    (source : BinaryNTTSourceSpec queries R) : ProbComp (CompilerContext R) :=
  Prod.fst <$> commonSecretSource queries R source.contextWitnessSampler
    source.errorSampler

noncomputable def randomContextSampler (R : Type)
    [CommRing R] [Fintype R] [SampleableType R]
    (inputs : ContextInputs R) : ProbComp (CompilerContext R) := do
  let pivot ← inputs.unitSampler
  let offset ← $ᵗ R
  return ⟨pivot, offset⟩

noncomputable def fullyUniformViewSampler (queries : ℕ) (R : Type)
    [CommRing R] [Fintype R] [SampleableType R]
    [SampleableType (Transcript queries R)]
    (inputs : ContextInputs R) : ProbComp (ContextualView queries R) := do
  let context ← randomContextSampler R inputs
  let rows ← $ᵗ (Transcript queries R)
  return (context, rows)

noncomputable def ordinaryFullProblem (queries : ℕ) (R : Type)
    [CommRing R] [Fintype R] [SampleableType R]
    [SampleableType (ScalarRow queries → R)]
    [SampleableType (Transcript queries R)]
    (source : BinaryNTTSourceSpec queries R) (inputs : ContextInputs R) :
    DecisionProblem (ContextualView queries R) where
  real := commonSecretSource queries R source.contextWitnessSampler source.errorSampler
  random := fullyUniformViewSampler queries R inputs

noncomputable def contextProblem (queries : ℕ) (R : Type)
    [CommRing R] [Fintype R] [SampleableType R]
    [SampleableType (ScalarRow queries → R)]
    (source : BinaryNTTSourceSpec queries R) (inputs : ContextInputs R) :
    DecisionProblem (CompilerContext R) where
  real := publicContextSampler source
  random := randomContextSampler R inputs

noncomputable def contextPullback {queries : ℕ} {R : Type}
    [CommRing R] [Fintype R] [SampleableType R]
    [SampleableType (Transcript queries R)]
    (distinguisher : Distinguisher (ContextualView queries R)) :
    Distinguisher (CompilerContext R) :=
  fun context => do
    let rows ← $ᵗ (Transcript queries R)
    distinguisher (context, rows)

theorem contextualRandom_evalDist_eq_publicContext
    (queries : ℕ) (R : Type)
    [CommRing R] [Fintype R] [SampleableType R]
    [SampleableType (ScalarRow queries → R)]
    [SampleableType (Transcript queries R)]
    (source : BinaryNTTSourceSpec queries R) :
    evalDist (contextualRandomRows queries R
      (commonSecretSource queries R source.contextWitnessSampler source.errorSampler)) =
      evalDist (do
        let context ← publicContextSampler source
        let rows ← $ᵗ (Transcript queries R)
        return (context, rows)) := by
  simp [contextualRandomRows, commonSecretSource, publicContextSampler,
    map_eq_bind_pure_comp, bind_assoc]

/-- The conditional-context source gap is bounded by two ordinary gaps: the
full real-to-uniform Binary-NTT transcript and the single public context row.
Thus preserving `(pivot,offset)` in the compiler theorem introduces no hidden
auxiliary-input assumption. -/
theorem contextual_advantage_le_full_add_context
    (queries : ℕ) (R : Type)
    [CommRing R] [Fintype R] [SampleableType R]
    [SampleableType (ScalarRow queries → R)]
    [SampleableType (Transcript queries R)]
    (source : BinaryNTTSourceSpec queries R) (inputs : ContextInputs R)
    (distinguisher : Distinguisher (ContextualView queries R)) :
    advantage (source.problem queries R) distinguisher ≤
      advantage (ordinaryFullProblem queries R source inputs) distinguisher +
      advantage (contextProblem queries R source inputs)
        (contextPullback distinguisher) := by
  let realSource := commonSecretSource queries R source.contextWitnessSampler
    source.errorSampler
  let conditionalRandom := contextualRandomRows queries R realSource
  let fullUniform := fullyUniformViewSampler queries R inputs
  let realOutput := realSource >>= distinguisher
  let conditionalOutput := conditionalRandom >>= distinguisher
  let uniformOutput := fullUniform >>= distinguisher
  have triangle := ProbComp.boolDistAdvantage_triangle
    realOutput uniformOutput conditionalOutput
  have hconditional :
      evalDist conditionalOutput =
        evalDist ((publicContextSampler source) >>= contextPullback distinguisher) := by
    simpa [conditionalOutput, conditionalRandom, realSource,
      contextPullback, bind_assoc] using
      (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        (contextualRandom_evalDist_eq_publicContext queries R source) distinguisher)
  have huniform :
      evalDist uniformOutput =
        evalDist ((randomContextSampler R inputs) >>= contextPullback distinguisher) := by
    simp [uniformOutput, fullUniform, fullyUniformViewSampler,
      contextPullback, bind_assoc]
  unfold advantage ProbComp.boolDistAdvantage
  change realOutput.boolDistAdvantage conditionalOutput ≤
    realOutput.boolDistAdvantage uniformOutput +
      ((publicContextSampler source >>= contextPullback distinguisher).boolDistAdvantage
        (randomContextSampler R inputs >>= contextPullback distinguisher))
  have hcondProb := evalDist_ext_iff.mp hconditional true
  have hunifProb := evalDist_ext_iff.mp huniform true
  unfold ProbComp.boolDistAdvantage at triangle ⊢
  rw [hcondProb, hunifProb] at triangle ⊢
  rw [abs_sub_comm
    (Pr[= true | publicContextSampler source >>= contextPullback distinguisher]).toReal
    (Pr[= true | randomContextSampler R inputs >>= contextPullback distinguisher]).toReal]
  exact triangle

end FormalProof4FHE.RLWE.BinaryNTTSecurity.CompactCoverBGVMixedSource
