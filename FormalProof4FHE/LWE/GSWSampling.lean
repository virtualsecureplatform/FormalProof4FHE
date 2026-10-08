/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.GSWPublicKey
import FormalProof4FHE.Probability.FiniteProduct

/-!
# Probabilistic one-key GSW generation and public encryption

Draw one binary secret, independent uniform public/control masks, and an independent
error vector. Split that vector between ordinary public-key samples and fresh self-key
controls. Materialize both public tables before returning them. Public encryption draws
binary selection coins and takes only the stored public key and message bits.

The scalar noise sampler is explicit. The exact distribution of the original error vector
and the correctness tail bound below do not assert that an arbitrary such sampler is secure.
A concrete efficient implementation compatible with ordinary LWE, its approximation/tail
guarantees, and the ordinary-LWE proof for the complete joint key view remain obligations.
-/

open Matrix OracleComp
open scoped BigOperators ENNReal

namespace FormalProof4FHE.LWE.GSWSampling

open GSWGadget GSWAccumulator GSWPublicKey

/-- Number of scalar errors drawn once, when generating the public and bootstrap keys. -/
def errorCount {Q : ℕ} (params : Parameters Q) (dimension samples : ℕ) : ℕ :=
  samples + dimension * ((dimension + 1) * params.levels)

/-- The one secret and all independent uniform mask challenges, prior to materialization. -/
abbrev KeySeed {Q : ℕ} (params : Parameters Q) (dimension samples : ℕ) :=
  (Fin dimension → Bool) ×
    Matrix (Fin dimension) (Fin samples) (ZMod Q) ×
    (Fin dimension → Matrix (Fin dimension) (Fin ((dimension + 1) * params.levels)) (ZMod Q))

/-- Original private key-generation draws, retained only for distribution/correctness proofs. -/
structure KeyDraws {Q : ℕ} (params : Parameters Q) (dimension samples : ℕ) where
  errors : Fin (errorCount params dimension samples) → ZMod Q
  seed : KeySeed params dimension samples

/-- Operational key pair. The secret stays with the client; both public tables contain data. -/
structure KeyMaterial {Q : ℕ} (params : Parameters Q) (dimension samples : ℕ) where
  secretBits : Fin dimension → Bool
  publicKey : PublicKey Q dimension samples
  controls : Vector (StoredCiphertext params (dimension + 1)) dimension

def publicErrors {Q dimension samples : ℕ} (params : Parameters Q)
    (draws : KeyDraws params dimension samples) : Fin samples → ZMod Q :=
  fun index ↦ draws.errors (Fin.castAdd (dimension * ((dimension + 1) * params.levels)) index)

def controlErrors {Q dimension samples : ℕ} (params : Parameters Q)
    (draws : KeyDraws params dimension samples) :
    Fin dimension → Fin ((dimension + 1) * params.levels) → ZMod Q :=
  fun index column ↦ draws.errors (Fin.natAdd samples (finProdFinEquiv (index, column)))

/-- Uniform masks/secret and original scalar errors are sampled independently. -/
def sampleKeyDraws {Q : ℕ} [NeZero Q] (params : Parameters Q) (dimension samples : ℕ)
    (errorSampler : ProbComp (ZMod Q)) : ProbComp (KeyDraws params dimension samples) := do
  let errors ← ProbComp.sampleIID (errorCount params dimension samples) errorSampler
  let seed ← $ᵗ (KeySeed params dimension samples)
  return ⟨errors, seed⟩

/-- Complete the two public tables privately before returning any matrix views. -/
def materialFromDraws {Q dimension samples : ℕ} [NeZero Q] (params : Parameters Q)
    (draws : KeyDraws params dimension samples) : KeyMaterial params dimension samples where
  secretBits := draws.seed.1
  publicKey := freshPublicKey (GSWSelfKey.binaryEmbed draws.seed.1)
    draws.seed.2.1 (publicErrors params draws)
  controls := storedFreshBootKey params draws.seed.1 draws.seed.2.2 (controlErrors params draws)

/-- Actual probabilistic key generation uses exactly one underlying secret. -/
def generateKeys {Q : ℕ} [NeZero Q] (params : Parameters Q) (dimension samples : ℕ)
    (errorSampler : ProbComp (ZMod Q)) : ProbComp (KeyMaterial params dimension samples) :=
  materialFromDraws params <$> sampleKeyDraws params dimension samples errorSampler

/-- Uniform independent public-encryption selection coins, returned as finite data. -/
def sampleInputCoins (samples columns inputs : ℕ) : ProbComp (Vector (SelectorCoins samples columns) inputs) := do
  let coins ← $ᵗ (Fin inputs → Fin samples → Fin columns → Bool)
  return Vector.ofFn fun index ↦ Vector.ofFn fun sample ↦ Vector.ofFn fun column ↦ coins index sample column

/-- Public encryption samples coins without receiving the client secret or control table. -/
def encryptInputs {Q dimension samples inputs : ℕ} [NeZero Q] (params : Parameters Q)
    (key : PublicKey Q dimension samples) (messages : Vector Bool inputs) :
    ProbComp (Vector (StoredCiphertext params (dimension + 1)) inputs) :=
  (fun coins ↦ encryptInputsStored params key coins messages) <$>
    sampleInputCoins samples ((dimension + 1) * params.levels) inputs

/-- Operational correctness experiment: generate keys, publicly encrypt, evaluate, then decrypt. -/
def correctnessExperiment {factor p dimension samples inputs wires : ℕ} [NeZero factor] [NeZero p]
    (params : Parameters (factor * p)) (level : Fin params.levels) (oneCode : ZMod p)
    (errorSampler : ProbComp (ZMod (factor * p))) (messages : Vector Bool inputs)
    (program : GSWCircuit.Program inputs wires) (output : Fin wires) : ProbComp Bool := do
  let keys ← generateKeys params dimension samples errorSampler
  let ciphertexts ← encryptInputs params keys.publicKey messages
  return decide (decrypt params (GSWSelfKey.binaryEmbed keys.secretBits)
    (ciphertextView params (GSWCircuit.evaluate params level oneCode keys.controls ciphertexts program output)) level =
      (GSWCircuit.runBits messages program).get output)

/-- Key correctness event, defined on the actual original noise draws. -/
def GoodDraws {Q dimension samples : ℕ} [NeZero Q] (params : Parameters Q) (bound : ℕ)
    (draws : KeyDraws params dimension samples) : Prop :=
  ∀ coordinate, (LatticeCrypto.centeredRepr (draws.errors coordinate)).natAbs ≤ bound

/-- Every event depending only on the original errors has its independent-product probability.
Uniform masks and the one secret do not alter or condition that error law. -/
theorem probEvent_sampleKeyDraws_errors {Q : ℕ} [NeZero Q] (params : Parameters Q)
    (dimension samples : ℕ) (errorSampler : ProbComp (ZMod Q))
    (event : (Fin (errorCount params dimension samples) → ZMod Q) → Prop) :
    Pr[(fun draws : KeyDraws params dimension samples ↦ event draws.errors) |
      sampleKeyDraws params dimension samples errorSampler] =
      Pr[event | ProbComp.sampleIID (errorCount params dimension samples) errorSampler] := by
  classical
  have hconditional : ∀ errors,
      Pr[(fun draws : KeyDraws params dimension samples ↦ event draws.errors) |
        (do let seed ← $ᵗ (KeySeed params dimension samples); return ⟨errors, seed⟩)] =
        if event errors then 1 else 0 := by
    intro errors
    have h := probEvent_bind_of_const ($ᵗ (KeySeed params dimension samples))
      (my := fun seed ↦ pure (⟨errors, seed⟩ : KeyDraws params dimension samples))
      (p := fun draws ↦ event draws.errors) (r := if event errors then 1 else 0)
      (by intro seed _; simp)
    simpa using h
  rw [sampleKeyDraws, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  apply tsum_congr
  intro errors
  rw [hconditional]
  by_cases hevent : event errors <;> simp [hevent]

/-- Exact probability that all generated key errors fit the fixed correctness budget. -/
theorem probEvent_goodDraws {Q : ℕ} [NeZero Q] (params : Parameters Q)
    (dimension samples bound : ℕ) (errorSampler : ProbComp (ZMod Q)) :
    Pr[GoodDraws params bound | sampleKeyDraws params dimension samples errorSampler] =
      Pr[(fun error : ZMod Q ↦ (LatticeCrypto.centeredRepr error).natAbs ≤ bound) | errorSampler] ^
        errorCount params dimension samples := by
  unfold GoodDraws
  rw [probEvent_sampleKeyDraws_errors params dimension samples errorSampler
    (fun errors ↦ ∀ coordinate, (LatticeCrypto.centeredRepr (errors coordinate)).natAbs ≤ bound)]
  simpa only [ProbComp.sampleIID, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    FiniteProduct.probEvent_fin_mOfFn_forall (errorCount params dimension samples)
      (fun _ ↦ errorSampler) (fun _ error ↦ (LatticeCrypto.centeredRepr error).natAbs ≤ bound)

/-- A union bound on generated key errors; it charges each scalar draw once. -/
theorem probEvent_badDraws_le {Q : ℕ} [NeZero Q] (params : Parameters Q)
    (dimension samples bound : ℕ) (errorSampler : ProbComp (ZMod Q)) :
    Pr[(fun draws ↦ ¬ GoodDraws params bound draws) |
      sampleKeyDraws params dimension samples errorSampler] ≤
      errorCount params dimension samples *
        Pr[(fun error : ZMod Q ↦ bound < (LatticeCrypto.centeredRepr error).natAbs) | errorSampler] := by
  classical
  unfold GoodDraws
  rw [probEvent_sampleKeyDraws_errors params dimension samples errorSampler
    (fun errors ↦ ¬ ∀ coordinate, (LatticeCrypto.centeredRepr (errors coordinate)).natAbs ≤ bound)]
  have hevent : (fun errors : Fin (errorCount params dimension samples) → ZMod Q ↦
      ¬ ∀ coordinate, (LatticeCrypto.centeredRepr (errors coordinate)).natAbs ≤ bound) =
      (fun errors ↦ ∃ coordinate ∈ (Finset.univ : Finset (Fin (errorCount params dimension samples))),
        bound < (LatticeCrypto.centeredRepr (errors coordinate)).natAbs) := by
    funext errors
    simp
  rw [hevent]
  apply (probEvent_exists_finset_le_sum Finset.univ _ _).trans
  have hcoordinate : ∀ coordinate : Fin (errorCount params dimension samples),
      Pr[(fun errors ↦ bound < (LatticeCrypto.centeredRepr (errors coordinate)).natAbs) |
        ProbComp.sampleIID (errorCount params dimension samples) errorSampler] =
      Pr[(fun error : ZMod Q ↦ bound < (LatticeCrypto.centeredRepr error).natAbs) | errorSampler] := by
    intro coordinate
    simpa only [ProbComp.sampleIID] using
      FiniteProduct.probEvent_fin_mOfFn_apply (errorCount params dimension samples)
        (fun _ ↦ errorSampler) coordinate
        (fun error : ZMod Q ↦ bound < (LatticeCrypto.centeredRepr error).natAbs)
  simp only [hcoordinate, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact le_rfl

/-- Good original draws imply whole-circuit correctness for every encryption-coin choice. -/
theorem decrypt_from_goodDraws {dimension inputs wires : ℕ} (hdimension : 0 < dimension)
    (draws : KeyDraws (GSWBootstrapParameters.params dimension) dimension (sampleCount dimension))
    (coins : Vector (SelectorCoins (sampleCount dimension)
      ((dimension + 1) * (GSWBootstrapParameters.params dimension).levels)) inputs)
    (messages : Vector Bool inputs) (program : GSWCircuit.Program inputs wires) (output : Fin wires)
    (hgood : GoodDraws (GSWBootstrapParameters.params dimension) (GSWBootstrapParameters.keyBound dimension) draws) :
    let keys := materialFromDraws (GSWBootstrapParameters.params dimension) draws
    decrypt (GSWBootstrapParameters.params dimension) (GSWSelfKey.binaryEmbed keys.secretBits)
      (ciphertextView (GSWBootstrapParameters.params dimension)
        (GSWCircuit.evaluate (GSWBootstrapParameters.params dimension) (GSWBootstrapParameters.level dimension)
          (GSWBootstrapParameters.oneCode dimension) keys.controls
          (encryptInputsStored (GSWBootstrapParameters.params dimension) keys.publicKey coins messages)
          program output)) (GSWBootstrapParameters.level dimension) =
      (GSWCircuit.runBits messages program).get output := by
  apply decrypt_evaluate_freshPublicKey hdimension draws.seed.1 draws.seed.2.1 _ draws.seed.2.2 _
    coins messages program output
  · intro sample
    exact hgood _
  · intro index column
    exact hgood _

/-- The operational experiment can be wrong only if the original key noise exceeded its budget. -/
theorem correctness_failure_le_badDraws {dimension inputs wires : ℕ} (hdimension : 0 < dimension)
    (errorSampler : ProbComp
      (ZMod (GSWBootstrapParameters.factor dimension * GSWBootstrapParameters.lookupModulus dimension)))
    (messages : Vector Bool inputs) (program : GSWCircuit.Program inputs wires) (output : Fin wires) :
    Pr[= false | correctnessExperiment (dimension := dimension) (samples := sampleCount dimension)
      (GSWBootstrapParameters.params dimension) (GSWBootstrapParameters.level dimension)
      (GSWBootstrapParameters.oneCode dimension) errorSampler messages program output] ≤
    Pr[(fun draws ↦ ¬ GoodDraws (GSWBootstrapParameters.params dimension)
      (GSWBootstrapParameters.keyBound dimension) draws) |
      sampleKeyDraws (GSWBootstrapParameters.params dimension) dimension (sampleCount dimension) errorSampler] := by
  classical
  rw [← probEvent_eq_eq_probOutput]
  simp only [correctnessExperiment, generateKeys, encryptInputs, map_eq_bind_pure_comp,
    Function.comp_apply, bind_assoc, pure_bind]
  apply probEvent_bind_le_probEvent
  intro draws _ hnotbad
  have hgood : GoodDraws (GSWBootstrapParameters.params dimension)
      (GSWBootstrapParameters.keyBound dimension) draws := not_not.mp hnotbad
  have hcorrect := fun coins ↦ decrypt_from_goodDraws hdimension draws coins messages program output hgood
  simp only [probEvent_bind_eq_tsum, probEvent_pure]
  simp [hcorrect]

/-- Whole-circuit failure bound independent of the input count, circuit size, depth, and fanout. -/
theorem correctness_failure_le {dimension inputs wires : ℕ} (hdimension : 0 < dimension)
    (errorSampler : ProbComp
      (ZMod (GSWBootstrapParameters.factor dimension * GSWBootstrapParameters.lookupModulus dimension)))
    (messages : Vector Bool inputs) (program : GSWCircuit.Program inputs wires) (output : Fin wires) :
    Pr[= false | correctnessExperiment (dimension := dimension) (samples := sampleCount dimension)
      (GSWBootstrapParameters.params dimension) (GSWBootstrapParameters.level dimension)
      (GSWBootstrapParameters.oneCode dimension) errorSampler messages program output] ≤
    errorCount (GSWBootstrapParameters.params dimension) dimension (sampleCount dimension) *
      Pr[(fun error ↦ GSWBootstrapParameters.keyBound dimension <
        (LatticeCrypto.centeredRepr error).natAbs) | errorSampler] :=
  (correctness_failure_le_badDraws hdimension errorSampler messages program output).trans
    (probEvent_badDraws_le (GSWBootstrapParameters.params dimension) dimension (sampleCount dimension)
      (GSWBootstrapParameters.keyBound dimension) errorSampler)

/-- Only quadratically many key-noise draws are charged by the concrete family. -/
theorem errorCount_le (dimension : ℕ) :
    errorCount (GSWBootstrapParameters.params dimension) dimension (sampleCount dimension) ≤
      272 * (dimension + 1) ^ 2 := by
  unfold errorCount sampleCount GSWBootstrapParameters.params
  nlinarith

/-- Explicit quadratic prefactor for the actual probabilistic whole-circuit experiment. -/
theorem correctness_failure_le_dimension_bound {dimension inputs wires : ℕ}
    (hdimension : 0 < dimension)
    (errorSampler : ProbComp
      (ZMod (GSWBootstrapParameters.factor dimension * GSWBootstrapParameters.lookupModulus dimension)))
    (messages : Vector Bool inputs) (program : GSWCircuit.Program inputs wires) (output : Fin wires) :
    Pr[= false | correctnessExperiment (dimension := dimension) (samples := sampleCount dimension)
      (GSWBootstrapParameters.params dimension) (GSWBootstrapParameters.level dimension)
      (GSWBootstrapParameters.oneCode dimension) errorSampler messages program output] ≤
    (272 * (dimension + 1) ^ 2 : ℕ) *
      Pr[(fun error ↦ GSWBootstrapParameters.keyBound dimension <
        (LatticeCrypto.centeredRepr error).natAbs) | errorSampler] := by
  apply (correctness_failure_le hdimension errorSampler messages program output).trans
  have hcount : (errorCount (GSWBootstrapParameters.params dimension) dimension
      (sampleCount dimension) : ℝ≥0∞) ≤ (272 * (dimension + 1) ^ 2 : ℕ) := by
    exact_mod_cast errorCount_le dimension
  exact mul_le_mul_of_nonneg_right hcount (by positivity)

end FormalProof4FHE.LWE.GSWSampling
