/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.RecursiveFeatureCircuit
import FormalProof4FHE.LWE.RecursiveFeatureSecurityParameters

/-!
# Correctness of the sampled same-key recursive-feature evaluator

The experiment uses the actual completed public-key/control sampler, encrypts
each input with the actual public encryption algorithm, and evaluates a shared
NAND program with those same stored controls. Support bounds are derived from
the scalar sampler, rather than assumed for the generated controls or inputs.
Circuit size and depth do not enter the correctness margins.

This is correctness only. The joint cubic-control security reduction and strict
polynomial-time implementation/reduction classes remain unproved.
-/

open Matrix OracleComp

namespace FormalProof4FHE.LWE.RecursiveFeatureFHECorrectness

open RecursiveMultiplication RecursiveFeatureGSW RecursiveFeatureBootstrap
open RecursiveFeatureSecurityView

theorem sampleDraws_error_bound {q n samples : ℕ} [NeZero q] (params : Parameters q)
    (secretSampler : ProbComp (Fin n → Bool)) (errorSampler : ProbComp (ZMod q)) (bound : ℕ)
    (herror : ∀ error ∈ support errorSampler, (LatticeCrypto.centeredRepr error).natAbs ≤ bound)
    (draws : Draws params n samples) (hdraws : draws ∈ support (sampleDraws params secretSampler errorSampler)) :
    ∀ column, (LatticeCrypto.centeredRepr (draws.2.2 column)).natAbs ≤ bound := by
  simp only [sampleDraws, mem_support_bind_iff] at hdraws
  obtain ⟨bits, _, challenge, _, errors, herrors, hdraws⟩ := hdraws
  simp only [support_pure, Set.mem_singleton_iff] at hdraws
  subst draws
  intro column
  exact herror _ (TFHE.Native.KeySwitchRecovery.mem_support_mOfFn_apply _ _ errors herrors _)

theorem publicTable_phase_bound {q n samples : ℕ} [NeZero q] (params : Parameters q)
    (draws : Draws params n samples) (bound : ℕ)
    (herrors : ∀ column, (LatticeCrypto.centeredRepr (draws.2.2 column)).natAbs ≤ bound) :
    ∀ sample, (LatticeCrypto.centeredRepr
      (dotProduct (featureSecret (GSWSelfKey.binaryEmbed draws.1)) (publicTable params draws sample))).natAbs ≤
        (n + 1) * bound := by
  intro sample
  unfold publicTable
  rw [← decrypt_eq_dotProduct, decrypt_freshCiphertext, zero_add]
  have hterms : ∀ row, (LatticeCrypto.centeredRepr
      (errorsAt params draws.2.2 (publicColumn params sample) row *
        GSWSelfKey.binaryEmbed (R := ZMod q) draws.1 row)).natAbs ≤ bound := by
    intro row
    cases hb : draws.1 row <;> simp [GSWSelfKey.binaryEmbed, hb, LatticeCrypto.centeredRepr_eq_valMinAbs]
    simpa only [errorsAt, LatticeCrypto.centeredRepr_eq_valMinAbs] using
      herrors (.inr (publicColumn params sample, some row))
  have hsum := centered_sum_bound _ bound hterms
  calc
    _ ≤ (LatticeCrypto.centeredRepr (bodyErrorAt params draws.2.2 (publicColumn params sample))).natAbs +
        (LatticeCrypto.centeredRepr (dotProduct (errorsAt params draws.2.2 (publicColumn params sample))
          (GSWSelfKey.binaryEmbed draws.1))).natAbs := TFHE.NoiseBounds.centeredRepr_add_natAbs_le _ _
    _ ≤ bound + n * bound := Nat.add_le_add (herrors _)
      (by simpa only [dotProduct, Fintype.card_fin] using hsum)
    _ = _ := by ring

theorem keygen_noiseBounds {q n samples : ℕ} [NeZero q] (params : Parameters q)
    (secretSampler : ProbComp (Fin n → Bool)) (errorSampler : ProbComp (ZMod q)) (bound : ℕ)
    (herror : ∀ error ∈ support errorSampler, (LatticeCrypto.centeredRepr error).natAbs ≤ bound)
    (pair : StoredView params n samples × (Fin n → Bool))
    (hpair : pair ∈ support (keygen params secretSampler errorSampler)) :
    (∀ sample, (LatticeCrypto.centeredRepr (dotProduct (featureSecret (GSWSelfKey.binaryEmbed pair.2))
      (GSWMasking.tableOfPublicKey pair.1.1 sample))).natAbs ≤ (n + 1) * bound) ∧
    (∀ index, NoiseBound params (GSWSelfKey.binaryEmbed pair.2) (originalView params pair.1.2 index)
      (GSWGadget.bitMessage (pair.2 index)) ((n + 1) * bound)) := by
  obtain ⟨draws, hdraws, hpair⟩ := mem_support_map_peel _ _ hpair
  subst pair
  have herrors := sampleDraws_error_bound params secretSampler errorSampler bound herror draws hdraws
  constructor
  · simpa only [storeView, publicView, GSWMasking.tableOfPublicKey_storeTable]
      using publicTable_phase_bound params draws bound herrors
  · intro index
    change NoiseBound params (GSWSelfKey.binaryEmbed draws.1)
      (originalView params (controls params draws) index) _ _
    rw [controls_view]
    exact noiseBound_freshOriginal params draws.1 _ _ _ _ bound
      (fun _ _ _ ↦ herrors _) (fun _ _ ↦ herrors _) index

noncomputable def encryptInputs {q n samples inputs : ℕ} [NeZero q] (params : Parameters q)
    (view : StoredView params n samples) (messages : Vector Bool inputs) :
    ProbComp (Vector (GSWAccumulator.StoredCiphertext params (rows n)) inputs) :=
  Vector.ofFn <$> Fin.mOfFn inputs (fun index ↦
    GSWMasking.encrypt params (GSWMasking.tableOfPublicKey view.1) (messages.get index))

theorem encryptInputs_noiseBounds {q n samples inputs : ℕ} [NeZero q] (params : Parameters q)
    (bits : Fin n → Bool) (view : StoredView params n samples) (messages : Vector Bool inputs) (bound : ℕ)
    (hkey : ∀ sample, (LatticeCrypto.centeredRepr (dotProduct (featureSecret (GSWSelfKey.binaryEmbed bits))
      (GSWMasking.tableOfPublicKey view.1 sample))).natAbs ≤ bound)
    (initial : Vector (GSWAccumulator.StoredCiphertext params (rows n)) inputs)
    (hinitial : initial ∈ support (encryptInputs params view messages)) :
    ∀ index, NoiseBound params (GSWSelfKey.binaryEmbed bits)
      (ofMatrix params (GSWAccumulator.ciphertextView params (initial.get index)))
      (GSWGadget.bitMessage (messages.get index)) (samples * bound) := by
  obtain ⟨ciphertexts, hciphertexts, hinitial⟩ := mem_support_map_peel _ _ hinitial
  subst initial
  intro index
  have hciphertext := TFHE.Native.KeySwitchRecovery.mem_support_mOfFn_apply _ _ ciphertexts hciphertexts index
  rw [RecursiveFeaturePublicKey.encrypt_eq_uniformCoins] at hciphertext
  obtain ⟨coins, _, hcoins⟩ := mem_support_map_peel _ _ hciphertext
  simpa only [Vector.get_ofFn, hcoins, RecursiveFeaturePublicKey.ofStored] using
    RecursiveFeaturePublicKey.noiseBound_encryptWithCoins params (GSWSelfKey.binaryEmbed bits)
      (GSWMasking.tableOfPublicKey view.1) coins (messages.get index) bound hkey

/-- Modulus equality transports the public evaluator to the security family's ciphertext type. -/
def evaluate {q factor p n inputs wires : ℕ} [NeZero q] [NeZero factor] [NeZero p]
    (hq : q = factor * p) (params : Parameters q) (original : StoredOriginal params n)
    (level : Fin params.levels) (oneCode : ZMod p)
    (initial : Vector (GSWAccumulator.StoredCiphertext params (rows n)) inputs)
    (program : GSWCircuit.Program inputs wires) :
    Vector (GSWAccumulator.StoredCiphertext params (rows n)) wires := by
  subst q
  exact RecursiveFeatureCircuit.evaluateWires params original level oneCode initial program

noncomputable def correctExp {q factor p n samples inputs wires : ℕ} [NeZero q] [NeZero factor] [NeZero p]
    (hq : q = factor * p) (params : Parameters q) (level : Fin params.levels) (oneCode : ZMod p)
    (secretSampler : ProbComp (Fin n → Bool)) (errorSampler : ProbComp (ZMod q))
    (messages : Vector Bool inputs) (program : GSWCircuit.Program inputs wires) (output : Fin wires) : ProbComp Bool := do
  let pair ← keygen (p := samples) params secretSampler errorSampler
  let initial ← encryptInputs params pair.1 messages
  let result := evaluate hq params pair.1.2 level oneCode initial program
  pure (decode params (GSWSelfKey.binaryEmbed pair.2)
    (ofMatrix params (GSWAccumulator.ciphertextView params (result.get output))) level ==
      (GSWCircuit.runBits messages program).get output)

theorem decode_evaluate {factor p n inputs wires : ℕ} [NeZero factor] [NeZero p]
    (params : Parameters (factor * p)) (level : Fin params.levels) (oneCode : ZMod p)
    (bits : Fin n → Bool) (original : StoredOriginal params n)
    (initial : Vector (GSWAccumulator.StoredCiphertext params (rows n)) inputs)
    (messages : Vector Bool inputs) (program : GSWCircuit.Program inputs wires) (output : Fin wires)
    (bound keyBound : ℕ)
    (hcode : TFHE.Gadget.Base.gadget params level = GSWModulusSwitch.up factor p oneCode)
    (hcontrols : ∀ index, NoiseBound params (GSWSelfKey.binaryEmbed bits) (originalView params original index)
      (GSWGadget.bitMessage (bits index)) keyBound)
    (hinputs : ∀ index, NoiseBound params (GSWSelfKey.binaryEmbed bits)
      (ofMatrix params (GSWAccumulator.ciphertextView params (initial.get index)))
      (GSWGadget.bitMessage (messages.get index)) bound)
    (houtput : p * rows n * GSWGadget.growth params (rows n) *
      ((GSWGadget.growth params (rows n) + 1) * keyBound) ≤ bound)
    (hround : 2 * ((GSWGadget.growth params (rows n) + 1) * bound + (rows n + 1) * (factor - 1)) <
      factor * TFHE.BootstrappingCorrectness.centeredDistance 0 oneCode)
    (hdecode : 2 * bound < TFHE.BootstrappingCorrectness.centeredDistance 0 (TFHE.Gadget.Base.gadget params level)) :
    decode params (GSWSelfKey.binaryEmbed bits)
      (ofMatrix params (GSWAccumulator.ciphertextView params
        ((evaluate rfl params original level oneCode initial program).get output))) level =
      (GSWCircuit.runBits messages program).get output := by
  apply decode_eq_bit _ _ _ _ bound level _ hdecode
  apply GSWCircuit.runStored_rel
    (RecursiveFeatureCircuit.operation params original level oneCode)
    (fun ciphertext bit ↦ NoiseBound params (GSWSelfKey.binaryEmbed bits)
      (ofMatrix params (GSWAccumulator.ciphertextView params ciphertext)) (GSWGadget.bitMessage bit) bound)
    initial messages program _ hinputs output
  intro first second firstBit secondBit hfirst hsecond column
  have h := noiseBound_refreshedNand params bits (originalView params original) _ _ level oneCode
    firstBit secondBit bound keyBound hcode hfirst hsecond hcontrols hround
  exact (h column).trans houtput

theorem correctExp_supported {q factor p n samples inputs wires : ℕ}
    [NeZero q] [NeZero factor] [NeZero p]
    (hq : q = factor * p) (params : Parameters q) (level : Fin params.levels) (oneCode : ZMod p)
    (secretSampler : ProbComp (Fin n → Bool)) (errorSampler : ProbComp (ZMod q))
    (messages : Vector Bool inputs) (program : GSWCircuit.Program inputs wires) (output : Fin wires)
    (scalarBound bound : ℕ)
    (herror : ∀ error ∈ support errorSampler, (LatticeCrypto.centeredRepr error).natAbs ≤ scalarBound)
    (hcode : TFHE.Gadget.Base.gadget params level =
      hq.symm ▸ GSWModulusSwitch.up factor p oneCode)
    (hfresh : samples * ((n + 1) * scalarBound) ≤ bound)
    (houtput : p * rows n * GSWGadget.growth params (rows n) *
      ((GSWGadget.growth params (rows n) + 1) * ((n + 1) * scalarBound)) ≤ bound)
    (hround : 2 * ((GSWGadget.growth params (rows n) + 1) * bound + (rows n + 1) * (factor - 1)) <
      factor * TFHE.BootstrappingCorrectness.centeredDistance 0 oneCode)
    (hdecode : 2 * bound < TFHE.BootstrappingCorrectness.centeredDistance 0 (TFHE.Gadget.Base.gadget params level))
    (result : Bool)
    (hresult : result ∈ support (correctExp (samples := samples) hq params level oneCode secretSampler errorSampler
      messages program output)) : result = true := by
  subst q
  simp only [correctExp, mem_support_bind_iff] at hresult
  obtain ⟨pair, hpair, initial, hinitial, hresult⟩ := hresult
  obtain ⟨hkey, hcontrols⟩ := keygen_noiseBounds params secretSampler errorSampler scalarBound herror pair hpair
  have hinputs := encryptInputs_noiseBounds params pair.2 pair.1 messages _ hkey initial hinitial
  have hdecodeResult := decode_evaluate params level oneCode pair.2 pair.1.2 initial messages program output
    bound ((n + 1) * scalarBound) hcode hcontrols (fun index column ↦ (hinputs index column).trans hfresh)
    houtput hround hdecode
  simpa only [support_pure, Set.mem_singleton_iff, hdecodeResult, beq_self_eq_true] using hresult

theorem correctExp_probability_one {q factor p n samples inputs wires : ℕ}
    [NeZero q] [NeZero factor] [NeZero p]
    (hq : q = factor * p) (params : Parameters q) (level : Fin params.levels) (oneCode : ZMod p)
    (secretSampler : ProbComp (Fin n → Bool)) (errorSampler : ProbComp (ZMod q))
    (messages : Vector Bool inputs) (program : GSWCircuit.Program inputs wires) (output : Fin wires)
    (scalarBound bound : ℕ)
    (herror : ∀ error ∈ support errorSampler, (LatticeCrypto.centeredRepr error).natAbs ≤ scalarBound)
    (hcode : TFHE.Gadget.Base.gadget params level =
      hq.symm ▸ GSWModulusSwitch.up factor p oneCode)
    (hfresh : samples * ((n + 1) * scalarBound) ≤ bound)
    (houtput : p * rows n * GSWGadget.growth params (rows n) *
      ((GSWGadget.growth params (rows n) + 1) * ((n + 1) * scalarBound)) ≤ bound)
    (hround : 2 * ((GSWGadget.growth params (rows n) + 1) * bound + (rows n + 1) * (factor - 1)) <
      factor * TFHE.BootstrappingCorrectness.centeredDistance 0 oneCode)
    (hdecode : 2 * bound < TFHE.BootstrappingCorrectness.centeredDistance 0 (TFHE.Gadget.Base.gadget params level)) :
    Pr[= true | correctExp (samples := samples) hq params level oneCode secretSampler errorSampler messages program output] = 1 := by
  apply (probOutput_eq_one_iff_forall _ _).mpr
  exact ⟨by simp,
    fun result hresult ↦ correctExp_supported hq params level oneCode secretSampler errorSampler
      messages program output scalarBound bound herror hcode hfresh houtput hround hdecode result hresult⟩

theorem transport_up_natCast {q factor p : ℕ} (hq : q = factor * p) (value : ℕ) :
    (hq.symm ▸ GSWModulusSwitch.up factor p (value : ZMod p)) = ((factor * value : ℕ) : ZMod q) := by
  subst q
  exact GSWModulusSwitch.up_natCast factor p value

open RecursiveQuadraticParameters

theorem family_growth (parameter : ℕ) :
    GSWGadget.growth (RecursiveFeaturePublicKeyParameters.params parameter)
      (RecursiveFeatureBootstrapParameters.featureRows parameter) =
      RecursiveFeatureBootstrapParameters.growth parameter := by
  simp only [GSWGadget.growth, RecursiveFeaturePublicKeyParameters.params,
    RecursiveFeatureBootstrapParameters.growth]
  simp

/-- The canonical security-family gadget matches the lookup, after the checked modulus equality. -/
theorem family_gadget_eq_up (parameter : ℕ)
    (hcapacity : RecursiveFeatureBootstrapParameters.lookupExponent parameter ≤ scale parameter ^ 2) :
    TFHE.Gadget.Base.gadget (RecursiveFeaturePublicKeyParameters.params parameter)
      (RecursiveFeaturePublicKeyParameters.level parameter) =
      (RecursiveFeatureBootstrapParameters.factor_mul_lookup parameter hcapacity) ▸
        GSWModulusSwitch.up (RecursiveFeatureBootstrapParameters.factor parameter)
          (RecursiveFeatureBootstrapParameters.lookupModulus parameter)
          (RecursiveFeatureBootstrapParameters.oneCode parameter) := by
  have hk : 0 < RecursiveFeatureBootstrapParameters.lookupExponent parameter := by
    unfold RecursiveFeatureBootstrapParameters.lookupExponent
    have hr := RecursiveFeatureBootstrapParameters.featureRows_ge parameter
    exact Nat.clog_pos (by decide) (by omega)
  have hp : RecursiveFeatureBootstrapParameters.lookupModulus parameter =
      2 * 2 ^ (RecursiveFeatureBootstrapParameters.lookupExponent parameter - 1) := by
    unfold RecursiveFeatureBootstrapParameters.lookupModulus
    calc
      _ = 2 ^ (RecursiveFeatureBootstrapParameters.lookupExponent parameter - 1 + 1) := by
        congr 1
        omega
      _ = _ := pow_succ' _ _
  have hhalf : RecursiveFeatureBootstrapParameters.lookupModulus parameter / 2 =
      2 ^ (RecursiveFeatureBootstrapParameters.lookupExponent parameter - 1) := by
    rw [hp]
    simp
  rw [RecursiveFeatureBootstrapParameters.oneCode, RecursiveFeatureBootstrapParameters.halfCode,
    transport_up_natCast (RecursiveFeatureBootstrapParameters.factor_mul_lookup parameter hcapacity).symm,
    hhalf]
  simp only [TFHE.Gadget.Base.gadget, RecursiveFeaturePublicKeyParameters.params,
    RecursiveFeaturePublicKeyParameters.level, RecursiveFeatureBootstrapParameters.factor,
    Nat.cast_pow, Nat.cast_ofNat, ← pow_add]
  congr 1
  omega

/-- This experiment uses exactly the canonical joint security-family keygen and encryption. -/
noncomputable def familyCorrectExp (parameter : ℕ)
    (hcapacity : RecursiveFeatureBootstrapParameters.lookupExponent parameter ≤ scale parameter ^ 2)
    {inputs wires : ℕ} (messages : Vector Bool inputs)
    (program : GSWCircuit.Program inputs wires) (output : Fin wires) : ProbComp Bool :=
  correctExp (samples := RecursiveFeaturePublicKeyParameters.publicSamples parameter)
    (RecursiveFeatureBootstrapParameters.factor_mul_lookup parameter hcapacity).symm
    (RecursiveFeaturePublicKeyParameters.params parameter) (RecursiveFeaturePublicKeyParameters.level parameter)
    (RecursiveFeatureBootstrapParameters.oneCode parameter)
    ($ᵗ (Fin (RecursiveFeaturePublicKeyParameters.dimension parameter) → Bool))
    (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter)) messages program output

/-- The family experiment is the actual encryption-scheme API followed by public evaluation. -/
theorem familyCorrectExp_eq_scheme (parameter : ℕ)
    (hcapacity : RecursiveFeatureBootstrapParameters.lookupExponent parameter ≤ scale parameter ^ 2)
    {inputs wires : ℕ} (messages : Vector Bool inputs)
    (program : GSWCircuit.Program inputs wires) (output : Fin wires) :
    familyCorrectExp parameter hcapacity messages program output = (do
      let pair ← (RecursiveFeatureSecurityParameters.family parameter).keygen
      let initial ← Vector.ofFn <$> Fin.mOfFn inputs (fun index ↦
        (RecursiveFeatureSecurityParameters.family parameter).encrypt pair.1 (messages.get index))
      let result := evaluate
        (RecursiveFeatureBootstrapParameters.factor_mul_lookup parameter hcapacity).symm
        (RecursiveFeaturePublicKeyParameters.params parameter) pair.1.2
        (RecursiveFeaturePublicKeyParameters.level parameter) (RecursiveFeatureBootstrapParameters.oneCode parameter)
        initial program
      let decoded ← (RecursiveFeatureSecurityParameters.family parameter).decrypt pair.2 (result.get output)
      pure (decoded == some ((GSWCircuit.runBits messages program).get output))) := by
  simp [familyCorrectExp, correctExp, RecursiveFeatureSecurityParameters.family, scheme, encryptInputs]
  rfl

theorem family_correctExp_probability_one (parameter : ℕ)
    (hbudget : RecursiveFeatureBootstrapParameters.lookupModulus parameter *
      RecursiveFeatureBootstrapParameters.postNandBound parameter < modulus parameter)
    {inputs wires : ℕ} (messages : Vector Bool inputs)
    (program : GSWCircuit.Program inputs wires) (output : Fin wires) :
    Pr[= true | familyCorrectExp parameter
      (RecursiveFeatureBootstrapParameters.capacity_of_budget parameter hbudget) messages program output] = 1 := by
  unfold familyCorrectExp
  apply correctExp_probability_one _ _ _ _ _ _ messages program output
    (radius parameter) (RecursiveFeatureBootstrapParameters.outputBound parameter)
  · exact fun error herror ↦ UniformInterval.sample_support_centered_bound _ _ _ error herror
  · exact family_gadget_eq_up parameter (RecursiveFeatureBootstrapParameters.capacity_of_budget parameter hbudget)
  · exact RecursiveFeatureBootstrapParameters.publicEncryptionBound_le_outputBound parameter
  · simp only [RecursiveFeatureBootstrapParameters.rows_eq_featureRows, family_growth]
    change RecursiveFeatureBootstrapParameters.outputBound parameter ≤
      RecursiveFeatureBootstrapParameters.outputBound parameter
    exact le_refl _
  · simpa only [RecursiveFeatureBootstrapParameters.rows_eq_featureRows, family_growth,
      RecursiveFeatureBootstrapParameters.postNandBound] using
      RecursiveFeatureBootstrapParameters.rounding_margin parameter hbudget
  · rw [RecursiveFeaturePublicKeyParameters.gadget_distance]
    have hhalf : modulus parameter / 2 = RecursiveFeatureBootstrapParameters.factor parameter *
        (RecursiveFeatureBootstrapParameters.lookupModulus parameter / 2) := by
      rw [← RecursiveFeatureBootstrapParameters.factor_mul_lookup parameter
        (RecursiveFeatureBootstrapParameters.capacity_of_budget parameter hbudget),
        RecursiveFeatureBootstrapParameters.lookup_even parameter]
      rw [show RecursiveFeatureBootstrapParameters.factor parameter *
        (2 * (RecursiveFeatureBootstrapParameters.lookupModulus parameter / 2)) =
          2 * (RecursiveFeatureBootstrapParameters.factor parameter *
            (RecursiveFeatureBootstrapParameters.lookupModulus parameter / 2)) by ring]
      simp
    rw [hhalf]
    exact RecursiveFeatureBootstrapParameters.output_margin parameter hbudget

/-- One sufficiently large parameter works for every finite shared NAND program and output. -/
theorem eventually_family_correctExp_probability_one :
    ∀ᶠ parameter in Filter.atTop,
      ∃ hcapacity : RecursiveFeatureBootstrapParameters.lookupExponent parameter ≤ scale parameter ^ 2,
        ∀ {inputs wires : ℕ} (messages : Vector Bool inputs) (program : GSWCircuit.Program inputs wires)
          (output : Fin wires), Pr[= true | familyCorrectExp parameter hcapacity messages program output] = 1 := by
  filter_upwards [RecursiveFeatureBootstrapParameters.eventually_budget] with parameter hbudget
  exact ⟨RecursiveFeatureBootstrapParameters.capacity_of_budget parameter hbudget,
    fun messages program output ↦ family_correctExp_probability_one parameter hbudget messages program output⟩

end FormalProof4FHE.LWE.RecursiveFeatureFHECorrectness
