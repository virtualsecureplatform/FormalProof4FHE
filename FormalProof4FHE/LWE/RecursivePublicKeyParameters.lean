/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.RecursivePublicKey
import FormalProof4FHE.TFHE.KeySwitchRecovery

/-!
# Public-encryption parameters for the recursive component

The public-key row count pays the subset-sum entropy cost, while the half-modulus
bit encoding tolerates every supported fresh error for sufficiently large parameters.
These statements concern public encryption with a fixed recursive hint batch;
closed homomorphic evaluation and reusable refresh remain to be constructed.
-/

open OracleComp AsymmEncAlg
open scoped ENNReal Topology

namespace FormalProof4FHE.LWE.RecursivePublicKeyParameters

open RecursiveQuadraticParameters

def publicSamples (parameter : ℕ) : ℕ :=
  (binaryDimension parameter + 1) * scale parameter ^ 2 + 2 * parameter + 1

/-- The public-key row count is polynomial in the security parameter. -/
noncomputable def publicSamplesPolynomial : Polynomial ℕ :=
  (2 * (Polynomial.X + 1) ^ 5 + 1) * (Polynomial.X + 1) ^ 2 + 2 * Polynomial.X + 1

theorem publicSamplesPolynomial_eval (parameter : ℕ) :
    publicSamplesPolynomial.eval parameter = publicSamples parameter := by
  simp [publicSamplesPolynomial, publicSamples, binaryDimension, scale]

theorem masking_cardinality_margin (parameter : ℕ) :
    modulus parameter ^ (binaryDimension parameter * 1 + 1) * 2 ^ (2 * parameter) ≤
      2 ^ publicSamples parameter := by
  unfold modulus publicSamples
  rw [Nat.mul_one, ← pow_mul, ← pow_add]
  apply pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ))
  have he := Nat.mul_comm (scale parameter ^ 2) (binaryDimension parameter + 1)
  omega

noncomputable def maskingBound (parameter : ℕ) : ℝ :=
  Real.sqrt ((modulus parameter : ℝ) ^ (binaryDimension parameter * 1 + 1) /
    (2 : ℝ) ^ publicSamples parameter) / 2

theorem maskingBound_le_half_pow (parameter : ℕ) :
    maskingBound parameter ≤ (1 / 2 : ℝ) ^ parameter := by
  have hmargin : (modulus parameter : ℝ) ^ (binaryDimension parameter * 1 + 1) *
      (2 : ℝ) ^ (2 * parameter) ≤ (2 : ℝ) ^ publicSamples parameter := by
    exact_mod_cast masking_cardinality_margin parameter
  have hsqrt : Real.sqrt ((modulus parameter : ℝ) ^ (binaryDimension parameter * 1 + 1) /
      (2 : ℝ) ^ publicSamples parameter) ≤ (1 / 2 : ℝ) ^ parameter := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 1 / (2 : ℝ) ^ (2 * parameter) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        simpa only [one_mul] using hmargin
      _ = _ := by rw [div_pow, one_pow, div_pow, one_pow, ← pow_mul, Nat.mul_comm parameter 2]
  unfold maskingBound
  have hnonneg := Real.sqrt_nonneg
    ((modulus parameter : ℝ) ^ (binaryDimension parameter * 1 + 1) /
      (2 : ℝ) ^ publicSamples parameter)
  linarith

theorem maskingBound_negligible :
    negligible (fun parameter ↦ ENNReal.ofReal (maskingBound parameter)) :=
  negligible_of_le (fun parameter ↦ ENNReal.ofReal_le_ofReal (maskingBound_le_half_pow parameter))
    DiscreteGaussianTail.half_pow_negligible

/-- Subset-sum encryption accumulates at most p supported scalar errors. -/
theorem eventually_public_quarter_margin :
    ∀ᶠ parameter in Filter.atTop,
      4 * publicSamples parameter * radius parameter < modulus parameter := by
  let polynomial : Polynomial ℕ := 4 * publicSamplesPolynomial
  have hn := negligible_polynomial_mul DiscreteGaussianTail.half_pow_negligible polynomial
  have hz : Filter.Tendsto
      (fun parameter ↦ ((polynomial.eval parameter : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal ((1 / 2 : ℝ) ^ parameter)) Filter.atTop (nhds 0) := by
    simpa only [pow_zero, one_mul] using hn 0
  have hevent := hz.eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
  filter_upwards [hevent] with parameter hparameter
  have hr : ((4 * publicSamples parameter : ℕ) : ℝ) * (1 / 2 : ℝ) ^ parameter < 1 := by
    have hc : ENNReal.ofReal (((4 * publicSamples parameter : ℕ) : ℝ) *
        (1 / 2 : ℝ) ^ parameter) < ENNReal.ofReal 1 := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ENNReal.ofReal_one]
      simpa [polynomial, publicSamplesPolynomial_eval] using hparameter
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).mp hc
  rw [div_pow, one_pow, mul_one_div] at hr
  have hreal := (div_lt_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ parameter)).mp hr
  have hnat : 4 * publicSamples parameter < 2 ^ parameter := by
    have ht : ((4 * publicSamples parameter : ℕ) : ℝ) < ((2 ^ parameter : ℕ) : ℝ) := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat, one_mul] using hreal
    exact_mod_cast ht
  exact (Nat.mul_lt_mul_of_pos_right hnat (by unfold radius; positivity)).trans_le
    (radius_times_two_pow_le_modulus parameter)

def oneCode (parameter : ℕ) : ZMod (modulus parameter) := ((modulus parameter / 2 : ℕ) : ZMod _)

theorem oneCode_distance (parameter : ℕ) :
    TFHE.BootstrappingCorrectness.centeredDistance 0 (oneCode parameter) = modulus parameter / 2 := by
  rw [TFHE.BootstrappingCorrectness.centeredDistance_symm]
  change (LatticeCrypto.centeredRepr (((modulus parameter / 2 : ℕ) : ZMod _) - 0)).natAbs = _
  rw [sub_zero, LatticeCrypto.centeredRepr_eq_valMinAbs,
    ZMod.valMinAbs_natCast_of_le_half (le_refl (modulus parameter / 2))]
  exact Int.natAbs_natCast _

theorem modulus_eq_two_mul_half (parameter : ℕ) :
    modulus parameter = 2 * (modulus parameter / 2) := by
  have hexp : 0 < scale parameter ^ 2 := by have := scale_pos parameter; positivity
  have hp : modulus parameter = 2 * 2 ^ (scale parameter ^ 2 - 1) := by
    unfold modulus
    rw [← pow_succ']
    congr 1
  rw [hp]
  simp

theorem decode_supported_publicEncryption (parameter : ℕ)
    (hmargin : 4 * publicSamples parameter * radius parameter < modulus parameter)
    (secret : Fin (binaryDimension parameter * 1) → ZMod (modulus parameter))
    (challenge : Matrix (Fin (binaryDimension parameter * 1)) (Fin (publicSamples parameter))
      (ZMod (modulus parameter)))
    (errors : Fin (publicSamples parameter) → ZMod (modulus parameter))
    (herrors : ∀ index, errors index ∈ support
      (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter)))
    (bits : Fin (publicSamples parameter) → Bool) (bit : Bool) :
    RecursivePublicKey.decode (oneCode parameter) secret
      (RecursivePublicKey.encryptWithCoins (RecursivePublicKey.bitEncode (oneCode parameter))
        (challenge, Matrix.vecMul secret challenge + errors) bits bit) = bit := by
  apply RecursivePublicKey.decode_publicEncryption _ _ _ _ _ _ (radius parameter)
    (fun index ↦ UniformInterval.sample_support_centered_bound _ _ _ _ (herrors index))
  rw [oneCode_distance]
  have heven := modulus_eq_two_mul_half parameter
  have ha : 4 * publicSamples parameter * radius parameter =
      2 * (2 * (publicSamples parameter * radius parameter)) := by ring
  omega

theorem eventually_decode_supported_publicEncryption :
    ∀ᶠ parameter in Filter.atTop,
      ∀ secret : Fin (binaryDimension parameter * 1) → ZMod (modulus parameter),
      ∀ challenge : Matrix (Fin (binaryDimension parameter * 1)) (Fin (publicSamples parameter))
        (ZMod (modulus parameter)),
      ∀ errors : Fin (publicSamples parameter) → ZMod (modulus parameter),
      (∀ index, errors index ∈ support
        (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter))) →
      ∀ bits : Fin (publicSamples parameter) → Bool, ∀ bit : Bool,
        RecursivePublicKey.decode (oneCode parameter) secret
          (RecursivePublicKey.encryptWithCoins (RecursivePublicKey.bitEncode (oneCode parameter))
            (challenge, Matrix.vecMul secret challenge + errors) bits bit) = bit := by
  filter_upwards [eventually_public_quarter_margin] with parameter hmargin
  intro secret challenge errors herrors bits bit
  exact decode_supported_publicEncryption parameter hmargin secret challenge errors herrors bits bit

def sampleRows (parameter hints : ℕ) : ℕ :=
  publicSamples parameter + hints * (binaryDimension parameter * 1 + 1)

noncomputable def sampleRowsPolynomial (hints : Polynomial ℕ) : Polynomial ℕ :=
  publicSamplesPolynomial + hints * (2 * (Polynomial.X + 1) ^ 5 + 1)

theorem sampleRowsPolynomial_eval (hints : Polynomial ℕ) (parameter : ℕ) :
    (sampleRowsPolynomial hints).eval parameter = sampleRows parameter (hints.eval parameter) := by
  simp [sampleRowsPolynomial, publicSamplesPolynomial_eval, sampleRows, binaryDimension, scale]

theorem family_implementationLoss_negligible (hints : Polynomial ℕ) :
    negligible (fun parameter ↦ ENNReal.ofReal
      (implementationLoss (sampleRows parameter (hints.eval parameter)) parameter)) := by
  simpa only [sampleRowsPolynomial_eval] using implementationLoss_negligible (sampleRowsPolynomial hints)

noncomputable def secretSampler (parameter : ℕ) :
    ProbComp (Fin (binaryDimension parameter * 1) → ZMod (modulus parameter)) :=
  FormalProof4FHE.BlockBinary.expand (ZMod (modulus parameter)) <$>
    ($ᵗ FormalProof4FHE.BlockBinary.Key 1 (binaryDimension parameter))

noncomputable def family (parameter hints : ℕ)
    (polynomial : RecursiveQuadratic.Polynomial (ZMod (modulus parameter))
      (binaryDimension parameter * 1) hints) :=
  RecursivePublicKey.scheme (oneCode parameter)
    (RecursiveQuadratic.columnsEquiv (binaryDimension parameter * 1) (publicSamples parameter) hints)
    polynomial (secretSampler parameter)
    (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter))

/-- The adapter only changes the experiment interface, not the published information. -/
noncomputable def familyAdversary (parameter hints : ℕ)
    (polynomial : RecursiveQuadratic.Polynomial (ZMod (modulus parameter))
      (binaryDimension parameter * 1) hints)
    (adversary : IND_CPA_Adv (family parameter hints polynomial)) :
    RecursivePublicKey.Adversary (modulus parameter) (binaryDimension parameter * 1)
      (publicSamples parameter) hints :=
  RecursivePublicKey.fromINDCPA (oneCode parameter)
    (RecursiveQuadratic.columnsEquiv (binaryDimension parameter * 1) (publicSamples parameter) hints)
    polynomial (secretSampler parameter)
    (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter)) adversary

/-- Standard one-time IND-CPA bound for public encryption with every recursive hint retained. -/
theorem oneTime_abs_signedAdvantage_le (parameter hints : ℕ)
    (polynomial : RecursiveQuadratic.Polynomial (ZMod (modulus parameter))
      (binaryDimension parameter * 1) hints)
    (adversary : IND_CPA_Adv (family parameter hints polynomial)) :
    |IND_CPA_OneTime_signedAdvantageReal (family parameter hints polynomial) adversary| ≤
      ordinaryReductionLoss parameter
        (RecursiveQuadratic.columnsEquiv (binaryDimension parameter * 1) (publicSamples parameter) hints)
        polynomial (RecursivePublicKey.gameGivenView (RecursivePublicKey.bitEncode (oneCode parameter))
          (familyAdversary parameter hints polynomial adversary)) +
      implementationLoss (sampleRows parameter hints) parameter + maskingBound parameter := by
  have hgame := RecursivePublicKey.oneTime_game_evalDist (oneCode parameter)
    (RecursiveQuadratic.columnsEquiv (binaryDimension parameter * 1) (publicSamples parameter) hints)
    polynomial (secretSampler parameter)
    (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter)) adversary
  have hbound := RecursivePublicKey.sampled_game_abs_advantage_le parameter
    (RecursiveQuadratic.columnsEquiv (binaryDimension parameter * 1) (publicSamples parameter) hints)
    polynomial (RecursivePublicKey.bitEncode (oneCode parameter))
    (familyAdversary parameter hints polynomial adversary)
  unfold IND_CPA_OneTime_signedAdvantageReal family
  rw [probOutput_congr (rfl : true = true) hgame]
  simpa only [familyAdversary, secretSampler, RecursivePublicKey.freshView_mapped_secret,
    maskingBound, sampleRows] using hbound

/-- Every outcome of honest key generation and public encryption decodes correctly. -/
theorem correctExp_supported (parameter hints : ℕ)
    (hmargin : 4 * publicSamples parameter * radius parameter < modulus parameter)
    (polynomial : RecursiveQuadratic.Polynomial (ZMod (modulus parameter))
      (binaryDimension parameter * 1) hints) (bit result : Bool)
    (hresult : result ∈ support ((family parameter hints polynomial).CorrectExp bit)) :
    result = true := by
  simp only [family, RecursivePublicKey.scheme, CorrectExp, mem_support_bind_iff] at hresult
  obtain ⟨pair, hpair, ciphertext, hciphertext, output, houtput, hresult⟩ := hresult
  simp only [RecursivePublicKey.keygen, mem_support_bind_iff] at hpair
  obtain ⟨secret, _, challenge, _, errors, herrors, hpair⟩ := hpair
  simp only [support_pure, Set.mem_singleton_iff] at hpair
  subst pair
  rw [RecursivePublicKey.encrypt_eq_uniformCoins] at hciphertext
  obtain ⟨bits, _, hbits⟩ := mem_support_map_peel
    (fun bits ↦ RecursivePublicKey.encryptWithCoins
      (RecursivePublicKey.bitEncode (oneCode parameter))
      (RecursiveQuadratic.fresh polynomial secret challenge
        (fun column ↦ errors (RecursiveQuadratic.columnsEquiv
          (binaryDimension parameter * 1) (publicSamples parameter) hints column))).1 bits bit)
    _ hciphertext
  subst ciphertext
  have heach : ∀ index : Fin (publicSamples parameter),
      errors (RecursiveQuadratic.columnsEquiv
        (binaryDimension parameter * 1) (publicSamples parameter) hints (.inl index)) ∈ support
        (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter)) := by
    intro index
    exact TFHE.Native.KeySwitchRecovery.mem_support_mOfFn_apply _ _ errors herrors _
  have hdecode := decode_supported_publicEncryption parameter hmargin secret
    (fun row column ↦ challenge row (.inl column))
    (fun column ↦ errors (RecursiveQuadratic.columnsEquiv
      (binaryDimension parameter * 1) (publicSamples parameter) hints (.inl column))) heach bits bit
  simp only [support_pure, Set.mem_singleton_iff] at houtput hresult
  subst output
  have hdecode' : RecursivePublicKey.decode (oneCode parameter) secret
      (RecursivePublicKey.encryptWithCoins (RecursivePublicKey.bitEncode (oneCode parameter))
        (RecursiveQuadratic.fresh polynomial secret challenge
          (fun column ↦ errors (RecursiveQuadratic.columnsEquiv
            (binaryDimension parameter * 1) (publicSamples parameter) hints column))).1 bits bit) = bit := hdecode
  rw [hdecode'] at hresult
  simpa only [decide_true] using hresult

theorem correctExp_probability_one (parameter hints : ℕ)
    (hmargin : 4 * publicSamples parameter * radius parameter < modulus parameter)
    (polynomial : RecursiveQuadratic.Polynomial (ZMod (modulus parameter))
      (binaryDimension parameter * 1) hints) (bit : Bool) :
    Pr[= true | (family parameter hints polynomial).CorrectExp bit] = 1 := by
  apply (probOutput_eq_one_iff_forall _ _).mpr
  exact ⟨by simp, fun result hresult ↦ correctExp_supported parameter hints hmargin polynomial bit result hresult⟩

theorem eventually_correctExp_probability_one :
    ∀ᶠ parameter in Filter.atTop, ∀ hints : ℕ,
      ∀ polynomial : RecursiveQuadratic.Polynomial (ZMod (modulus parameter))
        (binaryDimension parameter * 1) hints, ∀ bit : Bool,
        Pr[= true | (family parameter hints polynomial).CorrectExp bit] = 1 := by
  filter_upwards [eventually_public_quarter_margin] with parameter hmargin
  intro hints polynomial bit
  exact correctExp_probability_one parameter hints hmargin polynomial bit

end FormalProof4FHE.LWE.RecursivePublicKeyParameters
