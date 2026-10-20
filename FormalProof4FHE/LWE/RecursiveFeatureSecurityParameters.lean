/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.RecursiveFeatureSecurityView
import FormalProof4FHE.LWE.RecursiveFeaturePublicKeyParameters

/-!
# Concrete parameters for the complete same-key security experiment

The family samples one uniform binary secret and all scalar errors for the public
key and original-bit controls. The statistical masking term is negligible and the
joint scalar error count is polynomial. The remaining computational advantage is
exactly the full joint-view replacement game; no hardness of that game is assumed
here. In particular this is not an ordinary-LWE-only FHE security theorem.
-/

open OracleComp AsymmEncAlg

namespace FormalProof4FHE.LWE.RecursiveFeatureSecurityParameters

open RecursiveQuadraticParameters RecursiveFeaturePublicKeyParameters

noncomputable def family (parameter : ℕ) :=
  RecursiveFeatureSecurityView.scheme (n := dimension parameter) (p := publicSamples parameter)
    (params parameter) (level parameter) ($ᵗ (Fin (dimension parameter) → Bool))
    (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter))

noncomputable def jointReplacementAdvantage (parameter : ℕ)
    (adversary : IND_CPA_Adv (family parameter)) : ℝ :=
  RecursiveFeatureSecurityView.jointReplacementAdvantage (params parameter) (level parameter)
    ($ᵗ (Fin (dimension parameter) → Bool))
    (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter)) adversary

theorem oneTime_abs_signedAdvantage_le (parameter : ℕ)
    (adversary : IND_CPA_Adv (family parameter)) :
    |IND_CPA_OneTime_signedAdvantageReal (family parameter) adversary| ≤
      jointReplacementAdvantage parameter adversary + maskingBound parameter := by
  simpa only [family, jointReplacementAdvantage, maskingBound, maskingPerColumnBound,
    RecursiveFeatureSecurityView.Dimension, RecursiveFeaturePublicKey.Dimension, featureRows, params,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    using RecursiveFeatureSecurityView.oneTime_abs_signedAdvantage_le
      (params parameter) (level parameter) ($ᵗ (Fin (dimension parameter) → Bool))
      (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter)) adversary

/-- This discharges only the statistical term, not the complete joint-view hop. -/
theorem family_masking_negligible :
    negligible (fun parameter ↦ ENNReal.ofReal (maskingBound parameter)) :=
  maskingBound_negligible

def scalarErrorCount (parameter : ℕ) : ℕ :=
  RecursiveFeatureSecurityView.errorCount (params parameter) (dimension parameter) (publicSamples parameter)

noncomputable def scalarErrorCountPolynomial : Polynomial ℕ :=
  (publicSamplesPolynomial + 2 * (Polynomial.X + 1) ^ 5 *
    (featureRowsPolynomial * (Polynomial.X + 1) ^ 2)) * (2 * (Polynomial.X + 1) ^ 5 + 1)

theorem scalarErrorCountPolynomial_eval (parameter : ℕ) :
    scalarErrorCountPolynomial.eval parameter = scalarErrorCount parameter := by
  simp [scalarErrorCountPolynomial, scalarErrorCount, RecursiveFeatureSecurityView.errorCount,
    RecursiveFeatureSecurityView.scalarColumns, RecursiveFeatureGSW.rows, params,
    publicSamplesPolynomial_eval, featureRowsPolynomial_eval, featureRows, binaryDimension, scale]

end FormalProof4FHE.LWE.RecursiveFeatureSecurityParameters
