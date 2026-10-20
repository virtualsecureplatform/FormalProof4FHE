/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/
import FormalProof4FHE.LWE.GSWLinearCharacterCompiler

/-! The actual highest-weight certificate from the fixed n=3,m=2 experiment.
This finite source has a public key-recovery certificate; this test asserts
its compiler algebra and supported noise only, never cryptographic security. -/

open Matrix
open scoped BigOperators

namespace FormalProof4FHETest.GSWLinearCharacterSmoke

open FormalProof4FHE.LWE
open GSWLinearCharacterCompiler

abbrev Q : ℕ := 18446744073709551616

def sourceMask : Matrix (Fin 3) (Fin 6) (ZMod Q) := ![
  ![9688722355387783630, 18085368005483722332, 1597571103358201379,
    2275725516444398876, 775483396753042328, 18334540636102551761],
  ![8216375798825271815, 5490289608362407295, 3070054749901302341,
    2103868346419342137, 3207129860252534941, 13114751232533549987],
  ![8649685818590288781, 16372217236481684405, 3505302084769373235,
    14500034912534361601, 701236273800196516, 5986954609615606814]]

def integerCoefficients : Matrix (Fin 3) (Fin 6) ℤ := ![
  ![0, 3, 2, 1, 1, 2], ![-4, 2, 0, 0, 2, 6], ![-2, -2, -7, -5, -3, -7]]

def coefficients : Matrix (Fin 3) (Fin 6) (ZMod Q) :=
  fun pair column ↦ integerCoefficients pair column

theorem actual_coefficient_certificate :
    4 * coefficient3 sourceMask coefficients = (9223372036854775808 : ZMod Q) := by
  decide

theorem actual_coefficient_norm_le :
    (∑ pair, ∑ column, (LatticeCrypto.centeredRepr (coefficients pair column)).natAbs) ≤ 49 := by
  calc
    _ ≤ ∑ pair, ∑ column, (integerCoefficients pair column).natAbs := by
      apply Finset.sum_le_sum
      intro pair _
      apply Finset.sum_le_sum
      intro column _
      exact FormalProof4FHE.TFHE.NoiseBounds.centeredRepr_intCast_natAbs_le _
    _ = 49 := by decide

/-- Uniform in all eight binary keys and every supported source error vector. -/
theorem actual_top_control_error_bound (bits : Fin 3 → Bool) (error : Fin 6 → ZMod Q)
    (herror : ∀ column, (LatticeCrypto.centeredRepr (error column)).natAbs ≤ 256) :
    (LatticeCrypto.centeredRepr
      (RecursiveQuadratic.decrypt (GSWSelfKey.binaryEmbed bits)
        (compileCanonical first3 second3 sourceMask coefficients
          (vecMul (GSWSelfKey.binaryEmbed bits) sourceMask + error)) -
        9223372036854775808 * GSWSelfKey.binaryEmbed bits 0 *
          GSWSelfKey.binaryEmbed bits 1 * GSWSelfKey.binaryEmbed bits 2)).natAbs ≤ 12544 := by
  have h := phase_error_bound first3 second3 first3_ne_second3 sourceMask coefficients bits error 256 herror
  rw [cubicPhase_three, actual_coefficient_certificate] at h
  exact h.trans ((Nat.mul_le_mul_right 256 actual_coefficient_norm_le).trans_eq (by decide))

end FormalProof4FHETest.GSWLinearCharacterSmoke
