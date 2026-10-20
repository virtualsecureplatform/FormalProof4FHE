/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/
import FormalProof4FHE.LWE.GSWTripleLocalCompiler

/-! A real q/4 torsion term defeats an unscaled locality argument. Scaling
restores the actual source-error bound at a nonvanishing lower gadget weight. -/

open Matrix
open scoped BigOperators

namespace FormalProof4FHETest.GSWTripleLocalSmoke

open FormalProof4FHE.LWE GSWLinearCharacterCompiler GSWTripleLocalCompiler

abbrev Q : ℕ := 1024

def mask : Matrix (Fin 4) (Fin 3) (ZMod Q) :=
  ![![0, 0, 0], ![0, 0, 0], ![16, 0, 0], ![256, 512, 768]]

def coefficients : Matrix (Fin 3) (Fin 3) (ZMod Q) :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]

theorem outside_torsion : ∀ (pair : Fin 3) (row : Fin 1),
    4 * projectedMask mask coefficients pair (row.natAdd 3) = 0 := by decide

theorem outside_not_zero : projectedMask mask coefficients 0 (3 : Fin 4) ≠ 0 := by decide

theorem target_coefficient : 4 * coefficient3 (headMask (k := 1) mask) coefficients = (64 : ZMod Q) := by decide

theorem actual_ambient_cubic (head : Fin 3 → ZMod Q) (tail : Fin 1 → ZMod Q) :
    cubicPhase (fun pair ↦ (first3 pair).castAdd 1) (fun pair ↦ (second3 pair).castAdd 1)
      mask coefficients (Fin.append head tail) = 64 * head 0 * head 1 * head 2 := by
  rw [target_pair_cubic_phase (k := 1) mask coefficients outside_torsion, target_coefficient]

/-- The purported unscaled local quadratic has error 512 even with zero
source noise. This prevents silently replacing 4*A*u=0 by A*u=0. -/
theorem unscaled_local_failure :
    discrepancy (64 : ZMod Q)
      (GSWLinearCharacterCompiler.polynomial first3 second3 (headMask (k := 1) mask) coefficients
        (vecMul (Fin.append (fun _ : Fin 3 ↦ (0 : ZMod Q)) (fun _ : Fin 1 ↦ (1 : ZMod Q))) mask))
      false false false = 512 := by decide

theorem actual_scaled_error_bound (bits : Fin 3 → Bool) (tail : Fin 1 → ZMod Q)
    (error : Fin 3 → ZMod Q)
    (herror : ∀ column, (LatticeCrypto.centeredRepr (error column)).natAbs ≤ 1) :
    discrepancy (256 : ZMod Q)
      (GSWLinearCharacterCompiler.polynomial first3 second3 (headMask (k := 1) mask) (scaleCoefficients 4 coefficients)
        (vecMul (Fin.append (GSWSelfKey.binaryEmbed bits) tail) mask + error))
      (bits 0) (bits 1) (bits 2) ≤ 12 := by
  have h := local_compiler_scaled_error_bound (k := 1) mask coefficients outside_torsion 64 target_coefficient
    bits tail error 1 herror
  have hn : (∑ pair, ∑ column, (LatticeCrypto.centeredRepr (coefficients pair column)).natAbs) = 3 := by decide
  have hw : (4 : ZMod Q) * 64 = 256 := by decide
  rw [hw, hn] at h
  exact h

theorem scaled_lower_weight_margin :
    8 * 12 < RecursiveFeatureCubicApproximation.magnitude (4 * (64 : ZMod Q)) := by decide

theorem scaled_top_weight_vanishes :
    RecursiveFeatureCubicApproximation.magnitude (4 * (512 : ZMod Q)) = 0 := by decide

end FormalProof4FHETest.GSWTripleLocalSmoke
