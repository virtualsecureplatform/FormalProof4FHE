/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/
import FormalProof4FHE.LWE.GSWLinearCharacterSecurity
import FormalProof4FHETest.GSWLinearCharacterSmoke

/-! Exercise the saved coefficient witness inside the complete shared-source
draw. Two copies of the top control use the SAME six source errors, with
separate recursive zero masks. The source is recoverable; this is a universal
joint correctness check, not a finite cryptographic hardness claim. -/

open Matrix
open scoped BigOperators

namespace FormalProof4FHETest.GSWLinearCharacterSecuritySmoke

open FormalProof4FHE.LWE GSWLinearCharacterCompiler GSWLinearCharacterSecurity
open GSWLinearCharacterSmoke

def builder : Builder Q 3 6 2 (Fin 3) := fun _ _ ↦ coefficients

/-- The actual saved source mask, arbitrary shared supported errors and
arbitrary remaining masks. Both materialized controls meet the bound at once. -/
theorem actual_joint_control_error_bound (bits : Fin 3 → Bool)
    (masks : Matrix (Fin 3) (RecursiveQuadratic.Column 3 6 (2 + 2)) (ZMod Q))
    (hmask : (fun row column ↦ masks row (.inl column)) = sourceMask)
    (errors : RecursiveQuadratic.Column 3 6 (2 + 2) → ZMod Q)
    (herror : ∀ column, (LatticeCrypto.centeredRepr (errors column)).natAbs ≤ 256)
    (index : Fin 2) :
    (LatticeCrypto.centeredRepr
      (RecursiveQuadratic.decrypt (GSWSelfKey.binaryEmbed bits)
        ((freshDraw first3 second3 builder (GSWSelfKey.binaryEmbed bits) masks errors).2.2 index) -
        9223372036854775808 * GSWSelfKey.binaryEmbed bits 0 *
          GSWSelfKey.binaryEmbed bits 1 * GSWSelfKey.binaryEmbed bits 2)).natAbs ≤ 13568 := by
  have h := freshDraw_control_error_bound first3 second3 first3_ne_second3 builder
    bits masks errors 256 herror index
  dsimp only at h
  rw [hmask] at h
  change (LatticeCrypto.centeredRepr (_ - cubicPhase first3 second3 sourceMask coefficients
    (GSWSelfKey.binaryEmbed bits))).natAbs ≤
      (3 + 1) * 256 + (∑ pair, ∑ column,
        (LatticeCrypto.centeredRepr (coefficients pair column)).natAbs) * 256 at h
  rw [cubicPhase_three, actual_coefficient_certificate] at h
  exact h.trans ((Nat.add_le_add_left
    (Nat.mul_le_mul_right 256 actual_coefficient_norm_le) ((3 + 1) * 256)).trans_eq (by decide))

end FormalProof4FHETest.GSWLinearCharacterSecuritySmoke
