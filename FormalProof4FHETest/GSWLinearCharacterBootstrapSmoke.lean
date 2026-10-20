/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/
import FormalProof4FHE.LWE.GSWLinearCharacterBootstrap
import FormalProof4FHETest.GSWLinearCharacterSmoke

/-! Check the actual saved top-weight witness in the COMPLETE original-bit
control layout, together with lower/repeated-index and low-level handling.
This small source is recoverable. The sparse builder below is an integration
test, not a claimed full-budget or secure asymptotic generator. -/

open Matrix
open scoped BigOperators

namespace FormalProof4FHETest.GSWLinearCharacterBootstrapSmoke

open FormalProof4FHE FormalProof4FHE.LWE RecursiveMultiplication RecursiveFeatureGSW RecursiveFeatureBootstrap
open RecursiveFeatureControlHybrid RecursiveFeatureControlPolynomial
open GSWLinearCharacterCompiler GSWLinearCharacterPolynomial
open GSWLinearCharacterSmoke

def params : GSWGadget.Parameters Q where
  base := 2
  levels := 64
  one_lt_base := by decide
  modulus_le_capacity := by decide

def topLevel : Fin params.levels := ⟨63, by decide⟩

def slot (index : Fin 3) (coordinate : Feature 3) (level : Fin params.levels) :
    Fin (controlCount params 3) :=
  finProdFinEquiv (index, finProdFinEquiv (featureEquiv 3 coordinate, level))

def builder : GSWLinearCharacterBootstrap.Builder params 3 6 (Fin 3) := fun _ column ↦
  let coords := coordinates params 3 column
  if genuineCubic coords.1 coords.2.1 && decide (coords.2.2.val = 63) then coefficients else 0

theorem top_columnBound_le :
    GSWLinearCharacterBootstrap.columnBound params first3 second3 builder GSWLinearCharacterSmoke.sourceMask 256
      (slot 0 (some (.inr (1, 2))) topLevel) ≤ 12544 := by
  have hu : builder GSWLinearCharacterSmoke.sourceMask (slot 0 (some (.inr (1, 2))) topLevel) = coefficients := by
    simp [builder, slot, coordinates, genuineCubic, topLevel]
  have hw : TFHE.Gadget.Base.gadget params topLevel = (9223372036854775808 : ZMod Q) := by decide
  have ht : GSWLinearCharacterBootstrap.targetPolynomial params (0 : Fin 3) (some (.inr (1, 2))) topLevel =
      MvPolynomial.C (9223372036854775808 : ZMod Q) *
        MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 := by
    simp [GSWLinearCharacterBootstrap.targetPolynomial, genuineCubic, hw]
  unfold GSWLinearCharacterBootstrap.columnBound
  simp only [slot, coordinates, Equiv.symm_apply_apply] at hu ⊢
  rw [hu, cubicPolynomial_three, actual_coefficient_certificate, ht, sub_self, coefficientBound_zero, add_zero]
  exact (Nat.mul_le_mul_right 256 actual_coefficient_norm_le).trans_eq (by decide)

theorem low_columns_bound (index : Fin 3) (coordinate : Feature 3) (level : Fin params.levels)
    (hlevel : level.val < 2) :
    GSWLinearCharacterBootstrap.columnBound params first3 second3 builder GSWLinearCharacterSmoke.sourceMask 256
      (slot index coordinate level) ≤ 2 := by
  have hu : builder GSWLinearCharacterSmoke.sourceMask (slot index coordinate level) = 0 := by
    have hn : level.val ≠ 63 := by omega
    simp [builder, slot, coordinates, hn]
  rw [GSWLinearCharacterBootstrap.columnBound_zero params first3 second3 builder GSWLinearCharacterSmoke.sourceMask 256 _ hu]
  simp only [slot, coordinates, Equiv.symm_apply_apply]
  have hp := GSWLinearCharacterBootstrap.targetPolynomial_bound params index coordinate level
  exact hp.trans (by
    change 2 ^ level.val ≤ 2
    have he : level.val = 0 ∨ level.val = 1 := by omega
    rcases he with he | he <;> simp [he])

theorem noncubic_columns_zero (index : Fin 3) (coordinate : Feature 3) (level : Fin params.levels)
    (h : genuineCubic index coordinate = false) :
    GSWLinearCharacterBootstrap.columnBound params first3 second3 builder GSWLinearCharacterSmoke.sourceMask 256
      (slot index coordinate level) = 0 := by
  have hu : builder GSWLinearCharacterSmoke.sourceMask (slot index coordinate level) = 0 := by
    simp [builder, slot, coordinates, h]
  rw [GSWLinearCharacterBootstrap.columnBound_zero params first3 second3 builder GSWLinearCharacterSmoke.sourceMask 256 _ hu]
  simp only [slot, coordinates, Equiv.symm_apply_apply]
  rw [GSWLinearCharacterBootstrap.targetPolynomial_eq_zero params index coordinate level h,
    coefficientBound_zero]

/-- Full stored original-bit matrices, one source/error tape, all binary keys.
The selected control includes actual zero-source noise as well as compilation. -/
theorem actual_completed_top_error_bound (bits : Fin 3 → Bool)
    (masks : Matrix (Fin 3) (RecursiveQuadratic.Column 3 6 (2 + controlCount params 3)) (ZMod Q))
    (hmask : (fun row column ↦ masks row (.inl column)) = GSWLinearCharacterSmoke.sourceMask)
    (errors : RecursiveQuadratic.Column 3 6 (2 + controlCount params 3) → ZMod Q)
    (herror : ∀ column, (LatticeCrypto.centeredRepr (errors column)).natAbs ≤ 256) :
    (LatticeCrypto.centeredRepr
      (RecursiveQuadratic.decrypt (GSWSelfKey.binaryEmbed bits)
        (originalView params
          (GSWLinearCharacterBootstrap.freshOriginal params first3 second3 builder bits masks errors) 0
            (finProdFinEquiv (featureEquiv 3 (some (.inr (1, 2))), topLevel))) -
        9223372036854775808 * GSWSelfKey.binaryEmbed bits 0 *
          GSWSelfKey.binaryEmbed bits 1 * GSWSelfKey.binaryEmbed bits 2)).natAbs ≤ 13568 := by
  have h := GSWLinearCharacterBootstrap.freshOriginal_column_bound params first3 second3
    first3_ne_second3 builder bits masks errors 256 herror 0 (some (.inr (1, 2))) topLevel
  dsimp only at h
  rw [hmask, controlMessage_quadratic] at h
  have hw : TFHE.Gadget.Base.gadget params topLevel = (9223372036854775808 : ZMod Q) := by decide
  rw [hw] at h
  exact h.trans ((Nat.add_le_add_left top_columnBound_le ((3 + 1) * 256)).trans_eq (by decide))

end FormalProof4FHETest.GSWLinearCharacterBootstrapSmoke
