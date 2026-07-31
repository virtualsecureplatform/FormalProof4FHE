/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SourceAlignedFactorPropagation
import FormalProof4FHE.TFHE.CoefficientStructuredLWE
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Concrete Source-Aligned Gadget Constructions

This file discharges the finite algebraic obligations left by
`SourceAlignedFactorPropagation`:

* coefficient sample extraction is packaged as an additive equivalence;
* every ring gadget canonically induces a scalar gadget satisfying the exact extraction
  compatibility equation;
* the induced KSK body eliminates that scalar suffix and composes with sample extraction at the
  complete phase level;
* any finite mask family is represented by one column gadget with canonical unit factors; and
* all native BRK/TGSW masks are instantiated as one such gadget.  Each control occupies a
  disjoint factor block, so its exact real factor energy is its digit energy and the complete
  block trace has the sum of the per-control energies.

These constructions do not identify the resulting BRK-derived, widened KSK distribution with
the independently sampled native TFHE KSK.  That joint distribution/layout comparison is a
separate cryptographic construction obligation.
-/

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.TFHE.SourceAlignedFactorPropagation.Extraction

noncomputable section

open SubsetKeyTrapdoorTheorems.SourceAligned

theorem reciprocalCoefficients_involutive
    {R : Type} [AddGroup R] {degree : ℕ}
    (polynomial : Fin (degree + 1) → R) :
    SampleExtraction.reciprocalCoefficients
        (SampleExtraction.reciprocalCoefficients polynomial) = polynomial := by
  funext coefficient
  refine Fin.cases ?_ (fun positive ↦ ?_) coefficient
  · rfl
  · simp [SampleExtraction.reciprocalCoefficients]

theorem reciprocalCoefficients_add
    {R : Type} [AddCommGroup R] {degree : ℕ}
    (left right : Fin (degree + 1) → R) :
    SampleExtraction.reciprocalCoefficients (left + right) =
      SampleExtraction.reciprocalCoefficients left +
        SampleExtraction.reciprocalCoefficients right := by
  funext coefficient
  refine Fin.cases ?_ (fun positive ↦ ?_) coefficient
  · rfl
  · simp [SampleExtraction.reciprocalCoefficients, add_comm]

theorem extractVector_add
    {q degree rank : ℕ}
    (left right : Fin rank → RLWE.Rq q (degree + 1)) :
    extractVector (left + right) = extractVector left + extractVector right := by
  funext coordinate
  obtain ⟨⟨component, coefficient⟩, rfl⟩ := finProdFinEquiv.surjective coordinate
  simp only [extractVector, Equiv.symm_apply_apply, Pi.add_apply]
  rw [show LatticeCrypto.Poly.toPi (left component + right component) =
      LatticeCrypto.Poly.toPi (left component) +
        LatticeCrypto.Poly.toPi (right component) by
    exact Native.CoefficientStructuredLWE.coefficientEquiv_add
      q (degree + 1) (left component) (right component)]
  rw [reciprocalCoefficients_add]
  rfl

/-- Coefficient extraction is an additive equivalence, not merely a cardinality equivalence. -/
def extractVectorAddEquiv (q degree rank : ℕ) :
    (Fin rank → RLWE.Rq q (degree + 1)) ≃+
      (Fin (rank * (degree + 1)) → ZMod q) where
  toFun := extractVector
  invFun vector := fun component ↦
    LatticeCrypto.Poly.ofPi
      (SampleExtraction.reciprocalCoefficients fun coefficient ↦
        vector (finProdFinEquiv (component, coefficient)))
  left_inv vector := by
    funext component
    apply LatticeCrypto.Poly.ext_get_eq
    intro coefficient
    simp [extractVector, LatticeCrypto.Poly.ofPi, LatticeCrypto.Poly.toPi,
      Vector.get, reciprocalCoefficients_involutive]
  right_inv vector := by
    funext coordinate
    obtain ⟨⟨component, coefficient⟩, rfl⟩ := finProdFinEquiv.surjective coordinate
    simp only [extractVector, Equiv.symm_apply_apply, LatticeCrypto.Poly.toPi_ofPi,
      reciprocalCoefficients_involutive]
  map_add' := extractVector_add

@[simp]
theorem extractVectorAddEquiv_apply
    {q degree rank : ℕ}
    (vector : Fin rank → RLWE.Rq q (degree + 1)) :
    extractVectorAddEquiv q degree rank vector = extractVector vector := by
  rfl

/-- The scalar additive map obtained by conjugating a ring gadget through sample extraction. -/
def inducedScalarAddHom {q degree suffixRank factorRank : ℕ}
    (ringGadget : Matrix (Fin suffixRank) (Fin factorRank)
      (RLWE.Rq q (degree + 1))) :
    (Fin (factorRank * (degree + 1)) → ZMod q) →+
      (Fin (suffixRank * (degree + 1)) → ZMod q) :=
  (extractVectorAddEquiv q degree suffixRank).toAddMonoidHom.comp
    (ringGadget.mulVecLin.toAddMonoidHom.comp
      (extractVectorAddEquiv q degree factorRank).symm.toAddMonoidHom)

/-- Every additive map between `ZMod q` modules is canonically `ZMod q`-linear. -/
def inducedScalarLinearMap {q degree suffixRank factorRank : ℕ}
    (ringGadget : Matrix (Fin suffixRank) (Fin factorRank)
      (RLWE.Rq q (degree + 1))) :
    (Fin (factorRank * (degree + 1)) → ZMod q) →ₗ[ZMod q]
      (Fin (suffixRank * (degree + 1)) → ZMod q) :=
  (inducedScalarAddHom ringGadget).toZModLinearMap q

/-- Canonical scalar gadget induced from a ring gadget by coefficient sample extraction. -/
def inducedScalarGadget {q degree suffixRank factorRank : ℕ}
    (ringGadget : Matrix (Fin suffixRank) (Fin factorRank)
      (RLWE.Rq q (degree + 1))) :
    Matrix (Fin (suffixRank * (degree + 1)))
      (Fin (factorRank * (degree + 1))) (ZMod q) :=
  LinearMap.toMatrix' (inducedScalarLinearMap ringGadget)

@[simp]
theorem inducedScalarGadget_mulVec
    {q degree suffixRank factorRank : ℕ}
    (ringGadget : Matrix (Fin suffixRank) (Fin factorRank)
      (RLWE.Rq q (degree + 1)))
    (vector : Fin (factorRank * (degree + 1)) → ZMod q) :
    inducedScalarGadget ringGadget *ᵥ vector =
      extractVector
        (ringGadget *ᵥ (extractVectorAddEquiv q degree factorRank).symm vector) := by
  rw [inducedScalarGadget, LinearMap.toMatrix'_mulVec]
  rfl

/-- The induced scalar gadget satisfies the previously explicit compatibility obligation. -/
theorem inducedScalarGadget_compatible
    {q degree suffixRank factorRank : ℕ}
    (ringGadget : Matrix (Fin suffixRank) (Fin factorRank)
      (RLWE.Rq q (degree + 1))) :
    GadgetCompatible ringGadget (inducedScalarGadget ringGadget) := by
  intro factor
  rw [inducedScalarGadget_mulVec]
  have hinverse :
      (extractVectorAddEquiv q degree factorRank).symm (extractVector factor) = factor := by
    change (extractVectorAddEquiv q degree factorRank).symm
        (extractVectorAddEquiv q degree factorRank factor) = factor
    exact (extractVectorAddEquiv q degree factorRank).symm_apply_apply factor
  rw [hinverse]

/-- KSK bodies for the induced scalar gadget, in the source-aligned layout. -/
def inducedKeySwitchBody
    {q degree prefixRank suffixRank factorRank : ℕ}
    (ringGadget : Matrix (Fin suffixRank) (Fin factorRank)
      (RLWE.Rq q (degree + 1)))
    (prefixMask : Matrix
      (Fin (prefixRank * (degree + 1)))
      (Fin (factorRank * (degree + 1))) (ZMod q))
    (prefixSecret : Fin prefixRank → RLWE.Rq q (degree + 1))
    (suffixSecret : Fin suffixRank → RLWE.Rq q (degree + 1))
    (error : Fin (factorRank * (degree + 1)) → ZMod q) :
    Fin (factorRank * (degree + 1)) → ZMod q :=
  randomGadgetKSKBody prefixMask (inducedScalarGadget ringGadget)
    (SampleExtraction.extractedSecret prefixSecret)
    (SampleExtraction.extractedSecret suffixSecret) error

/-- Sample extraction followed by the induced KSK eliminates the complete extracted suffix mask
with exactly the coefficient-extracted ring phase and the selected KSK error. -/
theorem keySwitch_after_apply_phase
    {q degree prefixRank suffixRank factorRank : ℕ} [NeZero q]
    (ringGadget : Matrix (Fin suffixRank) (Fin factorRank)
      (RLWE.Rq q (degree + 1)))
    (prefixMask : Matrix
      (Fin (prefixRank * (degree + 1)))
      (Fin (factorRank * (degree + 1))) (ZMod q))
    (prefixSecret : Fin prefixRank → RLWE.Rq q (degree + 1))
    (suffixSecret : Fin suffixRank → RLWE.Rq q (degree + 1))
    (error : Fin (factorRank * (degree + 1)) → ZMod q)
    (ciphertext : FactorCiphertext (RLWE.Rq q (degree + 1))
      (Fin prefixRank) (Fin suffixRank) (Fin factorRank)) :
    ((apply ciphertext).keySwitch prefixMask
        (inducedKeySwitchBody ringGadget prefixMask prefixSecret suffixSecret error)).2 -
      dotProduct (SampleExtraction.extractedSecret prefixSecret)
        ((apply ciphertext).keySwitch prefixMask
          (inducedKeySwitchBody ringGadget prefixMask prefixSecret suffixSecret error)).1 =
      SampleExtraction.constantCoefficient
          (ciphertext.phase ringGadget prefixSecret suffixSecret) -
        dotProduct (extractVector ciphertext.factor) error := by
  unfold inducedKeySwitchBody
  rw [FactorCiphertext.keySwitch_phase]
  rw [phase_apply ringGadget (inducedScalarGadget ringGadget)
    (inducedScalarGadget_compatible ringGadget)]
  rfl

end

end FormalProof4FHE.TFHE.SourceAlignedFactorPropagation.Extraction

namespace FormalProof4FHE.TFHE.SourceAlignedFactorPropagation.ColumnAlignment

open SubsetKeyTrapdoorTheorems.SourceAligned

noncomputable section

set_option linter.unusedSectionVars false

section Algebra

variable {R Prefix Suffix Row : Type} [CommRing R]
  [Fintype Prefix] [Fintype Suffix] [Fintype Row] [DecidableEq Row]

/-- Regard an arbitrary finite family of public suffix masks as the columns of one gadget. -/
def columnGadget (suffixMasks : Row → Suffix → R) : Matrix Suffix Row R :=
  fun suffix row ↦ suffixMasks row suffix

/-- The canonical factor selecting one column of `columnGadget`. -/
def unitFactor (row : Row) : Row → R :=
  Pi.single row 1

@[simp]
theorem columnGadget_mulVec_unitFactor
    (suffixMasks : Row → Suffix → R) (row : Row) :
    columnGadget suffixMasks *ᵥ unitFactor row = suffixMasks row := by
  rw [unitFactor, Matrix.mulVec_single_one]
  rfl

/-- Attach the canonical unit factor to each row in a public mask/body family. -/
def alignedRow
    (prefixMasks : Row → Prefix → R)
    (bodies : Row → R) (row : Row) :
    FactorCiphertext R Prefix Suffix Row where
  prefixMask := prefixMasks row
  factor := unitFactor row
  body := bodies row

@[simp]
theorem alignedRow_suffixMask
    (prefixMasks : Row → Prefix → R)
    (suffixMasks : Row → Suffix → R)
    (bodies : Row → R) (row : Row) :
    (alignedRow prefixMasks bodies row).suffixMask (columnGadget suffixMasks) =
      suffixMasks row := by
  exact columnGadget_mulVec_unitFactor suffixMasks row

@[simp]
theorem alignedRow_phase
    (prefixMasks : Row → Prefix → R)
    (suffixMasks : Row → Suffix → R)
    (bodies : Row → R) (row : Row)
    (prefixSecret : Prefix → R) (suffixSecret : Suffix → R) :
    (alignedRow prefixMasks bodies row).phase (columnGadget suffixMasks)
        prefixSecret suffixSecret =
      bodies row - dotProduct prefixSecret (prefixMasks row) -
        dotProduct suffixSecret (suffixMasks row) := by
  unfold FactorCiphertext.phase
  rw [alignedRow_suffixMask]
  rfl

/-- A weighted sum of canonically aligned rows carries exactly the weight vector. -/
@[simp]
theorem linearCombination_alignedRow_factor
    (prefixMasks : Row → Prefix → R)
    (bodies : Row → R) (weights : Row → R) :
    (FactorCiphertext.linearCombination weights
      (alignedRow (Suffix := Suffix) prefixMasks bodies)).factor = weights := by
  funext coordinate
  simp [FactorCiphertext.linearCombination, alignedRow, unitFactor, Pi.single_apply]

end Algebra

section Energy

variable {Row : Type} [Fintype Row] [DecidableEq Row]

@[simp]
theorem factorEnergy_unitFactor (row : Row) :
    Energy.factorEnergy (unitFactor (R := ℝ) row) = 1 := by
  simp [Energy.factorEnergy, unitFactor, Pi.single_apply]

theorem factorInner_unitFactor
    (left right : Row) :
    Energy.factorInner (unitFactor (R := ℝ) left) (unitFactor right) =
      if left = right then 1 else 0 := by
  by_cases heq : left = right
  · subst right
    simp [Energy.factorInner_self]
  · have hreverse : right ≠ left := Ne.symm heq
    simp [Energy.factorInner, unitFactor, Pi.single_apply, heq, hreverse]

theorem sum_factorEnergy_unitFactor :
    (∑ row : Row, Energy.factorEnergy (unitFactor (R := ℝ) row)) =
      (Fintype.card Row : ℝ) := by
  simp

theorem factorEnergy_linearCombination_alignedRow
    {Prefix Suffix : Type} [Fintype Prefix] [Fintype Suffix]
    (prefixMasks : Row → Prefix → ℝ)
    (bodies : Row → ℝ) (weights : Row → ℝ) :
    Energy.factorEnergy
        (FactorCiphertext.linearCombination weights
          (alignedRow (Suffix := Suffix) prefixMasks bodies)).factor =
      ∑ row, (weights row) ^ 2 := by
  rw [linearCombination_alignedRow_factor]
  rfl

end Energy

end


end FormalProof4FHE.TFHE.SourceAlignedFactorPropagation.ColumnAlignment

namespace FormalProof4FHE.TFHE.SourceAlignedFactorPropagation.NativeAlignment

open SubsetKeyTrapdoorTheorems.SourceAligned
open ColumnAlignment

noncomputable section

set_option linter.unusedSectionVars false

/-- Total number of native BRK/TGSW rows, flattened first by control and then by TGSW row. -/
abbrev controlRowCount (ringRank levels lweDimension : ℕ) :=
  lweDimension * TGSW.rowCount ringRank levels

/-- Recover the control coordinate and TGSW row from a flattened native row. -/
def controlRowIndex {ringRank levels lweDimension : ℕ}
    (row : Fin (controlRowCount ringRank levels lweDimension)) :
    Fin lweDimension × Fin (TGSW.rowCount ringRank levels) :=
  finProdFinEquiv.symm row

/-- All native BRK row masks, arranged as columns of one ring gadget. -/
def commonRingGadget
    {q degree ringRank levels lweDimension : ℕ}
    (bootstrappingKey : Native.BootstrappingKey
      q degree ringRank levels lweDimension) :
    Matrix (Fin ringRank) (Fin (controlRowCount ringRank levels lweDimension))
      (RLWE.Rq q degree) :=
  fun coordinate row ↦
    (TLWE.entry
      (bootstrappingKey (controlRowIndex row).1)
      (controlRowIndex row).2).mask coordinate

/-- The scalar gadget canonically induced from all native BRK row masks. -/
def commonScalarGadget
    {q degree ringRank levels lweDimension : ℕ}
    (bootstrappingKey : Native.BootstrappingKey
      q (degree + 1) ringRank levels lweDimension) :
    Matrix (Fin (ringRank * (degree + 1)))
      (Fin (controlRowCount ringRank levels lweDimension * (degree + 1))) (ZMod q) :=
  Extraction.inducedScalarGadget (commonRingGadget bootstrappingKey)

/-- The native common ring gadget and its induced scalar gadget satisfy sample-extraction
compatibility by construction. -/
theorem commonScalarGadget_compatible
    {q degree ringRank levels lweDimension : ℕ}
    (bootstrappingKey : Native.BootstrappingKey
      q (degree + 1) ringRank levels lweDimension) :
    Extraction.GadgetCompatible (commonRingGadget bootstrappingKey)
      (commonScalarGadget bootstrappingKey) := by
  exact Extraction.inducedScalarGadget_compatible
    (commonRingGadget bootstrappingKey)

/-- Body of a selected native BRK/TGSW row. -/
def controlRowBody
    {q degree ringRank levels lweDimension : ℕ}
    (bootstrappingKey : Native.BootstrappingKey
      q degree ringRank levels lweDimension)
    (row : Fin (controlRowCount ringRank levels lweDimension)) :
    RLWE.Rq q degree :=
  (TLWE.entry
    (bootstrappingKey (controlRowIndex row).1)
    (controlRowIndex row).2).body

/-- Canonical factor annotation of a flattened native BRK row. -/
def alignedControlRow
    {q degree ringRank levels lweDimension : ℕ}
    (bootstrappingKey : Native.BootstrappingKey
      q degree ringRank levels lweDimension)
    (row : Fin (controlRowCount ringRank levels lweDimension)) :
    FactorCiphertext (RLWE.Rq q degree) (Fin 0) (Fin ringRank)
      (Fin (controlRowCount ringRank levels lweDimension)) :=
  alignedRow (Suffix := Fin ringRank) (fun _ _ ↦ 0)
    (controlRowBody bootstrappingKey) row

@[simp]
theorem alignedControlRow_suffixMask
    {q degree ringRank levels lweDimension : ℕ}
    (bootstrappingKey : Native.BootstrappingKey
      q degree ringRank levels lweDimension)
    (row : Fin (controlRowCount ringRank levels lweDimension)) :
    (alignedControlRow bootstrappingKey row).suffixMask
        (commonRingGadget bootstrappingKey) =
      (TLWE.entry
        (bootstrappingKey (controlRowIndex row).1)
        (controlRowIndex row).2).mask := by
  exact columnGadget_mulVec_unitFactor
    (fun row coordinate ↦
      (TLWE.entry
        (bootstrappingKey (controlRowIndex row).1)
        (controlRowIndex row).2).mask coordinate)
    row

@[simp]
theorem alignedControlRow_body
    {q degree ringRank levels lweDimension : ℕ}
    (bootstrappingKey : Native.BootstrappingKey
      q degree ringRank levels lweDimension)
    (row : Fin (controlRowCount ringRank levels lweDimension)) :
    (alignedControlRow bootstrappingKey row).body =
      (TLWE.entry
        (bootstrappingKey (controlRowIndex row).1)
        (controlRowIndex row).2).body := by
  rfl

/-- Materializing the implicit suffix mask recovers the complete native BRK row exactly. -/
theorem alignedControlRow_materialize
    {q degree ringRank levels lweDimension : ℕ}
    (bootstrappingKey : Native.BootstrappingKey
      q degree ringRank levels lweDimension)
    (row : Fin (controlRowCount ringRank levels lweDimension)) :
    (⟨(alignedControlRow bootstrappingKey row).suffixMask
        (commonRingGadget bootstrappingKey),
      (alignedControlRow bootstrappingKey row).body⟩ :
        TLWE.Ciphertext (RLWE.Rq q degree) ringRank) =
      TLWE.entry
        (bootstrappingKey (controlRowIndex row).1)
        (controlRowIndex row).2 := by
  rw [TLWE.Ciphertext.mk.injEq]
  exact ⟨alignedControlRow_suffixMask bootstrappingKey row,
    alignedControlRow_body bootstrappingKey row⟩

/-- Embed one control's TGSW digit vector into its disjoint block of the global factor. -/
def controlFactor {R : Type} [CommRing R]
    {ringRank levels lweDimension : ℕ}
    (control : Fin lweDimension)
    (weights : Fin (TGSW.rowCount ringRank levels) → R) :
    Fin (controlRowCount ringRank levels lweDimension) → R :=
  fun row ↦
    if (controlRowIndex row).1 = control then weights (controlRowIndex row).2 else 0

/-- A native external product against one control carries exactly that control's digit block. -/
theorem linearCombination_alignedControlRow_factor
    {q degree ringRank levels lweDimension : ℕ}
    (bootstrappingKey : Native.BootstrappingKey
      q degree ringRank levels lweDimension)
    (control : Fin lweDimension)
    (weights : Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q degree) :
    (FactorCiphertext.linearCombination weights fun row ↦
      alignedControlRow bootstrappingKey
        (finProdFinEquiv (control, row))).factor =
      controlFactor control weights := by
  funext coordinate
  obtain ⟨⟨otherControl, otherRow⟩, rfl⟩ :=
    finProdFinEquiv.surjective coordinate
  by_cases hcontrol : otherControl = control
  · subst otherControl
    simp [FactorCiphertext.linearCombination, alignedControlRow, alignedRow,
      unitFactor, controlFactor, controlRowIndex, Pi.single_apply]
  · simp [FactorCiphertext.linearCombination, alignedControlRow, alignedRow,
      unitFactor, controlFactor, controlRowIndex, Pi.single_apply, hcontrol]

/-- The exact real energy of one disjoint native control block is its digit energy. -/
theorem factorEnergy_controlFactor
    {ringRank levels lweDimension : ℕ}
    (control : Fin lweDimension)
    (weights : Fin (TGSW.rowCount ringRank levels) → ℝ) :
    Energy.factorEnergy (controlFactor control weights) =
      ∑ row, (weights row) ^ 2 := by
  unfold Energy.factorEnergy
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp [controlFactor, controlRowIndex]

/-- Assemble every control block into the global factor without overlaps. -/
def traceFactor
    {ringRank levels lweDimension : ℕ}
    (weights : Fin lweDimension → Fin (TGSW.rowCount ringRank levels) → ℝ) :
    Fin (controlRowCount ringRank levels lweDimension) → ℝ :=
  fun row ↦ weights (controlRowIndex row).1 (controlRowIndex row).2

/-- Adding the disjoint per-control factors produces the assembled trace factor exactly. -/
theorem sum_controlFactor_eq_traceFactor
    {ringRank levels lweDimension : ℕ}
    (weights : Fin lweDimension → Fin (TGSW.rowCount ringRank levels) → ℝ) :
    (∑ control, controlFactor control (weights control)) = traceFactor weights := by
  funext coordinate
  obtain ⟨⟨selectedControl, selectedRow⟩, rfl⟩ :=
    finProdFinEquiv.surjective coordinate
  simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single selectedControl]
  · simp [controlFactor, traceFactor, controlRowIndex]
  · intro other _ hne
    have hreverse : selectedControl ≠ other := Ne.symm hne
    simp [controlFactor, controlRowIndex, hreverse]
  · intro hnot
    exact (hnot (Finset.mem_univ selectedControl)).elim

/-- Exact trace energy is the sum of the per-control digit energies; there is no cross-control
or exponential factor in this disjoint-column representation. -/
theorem factorEnergy_traceFactor
    {ringRank levels lweDimension : ℕ}
    (weights : Fin lweDimension → Fin (TGSW.rowCount ringRank levels) → ℝ) :
    Energy.factorEnergy (traceFactor weights) =
      ∑ control, ∑ row, (weights control row) ^ 2 := by
  unfold Energy.factorEnergy
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp [traceFactor, controlRowIndex]

/-- Consequently, the energy of the accumulated disjoint control factors is the sum of their
individual digit energies. -/
theorem factorEnergy_sum_controlFactor
    {ringRank levels lweDimension : ℕ}
    (weights : Fin lweDimension → Fin (TGSW.rowCount ringRank levels) → ℝ) :
    Energy.factorEnergy (∑ control, controlFactor control (weights control)) =
      ∑ control, ∑ row, (weights control row) ^ 2 := by
  rw [sum_controlFactor_eq_traceFactor, factorEnergy_traceFactor]

end

end FormalProof4FHE.TFHE.SourceAlignedFactorPropagation.NativeAlignment
