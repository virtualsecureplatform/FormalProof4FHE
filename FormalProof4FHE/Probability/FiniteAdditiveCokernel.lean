/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.GroupTheory.Coset.Card

/-!
# Additive-Character Formula for Finite Cokernels

For a homomorphism into a finite abelian group, the cokernel cardinality is exactly the number
of complex additive characters that are trivial on its range.  This is the finite Pontryagin-dual
form needed to turn a cokernel-weighted pair sum into a character moment.
-/

namespace FormalProof4FHE.FiniteAdditiveCokernel

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {Domain Codomain : Type*}
variable [AddCommGroup Domain] [AddCommGroup Codomain]

/-- Complex additive characters of `Codomain` that vanish on an additive subgroup. -/
abbrev Annihilator (subgroup : AddSubgroup Codomain) :=
  {character : AddChar Codomain ℂ //
    ∀ value : subgroup, character value.1 = 1}

/-- Characters of a quotient are exactly characters of the ambient group that vanish on the
quotiented subgroup. -/
noncomputable def quotientAddCharEquivAnnihilator (subgroup : AddSubgroup Codomain) :
    AddChar (Codomain ⧸ subgroup) ℂ ≃ Annihilator subgroup where
  toFun character :=
    ⟨character.compAddMonoidHom (QuotientAddGroup.mk' subgroup), by
      intro value
      rw [AddChar.compAddMonoidHom_apply,
        show (QuotientAddGroup.mk' subgroup value.1) = 0 by
          exact QuotientAddGroup.eq_zero_iff value.1 |>.2 value.2]
      exact character.map_zero_eq_one⟩
  invFun character :=
    AddChar.toAddMonoidHomEquiv.symm
      (QuotientAddGroup.lift subgroup character.1.toAddMonoidHom (by
        intro value hvalue
        rw [AddMonoidHom.mem_ker]
        change Additive.ofMul (character.1 value) = 0
        simpa using character.2 ⟨value, hvalue⟩))
  left_inv character := by
    apply AddChar.ext
    intro value
    obtain ⟨representative, rfl⟩ := QuotientAddGroup.mk'_surjective subgroup value
    simp
  right_inv character := by
    apply Subtype.ext
    apply AddChar.ext
    intro value
    simp

/-- The annihilator has the cardinality of the corresponding finite quotient. -/
theorem card_annihilator_eq_card_quotient [Fintype Codomain]
    (subgroup : AddSubgroup Codomain) :
    Fintype.card (Annihilator subgroup) =
      Fintype.card (Codomain ⧸ subgroup) := by
  calc
    Fintype.card (Annihilator subgroup) =
        Fintype.card (AddChar (Codomain ⧸ subgroup) ℂ) :=
      Fintype.card_congr (quotientAddCharEquivAnnihilator subgroup).symm
    _ = Fintype.card (Codomain ⧸ subgroup) := AddChar.card_eq

/-- Instance-independent cardinality form of quotient-character duality. -/
theorem natCard_annihilator_eq_natCard_quotient [Finite Codomain]
    (subgroup : AddSubgroup Codomain) :
    Nat.card (Annihilator subgroup) = Nat.card (Codomain ⧸ subgroup) := by
  calc
    Nat.card (Annihilator subgroup) =
        Nat.card (AddChar (Codomain ⧸ subgroup) ℂ) :=
      Nat.card_congr (quotientAddCharEquivAnnihilator subgroup).symm
    _ = Nat.card (Codomain ⧸ subgroup) := by
      letI : Fintype (Codomain ⧸ subgroup) := Fintype.ofFinite _
      simpa only [Nat.card_eq_fintype_card] using
        (AddChar.card_eq (α := Codomain ⧸ subgroup))

/-- Finite-group cardinality identity in the form used by real-valued collision accounting. -/
theorem card_div_card_subgroup_eq_card_annihilator [Fintype Codomain]
    (subgroup : AddSubgroup Codomain) :
    (Fintype.card Codomain : ℝ) / Fintype.card subgroup =
      Fintype.card (Annihilator subgroup) := by
  have hcard : Fintype.card Codomain =
      Fintype.card (Codomain ⧸ subgroup) * Fintype.card subgroup := by
    simpa only [Nat.card_eq_fintype_card] using
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup subgroup
  have hsubgroup : (Fintype.card subgroup : ℝ) ≠ 0 := by positivity
  rw [card_annihilator_eq_card_quotient subgroup]
  exact (div_eq_iff hsubgroup).2 (by exact_mod_cast hcard)

/-- The cokernel ratio of an additive homomorphism is the number of characters that annihilate
every value in its range. -/
theorem card_div_card_range_eq_card_annihilator [Fintype Codomain]
    (homomorphism : Domain →+ Codomain) :
    (Fintype.card Codomain : ℝ) / Fintype.card homomorphism.range =
      Fintype.card (Annihilator homomorphism.range) :=
  card_div_card_subgroup_eq_card_annihilator homomorphism.range

/-- Instance-independent version of the cokernel formula, with the annihilator measured by
`Nat.card`. -/
theorem card_div_card_range_eq_natCard_annihilator [Fintype Codomain]
    (homomorphism : Domain →+ Codomain) :
    (Fintype.card Codomain : ℝ) / Fintype.card homomorphism.range =
      Nat.card (Annihilator homomorphism.range) := by
  rw [Nat.card_eq_fintype_card]
  exact card_div_card_range_eq_card_annihilator homomorphism

/-- Fully instance-independent real cokernel ratio. -/
theorem natCard_div_natCard_range_eq_natCard_annihilator [Finite Codomain]
    (homomorphism : Domain →+ Codomain) :
    (Nat.card Codomain : ℝ) / Nat.card homomorphism.range =
      Nat.card (Annihilator homomorphism.range) := by
  have hcard : Nat.card Codomain =
      Nat.card (Codomain ⧸ homomorphism.range) * Nat.card homomorphism.range :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup homomorphism.range
  have hrange : (Nat.card homomorphism.range : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := homomorphism.range)).ne'
  rw [natCard_annihilator_eq_natCard_quotient]
  exact (div_eq_iff hrange).2 (by exact_mod_cast hcard)

end

end FormalProof4FHE.FiniteAdditiveCokernel
