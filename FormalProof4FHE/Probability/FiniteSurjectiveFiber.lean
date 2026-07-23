/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import Mathlib.GroupTheory.Index

/-!
# Exact Preimage Counts for Finite Surjective Homomorphisms

A surjective additive homomorphism between finite groups has fibers of equal cardinality.  This
file packages the corresponding exact count over an arbitrary finite subset of the codomain.
-/

namespace FormalProof4FHE.FiniteSurjectiveFiber

noncomputable section

/-- The preimage of a finite codomain set under a surjective homomorphism consists of one
zero-fiber-sized coset for every element of that set. -/
theorem card_preimage_finset_eq_card_mul_zeroFiber
    {Domain Codomain : Type}
    [AddGroup Domain] [Fintype Domain]
    [AddGroup Codomain] [Fintype Codomain] [DecidableEq Codomain]
    (transform : Domain →+ Codomain) (hsurjective : Function.Surjective transform)
    (target : Finset Codomain) :
    (Finset.univ.filter fun input : Domain ↦ transform input ∈ target).card =
      target.card *
        (Finset.univ.filter fun input : Domain ↦ transform input = 0).card := by
  classical
  have hfiber (value : Codomain) :
      (Finset.univ.filter fun input : Domain ↦ transform input = value).card =
        (Finset.univ.filter fun input : Domain ↦ transform input = 0).card := by
    exact AddMonoidHom.card_fiber_eq_of_mem_range transform
      (Set.mem_range.2 (hsurjective value)) (Set.mem_range.2 (hsurjective 0))
  have hpartition := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter fun input : Domain ↦ transform input ∈ target)
    (t := target) (f := transform) (by
      intro input hinput
      exact (Finset.mem_filter.mp hinput).2)
  calc
    (Finset.univ.filter fun input : Domain ↦ transform input ∈ target).card =
        ∑ value ∈ target,
          ((Finset.univ.filter fun input : Domain ↦ transform input ∈ target).filter
            fun input ↦ transform input = value).card := hpartition
    _ = ∑ _value ∈ target,
          (Finset.univ.filter fun input : Domain ↦ transform input = 0).card := by
      apply Finset.sum_congr rfl
      intro value hvalue
      have hrestricted :
          ((Finset.univ.filter fun input : Domain ↦ transform input ∈ target).filter
              fun input ↦ transform input = value) =
            Finset.univ.filter fun input : Domain ↦ transform input = value := by
        ext input
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact fun hinput => hinput.2
        · intro hinput
          exact ⟨hinput ▸ hvalue, hinput⟩
      rw [hrestricted, hfiber value]
    _ = target.card *
        (Finset.univ.filter fun input : Domain ↦ transform input = 0).card := by
      simp

/-- The zero fiber times the codomain cardinality is the domain cardinality for a finite
surjective additive homomorphism. -/
theorem zeroFiberCard_mul_card_eq_card_of_surjective
    {Domain Codomain : Type}
    [AddGroup Domain] [Fintype Domain]
    [AddGroup Codomain] [Fintype Codomain] [DecidableEq Codomain]
    (transform : Domain →+ Codomain) (hsurjective : Function.Surjective transform) :
    (Finset.univ.filter fun input : Domain ↦ transform input = 0).card *
        Fintype.card Codomain =
      Fintype.card Domain := by
  have hcount := card_preimage_finset_eq_card_mul_zeroFiber
    transform hsurjective (Finset.univ : Finset Codomain)
  simpa [Nat.mul_comm] using hcount.symm

end

end FormalProof4FHE.FiniteSurjectiveFiber
