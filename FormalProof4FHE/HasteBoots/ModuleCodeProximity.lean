/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in vendor/ArkLib/LICENSE.
Authors of the underlying AHIV22 proofs: Katerina Hristova, František Silváši,
  Chung Thai Nguyen, Elias Judin, Aristotle (Harmonic).
Adapted from the pinned ArkLib AHIV22 and AHIV22Support modules to separate
scalar field and symbol module, and to derive independent test-row repetition.
-/
module

public import ArkLib.Data.CodingTheory.ProximityGap.AHIV22
public import FormalProof4FHE.HasteBoots.UniformImage
public import FormalProof4FHE.HasteBoots.ColumnSampling

@[expose] public section

/-! Proximity testing of module-valued linear codes with base-field coins.
Symbols need not be scalars in the coin field. For a fixed far word, each
random base-field row has error at most δ/|F|; `width` independent rows have
error at most (δ/|F|)^width. The radius must satisfy 3r < δ and r < |F|.
This conservative rectangular law does not assert δ/|F|^width, production
Fiat–Shamir freshness, or independence of shared column checks. -/

namespace FormalProof4FHE.HasteBoots.ModuleCodeProximity
noncomputable section

variable {F A : Type} [Field F] [AddCommGroup A] [Module F A]

/-- Recover a module-valued affine direction from two different scalar evaluations. -/
theorem direction_eq {u v c₀ c₁ : A} {r₀ r₁ : F}
    (h₀ : u + r₀ • v = c₀) (h₁ : u + r₁ • v = c₁) (hr : r₁ ≠ r₀) :
    v = (r₁-r₀)⁻¹ • (c₁-c₀) := by
  have difference : (r₁-r₀) • v = c₁-c₀ := by
    rw [sub_smul,← h₁,← h₀]
    abel
  rw [← difference,smul_smul,inv_mul_cancel₀ (sub_ne_zero.mpr hr),one_smul]

/-- Two different scalars determine the same affine direction, without multiplying symbols. -/
theorem directions_eq {u v c w : A} {r s : F}
    (hr : u+r • v = c+r • w) (hs : u+s • v = c+s • w) (hrs : r ≠ s) :
    v = w := by
  have zero : (r-s) • (v-w) = 0 := by
    rw [sub_smul,smul_sub,smul_sub]
    calc
      (r • v-r • w)-(s • v-s • w) =
          (u+r • v-(c+r • w))-(u+s • v-(c+s • w)) := by abel
      _ = 0 := by rw [hr,hs]; abel
  have cancel := congrArg (fun value : A => (r-s)⁻¹ • value) zero
  simpa only [smul_smul,inv_mul_cancel₀ (sub_ne_zero.mpr hrs),one_smul,smul_zero,sub_eq_zero] using cancel

open Code ProbabilityTheory
open scoped ProbabilityTheory
open scoped BigOperators
variable [Fintype F] {ι : Type} [Fintype ι] [DecidableEq A]

/-- More than the code distance many close scalars force common nearby base and direction codewords. -/
theorem many_close_scalars
    (CRS : Submodule F (ι → A)) {e : ℕ} {u v : ι → A}
    (h3e_lt : 3 * e < ‖(CRS : Set (ι → A))‖₀)
    (hRS_gt' : ‖(CRS : Set (ι → A))‖₀ <
      Nat.card {r : F // Δ₀(u + r • v, (CRS : Set (ι → A))) ≤ e}) :
    ∃ cBase ∈ CRS, ∃ w ∈ CRS, ∃ D : Finset ι, D.card ≤ e ∧
      ∀ j ∉ D, u j = cBase j ∧ v j = w j := by
  classical
  set C : Set (ι → A) := (CRS : Set (ι → A))
  let RS : Type := {r : F // Δ₀(u + r • v, C) ≤ e}
  have hRS_gt : ‖C‖₀ < Fintype.card RS := by
    rw [← Nat.card_eq_fintype_card]
    exact hRS_gt'
  have huniv_one_lt : 1 < (Finset.univ : Finset RS).card := by
    rw [Finset.card_univ]
    omega
  obtain ⟨r0, -, r1, -, hr01⟩ := Finset.one_lt_card.mp huniv_one_lt
  -- Decode each good scalar to a codeword and a disagreement set of size at most `e`.
  have h_close_codeword (r : RS) : ∃ c ∈ C, Δ₀(u + r.1 • v, c) ≤ e :=
    (Code.closeToCode_iff_closeToCodeword_of_minDist (u := u + r.1 • v) (C := C) (e := e)).1
      r.2
  choose c hc_mem hc_dist using h_close_codeword
  have h_disagree (r : RS) :
      ∃ D : Finset ι, D.card ≤ e ∧ ∀ j, j ∉ D → (u + r.1 • v) j = c r j :=
    (Code.closeToWord_iff_exists_possibleDisagreeCols (u := u + r.1 • v) (v := c r) (e := e)).1
      (hc_dist r)
  choose E hE_card hE_agree using h_disagree
  have hE_agree' (r : RS) (j : ι) (hj : j ∉ E r) : u j + r.1 • v j = c r j :=
    hE_agree r j hj
  -- The direction codeword `w` and the base codeword `cBase`, read off from `r0` and `r1`.
  let w : ι → A := (r1.1 - r0.1)⁻¹ • (c r1 - c r0)
  let cBase : ι → A := c r0 - r0.1 • w
  have hw_mem : w ∈ CRS := CRS.smul_mem _ (CRS.sub_mem (hc_mem r1) (hc_mem r0))
  have hcBase_mem : cBase ∈ CRS := CRS.sub_mem (hc_mem r0) (CRS.smul_mem _ hw_mem)
  have h_base (j : ι) (h0 : j ∉ E r0) (h1 : j ∉ E r1) : u j = cBase j ∧ v j = w j := by
    have hv : v j = w j :=
      direction_eq (hE_agree' r0 j h0) (hE_agree' r1 j h1)
        fun h ↦ hr01 (Subtype.ext h.symm)
    refine ⟨?_, hv⟩
    simp only [cBase, Pi.sub_apply, Pi.smul_apply, ← hv, ← hE_agree' r0 j h0]
    abel
  -- Every decoded codeword lies on the line `cBase + r • w`: the two codewords agree outside
  -- `E r0 ∪ E r1 ∪ E r`, which has fewer than `‖C‖₀` elements.
  have h_codeword_eq (r : RS) : c r = cBase + r.1 • w := by
    refine Code.eq_of_lt_dist (C := C) (hc_mem r) (CRS.add_mem hcBase_mem (CRS.smul_mem _ hw_mem))
      (lt_of_le_of_lt (hamming_dist_le_of_subset_disagree (E r0 ∪ E r1 ∪ E r) fun j hj ↦ ?_) ?_)
    · by_contra hU
      simp only [Finset.mem_union, not_or] at hU
      obtain ⟨hu, hv⟩ := h_base j hU.1.1 hU.1.2
      refine hj ?_
      rw [← hE_agree' r j hU.2]
      simp only [Pi.add_apply, Pi.smul_apply, hu, hv]
    · have h3 := (Finset.card_union_le (E r0 ∪ E r1) (E r)).trans
        (Nat.add_le_add_right (Finset.card_union_le (E r0) (E r1)) _)
      have := hE_card r0
      have := hE_card r1
      have := hE_card r
      omega
  have h_line (r : RS) (j : ι) (hj : j ∉ E r) : u j + r.1 • v j = cBase j + r.1 • w j := by
    rw [hE_agree' r j hj, h_codeword_eq r]
    rfl
  -- The global disagreement set where `u` or `v` fail to match `cBase`/`w`.
  let D : Finset ι := {j | u j ≠ cBase j ∨ v j ≠ w j}
  -- At a coordinate of `D`, at most one good scalar avoids its disagreement set.
  have h_err_ge (j : ι) (hj : j ∈ D) :
      Fintype.card RS - 1 ≤ (Finset.univ.filter fun r : RS ↦ j ∈ E r).card := by
    have hclean_le1 : (Finset.univ.filter fun r : RS ↦ j ∉ E r).card ≤ 1 := by
      refine Finset.card_le_one.2 fun r hr s hs ↦ Subtype.ext ?_
      by_contra hrs
      have hr' : j ∉ E r := (Finset.mem_filter.mp hr).2
      have hs' : j ∉ E s := (Finset.mem_filter.mp hs).2
      have hv : v j = w j :=
        directions_eq (h_line r j hr') (h_line s j hs') hrs
      have hu : u j = cBase j := add_right_cancel (hv ▸ h_line r j hr')
      exact (Finset.mem_filter.mp hj).2.elim (· hu) (· hv)
    have hpart := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset RS))
      (p := fun r : RS ↦ j ∈ E r)
    rw [Finset.card_univ] at hpart
    omega
  -- Count the incidences `j ∈ E r` over `j ∈ D` from both sides.
  have h_incidences : ∑ j, (Finset.univ.filter fun r : RS ↦ j ∈ E r).card = ∑ r, (E r).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have h_pairs : D.card * (Fintype.card RS - 1) ≤ Fintype.card RS * e :=
    calc
      D.card * (Fintype.card RS - 1)
          ≤ ∑ j ∈ D, (Finset.univ.filter fun r : RS ↦ j ∈ E r).card :=
        smul_eq_mul D.card _ ▸ Finset.card_nsmul_le_sum D _ _ h_err_ge
      _ ≤ ∑ j, (Finset.univ.filter fun r : RS ↦ j ∈ E r).card :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ D)
      _ = ∑ r, (E r).card := h_incidences
      _ ≤ ∑ _r : RS, e := Finset.sum_le_sum fun r _ ↦ hE_card r
      _ = Fintype.card RS * e := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hD_card : D.card ≤ e := by
    by_contra hD_gt
    obtain ⟨m, hm⟩ : ∃ m, Fintype.card RS = m + 1 := ⟨Fintype.card RS - 1, by omega⟩
    have hle : (e + 1) * m ≤ (m + 1) * e := by
      rw [hm, Nat.add_sub_cancel] at h_pairs
      exact (Nat.mul_le_mul_right m (by omega)).trans h_pairs
    rw [add_mul, one_mul, add_mul, one_mul, mul_comm m e] at hle
    omega
  exact ⟨cBase, hcBase_mem, w, hw_mem, D, hD_card, fun j hj ↦ by simpa [D, not_or] using hj⟩


/-- A far direction permits at most the code distance many close points on every affine line. -/
theorem few_close_scalars (code : Submodule F (ι → A)) (radius : ℕ) (u v : ι → A)
    (small : 3*radius < Code.minDist (code : Set (ι → A)))
    (far : radius < Code.distFromCode v (code : Set (ι → A))) :
    Nat.card {r : F // Code.distFromCode (u+r • v) (code : Set (ι → A)) ≤ radius} ≤
      Code.minDist (code : Set (ι → A)) := by
  apply le_of_not_gt
  intro many
  obtain ⟨_,_,w,coded,D,size,agree⟩ := many_close_scalars code (e := radius) (u := u) (v := v)
    (by simpa only [Code.dist_eq_minDist] using small)
    (by simpa only [Code.dist_eq_minDist] using many)
  have close : hammingDist v w ≤ D.card :=
    hamming_dist_le_of_subset_disagree D (fun j different => by
      by_contra outside
      exact different (agree j outside).2)
  exact not_lt_of_ge ((Code.distFromCode_le_dist_to_mem _ _ coded).trans
    (by exact_mod_cast close.trans size)) far

/-- Nonzero whole symbols, counted by column rather than scalar coordinate. -/
def support (value : ι → A) : Finset ι := Finset.univ.filter (fun j => value j ≠ 0)

/-- Sparse vectors in a finite module subspace share one small support when the scalar field is larger than the radius. -/
theorem common_support [Finite A] (space : Submodule F (ι → A)) (radius : ℕ)
    (sparse : ∀ value : space, (support (value : ι → A)).card ≤ radius)
    (large : radius < Fintype.card F) :
    ∃ D : Finset ι, D.card ≤ radius ∧ ∀ value : space, ∀ j, j ∉ D → (value : ι → A) j = 0 := by
  classical
  let : Fintype space := Fintype.ofFinite space
  let weight : space → ℕ := fun value => (support (value : ι → A)).card
  obtain ⟨base,maximal⟩ := Finset.exists_maximalFor (f := weight)
    (s := (Finset.univ : Finset space)) Finset.univ_nonempty
  have maxWeight (value : space) : weight value ≤ weight base := by
    by_contra larger
    exact (not_lt_of_ge (maximal.2 (by simp) (Nat.le_of_lt (lt_of_not_ge larger))))
      (lt_of_not_ge larger)
  let D := support (base : ι → A)
  refine ⟨D,sparse base, ?_⟩
  intro value i outside
  by_contra nonzero
  have baseZero : (base : ι → A) i = 0 := by simpa [D,support] using outside
  let S := D.filter (fun j => (value : ι → A) j ≠ 0)
  have subset : S ⊆ support (value : ι → A) := by
    intro j member
    simp only [S,Finset.mem_filter] at member
    simpa [support] using member.2
  have strict : S.card < (support (value : ι → A)).card := by
    apply Finset.card_lt_card
    refine ⟨subset, ?_⟩
    intro reverse
    have inSupport : i ∈ support (value : ι → A) := by simpa [support] using nonzero
    exact outside (Finset.mem_filter.mp (reverse inSupport)).1
  have smallS : S.card+1 ≤ D.card :=
    Nat.succ_le_of_lt (strict.trans_le (maxWeight value))
  let cancel := fun j => (Finset.univ : Finset F).filter
    (fun scalar => (base : ι → A) j+scalar • (value : ι → A) j = 0)
  let bad := S.biUnion cancel
  have cancelSize (j : ι) (member : j ∈ S) : (cancel j).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro r hr t ht
    apply smul_left_injective F (Finset.mem_filter.mp member).2
    exact add_left_cancel ((Finset.mem_filter.mp hr).2.trans (Finset.mem_filter.mp ht).2.symm)
  have badSize : bad.card ≤ S.card := by
    calc
      bad.card ≤ ∑ j ∈ S, (cancel j).card := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ S, 1 := Finset.sum_le_sum cancelSize
      _ = S.card := by simp
  have bounded : (insert 0 bad).card < Fintype.card F :=
    (Finset.card_insert_le 0 bad).trans_lt
      ((Nat.add_le_add_right badSize 1).trans_lt (smallS.trans_lt ((sparse base).trans_lt large)))
  obtain ⟨scalar,member⟩ := Finset.card_pos.mp
    (show 0 < ((Finset.univ : Finset F) \ insert 0 bad).card by
      simpa only [Finset.card_univ_sdiff] using Nat.sub_pos_of_lt bounded)
  have notBad := (Finset.mem_sdiff.mp member).2
  have scalarNonzero : scalar ≠ 0 := by
    intro same
    exact notBad (by simp [same])
  have oldSupport : D ⊆ support ((base : ι → A)+scalar • (value : ι → A)) := by
    intro j inD
    have baseNonzero : (base : ι → A) j ≠ 0 := by simpa [D,support] using inD
    by_cases valueZero : (value : ι → A) j = 0
    · simpa [support,valueZero] using baseNonzero
    · simp only [support,Finset.mem_filter,Finset.mem_univ,true_and,Pi.add_apply,Pi.smul_apply]
      intro vanishes
      apply notBad
      apply Finset.mem_insert_of_mem
      apply Finset.mem_biUnion.mpr
      exact ⟨j,by simp [S,inD,valueZero],by simp [cancel,vanishes]⟩
  have newCoordinate : i ∈ support ((base : ι → A)+scalar • (value : ι → A)) := by
    simp [support,baseZero,scalarNonzero,nonzero]
  have grows : D.card < (support ((base : ι → A)+scalar • (value : ι → A))).card := by
    apply Finset.card_lt_card
    exact ⟨oldSupport,fun reverse => outside (reverse newCoordinate)⟩
  exact (not_lt_of_ge (maxWeight (base+scalar • value))) grows


/-- A column-wise far stack has a far base-field linear combination of its source rows. -/
theorem far_direction [Finite A] {κ : Type} [Fintype κ]
    (L : Submodule F (ι → A)) (U_star : WordStack (A := A) κ ι) (e : ℕ)
    (hF : e < Fintype.card F) (small : 3*e < Code.minDist (L : Set (ι → A)))
    (hU : e < Code.distFromCode (⋈|U_star) (L^⋈κ)) :
    ∃ v ∈ Submodule.span F (Set.range U_star), e < Code.distFromCode v (L : Set (ι → A)) := by
  classical
  have h3e_lt_d : 3*e < ‖(L : Set (ι → A))‖₀ := by
    simpa only [Code.dist_eq_minDist] using small
  have h2e_lt_d : 2 * e < ‖(L : Set (ι → A))‖₀ := by omega
  by_contra h_contra
  push Not at h_contra
  have h_close (v : Submodule.span F (Set.range U_star)) :
      Δ₀((v : ι → A), (L : Set (ι → A))) ≤ e :=
    h_contra v v.property
  have h_exists_codeword (v : Submodule.span F (Set.range U_star)) :
      ∃ c ∈ (L : Set (ι → A)), Δ₀((v : ι → A), c) ≤ e := by
    simpa using
      (Code.closeToCode_iff_closeToCodeword_of_minDist (u := (v : ι → A))
        (C := (L : Set (ι → A))) (e := e)).1 (h_close v)
  choose dec hdec_mem hdec_dist using h_exists_codeword
  have hdec_add (v w : Submodule.span F (Set.range U_star)) : dec (v + w) = dec v + dec w := by
    apply Code.eq_of_lt_dist (C := (L : Set (ι → A)))
    · exact hdec_mem (v + w)
    · exact Submodule.add_mem _ (hdec_mem v) (hdec_mem w)
    · have h1 : Δ₀(dec (v + w), (v + w : ι → A)) ≤ e := by
        simpa [hammingDist_comm] using hdec_dist (v + w)
      have h2 : Δ₀((v + w : ι → A), dec v + dec w) ≤ 2 * e := by
        have hv :
            Δ₀((v + w : ι → A), (v : ι → A) + dec w) = Δ₀((w : ι → A), dec w) := by
          change Δ₀((fun i => (v : ι → A) i + (w : ι → A) i),
            fun i => (v : ι → A) i + dec w i) = Δ₀((w : ι → A), dec w)
          exact hammingDist_comp (f := fun i ↦ fun t : A ↦ (v : ι → A) i + t)
              (x := (w : ι → A)) (y := dec w)
              (hf := fun _ ↦ by
                intro a b hab
                exact add_left_cancel hab)
        have hw :
            Δ₀((v : ι → A) + dec w, dec v + dec w) = Δ₀((v : ι → A), dec v) := by
          change Δ₀((fun i => (v : ι → A) i + dec w i),
            fun i => dec v i + dec w i) = Δ₀((v : ι → A), dec v)
          exact hammingDist_comp (f := fun i ↦ fun t : A ↦ t + dec w i)
              (x := (v : ι → A)) (y := dec v)
              (hf := fun _ ↦ by
                intro a b hab
                exact add_right_cancel hab)
        have : Δ₀((v + w : ι → A), dec v + dec w)
            ≤ Δ₀((v + w : ι → A), (v : ι → A) + dec w)
              + Δ₀((v : ι → A) + dec w, dec v + dec w) := by
          exact hammingDist_triangle (v + w : ι → A) ((v : ι → A) + dec w) (dec v + dec w)
        calc
          Δ₀((v + w : ι → A), dec v + dec w)
              ≤ Δ₀((v + w : ι → A), (v : ι → A) + dec w)
                + Δ₀((v : ι → A) + dec w, dec v + dec w) := this
          _   = Δ₀((w : ι → A), dec w) + Δ₀((v : ι → A), dec v) := by
              simp [hv, hw, add_comm]
          _   ≤ e + e := Nat.add_le_add (hdec_dist w) (hdec_dist v)
          _   = 2 * e := by ring
      have h3 : Δ₀(dec (v + w), dec v + dec w) ≤ 3 * e := by
        calc
          Δ₀(dec (v + w), dec v + dec w)
              ≤ Δ₀(dec (v + w), (v + w : ι → A))
                + Δ₀((v + w : ι → A), dec v + dec w) := by
                  exact
                    hammingDist_triangle (dec (v + w)) (v + w : ι → A) (dec v + dec w)
          _   ≤ e + 2 * e := Nat.add_le_add h1 h2
          _   = 3 * e := by ring
      exact lt_of_le_of_lt h3 h3e_lt_d
  have hdec_smul (a : F) (v : Submodule.span F (Set.range U_star)) : dec (a • v) = a • dec v := by
    apply Code.eq_of_lt_dist (C := (L : Set (ι → A)))
    · exact hdec_mem (a • v)
    · exact Submodule.smul_mem _ a (hdec_mem v)
    · have h1 : Δ₀(dec (a • v), (a • v : ι → A)) ≤ e := by
        simpa [hammingDist_comm] using hdec_dist (a • v)
      have h2 : Δ₀((a • v : ι → A), a • dec v) ≤ e := by
        have := hammingDist_smul_le_hammingDist (k := a) (x := (v : ι → A)) (y := dec v)
        exact le_trans this (hdec_dist v)
      have h3 : Δ₀(dec (a • v), a • dec v) ≤ 2 * e := by
        calc
          Δ₀(dec (a • v), a • dec v)
              ≤ Δ₀(dec (a • v), (a • v : ι → A))
                  + Δ₀((a • v : ι → A), a • dec v) := by
                exact hammingDist_triangle (dec (a • v)) (a • v : ι → A) (a • dec v)
          _   ≤ e + e := Nat.add_le_add h1 h2
          _   = 2 * e := by ring
      exact lt_of_le_of_lt h3 h2e_lt_d
  let decLin : Submodule.span F (Set.range U_star) →ₗ[F] (ι → A) :=
    { toFun := dec, map_add' := hdec_add, map_smul' := hdec_smul }
  let err : Submodule.span F (Set.range U_star) →ₗ[F] (ι → A) :=
    Submodule.subtype (Submodule.span F (Set.range U_star)) - decLin
  have herr_wt (x : LinearMap.range err) :
      (support (x : ι → A)).card ≤ e := by
    rcases x.property with ⟨v, hv⟩
    have h_supp :
        (support ((err v) : ι → A)).card = Δ₀((v : ι → A), dec v) := by
      simp [err, decLin, support, hammingDist, Pi.sub_apply, sub_ne_zero]
    simpa [hv.symm, h_supp] using hdec_dist v
  obtain ⟨D, hD_card, hD_zero⟩ :=
    common_support (LinearMap.range err) e herr_wt hF
  have h_row_in_span (k : κ) : U_star k ∈ Submodule.span F (Set.range U_star) := by
    exact Submodule.subset_span ⟨k, rfl⟩
  let V : WordStack (A := A) κ ι := fun k ↦ dec ⟨U_star k, h_row_in_span k⟩
  have hV_mem : (⋈|V) ∈ (L^⋈κ) := by
    refine (Code.mem_moduleInterleavedCode_iff (F := F) (A := A) (κ := κ) (ι := ι) (MC := L)
      (v := (⋈|V))).2 ?_
    intro k
    change dec ⟨U_star k, h_row_in_span k⟩ ∈ L
    exact hdec_mem ⟨U_star k, h_row_in_span k⟩
  have h_dist_rows : ∀ k j, j ∉ D → U_star k j = V k j := by
    intro k j hj
    have hz :
        (err ⟨U_star k, h_row_in_span k⟩ : ι → A) j = 0 := by
      have : (err ⟨U_star k, h_row_in_span k⟩) ∈ LinearMap.range err :=
        ⟨⟨U_star k, h_row_in_span k⟩, rfl⟩
      exact hD_zero ⟨err ⟨U_star k, h_row_in_span k⟩, this⟩ j hj
    have : (U_star k j : A) - V k j = 0 := by
      simpa [err, decLin, V, Pi.sub_apply] using hz
    exact sub_eq_zero.mp this
  have hUV_le : Δ₀(⋈|U_star, ⋈|V) ≤ e := by
    refine le_trans
      (hamming_dist_le_of_subset_disagree (ι := ι) (u := (⋈|U_star)) (v := (⋈|V))
        (D := D) ?_)
      hD_card
    intro j hj
    by_contra hjD
    apply hj
    funext k
    change U_star k j = V k j
    exact h_dist_rows k j hjD
  have h_dist_to_code : Δ₀(⋈|U_star, (L^⋈κ)) ≤ e := by
    exact le_trans
      (Code.distFromCode_le_dist_to_mem (C := (L^⋈κ)) (u := (⋈|U_star)) (v := (⋈|V))
        hV_mem)
      (by exact_mod_cast hUV_le)
  exact (not_lt_of_ge h_dist_to_code) hU


/-- Double-count affine translations to bound uniform row-span proximity by the code distance divided by scalar-field size. -/
theorem span_bound [Finite A] {κ : Type} [Fintype κ]
    (code : Submodule F (ι → A)) (word : WordStack (A := A) κ ι) (radius : ℕ)
    [SampleableType (Submodule.span F (Set.range word))]
    (large : radius < Fintype.card F)
    (small : 3*radius < Code.minDist (code : Set (ι → A)))
    (far : radius < Code.distFromCode (⋈|word) (code^⋈κ)) :
    Pr{let sampled ← $ᵗ (Submodule.span F (Set.range word))}[
      Code.distFromCode (sampled : ι → A) (code : Set (ι → A)) ≤ radius] ≤
      (Code.minDist (code : Set (ι → A)) : ENNReal) / Fintype.card F := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let d := Code.minDist (code : Set (ι → A))
  obtain ⟨v_star,hv_mem,hv_far⟩ := far_direction code word radius large small far
  -- Every affine line in direction `v_star` has at most `d` points close to the code.
  have hline_le (u : ι → A) : Nat.card {r : F // Δ₀(u + r • v_star, (code : Set (ι → A))) ≤ radius} ≤ d :=
    few_close_scalars code radius u v_star small hv_far
  -- Double count the pairs `(w, r)` with `w + r • v_star` close to the code.
  let S : Submodule F (ι → A) := Submodule.span F (Set.range word)
  let vDir : S := ⟨v_star, hv_mem⟩
  let Pbad : S → Prop := fun w ↦ Δ₀((w : ι → A), (code : Set (ι → A))) ≤ radius
  let bad : Finset S := Finset.filter Pbad Finset.univ
  have htranslate (r : F) :
      (Finset.univ.filter fun w : S ↦ Pbad (w + r • vDir)).card = bad.card :=
    Finset.card_equiv (Equiv.addRight (r • vDir)) fun w ↦ by simp [bad]
  have hcount : bad.card * Fintype.card F ≤ Fintype.card S * d :=
    calc
      bad.card * Fintype.card F
          = ∑ r : F, (Finset.univ.filter fun w : S ↦ Pbad (w + r • vDir)).card := by
        rw [Finset.sum_congr rfl fun r _ ↦ htranslate r, Finset.sum_const, Finset.card_univ,
          smul_eq_mul, mul_comm]
      _ = ∑ w : S, (Finset.univ.filter fun r : F ↦ Pbad (w + r • vDir)).card := by
        simp only [Finset.card_filter]
        exact Finset.sum_comm
      _ ≤ ∑ _w : S, d := Finset.sum_le_sum fun w _ ↦ by
        rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
        exact hline_le w
      _ = Fintype.card S * d := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hprob :
      Pr{let w_star ← $ᵗ (Submodule.span F (Set.range word))}[Δ₀(w_star, (code : Set (ι → A))) ≤ radius] =
        (bad.card : ENNReal) / Fintype.card S := by
    rw [SampleableType.prEvent_uniformSample]
  rw [hprob]
  refine ENNReal.div_le_of_le_mul ?_
  rw [mul_comm, ← mul_div_assoc, ENNReal.le_div_iff_mul_le
    (Or.inl (by exact_mod_cast Fintype.card_ne_zero)) (Or.inl (ENNReal.natCast_ne_top _))]
  exact_mod_cast hcount

/-- The actual coefficient-to-row-span linear map. -/
def toSpan {κ : Type} [Fintype κ] (word : WordStack (A := A) κ ι) :
    (κ → F) →ₗ[F] Submodule.span F (Set.range word) :=
  (Fintype.linearCombination F (Matrix.of.symm word)).codRestrict _ (fun coefficients => by
    apply Submodule.sum_mem
    intro row _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨row,rfl⟩))

omit [Fintype F] [Fintype ι] [DecidableEq A] in
/-- Every row-span element is produced by some coefficient vector. -/
theorem toSpan_surjective {κ : Type} [Fintype κ] (word : WordStack (A := A) κ ι) :
    Function.Surjective (toSpan (F := F) word) := by
  intro value
  obtain ⟨coefficients,equal⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp value.property
  exact ⟨coefficients,Subtype.ext equal⟩

/-- Surjective uniform fibers transport the row-span law to actual uniform coefficient vectors, allowing dependent source rows. -/
theorem coefficient_bound [Finite A] {κ : Type} [Fintype κ]
    (code : Submodule F (ι → A)) (word : WordStack (A := A) κ ι) (radius : ℕ)
    [SampleableType (κ → F)] [SampleableType (Submodule.span F (Set.range word))]
    [SampleableType (toSpan (F := F) word).toAddMonoidHom.ker]
    (large : radius < Fintype.card F)
    (small : 3*radius < Code.minDist (code : Set (ι → A)))
    (far : radius < Code.distFromCode (⋈|word) (code^⋈κ)) :
    Pr{let coefficients ← $ᵗ (κ → F)}[
      Code.distFromCode (Fintype.linearCombination F (Matrix.of.symm word) coefficients)
        (code : Set (ι → A)) ≤ radius] ≤
      (Code.minDist (code : Set (ι → A)) : ENNReal) / Fintype.card F := by
  exact (UniformImage.uniform_event (toSpan (F := F) word).toAddMonoidHom (toSpan_surjective (F := F) word)
    (fun value => Code.distFromCode value.val (code : Set (ι → A)) ≤ radius)).trans_le
      (span_bound code word radius large small far)

/-- Exact product law for predicates of independently uniform test rows; this is not a shared-column acceptance product. -/
theorem uniform_repetition {C : Type} [Fintype C] [SampleableType C]
    (width : ℕ) [SampleableType (Fin width → C)] (event : C → Prop) :
    Pr{let rows ← $ᵗ (Fin width → C)}[∀ lane, event (rows lane)] =
      (Pr{let row ← $ᵗ C}[event row])^width := by
  classical
  let good := (Finset.univ : Finset C).filter event
  have count : (Finset.univ.filter (fun rows : Fin width → C => ∀ lane, event (rows lane))).card =
      good.card^width := by
    rw [← Fintype.card_subtype]
    calc _ = Fintype.card {rows : Fin width → C // ∀ lane, rows lane ∈ good} := by
           apply Fintype.card_congr
           exact Equiv.subtypeEquivRight (fun rows => by simp [good])
         _ = good.card^width := ColumnSampling.card_goodDraws good width
  rw [SampleableType.prEvent_uniformSample,count,SampleableType.prEvent_uniformSample,Fintype.card_fun]
  simp only [Fintype.card_fin,Nat.cast_pow,div_eq_mul_inv,ENNReal.inv_pow,mul_pow,good]

/-- Independent scalar test rows give the conservative power bound with no relation between alphabet dimension and test width. -/
theorem rectangular_bound [Finite A] {κ : Type} [Fintype κ]
    (code : Submodule F (ι → A)) (word : WordStack (A := A) κ ι) (radius width : ℕ)
    [SampleableType (κ → F)] [SampleableType (Fin width → κ → F)]
    [SampleableType (Submodule.span F (Set.range word))]
    [SampleableType (toSpan (F := F) word).toAddMonoidHom.ker]
    (large : radius < Fintype.card F)
    (small : 3*radius < Code.minDist (code : Set (ι → A)))
    (far : radius < Code.distFromCode (⋈|word) (code^⋈κ)) :
    Pr{let matrix ← $ᵗ (Fin width → κ → F)}[∀ lane,
      Code.distFromCode (Fintype.linearCombination F (Matrix.of.symm word) (matrix lane))
        (code : Set (ι → A)) ≤ radius] ≤
      ((Code.minDist (code : Set (ι → A)) : ENNReal) / Fintype.card F)^width := by
  classical
  exact (uniform_repetition (C := κ → F) width (fun coefficients =>
    Code.distFromCode (Fintype.linearCombination F (Matrix.of.symm word) coefficients)
      (code : Set (ι → A)) ≤ radius)).trans_le
    (pow_le_pow_left₀ zero_le (coefficient_bound code word radius large small far) width)


end
end FormalProof4FHE.HasteBoots.ModuleCodeProximity
