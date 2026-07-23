/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.FiniteProduct
import FormalProof4FHE.Probability.MajorityAmplification

/-!
# Flattening Explicit Majority Batches

The executable majority amplifier stores inputs in a depth-indexed ternary tree.  This module
gives an exact equivalence between that tree and a flat function with one coordinate per leaf,
then extends it to the vector of trees used for whole-key recovery.  These are deterministic
reshapings: no probability or cryptographic assumption is involved.
-/

namespace FormalProof4FHE.MajorityAmplification

/-- A depth-indexed ternary majority tree is equivalent to a flat family with exactly
`majorityBatchViewCount rounds` entries. -/
def majorityBatchEquiv (Input : Type) :
    (rounds : ℕ) → MajorityBatch Input rounds ≃
      (Fin (majorityBatchViewCount rounds) → Input)
  | 0 =>
      { toFun := fun input _ ↦ input
        invFun := fun inputs ↦ inputs ⟨0, by simp [majorityBatchViewCount]⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun inputs ↦ by
          funext index
          have hcount : majorityBatchViewCount 0 = 1 := by
            rw [majorityBatchViewCount_eq_pow]
            norm_num
          have hlt : index.val < 1 := by
            rw [← hcount]
            exact index.isLt
          have hindex : index = ⟨0, by simp [majorityBatchViewCount]⟩ := by
            apply Fin.ext
            change index.val = 0
            omega
          subst index
          rfl }
  | rounds + 1 =>
      { toFun := fun inputs index ↦
          let pair := finProdFinEquiv.symm index
          majorityBatchEquiv Input rounds (inputs pair.1) pair.2
        invFun := fun inputs branch ↦
          (majorityBatchEquiv Input rounds).symm
            (fun index ↦ inputs (finProdFinEquiv (branch, index)))
        left_inv := fun inputs ↦ by
          funext branch
          apply (majorityBatchEquiv Input rounds).injective
          funext index
          simp
        right_inv := fun inputs ↦ by
          funext index
          simp only [Equiv.apply_symm_apply]
          exact congrArg inputs (finProdFinEquiv.apply_symm_apply index) }

/-- A vector of ternary majority trees is equivalent to one flat family indexed first by the
vector coordinate and then by the leaf position. -/
def vectorMajorityBatchEquiv (Input : Type) (count rounds : ℕ) :
    (Fin count → MajorityBatch Input rounds) ≃
      (Fin (count * majorityBatchViewCount rounds) → Input) where
  toFun inputs index :=
    let pair := finProdFinEquiv.symm index
    majorityBatchEquiv Input rounds (inputs pair.1) pair.2
  invFun inputs coordinate :=
    (majorityBatchEquiv Input rounds).symm
      (fun index ↦ inputs (finProdFinEquiv (coordinate, index)))
  left_inv inputs := by
    funext coordinate
    apply (majorityBatchEquiv Input rounds).injective
    funext index
    simp
  right_inv inputs := by
    funext index
    simp only [Equiv.apply_symm_apply]
    exact congrArg inputs (finProdFinEquiv.apply_symm_apply index)

/-! ## Computation rules -/

@[simp]
theorem majorityBatchEquiv_symm_zero {Input : Type}
    (inputs : Fin (majorityBatchViewCount 0) → Input) :
    (majorityBatchEquiv Input 0).symm inputs =
      inputs ⟨0, by rw [majorityBatchViewCount_eq_pow]; norm_num⟩ := by
  rfl

@[simp]
theorem majorityBatchEquiv_symm_succ_apply {Input : Type} (rounds : ℕ)
    (inputs : Fin (majorityBatchViewCount (rounds + 1)) → Input)
    (branch : Fin 3) :
    ((majorityBatchEquiv Input (rounds + 1)).symm inputs) branch =
      (majorityBatchEquiv Input rounds).symm
        (fun index ↦ inputs (finProdFinEquiv (branch, index))) := by
  rfl

@[simp]
theorem vectorMajorityBatchEquiv_symm_apply {Input : Type} (count rounds : ℕ)
    (inputs : Fin (count * majorityBatchViewCount rounds) → Input)
    (coordinate : Fin count) :
    ((vectorMajorityBatchEquiv Input count rounds).symm inputs) coordinate =
      (majorityBatchEquiv Input rounds).symm
        (fun index ↦ inputs (finProdFinEquiv (coordinate, index))) := by
  rfl

theorem probOutput_sampleMajorityBatch_zero {Input : Type}
    (sampler : ProbComp Input) (value : MajorityBatch Input 0) :
    Pr[= value | sampleMajorityBatch 0 sampler] = Pr[= value | sampler] := by
  rfl

theorem probOutput_sampleMajorityBatch_succ {Input : Type} [Finite Input]
    (rounds : ℕ) (sampler : ProbComp Input)
    (values : MajorityBatch Input (rounds + 1)) :
    Pr[= values | sampleMajorityBatch (rounds + 1) sampler] =
      ∏ branch : Fin 3,
        Pr[= values branch | sampleMajorityBatch rounds sampler] := by
  exact FormalProof4FHE.FiniteProduct.probOutput_fin_mOfFn 3
    (fun _ ↦ sampleMajorityBatch rounds sampler) values

/-! ## Independent sampling under flattening -/

/-- Flattening an independently sampled ternary tree gives an ordinary independent product over
its exact leaf count. -/
theorem evalDist_majorityBatchEquiv_sample {Input : Type} [Finite Input]
    (rounds : ℕ) (sampler : ProbComp Input) :
    evalDist (majorityBatchEquiv Input rounds <$>
      sampleMajorityBatch rounds sampler) =
      evalDist (Fin.mOfFn (majorityBatchViewCount rounds) fun _ ↦ sampler) := by
  induction rounds with
  | zero =>
      apply evalDist_ext
      intro values
      rw [probOutput_map_equiv, majorityBatchEquiv_symm_zero,
        FormalProof4FHE.FiniteProduct.probOutput_fin_mOfFn]
      rw [probOutput_sampleMajorityBatch_zero]
      let zeroIndex : Fin (majorityBatchViewCount 0) :=
        ⟨0, by rw [majorityBatchViewCount_eq_pow]; norm_num⟩
      letI : Unique (Fin (majorityBatchViewCount 0)) := {
        default := zeroIndex
        uniq index := by
          apply Fin.ext
          have hcount : majorityBatchViewCount 0 = 1 := by
            rw [majorityBatchViewCount_eq_pow]
            norm_num
          have hlt : index.val < 1 := by
            rw [← hcount]
            exact index.isLt
          change index.val = 0
          omega
      }
      rw [Fintype.prod_unique]
      congr 2
  | succ rounds ih =>
      apply evalDist_ext
      intro values
      rw [probOutput_map_equiv]
      rw [probOutput_sampleMajorityBatch_succ,
        FormalProof4FHE.FiniteProduct.probOutput_fin_mOfFn]
      simp_rw [majorityBatchEquiv_symm_succ_apply]
      have hchild (branch : Fin 3) :
          Pr[= (majorityBatchEquiv Input rounds).symm
              (fun index ↦ values (finProdFinEquiv (branch, index))) |
              sampleMajorityBatch rounds sampler] =
            ∏ index,
              Pr[= values (finProdFinEquiv (branch, index)) | sampler] := by
        have h := evalDist_ext_iff.mp ih
          (fun index ↦ values (finProdFinEquiv (branch, index)))
        rw [probOutput_map_equiv,
          FormalProof4FHE.FiniteProduct.probOutput_fin_mOfFn] at h
        exact h
      simp_rw [hchild]
      calc
        (∏ branch : Fin 3, ∏ index : Fin (majorityBatchViewCount rounds),
            Pr[= values (finProdFinEquiv (branch, index)) | sampler]) =
          ∏ pair : Fin 3 × Fin (majorityBatchViewCount rounds),
            Pr[= values (finProdFinEquiv pair) | sampler] :=
              (Fintype.prod_prod_type
                (fun pair : Fin 3 × Fin (majorityBatchViewCount rounds) ↦
                  Pr[= values (finProdFinEquiv pair) | sampler])).symm
        _ = ∏ index : Fin (3 * majorityBatchViewCount rounds),
            Pr[= values index | sampler] := by
              apply Fintype.prod_equiv finProdFinEquiv
              intro pair
              rfl

/-- Flattening a vector of independently sampled majority trees gives one ordinary independent
product over `count * majorityBatchViewCount rounds` inputs. -/
theorem evalDist_vectorMajorityBatchEquiv_sample {Input : Type} [Finite Input]
    (count rounds : ℕ) (sampler : ProbComp Input) :
    evalDist (vectorMajorityBatchEquiv Input count rounds <$>
      Fin.mOfFn count (fun _ ↦ sampleMajorityBatch rounds sampler)) =
      evalDist (Fin.mOfFn (count * majorityBatchViewCount rounds) fun _ ↦ sampler) := by
  apply evalDist_ext
  intro values
  rw [probOutput_map_equiv,
    FormalProof4FHE.FiniteProduct.probOutput_fin_mOfFn,
    FormalProof4FHE.FiniteProduct.probOutput_fin_mOfFn]
  simp_rw [vectorMajorityBatchEquiv_symm_apply]
  have htree (coordinate : Fin count) :
      Pr[= (majorityBatchEquiv Input rounds).symm
          (fun index ↦ values (finProdFinEquiv (coordinate, index))) |
          sampleMajorityBatch rounds sampler] =
        ∏ index,
          Pr[= values (finProdFinEquiv (coordinate, index)) | sampler] := by
    have h := evalDist_ext_iff.mp
      (evalDist_majorityBatchEquiv_sample rounds sampler)
      (fun index ↦ values (finProdFinEquiv (coordinate, index)))
    rw [probOutput_map_equiv,
      FormalProof4FHE.FiniteProduct.probOutput_fin_mOfFn] at h
    exact h
  simp_rw [htree]
  calc
    (∏ coordinate : Fin count, ∏ index : Fin (majorityBatchViewCount rounds),
        Pr[= values (finProdFinEquiv (coordinate, index)) | sampler]) =
      ∏ pair : Fin count × Fin (majorityBatchViewCount rounds),
        Pr[= values (finProdFinEquiv pair) | sampler] :=
          (Fintype.prod_prod_type
            (fun pair : Fin count × Fin (majorityBatchViewCount rounds) ↦
              Pr[= values (finProdFinEquiv pair) | sampler])).symm
    _ = ∏ index : Fin (count * majorityBatchViewCount rounds),
        Pr[= values index | sampler] := by
          apply Fintype.prod_equiv finProdFinEquiv
          intro pair
          rfl

/-- A consumer of a vector of independently sampled majority trees may equivalently consume the
flat IID leaf vector and deterministically rebuild the trees. -/
theorem evalDist_sampleVectorMajorityBatch_bind_eq_flat
    {Input Output : Type} [Finite Input]
    (count rounds : ℕ) (sampler : ProbComp Input)
    (postprocess : (Fin count → MajorityBatch Input rounds) → ProbComp Output) :
    evalDist (Fin.mOfFn count
        (fun _ ↦ sampleMajorityBatch rounds sampler) >>= postprocess) =
      evalDist (Fin.mOfFn (count * majorityBatchViewCount rounds)
        (fun _ ↦ sampler) >>= fun inputs ↦
          postprocess ((vectorMajorityBatchEquiv Input count rounds).symm inputs)) := by
  let sampledTrees := Fin.mOfFn count
    (fun _ ↦ sampleMajorityBatch rounds sampler)
  let flatten := vectorMajorityBatchEquiv Input count rounds
  let finish (inputs : Fin (count * majorityBatchViewCount rounds) → Input) :=
    postprocess (flatten.symm inputs)
  have hflatten := evalDist_vectorMajorityBatchEquiv_sample count rounds sampler
  have hpost :
      evalDist ((flatten <$> sampledTrees) >>= finish) =
        evalDist (Fin.mOfFn (count * majorityBatchViewCount rounds)
          (fun _ ↦ sampler) >>= finish) := by
    calc
      _ = evalDist (flatten <$> sampledTrees) >>=
            fun inputs ↦ evalDist (finish inputs) := evalDist_bind _ _
      _ = evalDist (Fin.mOfFn (count * majorityBatchViewCount rounds)
              (fun _ ↦ sampler)) >>=
            fun inputs ↦ evalDist (finish inputs) := by rw [hflatten]
      _ = _ := (evalDist_bind _ _).symm
  simpa [sampledTrees, flatten, finish, map_eq_bind_pure_comp, bind_assoc] using hpost

end FormalProof4FHE.MajorityAmplification
