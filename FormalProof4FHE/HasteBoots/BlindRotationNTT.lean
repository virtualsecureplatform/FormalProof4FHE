module
public import FormalProof4FHE.HasteBoots.NativeBlindRotation
public import FormalProof4FHE.HasteBoots.NTTButterfly
public import FormalProof4FHE.HasteBoots.BlockEncoder
public import Mathlib.Algebra.Field.ZMod
@[expose] public section

/-! The reference blind-rotation convolution is multiplication under the
proved odd, bit-reversed negacyclic NTT. This is arithmetic semantics, not
native stage acceptance, key-layout or Rust/physical refinement. -/
namespace FormalProof4FHE.HasteBoots.BlindRotationNTT
open scoped BigOperators
open NativeBlindRotation (Poly Cipher Control digit mul externalProduct)
noncomputable section

def evaluate {q n : ℕ} (coefficients : Poly q n) (point : ZMod q) : ZMod q :=
  ∑ index, coefficients index * point^index.val

theorem scatter {q n : ℕ} (left right : Poly q n) (point : ZMod q) (negative : point^n = -1) (i j : Fin n) :
    (∑ index : Fin n, (if (i.val+j.val)%n = index.val then
      if i.val+j.val < n then left i*right j else -(left i*right j) else 0)*point^index.val) =
      left i*right j*point^(i.val+j.val) := by
  classical
  have positive : 0 < n := Nat.zero_lt_of_lt i.isLt
  let position : Fin n := ⟨(i.val+j.val)%n, Nat.mod_lt _ positive⟩
  rw [Finset.sum_eq_single position]
  · simp only [position, ite_true]
    by_cases low : i.val+j.val < n
    · rw [ite_eq_left low, Nat.mod_eq_of_lt low]
    · rw [ite_eq_right low]
      have upper : i.val+j.val < 2*n := by have := i.isLt; have := j.isLt; omega
      have reduced : (i.val+j.val)%n = i.val+j.val-n := by
        rw [Nat.mod_eq_sub_mod (by omega : n ≤ i.val+j.val), Nat.mod_eq_of_lt (by omega)]
      have power : point^(i.val+j.val) = -point^(i.val+j.val-n) := by
        calc
          _ = point^(n+(i.val+j.val-n)) := congrArg (point^·) (by omega)
          _ = _ := by rw [pow_add, negative, neg_one_mul]
      rw [reduced, power]
      ring
  · intro index _ different
    have unequal : (i.val+j.val)%n ≠ index.val := fun same => different (Fin.ext same.symm)
    simp only [ite_eq_right unequal, zero_mul]
  · simp

theorem evaluate_mul {q n : ℕ} (left right : Poly q n) (point : ZMod q) (negative : point^n = -1) :
    evaluate (mul left right) point = evaluate left point * evaluate right point := by
  classical
  unfold evaluate NativeBlindRotation.mul
  simp only [Finset.sum_mul]
  calc
    (∑ index : Fin n, ∑ i : Fin n, ∑ j : Fin n,
      (if (i.val+j.val)%n = index.val then if i.val+j.val < n then left i*right j else -(left i*right j) else 0)*point^index.val) =
        ∑ i : Fin n, ∑ j : Fin n, ∑ index : Fin n,
          (if (i.val+j.val)%n = index.val then if i.val+j.val < n then left i*right j else -(left i*right j) else 0)*point^index.val := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i : Fin n, ∑ j : Fin n, left i*right j*point^(i.val+j.val) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact scatter left right point negative i j
    _ = ∑ i : Fin n, (left i*point^i.val)*(∑ j : Fin n, right j*point^j.val) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_add]
      ring

section Field
variable {q : ℕ} [Fact q.Prime]

def transform (log : ℕ) (psi : ZMod q) : (Poly q (2^log)) →ₗ[ZMod q] Poly q (2^log) :=
  NTTRowCheck.evaluation (NTTButterfly.nodes log psi)

theorem transform_mul (log : ℕ) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (left right : Poly q (2^log)) :
    transform log psi (mul left right) = transform log psi left * transform log psi right := by
  funext index
  exact evaluate_mul left right _ (NTTButterfly.nodes_power log psi primitive index)

theorem transform_injective (log : ℕ) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1))) :
    Function.Injective (transform log psi) := by
  intro first second same
  have encoded : BlockEncoder.encode (NTTButterfly.domain log psi primitive) (fun index (_ : Fin 1) => first index) =
      BlockEncoder.encode (NTTButterfly.domain log psi primitive) (fun index (_ : Fin 1) => second index) := by
    funext index lane
    exact congrFun same index
  have coefficients := BlockEncoder.encode_injective (NTTButterfly.domain log psi primitive)
    (by simp only [Fintype.card_fin]; exact le_rfl) encoded
  funext index
  exact congrFun (congrFun coefficients index) 0


theorem butterfly_mul (log : ℕ) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (left right : Poly q (2^log)) :
    NTTButterfly.flatTransform log psi (psi^2) (mul left right) =
      NTTButterfly.flatTransform log psi (psi^2) left * NTTButterfly.flatTransform log psi (psi^2) right := by
  simp only [NTTButterfly.negacyclic_evaluation log psi primitive]
  exact transform_mul log psi primitive left right

theorem butterfly_injective (log : ℕ) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1))) :
    Function.Injective (NTTButterfly.flatTransform log psi (psi^2)) := by
  intro first second same
  apply transform_injective log psi primitive
  change NTTRowCheck.evaluation (NTTButterfly.nodes log psi) first = NTTRowCheck.evaluation (NTTButterfly.nodes log psi) second
  simpa only [NTTButterfly.negacyclic_evaluation log psi primitive] using same

theorem externalProduct_transform {levels : ℕ} (log : ℕ) (psi : ZMod q)
    (primitive : IsPrimitiveRoot psi (2^(log+1))) (bits : ℕ)
    (control : Control q (2^log) levels) (input : Cipher q (2^log)) (half : Bool) :
    transform log psi (externalProduct bits control input half) =
      ∑ source : Bool, ∑ level : Fin levels,
        transform log psi (digit bits level (input source)) * transform log psi (control source level half) := by
  have represented : externalProduct bits control input half =
      ∑ source : Bool, ∑ level : Fin levels, mul (digit bits level (input source)) (control source level half) := by
    funext index
    simp only [externalProduct, Finset.sum_apply]
  rw [represented, map_sum]
  simp only [map_sum, transform_mul log psi primitive]

/-- Truthful NTT source relations and the pointwise product identity determine
exactly the reference coefficient-domain external product. -/
theorem externalProduct_of_pointwise {levels : ℕ} (log : ℕ) (psi : ZMod q)
    (primitive : IsPrimitiveRoot psi (2^(log+1))) (bits : ℕ)
    (control : Control q (2^log) levels) (input output : Cipher q (2^log))
    (identity : ∀ half, transform log psi (output half) =
      ∑ source : Bool, ∑ level : Fin levels,
        transform log psi (digit bits level (input source)) * transform log psi (control source level half)) :
    output = externalProduct bits control input := by
  funext half
  apply transform_injective log psi primitive
  rw [externalProduct_transform log psi primitive]
  exact identity half
end Field
end
end FormalProof4FHE.HasteBoots.BlindRotationNTT
