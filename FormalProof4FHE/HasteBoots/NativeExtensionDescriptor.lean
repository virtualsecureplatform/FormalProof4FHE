module

public import FormalProof4FHE.HasteBoots.NativeExtensionFields
public import FormalProof4FHE.HasteBoots.TranscriptFrame
public import Mathlib.FieldTheory.KummerPolynomial

@[expose] public section

/-!
# Native extension multiplication-table descriptors

`extension_basis` serializes degree as u64le, then the canonical base-field
coordinates of monomial(i)*monomial(j), with i outermost and k innermost,
each as u128le. The binomial table below is derived from a proved power
basis and its root relation. Rust storage, cache execution, and `.value()`
correspondence remain separate refinement obligations.
-/

namespace FormalProof4FHE.HasteBoots.NativeExtensionDescriptor

open InputIndexedOracle (Input)
open TranscriptFrame (littleEndian)

section Algebra

variable {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {degree : ℕ}

/-- A product of two basis monomials wraps at most once. -/
theorem product_coordinate (basis : Module.Basis (Fin degree) R K) (root : K) (w : R)
    (powers : ∀ i, basis i = root ^ i.val) (relation : root ^ degree = algebraMap R K w)
    (i j k : Fin degree) :
    basis.equivFun (basis i * basis j) k =
      if i.val + j.val < degree then (if i.val + j.val = k.val then 1 else 0)
      else (if i.val + j.val - degree = k.val then w else 0) := by
  rw [powers i, powers j, ← pow_add]
  by_cases wraps : i.val + j.val < degree
  · rw [ite_eq_left wraps, ← powers ⟨i.val + j.val, wraps⟩]
    simp only [Module.Basis.equivFun_self, Fin.ext_iff]
  · rw [ite_eq_right wraps]
    have index : i.val + j.val - degree < degree := by omega
    have splitSum : i.val + j.val = degree + (i.val + j.val - degree) := by omega
    have product : root ^ (i.val + j.val) = w • basis ⟨i.val + j.val - degree, index⟩ := by
      calc
        root ^ (i.val + j.val) = root ^ (degree + (i.val + j.val - degree)) := congrArg (root ^ ·) splitSum
        _ = algebraMap R K w * root ^ (i.val + j.val - degree) := by rw [pow_add, relation]
        _ = w • basis ⟨i.val + j.val - degree, index⟩ := by rw [Algebra.smul_def, powers]
    rw [product, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, Module.Basis.equivFun_self, Fin.ext_iff]
    split <;> simp only [mul_one, mul_zero]


end Algebra

/-- The computable canonical integer table, justified below by field coordinates. -/
def entry (degree w : ℕ) (i j k : Fin degree) : ℕ :=
  if i.val + j.val < degree then (if i.val + j.val = k.val then 1 else 0)
  else (if i.val + j.val - degree = k.val then w else 0)

theorem entry_fits (degree w : ℕ) (fits : w < 256 ^ 16) (i j k : Fin degree) :
    entry degree w i j k < 256 ^ 16 := by
  unfold entry
  split <;> split
  · decide
  · decide
  · exact fits
  · decide

def tableBytes (degree : ℕ) (value : Fin degree → Fin degree → Fin degree → ℕ) : Input :=
  littleEndian 8 degree ++ (List.finRange degree).flatMap (fun i =>
    (List.finRange degree).flatMap (fun j =>
      (List.finRange degree).flatMap (fun k => littleEndian 16 (value i j k))))

theorem tableBytes_length (degree : ℕ) (value : Fin degree → Fin degree → Fin degree → ℕ) :
    (tableBytes degree value).length = 8 + 16 * degree ^ 3 := by
  simp [tableBytes, List.length_flatMap, TranscriptFrame.littleEndian_length]
  ring

def descriptor (degree w : ℕ) : Input := tableBytes degree (entry degree w)

noncomputable def basisDescriptor {p degree : ℕ} {K : Type} [CommRing K] [Algebra (ZMod p) K]
    (basis : Module.Basis (Fin degree) (ZMod p) K) : Input :=
  tableBytes degree (fun i j k => (basis.equivFun (basis i * basis j) k).val)

theorem canonical_entry {p degree : ℕ} {K : Type} [CommRing K] [Algebra (ZMod p) K]
    (valid : 1 < p) (w : ℕ) (fits : w < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (root : K) (powers : ∀ i, basis i = root ^ i.val)
    (relation : root ^ degree = algebraMap (ZMod p) K (w : ZMod p)) (i j k : Fin degree) :
    (basis.equivFun (basis i * basis j) k).val = entry degree w i j k := by
  rw [product_coordinate basis root (w : ZMod p) powers relation]
  unfold entry
  split
  · split
    · simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt valid
    · simpa only [Nat.cast_zero] using ZMod.val_natCast_of_lt (by omega : 0 < p)
  · split
    · exact ZMod.val_natCast_of_lt fits
    · simpa only [Nat.cast_zero] using ZMod.val_natCast_of_lt (by omega : 0 < p)

theorem basisDescriptor_eq {p degree : ℕ} {K : Type} [CommRing K] [Algebra (ZMod p) K]
    (valid : 1 < p) (w : ℕ) (fits : w < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (root : K) (powers : ∀ i, basis i = root ^ i.val)
    (relation : root ^ degree = algebraMap (ZMod p) K (w : ZMod p)) :
    basisDescriptor basis = descriptor degree w := by
  unfold basisDescriptor descriptor
  congr 1
  funext i j k
  exact canonical_entry valid w fits basis root powers relation i j k

open NativeFields NativeExtensionFields Polynomial AdjoinRoot

theorem goldilocks_descriptor : basisDescriptor goldilocksBasis = descriptor 3 7 := by
  apply basisDescriptor_eq (by decide : 1 < goldilocksModulus) 7 (by decide)
    goldilocksBasis (root goldilocksPolynomial) goldilocks_basis_power
  exact root_X_pow_sub_C_pow 3 (7 : Goldilocks)

theorem babyBear_descriptor : basisDescriptor babyBearBasis = descriptor 6 31 := by
  apply basisDescriptor_eq (by decide : 1 < babyBearModulus) 31 (by decide)
    babyBearBasis (root babyBearPolynomial) babyBear_basis_power
  exact root_X_pow_sub_C_pow 6 (31 : BabyBear)

end FormalProof4FHE.HasteBoots.NativeExtensionDescriptor
