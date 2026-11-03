module

public import FormalProof4FHE.HasteBoots.NTTRowCheck
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

@[expose] public section

/-!
# Exact-arithmetic radix-two butterflies and native output order

Each butterfly reads coefficient halves, adds/subtracts a common twiddle and
recurses into contiguous output halves. The first recursion branch is the high
output-address bit, while it is the low bit of the evaluation-point exponent.
This is the bit-reversed order of the native negacyclic transform. Correctness
below is for field arithmetic; optimized concrete-ntt kernels, lazy residues,
machine indices and Rust memory refinement remain separate obligations.
-/

open scoped BigOperators

namespace FormalProof4FHE.HasteBoots.NTTButterfly

/-- Recursion branches are high output bits, unlike source-fold cube bits. -/
def outputIndex : (n : ℕ) → MatrixFold.Cube n ≃ Fin (2 ^ n)
  | 0 => show Unit ≃ Fin 1 from Equiv.ofUnique _ _
  | n + 1 =>
    (Equiv.prodCongr finTwoEquiv.symm (outputIndex n)).trans
      (finProdFinEquiv.trans (finCongr (by omega : 2 * 2 ^ n = 2 ^ (n + 1))))

theorem outputIndex_succ_val {n : ℕ} (bit : Bool) (tail : MatrixFold.Cube n) :
    (outputIndex (n + 1) (bit, tail)).val =
      (if bit then 2 ^ n else 0) + (outputIndex n tail).val := by
  change (outputIndex n tail).val + 2 ^ n * (finTwoEquiv.symm bit).val = _
  cases bit <;> simp [finTwoEquiv, Nat.add_comm]

/-- Reverses all n bits: output address to odd-root exponent address. -/
def reverseIndex (n : ℕ) : Fin (2 ^ n) ≃ Fin (2 ^ n) :=
  (outputIndex n).symm.trans (FlatMatrixFold.index n)

theorem reverseIndex_outputIndex (n : ℕ) (cell : MatrixFold.Cube n) :
    reverseIndex n (outputIndex n cell) = FlatMatrixFold.index n cell := by
  simp only [reverseIndex, Equiv.trans_apply, Equiv.symm_apply_apply]

/-- Lower and upper halves of a native coefficient array. -/
def halves (n : ℕ) : (Fin (2 ^ n) ⊕ Fin (2 ^ n)) ≃ Fin (2 ^ (n + 1)) :=
  finSumFinEquiv.trans (finCongr (by omega : 2 ^ n + 2 ^ n = 2 ^ (n + 1)))

theorem halves_left_val (n : ℕ) (position : Fin (2 ^ n)) :
    (halves n (.inl position)).val = position.val := rfl

theorem halves_right_val (n : ℕ) (position : Fin (2 ^ n)) :
    (halves n (.inr position)).val = 2 ^ n + position.val := rfl

variable {F : Type} [Field F]

def evaluate {n : ℕ} (coefficients : Fin (2 ^ n) → F) (point : F) : F :=
  ∑ power, coefficients power * point ^ power.val

/-- The actual two-half polynomial identity used by each butterfly. -/
theorem evaluate_halves {n : ℕ} (coefficients : Fin (2 ^ (n + 1)) → F) (point : F) :
    evaluate coefficients point =
      evaluate (fun j => coefficients (halves n (.inl j))) point +
        point ^ (2 ^ n) * evaluate (fun j => coefficients (halves n (.inr j))) point := by
  unfold evaluate
  rw [← (halves n).sum_comp]
  simp only [Fintype.sum_sum_type, halves_left_val, halves_right_val, pow_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro position _
  ring

/-- The two output branches share the same multiplication before add/subtract. -/
def reduced {n : ℕ} (base : F) (coefficients : Fin (2 ^ (n + 1)) → F) (bit : Bool) : Fin (2 ^ n) → F :=
  fun j => coefficients (halves n (.inl j)) +
    (if bit then -(base ^ (2 ^ n)) else base ^ (2 ^ n)) * coefficients (halves n (.inr j))

def transform : (n : ℕ) → F → F → (Fin (2 ^ n) → F) → MatrixFold.Cube n → F
  | 0, _, _, coefficients, _ => coefficients 0
  | n + 1, base, omega, coefficients, (bit, tail) =>
    transform n (base * if bit then omega else 1) (omega ^ 2) (reduced base coefficients bit) tail

/-- Point reached at a recursion leaf; exponent bits run in the opposite order
to contiguous output addresses. -/
def point (n : ℕ) (base omega : F) (cell : MatrixFold.Cube n) : F :=
  base * omega ^ (FlatMatrixFold.index n cell).val

theorem point_succ {n : ℕ} (base omega : F) (bit : Bool) (tail : MatrixFold.Cube n) :
    point (n + 1) base omega (bit, tail) =
      point n (base * if bit then omega else 1) (omega ^ 2) tail := by
  simp only [point]
  rw [FlatMatrixFold.index_succ_val]
  simp only [pow_add, pow_mul]
  cases bit <;> simp
  ring

/-- Primitivity supplies the exact sign change needed by the upper branch. -/
theorem half_power {n : ℕ} {omega : F} (root : IsPrimitiveRoot omega (2 ^ (n + 1))) :
    omega ^ (2 ^ n) = -1 := by
  exact (root.pow (by positivity) (by rw [Nat.pow_succ] : 2 ^ (n + 1) = 2 ^ n * 2)).eq_neg_one_of_two_right

theorem square_primitive {n : ℕ} {omega : F} (root : IsPrimitiveRoot omega (2 ^ (n + 1))) :
    IsPrimitiveRoot (omega ^ 2) (2 ^ n) :=
  root.pow (by positivity) (by rw [Nat.pow_succ]; omega)

/-- At every leaf, the n-th half power is exactly the branch's twiddle. -/
theorem point_half_power {n : ℕ} (base omega : F) (root : IsPrimitiveRoot omega (2 ^ (n + 1)))
    (bit : Bool) (tail : MatrixFold.Cube n) :
    (point (n + 1) base omega (bit, tail)) ^ (2 ^ n) =
      if bit then -(base ^ (2 ^ n)) else base ^ (2 ^ n) := by
  simp only [point]
  rw [FlatMatrixFold.index_succ_val, mul_pow, pow_add]
  have periodic : omega ^ (2 * (FlatMatrixFold.index n tail).val * 2 ^ n) = 1 := by
    calc
      _ = (omega ^ (2 ^ (n + 1))) ^ (FlatMatrixFold.index n tail).val := by
        rw [← pow_mul, Nat.pow_succ]
        congr 1
        ring
      _ = 1 := by rw [root.pow_eq_one, one_pow]
  cases bit <;> simp only [Bool.false_eq_true, reduceIte, pow_zero, mul_one, pow_one, mul_pow,
    ← pow_mul, periodic, half_power root, mul_neg, mul_one]

/-- Exact field butterflies compute polynomial evaluation at the required
bit-reversed points, with no supplied transform-correctness hypothesis. -/
theorem transform_evaluate (n : ℕ) (base omega : F) (root : IsPrimitiveRoot omega (2 ^ n))
    (coefficients : Fin (2 ^ n) → F) (cell : MatrixFold.Cube n) :
    transform n base omega coefficients cell = evaluate coefficients (point n base omega cell) := by
  induction n generalizing base omega with
  | zero => simp [transform, evaluate]
  | succ n ih =>
    rcases cell with ⟨bit, tail⟩
    rw [transform, ih _ _ (square_primitive root), ← point_succ, evaluate_halves]
    simp only [evaluate, reduced, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    rw [point_half_power base omega root bit tail]

/-- The same result array addressed in contiguous native output order. -/
def flatTransform (n : ℕ) (base omega : F) (coefficients : Fin (2 ^ n) → F) : Fin (2 ^ n) → F :=
  fun index => transform n base omega coefficients ((outputIndex n).symm index)

/-- Native negacyclic evaluation nodes: odd powers, in bit-reversed order. -/
def nodes (n : ℕ) (psi : F) (index : Fin (2 ^ n)) : F :=
  psi ^ (2 * (reverseIndex n index).val + 1)

theorem nodes_eq_point (n : ℕ) (psi : F) (index : Fin (2 ^ n)) :
    nodes n psi index = point n psi (psi ^ 2) ((outputIndex n).symm index) := by
  simp only [nodes, point, reverseIndex, Equiv.trans_apply, pow_add, pow_one, ← pow_mul]
  ring

/-- Correctness of negacyclic field butterflies, including native array order. -/
theorem negacyclic_evaluation (n : ℕ) (psi : F) (root : IsPrimitiveRoot psi (2 ^ (n + 1)))
    (coefficients : Fin (2 ^ n) → F) :
    flatTransform n psi (psi ^ 2) coefficients = NTTRowCheck.evaluation (nodes n psi) coefficients := by
  funext index
  rw [flatTransform, transform_evaluate n psi (psi ^ 2) (square_primitive root), ← nodes_eq_point]
  rfl

/-- Every native-order point is a root of X^N+1. -/
theorem nodes_power (n : ℕ) (psi : F) (root : IsPrimitiveRoot psi (2 ^ (n + 1))) (index : Fin (2 ^ n)) :
    nodes n psi index ^ (2 ^ n) = -1 := by
  rw [nodes, ← pow_mul]
  calc
    _ = (psi ^ (2 ^ (n + 1))) ^ (reverseIndex n index).val * psi ^ (2 ^ n) := by
      rw [← pow_mul, ← pow_add, Nat.pow_succ]
      congr 1
      ring
    _ = -1 := by rw [root.pow_eq_one, one_pow, one_mul, half_power root]

/-- The bit permutation preserves distinct odd roots, so the concrete NTT
nodes supply the injective domain required by the PCS code theorems. -/
theorem nodes_injective (n : ℕ) (psi : F) (root : IsPrimitiveRoot psi (2 ^ (n + 1))) :
    Function.Injective (nodes n psi) := by
  intro first second equal
  have bound (index : Fin (2 ^ n)) : 2 * (reverseIndex n index).val + 1 < 2 ^ (n + 1) := by
    have less := (reverseIndex n index).isLt
    rw [Nat.pow_succ]
    omega
  have exponents := root.pow_inj (bound first) (bound second) equal
  apply (reverseIndex n).injective
  apply Fin.ext
  omega

def domain (n : ℕ) (psi : F) (root : IsPrimitiveRoot psi (2 ^ (n + 1))) : Fin (2 ^ n) ↪ F :=
  ⟨nodes n psi, nodes_injective n psi root⟩

end FormalProof4FHE.HasteBoots.NTTButterfly
