module
public import FormalProof4FHE.HasteBoots.CostedMerkleTree
@[expose] public section

/-! Concrete construction of native perfect-tree leaf indices. Power generation,
quotient/parity tests and path constructors are charged in the abstract
word/access/control model. Physical integer/compiler refinement is separate. -/
namespace FormalProof4FHE.HasteBoots.MerkleLeafIndexCost
open SolverOperationCost (Run)
open BinaryTree

def power : ℕ → Run ℕ
  | 0 => ⟨1,1⟩
  | n+1 => let previous := power n; ⟨previous.value*2,previous.cost+3⟩

theorem power_value (n : ℕ) : (power n).value = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [power,ih,Nat.pow_succ]

theorem power_cost (n : ℕ) : (power n).cost = 3*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [power,ih]; omega

def path : (height : ℕ) → ℕ → Run (SkeletonLeafIndex (Skeleton.perfect height))
  | 0,_ => ⟨.ofLeaf,1⟩
  | height+1,position =>
    let width := power height
    let rest := path height position
    ⟨if position/width.value%2 = 0 then .ofLeft rest.value else .ofRight rest.value,
      width.cost+rest.cost+7⟩

theorem path_value (height position : ℕ) :
    (path height position).value = SkeletonLeafIndex.ofNat height position := by
  induction height with
  | zero => rfl
  | succ height ih => simp only [path,power_value,SkeletonLeafIndex.ofNat,ih]

def pathBound (height : ℕ) := 2*height*height+7*height+1

theorem path_cost (height position : ℕ) : (path height position).cost ≤ pathBound height := by
  induction height with
  | zero => simp [path,pathBound]
  | succ height ih =>
    simp only [path,power_cost,pathBound] at *
    nlinarith

theorem path_equiv (height : ℕ) (position : Fin (2^height)) :
    (path height position.val).value = SkeletonLeafIndex.perfectEquiv height position := by
  rw [path_value,SkeletonLeafIndex.perfectEquiv_apply]
end FormalProof4FHE.HasteBoots.MerkleLeafIndexCost
