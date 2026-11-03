module

public import FormalProof4FHE.HasteBoots.MerkleAvailability
public import Mathlib.Data.Nat.Bitwise

@[expose] public section

/-!
# Native bottom-up Merkle path evaluation

The path starts with the leaf digest and then lists siblings from the leaf
upwards. The loop reads successive low bits of the original column index.
VCVio's typed path lists siblings in the opposite order; `root_eq_typed`
establishes the bridge without assuming a path interpretation premise.
Machine-size bounds and byte serialization remain separate refinements.
-/

open BinaryTree

namespace FormalProof4FHE.HasteBoots.NativeMerklePath

variable {Digest : Type}

/-- Hash an accumulator with its sibling in the direction selected by the low bit. -/
def branch (hash : Digest → Digest → Digest) (index : ℕ) (acc sibling : Digest) : Digest :=
  if index % 2 = 0 then hash acc sibling else hash sibling acc

/-- Exact natural-number interpretation of the native right-shift and low-bit mask. -/
theorem direction (index level : ℕ) :
    ((index >>> level) &&& 1) = (index / 2 ^ level) % 2 := by
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

/-- Bottom-up path evaluation, dropping one index bit at each level. -/
def root (hash : Digest → Digest → Digest) : ℕ → Digest → List Digest → Digest
  | _, leaf, [] => leaf
  | index, leaf, sibling :: rest =>
      root hash (index / 2) (branch hash index leaf sibling) rest

/-- Processing a path prefix discards precisely that many low index bits. -/
theorem root_append (hash : Digest → Digest → Digest) (index : ℕ) (leaf : Digest)
    (first rest : List Digest) :
    root hash index leaf (first ++ rest) =
      root hash (index / 2 ^ first.length) (root hash index leaf first) rest := by
  induction first generalizing index leaf with
  | nil => simp only [List.nil_append, List.length_nil, pow_zero, Nat.div_one, root]
  | cons sibling first ih =>
    simp only [List.cons_append, root, ih, List.length_cons]
    rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm 2]

/-- The final sibling is the root-level sibling, selected by the highest path bit. -/
theorem root_snoc (hash : Digest → Digest → Digest) (index : ℕ) (leaf : Digest)
    (siblings : List Digest) (last : Digest) :
    root hash index leaf (siblings ++ [last]) =
      branch hash (index / 2 ^ siblings.length) (root hash index leaf siblings) last := by
  rw [root_append]
  rfl

/-- The native loop's counter and hash accumulator, before taking its final digest. -/
def loopFrom (hash : Digest → Digest → Digest) (index level : ℕ) (leaf : Digest)
    (siblings : List Digest) : ℕ × Digest :=
  siblings.foldl (fun state sibling =>
    (state.1 + 1, branch hash (index / 2 ^ state.1) state.2 sibling)) (level, leaf)

theorem loopFrom_root (hash : Digest → Digest → Digest) (index level : ℕ) (leaf : Digest)
    (siblings : List Digest) :
    (loopFrom hash index level leaf siblings).2 = root hash (index / 2 ^ level) leaf siblings := by
  induction siblings generalizing level leaf with
  | nil => rfl
  | cons sibling rest ih =>
    change (loopFrom hash index (level + 1)
      (branch hash (index / 2 ^ level) leaf sibling) rest).2 = _
    rw [ih, root, Nat.div_div_eq_div_mul, Nat.pow_succ]

/-- Literal fixed-index, increasing-level loop and the bit-dropping recursion agree. -/
theorem loop_eq_root (hash : Digest → Digest → Digest) (index : ℕ) (leaf : Digest)
    (siblings : List Digest) :
    (loopFrom hash index 0 leaf siblings).2 = root hash index leaf siblings := by
  simpa only [pow_zero, Nat.div_one] using loopFrom_root hash index 0 leaf siblings

/-- VCVio's root-to-leaf typed proof is the reverse of the native sibling list. -/
theorem root_eq_typed (hash : Digest → Digest → Digest) (height index : ℕ) (leaf : Digest)
    (proof : List.Vector Digest (SkeletonLeafIndex.ofNat height index).depth) :
    root hash index leaf proof.toList.reverse =
      InductiveMerkleTree.getPutativeRootWithHash (SkeletonLeafIndex.ofNat height index) leaf proof hash := by
  induction height generalizing index leaf with
  | zero =>
    change List.Vector Digest 0 at proof
    rw [List.Vector.eq_nil proof]
    rfl
  | succ height ih =>
    generalize selected : SkeletonLeafIndex.ofNat (height + 1) index = idx at proof ⊢
    have form : (if index / 2 ^ height % 2 = 0 then
        SkeletonLeafIndex.ofLeft (SkeletonLeafIndex.ofNat height index) else
        SkeletonLeafIndex.ofRight (SkeletonLeafIndex.ofNat height index)) = idx := by
      simpa only [SkeletonLeafIndex.ofNat] using selected
    by_cases bit : index / 2 ^ height % 2 = 0
    · rw [ite_eq_left bit] at form
      cases form
      have split : proof.toList.reverse = proof.tail.toList.reverse ++ [proof.head] := by
        have asList : proof.toList = proof.head :: proof.tail.toList := by
          rw [← proof.cons_head_tail]
          rfl
        rw [asList, List.reverse_cons]
      have length : proof.tail.toList.length = height := by
        simp only [List.Vector.toList_length, SkeletonLeafIndex.depth,
          SkeletonLeafIndex.depth_ofNat, Nat.add_sub_cancel]
      rw [split, root_snoc, List.length_reverse, length]
      change branch hash (index / 2 ^ height) _ _ =
        hash (InductiveMerkleTree.getPutativeRootWithHash (SkeletonLeafIndex.ofNat height index)
          leaf proof.tail hash) proof.head
      rw [branch, ite_eq_left bit]
      exact congrArg (fun digest => hash digest proof.head) (ih index leaf proof.tail)
    · rw [ite_eq_right bit] at form
      cases form
      have split : proof.toList.reverse = proof.tail.toList.reverse ++ [proof.head] := by
        have asList : proof.toList = proof.head :: proof.tail.toList := by
          rw [← proof.cons_head_tail]
          rfl
        rw [asList, List.reverse_cons]
      have length : proof.tail.toList.length = height := by
        simp only [List.Vector.toList_length, SkeletonLeafIndex.depth,
          SkeletonLeafIndex.depth_ofNat, Nat.add_sub_cancel]
      rw [split, root_snoc, List.length_reverse, length]
      change branch hash (index / 2 ^ height) _ _ =
        hash proof.head (InductiveMerkleTree.getPutativeRootWithHash (SkeletonLeafIndex.ofNat height index)
          leaf proof.tail hash)
      rw [branch, ite_eq_right bit]
      exact congrArg (fun digest => hash proof.head digest) (ih index leaf proof.tail)

/-- Convert native bottom-up siblings to VCVio's root-to-leaf typed proof. -/
def typedProof (height index : ℕ) (siblings : List.Vector Digest height) :
    List.Vector Digest (SkeletonLeafIndex.ofNat height index).depth :=
  ⟨siblings.toList.reverse, by
    rw [List.length_reverse, List.Vector.toList_length, SkeletonLeafIndex.depth_ofNat]⟩

/-- The native path array, with its actual order, evaluates to the typed Merkle root. -/
theorem root_native_eq_typed (hash : Digest → Digest → Digest) (height index : ℕ)
    (leaf : Digest) (siblings : List.Vector Digest height) :
    root hash index leaf siblings.toList =
      InductiveMerkleTree.getPutativeRootWithHash (SkeletonLeafIndex.ofNat height index)
        leaf (typedProof height index siblings) hash := by
  have equality := root_eq_typed hash height index leaf (typedProof height index siblings)
  simpa only [typedProof, List.Vector.toList, List.reverse_reverse] using equality

end FormalProof4FHE.HasteBoots.NativeMerklePath
