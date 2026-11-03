module

public import FormalProof4FHE.HasteBoots.NativeMerklePath

@[expose] public section

/-!
# Effect-preserving native Merkle path interpretation

The bottom-up native loop makes the same ordered oracle requests as the typed
VCVio verifier. This is an equality of computations, not only of pure roots.
It therefore preserves cache hits, repeated inputs and shared oracle cells.
-/

open BinaryTree

namespace FormalProof4FHE.HasteBoots.NativeMerklePathM

variable {Digest : Type} {M : Type → Type} [Monad M] [LawfulMonad M]

def branch (hash : Digest → Digest → M Digest) (index : ℕ) (acc sibling : Digest) : M Digest :=
  if index % 2 = 0 then hash acc sibling else hash sibling acc

def root (hash : Digest → Digest → M Digest) : ℕ → Digest → List Digest → M Digest
  | _, leaf, [] => pure leaf
  | index, leaf, sibling :: rest => do
      let next ← branch hash index leaf sibling
      root hash (index / 2) next rest

/-- Fixed original index and increasing loop counter, exactly as in the native checker. -/
def loopFrom (hash : Digest → Digest → M Digest) (index : ℕ) : ℕ → Digest → List Digest → M Digest
  | _, leaf, [] => pure leaf
  | level, leaf, sibling :: rest => do
      let next ← branch hash (index / 2 ^ level) leaf sibling
      loopFrom hash index (level + 1) next rest

omit [LawfulMonad M] in
theorem loopFrom_root (hash : Digest → Digest → M Digest) (index level : ℕ) (leaf : Digest)
    (siblings : List Digest) :
    loopFrom hash index level leaf siblings = root hash (index / 2 ^ level) leaf siblings := by
  induction siblings generalizing level leaf with
  | nil => rfl
  | cons sibling rest ih =>
    simp only [loopFrom, root, ih, Nat.div_div_eq_div_mul, Nat.pow_succ]

omit [LawfulMonad M] in
theorem loop_eq_root (hash : Digest → Digest → M Digest) (index : ℕ) (leaf : Digest)
    (siblings : List Digest) :
    loopFrom hash index 0 leaf siblings = root hash index leaf siblings := by
  simpa only [pow_zero, Nat.div_one] using loopFrom_root hash index 0 leaf siblings

theorem root_append (hash : Digest → Digest → M Digest) (index : ℕ) (leaf : Digest)
    (first rest : List Digest) :
    root hash index leaf (first ++ rest) = (do
      let middle ← root hash index leaf first
      root hash (index / 2 ^ first.length) middle rest) := by
  induction first generalizing index leaf with
  | nil => simp only [List.nil_append, List.length_nil, pow_zero, Nat.div_one, root, pure_bind]
  | cons sibling first ih =>
    simp only [List.cons_append, root, ih, bind_assoc, List.length_cons]
    rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm 2]

theorem root_snoc (hash : Digest → Digest → M Digest) (index : ℕ) (leaf : Digest)
    (siblings : List Digest) (last : Digest) :
    root hash index leaf (siblings ++ [last]) = (do
      let middle ← root hash index leaf siblings
      branch hash (index / 2 ^ siblings.length) middle last) := by
  rw [root_append]
  simp only [root, bind_pure]

/-- Equality with the addressed generic verifier at the constant Unit address. -/
theorem root_eq_typed (hash : Digest → Digest → M Digest) (height index : ℕ) (leaf : Digest)
    (proof : List.Vector Digest (SkeletonLeafIndex.ofNat height index).depth) :
    root hash index leaf proof.toList.reverse =
      AddressedMerkleTree.getPutativeRootAddressedM (fun _ => hash)
        (SkeletonLeafIndex.ofNat height index) leaf proof := by
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
      simp only [branch, ite_eq_left bit]
      change (root hash index leaf proof.tail.toList.reverse >>= fun middle => hash middle proof.head) = _
      exact congrArg (fun computed : M Digest => computed >>= fun middle => hash middle proof.head)
        (ih index leaf proof.tail)
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
      simp only [branch, ite_eq_right bit]
      change (root hash index leaf proof.tail.toList.reverse >>= fun middle => hash proof.head middle) = _
      exact congrArg (fun computed : M Digest => computed >>= fun middle => hash proof.head middle)
        (ih index leaf proof.tail)

/-- Native siblings produce exactly the typed oracle computation after reversal. -/
theorem root_native_eq_typed (hash : Digest → Digest → M Digest) (height index : ℕ)
    (leaf : Digest) (siblings : List.Vector Digest height) :
    root hash index leaf siblings.toList =
      AddressedMerkleTree.getPutativeRootAddressedM (fun _ => hash)
        (SkeletonLeafIndex.ofNat height index) leaf (NativeMerklePath.typedProof height index siblings) := by
  have equality := root_eq_typed hash height index leaf (NativeMerklePath.typedProof height index siblings)
  simpa only [NativeMerklePath.typedProof, List.Vector.toList, List.reverse_reverse] using equality

end FormalProof4FHE.HasteBoots.NativeMerklePathM
