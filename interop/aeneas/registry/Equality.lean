/-! The actual native derived SHA512 digest equality agrees with all 64 model
bytes. This proves comparison behavior, not collision resistance or hash code. -/
namespace HasteBootsExtractedRegistryEquality
open Aeneas Aeneas.Std Result
open formalproof4fhe_native_registry_fixture (roots_equal)
open HasteBootsExtractedRegistryProof (Digest)
open HasteBootsExtractedRegistryDecode (root root_injective)
noncomputable section
local instance : DecidableEq Digest := Classical.decEq _
local instance : DecidableEq FormalProof4FHE.HasteBoots.NativeRootMessage.Digest := Classical.decEq _

theorem byte_pairs (left right : List U8) (lengths : left.length = right.length) :
    List.allM (fun (pair : U8 × U8) => do
      let different ← core.cmp.PartialEqU8.ne pair.1 pair.2
      Result.ok (!different)) (left.zip right) = .ok (decide (left = right)) := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => rfl
    | cons byte tail => simp only [List.length_nil,List.length_cons] at lengths; omega
  | cons byte tail ih =>
    cases right with
    | nil => simp only [List.length_nil,List.length_cons] at lengths; omega
    | cons other rest =>
      have sizes : tail.length = rest.length := Nat.succ.inj lengths
      simp only [List.zip_cons_cons,List.allM]
      by_cases same : byte = other
      · subst other
        simpa [core.cmp.PartialEqU8,liftFun2] using ih rest sizes
      · simp [liftFun2,same]
        rfl

theorem roots_equal_exact (left right : Digest) :
    roots_equal left right = .ok (decide (left = right)) := by
  have lists := byte_pairs left.val right.val (left.property.trans right.property.symm)
  have lengths : left.val.length = right.val.length := left.property.trans right.property.symm
  have equal : (left = right) ↔ (left.val = right.val) := Subtype.ext_iff
  simpa [lengths,equal,roots_equal,formalproof4fhe_native_registry_fixture.pcs.utils.hash.Digest512.Insts.CoreCmpPartialEqDigest512.eq,
    core.array.equality.PartialEqArray.eq,Array.length] using lists

theorem roots_equal_model (left right : Digest) :
    roots_equal left right = .ok (decide (root left = root right)) := by
  rw [roots_equal_exact]
  have same : (left = right) ↔ (root left = root right) := ⟨congrArg root,fun equal => root_injective equal⟩
  simp only [same]

theorem roots_equal_true (left right : Digest) :
    roots_equal left right = .ok true ↔ root left = root right := by
  rw [roots_equal_model]
  simp only [Result.ok.injEq,decide_eq_true_eq]

theorem roots_equal_false (left right : Digest) :
    roots_equal left right = .ok false ↔ root left ≠ root right := by
  rw [roots_equal_model]
  simp only [Result.ok.injEq,decide_eq_false_iff_not]

end
end HasteBootsExtractedRegistryEquality
