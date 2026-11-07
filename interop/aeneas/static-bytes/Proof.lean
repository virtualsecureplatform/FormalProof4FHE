/-! Exact contents of extracted byte constants. This is a compiler regression
and tag-value agreement, not a native NTT/context refinement theorem. -/
namespace HasteBootsStaticBytesProof
open Aeneas Aeneas.Std Result
open hasteboots_static_bytes

def contents (value : Result (Slice U8)) : Result (List ℕ) := do
  let bytes ← value
  .ok (bytes.val.map (fun byte => byte.val))

def arrayContents : Result (List ℕ) := do
  let bytes ← array
  .ok (bytes.val.map (fun byte => byte.val))

def copiedContents : Result (List ℕ × List ℕ) := do
  let pair ← copy_domain
  .ok (pair.1.val.map (fun byte => byte.val),pair.2.val.map (fun byte => byte.val))

def tag : List ℕ := [98,108,111,99,107,45,114,115,47,110,101,103,97,99,121,99,108,105,99,45,110,116,116,47,118,49]

theorem domain_bytes : contents domain = .ok tag := rfl

theorem array_bytes : arrayContents = .ok [0,127,128,255] := rfl

theorem empty_bytes : contents empty = .ok [] := rfl

theorem copied_bytes : copiedContents = .ok (tag,tag) := rfl

theorem escaped_bytes : contents escaped = .ok [34,92,10,9,13,0,127,207,128] := rfl

theorem borrow_identity (input : Slice U8) : preserve_borrow input = .ok input := rfl

theorem domain_length : ∃ bytes, domain = .ok bytes ∧ bytes.val.length = 26 := by
  exact ⟨_,rfl,rfl⟩

theorem domain_model : contents domain = .ok
    (FormalProof4FHE.HasteBoots.NativeGoldBlockCode.domain.val.map Fin.val) := rfl

end HasteBootsStaticBytesProof
