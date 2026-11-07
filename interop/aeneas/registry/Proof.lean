/-! Checked field/index reads from the actual native verifier-oracle carrier.
Borrowed references use Aeneas's value translation; heap identity is separate. -/
namespace HasteBootsExtractedRegistryProof
open Aeneas Aeneas.Std Result
open formalproof4fhe_native_registry_fixture
abbrev Oracle (O P : Type) := snarks.packed_oracle.CanonicalVerifierOracle O P
abbrev Digest := pcs.utils.hash.Digest512

theorem fields_exact {O P : Type} (source : Oracle O P) :
    fields source = .ok (source.parameters,source.commitment.root) := rfl

theorem length_exact {O P : Type} (registry : Slice (Oracle O P)) :
    registry_len registry = .ok (Slice.len registry) := rfl

theorem length_value {O P : Type} (registry : Slice (Oracle O P)) (word : Usize)
    (executed : registry_len registry = .ok word) : word.val = registry.val.length := by
  have same : Slice.len registry = word := Result.ok.inj executed
  rw [← same,Slice.len_val]

theorem get_exact {O P : Type} (registry : Slice (Oracle O P)) (index : Usize) :
    registry_get registry index =
      .ok (registry.val[index.val]?.map (fun source => (source.parameters,source.commitment.root))) := by
  change (match registry.val[index.val]? with
    | none => Result.ok none
    | some source => Result.ok (some (source.parameters,source.commitment.root))) = _
  cases registry.val[index.val]? <;> rfl

theorem get_present {O P : Type} (registry : Slice (Oracle O P)) (index : Usize) (source : Oracle O P)
    (present : registry.val[index.val]? = some source) :
    registry_get registry index = .ok (some (source.parameters,source.commitment.root)) := by
  rw [get_exact,present]
  rfl

theorem get_absent {O P : Type} (registry : Slice (Oracle O P)) (index : Usize)
    (outside : registry.val.length ≤ index.val) : registry_get registry index = .ok none := by
  rw [get_exact,List.getElem?_eq_none outside]
  rfl

theorem root_bytes_exact {P : Type} (source : Oracle Digest P) :
    root_bytes source = .ok source.commitment.root := rfl

theorem root_length (root : Digest) : root.val.length = 64 := by
  have literal : (64#usize).val = 64 := by scalar_tac
  exact root.property.trans literal

end HasteBootsExtractedRegistryProof
