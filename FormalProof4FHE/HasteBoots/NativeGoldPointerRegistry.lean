module
public import FormalProof4FHE.HasteBoots.NativePointerStorage
public import FormalProof4FHE.HasteBoots.NativeGoldParameterStore
@[expose] public section

/-! Generation-aware pointer resolution into the constructed parameter arena.
The heap stores logical arena handles; resolution retains every original root
and position. This is an operational specification, not a Rust allocator,
object-layout, borrow, or physical-work refinement. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldPointerRegistry
open NativeGoldParameterStore (Entry Reference GoodEntry)
open NativePointerStorage (Cell Pointer read)

structure Borrow where
  pointer : Pointer
  root : NativeRootMessage.Digest

def resolve (heap : List (Cell ℕ)) : List Borrow → Option (List Reference)
  | [] => some []
  | borrowed::tail =>
    match read heap borrowed.pointer with
    | none => none
    | some handle => (resolve heap tail).map (fun rest => ⟨handle,borrowed.root⟩::rest)

theorem resolve_length (heap : List (Cell ℕ)) (borrows : List Borrow) (references : List Reference)
    (executed : resolve heap borrows = some references) : references.length = borrows.length := by
  induction borrows generalizing references with
  | nil => cases executed; rfl
  | cons borrowed tail ih =>
    simp only [resolve] at executed
    cases found : read heap borrowed.pointer with
    | none => simp only [found] at executed; cases executed
    | some handle =>
      simp only [found] at executed
      cases rest : resolve heap tail with
      | none => simp only [rest,Option.map_none] at executed; cases executed
      | some output =>
        simp only [rest,Option.map_some] at executed
        cases executed
        simpa only [List.length_cons] using congrArg Nat.succ (ih output rest)

theorem resolve_slot (heap : List (Cell ℕ)) (borrows : List Borrow) (references : List Reference)
    (executed : resolve heap borrows = some references) (index : ℕ) (bound : index < borrows.length) :
    ∃ borrowed reference, borrows[index]? = some borrowed ∧ references[index]? = some reference ∧
      read heap borrowed.pointer = some reference.handle ∧ reference.root = borrowed.root := by
  induction borrows generalizing references index with
  | nil => cases bound
  | cons borrowed tail ih =>
    simp only [resolve] at executed
    cases found : read heap borrowed.pointer with
    | none => simp only [found] at executed; cases executed
    | some handle =>
      simp only [found] at executed
      cases rest : resolve heap tail with
      | none => simp only [rest,Option.map_none] at executed; cases executed
      | some output =>
        simp only [rest,Option.map_some] at executed
        cases executed
        cases index with
        | zero => exact ⟨borrowed,⟨handle,borrowed.root⟩,rfl,rfl,found,rfl⟩
        | succ index => exact ih output rest index (by simpa using bound)

def references (heap : List (Cell ℕ)) (borrows : NativePrefixCodec.Vector Borrow) :
    Option (NativePrefixCodec.Vector Reference) :=
  match executed : resolve heap borrows.val with
  | none => none
  | some output => some ⟨output,by rw [resolve_length heap borrows.val output executed]; exact borrows.property⟩

theorem references_values (heap : List (Cell ℕ)) (borrows : NativePrefixCodec.Vector Borrow)
    (output : NativePrefixCodec.Vector Reference) (executed : references heap borrows = some output) :
    resolve heap borrows.val = some output.val ∧ output.val.length = borrows.val.length := by
  unfold references at executed
  split at executed
  · cases executed
  · rename_i values resolved
    cases executed
    exact ⟨resolved,resolve_length heap borrows.val values resolved⟩

def registry (entries : List Entry) (heap : List (Cell ℕ)) (borrows : NativePrefixCodec.Vector Borrow) :=
  (references heap borrows).bind (NativeGoldParameterStore.registry entries)

theorem registry_resolves (entries : List Entry) (heap : List (Cell ℕ)) (borrows : NativePrefixCodec.Vector Borrow)
    (output : NativePrefixCodec.Vector (NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored))
    (executed : registry entries heap borrows = some output) :
    ∃ resolved, references heap borrows = some resolved ∧ NativeGoldParameterStore.registry entries resolved = some output := by
  unfold registry at executed
  cases found : references heap borrows with
  | none => simp only [found,Option.bind_none] at executed; cases executed
  | some resolved => exact ⟨resolved,rfl,by simpa only [found,Option.bind_some] using executed⟩

theorem registry_length (entries : List Entry) (heap : List (Cell ℕ)) (borrows : NativePrefixCodec.Vector Borrow)
    (output : NativePrefixCodec.Vector (NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored))
    (executed : registry entries heap borrows = some output) : output.val.length = borrows.val.length := by
  obtain ⟨resolved,resolution,retained⟩ := registry_resolves entries heap borrows output executed
  exact (NativeGoldParameterStore.registry_values entries resolved output retained).2.trans
    (references_values heap borrows resolved resolution).2

theorem registry_slot (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (heap : List (Cell ℕ)) (borrows : NativePrefixCodec.Vector Borrow)
    (output : NativePrefixCodec.Vector (NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored))
    (executed : registry entries heap borrows = some output) (index : Fin output.val.length) :
    ∃ borrowed cell entry, borrows.val[index.val]? = some borrowed ∧ cell ∈ heap ∧
      borrowed.pointer.provenance = some cell.origin ∧ borrowed.pointer.address = cell.address ∧
      entries[cell.value]? = some entry ∧ GoodEntry entry ∧
      output.val.get index = ⟨entry.initialized.parameters,borrowed.root⟩ := by
  obtain ⟨resolved,resolution,retained⟩ := registry_resolves entries heap borrows output executed
  have values := references_values heap borrows resolved resolution
  have lengths := (NativeGoldParameterStore.registry_values entries resolved output retained).2
  obtain ⟨borrowed,reference,atBorrow,atReference,found,root⟩ := resolve_slot heap borrows.val resolved.val values.1 index.val
    (by rw [← values.2,← lengths]; exact index.isLt)
  obtain ⟨selected,entry,atSelected,atEntry,good,oracle⟩ := NativeGoldParameterStore.registry_slot entries reachable resolved output retained index
  have same : selected = reference := Option.some.inj (atSelected.symm.trans atReference)
  subst selected
  obtain ⟨cell,member,origin,address,value⟩ := NativePointerStorage.read_selected heap borrowed.pointer reference.handle found
  exact ⟨borrowed,cell,entry,atBorrow,member,origin,address,by simpa only [value] using atEntry,good,by simpa only [root] using oracle⟩

end FormalProof4FHE.HasteBoots.NativeGoldPointerRegistry
