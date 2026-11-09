module
public import FormalProof4FHE.HasteBoots.NativeByteBorrow
@[expose] public section

/-! Loans over live storage check permissions and extent without reading bytes.
Initialized-byte borrowing remains a separate operation. These storage loans do
not by themselves establish the validity of any Rust pointee type. -/
namespace FormalProof4FHE.HasteBoots.NativeByteBorrowStorage
open NativeByteBorrow
open NativeByteMemory (Layout)
open NativePointerStorage (Pointer)

def borrow (state : State) (parent : Option Nat) (mode : Mode) (pointer : Pointer) (layout : Layout) :
    Option (Nat × State) :=
  if parentAllowed state parent mode pointer layout && NativeByteRange.checkRange state.memory pointer layout then
    some (state.nextTag,⟨state.memory,state.nextTag+1,⟨state.nextTag,parent,pointer,layout,mode⟩ :: state.leases⟩)
  else none

theorem borrow_success (state : State) (parent : Option Nat) (mode : Mode) (pointer : Pointer) (layout : Layout)
    (tag : Nat) (next : State) (executed : borrow state parent mode pointer layout = some (tag,next)) :
    tag = state.nextTag ∧ next.memory = state.memory ∧ next.nextTag = state.nextTag+1 ∧
      next.leases = ⟨tag,parent,pointer,layout,mode⟩ :: state.leases ∧
      parentAllowed state parent mode pointer layout = true ∧ NativeByteRange.checkRange state.memory pointer layout = true := by
  unfold borrow at executed
  split at executed
  next checked =>
    cases executed
    exact ⟨rfl,rfl,rfl,rfl,(Bool.and_eq_true_iff.mp checked).1,(Bool.and_eq_true_iff.mp checked).2⟩
  next => cases executed

theorem checked_geometry (state : NativeByteMemory.State) (pointer : Pointer) (layout : Layout)
    (checked : NativeByteRange.checkRange state pointer layout = true) : NativeByteRange.Geometry pointer layout := by
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp checked).1

theorem borrow_geometry (state : State) (parent : Option Nat) (mode : Mode) (pointer : Pointer) (layout : Layout)
    (tag : Nat) (next : State) (executed : borrow state parent mode pointer layout = some (tag,next)) :
    NativeByteRange.Geometry pointer layout :=
  checked_geometry state.memory pointer layout (borrow_success state parent mode pointer layout tag next executed).2.2.2.2.2

theorem borrow_complete (state : State) (parent : Option Nat) (mode : Mode) (pointer : Pointer) (layout : Layout)
    (allowed : parentAllowed state parent mode pointer layout = true)
    (checked : NativeByteRange.checkRange state.memory pointer layout = true) :
    borrow state parent mode pointer layout =
      some (state.nextTag,⟨state.memory,state.nextTag+1,⟨state.nextTag,parent,pointer,layout,mode⟩ :: state.leases⟩) := by
  simp only [borrow,allowed,checked,Bool.and_self,ite_true]

theorem initialized_refines (state : State) (parent : Option Nat) (mode : Mode) (pointer : Pointer) (layout : Layout)
    (tag : Nat) (next : State) (executed : NativeByteBorrow.borrow state parent mode pointer layout = some (tag,next)) :
    borrow state parent mode pointer layout = some (tag,next) := by
  obtain ⟨fresh,memory,counter,leases,allowed,bytes,loaded⟩ := NativeByteBorrow.borrow_success state parent mode pointer layout tag next executed
  rw [borrow_complete state parent mode pointer layout allowed (NativeByteRange.loadRange_checked _ _ _ _ loaded)]
  subst tag
  cases state
  cases next
  simp_all

theorem borrow_wellFormed (state : State) (valid : WellFormed state) (parent : Option Nat)
    (mode : Mode) (pointer : Pointer) (layout : Layout) (tag : Nat) (next : State)
    (executed : borrow state parent mode pointer layout = some (tag, next)) : WellFormed next := by
  obtain ⟨sameTag, memory, counter, leases, allowed, checked⟩ := borrow_success state parent mode pointer layout tag next executed
  have geometry := checked_geometry state.memory pointer layout checked
  constructor
  · rw [memory]; exact valid.1
  · constructor
    · intro lease member
      rw [leases] at member
      rcases List.mem_cons.mp member with fresh | old
      · subst lease
        refine ⟨by change tag < next.nextTag; omega, geometry, ?_⟩
        cases parent with
        | none => trivial
        | some id =>
          obtain ⟨older, found, before, modes, origin, lower, upper, _⟩ := parent_checked state id mode pointer layout allowed
          obtain ⟨member, same⟩ := lookup_selected state.leases id older found
          refine ⟨by change id < tag; omega, older, ?_, same, modes, origin, lower, upper⟩
          rw [leases]
          exact List.mem_cons_of_mem _ member
      · obtain ⟨before, shape, parentValid⟩ := valid.2.1 lease old
        refine ⟨by omega, shape, ?_⟩
        cases parental : lease.parent with
        | none => trivial
        | some id =>
          rw [parental] at parentValid
          obtain ⟨before, older, selected, same, parentScope⟩ := parentValid
          refine ⟨before, older, ?_, same, parentScope⟩
          rw [leases]
          exact List.mem_cons_of_mem _ selected
    · rw [leases, List.pairwise_cons]
      refine ⟨?_, valid.2.2⟩
      intro old member same
      have before := (valid.2.1 old member).1
      change tag = old.tag at same
      omega

theorem borrow_live (state : State) (parent : Option Nat) (mode : Mode) (pointer : Pointer) (layout : Layout)
    (tag : Nat) (next : State) (positive : 0 < layout.size)
    (executed : borrow state parent mode pointer layout = some (tag,next)) :
    ∃ block ∈ state.memory.blocks, NativeByteRange.Covers block pointer layout.size := by
  have checked := (borrow_success state parent mode pointer layout tag next executed).2.2.2.2.2
  simp only [NativeByteRange.checkRange,Bool.and_eq_true] at checked
  rw [ite_eq_right (Nat.ne_of_gt positive)] at checked
  obtain ⟨block,member,covered⟩ := List.any_eq_true.mp checked.2
  exact ⟨block,member,of_decide_eq_true covered⟩

theorem root_exclusive_separated (state : State) (pointer : Pointer) (layout : Layout) (tag : Nat) (next : State)
    (executed : borrow state none .exclusive pointer layout = some (tag,next)) (lease : Lease)
    (member : lease ∈ state.leases) : ¬ Overlap pointer layout lease.pointer lease.layout :=
  raw_exclusive_no_overlap state pointer layout
    (borrow_success state none .exclusive pointer layout tag next executed).2.2.2.2.1 lease member

end FormalProof4FHE.HasteBoots.NativeByteBorrowStorage
