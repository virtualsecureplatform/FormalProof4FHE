module
public import FormalProof4FHE.HasteBoots.NativeResidentVecBorrow
@[expose] public section

/-! Incoming reference and lease preservation through checked traversal steps.
Heap contents are framed separately. This does not establish native Rust region
or lifetime correspondence. Older ledger entries retain their complete leases. -/
namespace FormalProof4FHE.HasteBoots.NativeIncomingReference
open NativeReferenceMachine (State Reference Op)
open NativePointerStorage (Pointer)

structure Preserves (before after : State) : Prop where
  counter : before.nextTag ≤ after.nextTag
  references : ∀ reference ∈ before.references, reference ∈ after.references
  registers : ∀ pointer ∈ before.pointers.registers, pointer ∈ after.pointers.registers
  births : ∀ birth ∈ before.births, birth ∈ after.births
  lookup : ∀ tag, tag < before.nextTag → NativeByteBorrow.lookup after.leases tag = NativeByteBorrow.lookup before.leases tag

theorem Preserves.refl (world : State) : Preserves world world :=
  ⟨Nat.le_refl _,fun _ member => member,fun _ member => member,fun _ member => member,fun _ _ => rfl⟩

theorem Preserves.trans {before middle after : State} (first : Preserves before middle) (second : Preserves middle after) :
    Preserves before after := by
  refine ⟨first.counter.trans second.counter,?_,?_,?_,?_⟩
  · intro reference member; exact second.references reference (first.references reference member)
  · intro pointer member; exact second.registers pointer (first.registers pointer member)
  · intro birth member; exact second.births birth (first.births birth member)
  · intro tag older
    exact (second.lookup tag (Nat.lt_of_lt_of_le older first.counter)).trans (first.lookup tag older)

theorem stable (before after : State) (same : NativeReferenceMachine.SameAuthority before after)
    (pointers : NativePointerMachine.Runs before.pointers after.pointers) : Preserves before after := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [same.1]
  · intro reference member; rw [same.2.2.1]; exact member
  · intro pointer member; exact NativeReferenceMachine.pointer_runs_keep_register _ _ pointers pointer member
  · intro birth member; rw [same.2.2.2]; exact member
  · intro tag _; rw [same.2.1]

theorem grant (before after : State) (parent : Option Nat) (mode : NativeByteBorrow.Mode)
    (pointer : Pointer) (layout : NativeByteMemory.Layout)
    (granted : NativeReferenceMachine.grant before parent mode pointer layout = some after) : Preserves before after := by
  obtain ⟨tag,ledger,borrowed,pointers,counter,leases,references,births⟩ :=
    NativeReferenceMachine.grant_success before after parent mode pointer layout granted
  obtain ⟨fresh,_,raised,leaseEq,_⟩ := NativeByteBorrow.borrow_success (NativeReferenceMachine.ledger before)
    parent mode pointer layout tag ledger borrowed
  change tag = before.nextTag at fresh
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [counter,raised]; exact Nat.le_succ _
  · intro reference member; rw [references]; exact List.mem_cons_of_mem _ member
  · intro value member; rw [pointers]; exact member
  · intro birth member; rw [births]; exact List.mem_cons_of_mem _ member
  · intro query older
    rw [leases,leaseEq,fresh]
    simp only [NativeByteBorrow.lookup,show before.nextTag ≠ query by omega,ite_false]
    rfl

def keepsLoans : Op → Bool
  | .endBorrow _ => false
  | _ => true

theorem step (before after : State) (op : Op) (executed : NativeReferenceMachine.execute before op = some after)
    (checked : keepsLoans op = true := by rfl) : Preserves before after := by
  cases op with
  | raw op =>
    have projected := NativeReferenceMachine.execute_projects before after (.raw op) executed
    apply stable before after _ projected
    simp only [NativeReferenceMachine.execute] at executed
    split at executed
    · obtain ⟨pointers,_,same⟩ := Option.map_eq_some_iff.mp executed
      subst after
      exact ⟨rfl,rfl,rfl,rfl⟩
    · cases executed
  | borrow register mode layout =>
    obtain ⟨pointer,_,granted⟩ := Option.bind_eq_some_iff.mp executed
    exact grant before after none mode pointer layout granted
  | reborrow parent register mode layout =>
    simp only [NativeReferenceMachine.execute,Option.bind_eq_some_iff] at executed
    obtain ⟨reference,_,pointer,_,granted⟩ := executed
    exact grant before after (some reference.tag) mode pointer layout granted
  | access reference offset action =>
    obtain ⟨_,lease,pointer,prepared,_,_,_,_,_,_,_,performed⟩ :=
      NativeReferenceMachine.access_success before after reference offset action executed
    exact stable before after (NativeReferenceMachine.perform_authority before after prepared pointer action performed)
      (NativeReferenceMachine.execute_projects before after (.access reference offset action) executed)
  | endBorrow reference => cases checked

theorem closeScope (entered current : State) (preserved : Preserves entered current) :
    Preserves entered (NativeReferenceCleanup.closeScope entered current).world := by
  have frame := NativeReferenceCleanup.release_frame current (NativeReferenceCleanup.scopeTags entered current)
  have counter := congrArg NativeReferenceMachine.State.nextTag frame
  have references := congrArg NativeReferenceMachine.State.references frame
  have pointers := congrArg NativeReferenceMachine.State.pointers frame
  have births := congrArg NativeReferenceMachine.State.births frame
  change (NativeReferenceCleanup.closeScope entered current).world.nextTag = current.nextTag at counter
  change (NativeReferenceCleanup.closeScope entered current).world.references = current.references at references
  change (NativeReferenceCleanup.closeScope entered current).world.pointers = current.pointers at pointers
  change (NativeReferenceCleanup.closeScope entered current).world.births = current.births at births
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [counter]; exact preserved.counter
  · intro reference member; rw [references]; exact preserved.references reference member
  · intro pointer member; rw [pointers]; exact preserved.registers pointer member
  · intro birth member; rw [births]; exact preserved.births birth member
  · intro tag older
    rw [NativeResidentVecBorrow.closeScope_lookup entered current tag older]
    exact preserved.lookup tag older

theorem issue (before after : State) (mutable : Bool) (input output : NativeSliceLLBC.Value) (element : NativeSliceLLBC.Element)
    (issued : NativeSliceLLBC.issue before mutable input element = some (output,after)) : Preserves before after := by
  cases input with
  | unit => cases issued
  | usize word => cases issued
  | raw raw =>
    rcases raw with ⟨pointer,length⟩
    cases length with
    | none => cases issued
    | some length =>
      simp only [NativeSliceLLBC.issue] at issued
      split at issued
      · obtain ⟨next,executed,same⟩ := Option.map_eq_some_iff.mp issued
        cases same
        exact step before after _ executed
      · cases issued
  | reference mode reference length =>
    simp only [NativeSliceLLBC.issue,Option.bind_eq_some_iff] at issued
    obtain ⟨lease,_,issued⟩ := issued
    split at issued
    · obtain ⟨next,executed,same⟩ := Option.map_eq_some_iff.mp issued
      cases same
      exact step before after _ executed
    · cases issued

theorem index (world : State) (slice : NativeByteSliceIndex.Slice) (offset : NativeWord64Memory.Word) :
    Preserves world (NativeByteSliceIndex.index world slice offset).world := by
  unfold NativeByteSliceIndex.index
  split
  · split
    · exact .refl _
    · rename_i selected found
      split
      · exact .refl _
      · rename_i pointer shifted
        split
        · exact .refl _
        · rename_i prepared address
          have first := step world prepared _ address
          split
          · exact first
          · rename_i next issued
            exact first.trans (step prepared next _ issued)
  · exact .refl _

theorem iteration (world : State) (slice : NativeByteSliceIndex.Slice) (offset : NativeWord64Memory.Word) :
    Preserves world (NativeByteDropTraversal.iteration world slice offset).world := by
  cases actual : NativeSliceLLBC.issue world true (.reference true slice.reference slice.length) .byte with
  | none => simp only [NativeByteDropTraversal.iteration,actual,NativeByteDropTraversal.Iteration.world]; exact .refl _
  | some pair =>
    rcases pair with ⟨value,borrowed⟩
    have first := issue world borrowed true _ value .byte actual
    obtain ⟨length,same⟩ := NativeSliceLLBC.issue_returned_tag world borrowed true _ value actual
    subst value
    simp only [NativeByteDropTraversal.iteration,actual]
    cases indexed : NativeByteSliceIndex.index borrowed ⟨⟨world.nextTag⟩,length⟩ offset with
    | invalid next =>
      have second := index borrowed ⟨⟨world.nextTag⟩,length⟩ offset
      rw [indexed] at second
      exact first.trans second
    | value child next =>
      simp only []
      have second := index borrowed ⟨⟨world.nextTag⟩,length⟩ offset
      rw [indexed] at second
      have prior := first.trans second
      cases recovered : NativeByteSliceIndex.rawByte next child with
      | none => exact prior
      | some pointer =>
        simp only []
        split <;> exact closeScope world next prior

theorem executes (slice : NativeByteSliceIndex.Slice) (cursor : Nat) (world : State) (last : Option Pointer)
    (result : NativeByteDropTraversal.Result) (executed : NativeByteDropTraversal.Executes slice cursor world last result) :
    Preserves world result.world := by
  induction executed with
  | stop cursor world last done => exact .refl _
  | fail cursor world next last before failed =>
    have preserved := iteration world slice ⟨cursor,Nat.lt_trans before slice.length.isLt⟩
    simpa only [failed,NativeByteDropTraversal.Iteration.world] using preserved
  | next cursor world next last pointer result before actual later ih =>
    have preserved := iteration world slice ⟨cursor,Nat.lt_trans before slice.length.isLt⟩
    have first : Preserves world next := by simpa only [actual,NativeByteDropTraversal.Iteration.world] using preserved
    exact first.trans ih

theorem runFrom (slice : NativeByteSliceIndex.Slice) (cursor : Nat) (bounded : cursor ≤ slice.length.val)
    (world : State) (last : Option Pointer) : Preserves world (NativeByteDropTraversal.runFrom slice cursor bounded world last).world :=
  executes slice cursor world last _ (NativeByteDropTraversal.runFrom_executes slice cursor bounded world last)

theorem run (world : State) (slice : NativeByteSliceIndex.Slice) : Preserves world (NativeByteDropTraversal.run world slice).world :=
  runFrom slice 0 (Nat.zero_le _) world none

theorem resident {before after : State} {mutable : Bool} {reference : Reference} {count capacity length : NativeWord64Memory.Word}
    {base buffer : Pointer}
    (preserved : Preserves before after)
    (view : NativeResidentVecBorrow.Resident before (.reference mutable reference count) base capacity length buffer)
    (older : reference.tag < before.nextTag) (heap : after.pointers.heap = before.pointers.heap) :
    NativeResidentVecBorrow.Resident after (.reference mutable reference count) base capacity length buffer := by
  obtain ⟨flag,ref,extent,lease,same,member,registered,baseEq,mode,shape,present,contents⟩ := view
  cases same
  exact ⟨mutable,reference,count,lease,rfl,preserved.references reference member,
    (preserved.lookup reference.tag older).trans registered,baseEq,mode,shape,preserved.registers base present,contents.heap_frame heap⟩

theorem traversal_resident (world : State) (slice : NativeByteSliceIndex.Slice)
    (mutable : Bool) (reference : Reference) (count capacity length : NativeWord64Memory.Word) (base buffer : Pointer)
    (view : NativeResidentVecBorrow.Resident world (.reference mutable reference count) base capacity length buffer)
    (older : reference.tag < world.nextTag) :
    NativeResidentVecBorrow.Resident (NativeByteDropTraversal.run world slice).world (.reference mutable reference count)
      base capacity length buffer :=
  resident (run world slice) view older (NativeByteDropTraversal.run_heap_frame world slice)

end FormalProof4FHE.HasteBoots.NativeIncomingReference
