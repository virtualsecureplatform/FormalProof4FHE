module
public import FormalProof4FHE.HasteBoots.NativeScopeRestoration
@[expose] public section

/-! Sufficient modeled slice conditions for successful unbounded traversal.
The conditions distinguish initialized elements and physical alias availability
from native Rust construction, compiler and lifetime correspondence. -/
namespace FormalProof4FHE.HasteBoots.NativeByteTraversalCompleteness
open NativeReferenceMachine (State Reference)
open NativeByteSliceIndex (Slice)
open NativeByteBorrow (Lease)
open NativePointerStorage (Pointer)
open NativeWord64Memory (Word)
open NativeBorrowFrontier (ExclusiveFrontier)

/-- A reachable resident slice with initialized elements and an available
exclusive loan. Spare allocation capacity is deliberately absent. -/
def Ready (world : State) (slice : Slice) : Prop :=
  NativeReferenceMachine.Reachable world ∧ ∃ lease,
    NativeByteBorrow.lookup world.leases slice.reference.tag = some lease ∧
    slice.reference ∈ world.references ∧ lease.pointer ∈ world.pointers.registers ∧
    lease.layout = ⟨slice.length.val,1⟩ ∧ ExclusiveFrontier (NativeReferenceMachine.ledger world) lease ∧
    ∃ bytes, NativeByteRange.loadRange world.pointers.heap.memory lease.pointer ⟨slice.length.val,1⟩ = some bytes

theorem issue_complete (world : State) (slice : Slice) (ready : Ready world slice) :
    ∃ next, NativeSliceLLBC.issue world true (.reference true slice.reference slice.length) .byte =
      some (.reference true ⟨world.nextTag⟩ slice.length,next) ∧ Ready next ⟨⟨world.nextTag⟩,slice.length⟩ := by
  obtain ⟨reachable,lease,registered,referenceResident,pointerResident,shape,frontier,bytes,loaded⟩ := ready
  have valid := NativeReferenceMachine.reachable_wellFormed world reachable
  have ledgerValid : NativeByteBorrow.WellFormed (NativeReferenceMachine.ledger world) := ⟨valid.1.1,valid.2.1⟩
  obtain ⟨pointer,next,shifted,granted,available⟩ := NativeBorrowFrontier.grant_subrange world ledgerValid lease frontier
    slice.length.val 0 slice.length.val shape bytes loaded (by omega)
  rw [NativeResidentVecBorrow.pointerAt_zero] at shifted
  have same := Option.some.inj shifted
  subst pointer
  have tag := (NativeByteBorrow.lookup_selected _ _ _ registered).2
  have executed : NativeReferenceMachine.execute world
      (.reborrow (world.references.idxOf slice.reference) (world.pointers.registers.idxOf lease.pointer)
        .exclusive ⟨slice.length.val,1⟩) = some next := by
    simp only [NativeReferenceMachine.execute,List.getElem?_idxOf referenceResident,
      List.getElem?_idxOf pointerResident,Option.bind_some]
    simpa only [tag] using granted
  have issued : NativeSliceLLBC.issue world true (.reference true slice.reference slice.length) .byte =
      some (.reference true ⟨world.nextTag⟩ slice.length,next) := by
    simp only [NativeSliceLLBC.issue,registered,Option.bind_some,shape,NativeSliceLLBC.layout,
      NativeSliceLLBC.Element.width,Nat.one_mul,List.getElem?_idxOf referenceResident,
      List.getElem?_idxOf pointerResident,and_self,ite_true,NativeSliceLLBC.mode,executed,Option.map_some]
  obtain ⟨fresh,ledger,borrowed,pointers,_,_,references,_⟩ := NativeReferenceMachine.grant_success world next _ _ _ _ granted
  have freshTag := (NativeByteBorrow.borrow_success (NativeReferenceMachine.ledger world) _ _ _ _ fresh ledger borrowed).1
  refine ⟨next,issued,?_,⟨world.nextTag,some lease.tag,lease.pointer,⟨slice.length.val,1⟩,.exclusive⟩,?_,?_,?_,rfl,available,bytes,?_⟩
  · exact NativeSliceLLBC.reference_runs_reachable world next reachable (NativeSliceLLBC.issue_projects _ _ _ _ _ issued)
  · exact available.2.1
  · rw [references,freshTag]; exact List.mem_cons_self
  · rw [pointers]; exact pointerResident
  · rw [pointers]; exact loaded

/-- Indexing also leaves the recovered raw byte pointer in the actual native
registers; no pointer-recovery success premise is supplied. -/
theorem index_raw_complete (world : State) (slice : Slice) (ready : Ready world slice) (offset : Word)
    (bounded : offset.val < slice.length.val) :
    ∃ pointer next, NativeByteSliceIndex.index world slice offset = .value ⟨world.nextTag⟩ next ∧
      NativeByteSliceIndex.rawByte next ⟨world.nextTag⟩ = some pointer := by
  obtain ⟨reachable,lease,registered,referenceResident,pointerResident,shape,frontier,bytes,loaded⟩ := ready
  have valid := NativeReferenceMachine.reachable_wellFormed world reachable
  obtain ⟨pointer,next,indexed,shifted,available⟩ := NativeBorrowFrontier.index_complete world ⟨valid.1.1,valid.2.1⟩
    slice lease registered referenceResident pointerResident shape frontier bytes loaded offset bounded
  obtain ⟨_,selected,point,prepared,selection,atPoint,preparation,issued,_⟩ := NativeByteSliceIndex.index_success _ _ _ _ _ indexed
  obtain ⟨selectedLease,selectedReference,selectedPointer,_,_⟩ := NativeByteSliceIndex.select_success _ _ _ selection
  have sameLease := Option.some.inj (selectedLease.symm.trans registered)
  have samePoint : point = pointer := by rw [sameLease] at atPoint; exact Option.some.inj (atPoint.symm.trans shifted)
  subst point
  have provenance := (NativeByteRange.pointerAt_fields selected.lease.pointer offset.val pointer atPoint).2
  have scratch : (⟨pointer.address,selected.lease.pointer.provenance⟩ : Pointer) = pointer := by rw [← provenance]
  have preparedEq : prepared = {world with pointers := NativePointerMachine.push world.pointers pointer} := by
    simp only [NativeReferenceMachine.execute,NativeReferenceMachine.rawPermissions,ite_true,
      NativePointerMachine.execute,selectedPointer,Option.map_some,NativeReferenceMachine.setPointers,scratch,
      Option.some.injEq] at preparation
    exact preparation.symm
  have sourceReference : prepared.references[selected.parent]? = some slice.reference := by rw [preparedEq]; exact selectedReference
  have sourcePointer : prepared.pointers.registers[0]? = some pointer := by rw [preparedEq]; rfl
  have grantEq : NativeReferenceMachine.grant prepared (some slice.reference.tag) .exclusive pointer ⟨1,1⟩ = some next := by
    simpa only [NativeReferenceMachine.execute,sourceReference,sourcePointer,Option.bind_some] using issued
  obtain ⟨fresh,ledger,borrowed,pointers,_,_,references,_⟩ := NativeReferenceMachine.grant_success prepared next _ _ _ _ grantEq
  have freshTag := (NativeByteBorrow.borrow_success (NativeReferenceMachine.ledger prepared) _ _ _ _ fresh ledger borrowed).1
  change fresh = prepared.nextTag at freshTag
  have freshBefore : fresh = world.nextTag := by simpa only [preparedEq] using freshTag
  have refMember : (⟨world.nextTag⟩ : Reference) ∈ next.references := by rw [references,freshBefore]; exact List.mem_cons_self
  have ptrMember : pointer ∈ next.pointers.registers := by rw [pointers,preparedEq]; exact List.mem_cons_self
  have registeredFresh : NativeByteBorrow.lookup next.leases world.nextTag =
      some ⟨world.nextTag,some lease.tag,pointer,⟨1,1⟩,.exclusive⟩ := available.2.1
  refine ⟨pointer,next,indexed,?_⟩
  simp only [NativeByteSliceIndex.rawByte,Option.bind_eq_bind',registeredFresh,Option.bind_some,List.getElem?_idxOf refMember,
    List.getElem?_idxOf ptrMember,and_self,ite_true]

theorem ready_restore (before after : State) (slice : Slice) (ready : Ready before slice)
    (reachable : NativeReferenceMachine.Reachable after) (preserved : NativeIncomingReference.Preserves before after)
    (heap : after.pointers.heap = before.pointers.heap) (leases : after.leases = before.leases) : Ready after slice := by
  obtain ⟨_,lease,registered,referenceResident,pointerResident,shape,frontier,bytes,loaded⟩ := ready
  refine ⟨reachable,lease,?_,preserved.references _ referenceResident,preserved.registers _ pointerResident,shape,?_,bytes,?_⟩
  · rw [leases]; exact registered
  · exact NativeBorrowFrontier.frontier_transport (NativeReferenceMachine.ledger before) (NativeReferenceMachine.ledger after) lease frontier leases
  · rw [heap]; exact loaded

/-- Each bounded iteration succeeds and restores the incoming lease list;
reachability discharges the real cleanup-completion obligation. -/
theorem iteration_complete (world : State) (slice : Slice) (ready : Ready world slice) (offset : Word)
    (bounded : offset.val < slice.length.val) :
    ∃ pointer next, NativeByteDropTraversal.iteration world slice offset = .value pointer next ∧
      Ready next slice ∧ next.leases = world.leases := by
  obtain ⟨borrowed,issued,borrowedReady⟩ := issue_complete world slice ready
  obtain ⟨pointer,indexed,indexedRun,recovered⟩ := index_raw_complete borrowed ⟨⟨world.nextTag⟩,slice.length⟩ borrowedReady offset bounded
  have indexReachable : NativeReferenceMachine.Reachable indexed := by
    have checked := NativeByteSliceIndex.index_reachable borrowed borrowedReady.1 ⟨⟨world.nextTag⟩,slice.length⟩ offset
    simpa only [indexedRun,NativeByteSliceIndex.Result.world] using checked
  have issuedExtension := NativeScopeRestoration.issue world borrowed true _ _ .byte issued
  have indexedExtension : NativeScopeRestoration.Extends borrowed indexed := by
    simpa only [indexedRun,NativeByteSliceIndex.Result.world] using NativeScopeRestoration.index borrowed ⟨⟨world.nextTag⟩,slice.length⟩ offset
  have restored := NativeScopeRestoration.closeScope_reachable_restores world indexed (issuedExtension.trans indexedExtension)
    (NativeReferenceMachine.reachable_wellFormed world ready.1).2.1 indexReachable
  have computed : NativeByteDropTraversal.iteration world slice offset =
      .value pointer (NativeReferenceCleanup.closeScope world indexed).world := by
    simp only [NativeByteDropTraversal.iteration,issued,indexedRun,recovered,restored.1,List.isEmpty_nil,ite_true]
  have heap : (NativeReferenceCleanup.closeScope world indexed).world.pointers.heap = world.pointers.heap := by
    simpa only [computed,NativeByteDropTraversal.Iteration.world] using NativeByteDropTraversal.iteration_heap_frame world slice offset
  have preserved : NativeIncomingReference.Preserves world (NativeReferenceCleanup.closeScope world indexed).world := by
    simpa only [computed,NativeByteDropTraversal.Iteration.world] using NativeIncomingReference.iteration world slice offset
  refine ⟨pointer,_,computed,?_,restored.2⟩
  exact ready_restore world _ slice ready (NativeReferenceCleanup.closeScope_reachable world indexed indexReachable)
    preserved heap restored.2

/-- Well-founded recursion runs to the original extent; each iteration restores
the same incoming loans, so the sufficient slice conditions remain available. -/
theorem runFrom_complete (slice : Slice) (cursor : Nat) (bounded : cursor ≤ slice.length.val)
    (world : State) (last : Option Pointer) (ready : Ready world slice) :
    (NativeByteDropTraversal.runFrom slice cursor bounded world last).complete = true ∧
      Ready (NativeByteDropTraversal.runFrom slice cursor bounded world last).world slice ∧
      (NativeByteDropTraversal.runFrom slice cursor bounded world last).world.leases = world.leases ∧
      (NativeByteDropTraversal.runFrom slice cursor bounded world last).cursor = slice.length.val := by
  rw [NativeByteDropTraversal.runFrom]
  split
  · rename_i before
    obtain ⟨pointer,next,actual,nextReady,leases⟩ := iteration_complete world slice ready ⟨cursor,Nat.lt_trans before slice.length.isLt⟩ before
    rw [actual]
    have later := runFrom_complete slice (cursor + 1) (by omega) next (some pointer) nextReady
    exact ⟨later.1,later.2.1,later.2.2.1.trans leases,later.2.2.2⟩
  · exact ⟨rfl,ready,rfl,by change cursor = slice.length.val; omega⟩
termination_by slice.length.val - cursor

theorem run_complete (world : State) (slice : Slice) (ready : Ready world slice) :
    (NativeByteDropTraversal.run world slice).complete = true ∧
      Ready (NativeByteDropTraversal.run world slice).world slice ∧
      (NativeByteDropTraversal.run world slice).world.leases = world.leases ∧
      (NativeByteDropTraversal.run world slice).cursor = slice.length.val :=
  runFrom_complete slice 0 (Nat.zero_le _) world none ready

end FormalProof4FHE.HasteBoots.NativeByteTraversalCompleteness
