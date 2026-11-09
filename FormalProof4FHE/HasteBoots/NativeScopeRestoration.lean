module
public import FormalProof4FHE.HasteBoots.NativeBorrowFrontier
public import FormalProof4FHE.HasteBoots.NativeIncomingReference
@[expose] public section

/-! Fresh-loan prefixes and exact restoration by completed scope cleanup.
These statements track the actual loan list and retain its order. They do not
assert a native Rust lifetime correspondence. -/
namespace FormalProof4FHE.HasteBoots.NativeScopeRestoration
open NativeReferenceMachine (State Op)
open NativeByteBorrow (Lease)
open NativePointerStorage (Pointer)

structure Extends (before after : State) : Prop where
  counter : before.nextTag ≤ after.nextTag
  leases : ∃ newer, after.leases = newer ++ before.leases ∧ ∀ lease ∈ newer, before.nextTag ≤ lease.tag

theorem Extends.refl (world : State) : Extends world world := ⟨Nat.le_refl _,[],rfl,by simp⟩

theorem Extends.trans {before middle after : State} (first : Extends before middle) (second : Extends middle after) :
    Extends before after := by
  obtain ⟨left,leftEq,leftAge⟩ := first.leases
  obtain ⟨right,rightEq,rightAge⟩ := second.leases
  refine ⟨Nat.le_trans first.counter second.counter,right ++ left,?_,?_⟩
  · rw [rightEq,leftEq,List.append_assoc]
  · intro lease member
    rcases List.mem_append.mp member with newer | older
    · exact Nat.le_trans first.counter (rightAge lease newer)
    · exact leftAge lease older

theorem stable (before after : State) (same : NativeReferenceMachine.SameAuthority before after) : Extends before after := by
  exact ⟨same.1.ge,[],by simpa only [List.nil_append] using same.2.1,by simp⟩

theorem grant (before after : State) (parent : Option Nat) (mode : NativeByteBorrow.Mode)
    (pointer : Pointer) (layout : NativeByteMemory.Layout)
    (granted : NativeReferenceMachine.grant before parent mode pointer layout = some after) : Extends before after := by
  obtain ⟨tag,ledger,borrowed,_,counter,leases,_,_⟩ := NativeReferenceMachine.grant_success before after parent mode pointer layout granted
  obtain ⟨fresh,_,raised,leaseEq,_⟩ := NativeByteBorrow.borrow_success (NativeReferenceMachine.ledger before)
    parent mode pointer layout tag ledger borrowed
  refine ⟨?_,[⟨tag,parent,pointer,layout,mode⟩],?_,?_⟩
  · rw [counter,raised]; exact Nat.le_succ _
  · simpa only [List.singleton_append,NativeReferenceMachine.ledger] using leases.trans leaseEq
  · intro lease member
    have same := List.mem_singleton.mp member
    subst lease
    exact fresh.ge

theorem step (before after : State) (op : Op) (executed : NativeReferenceMachine.execute before op = some after)
    (checked : NativeIncomingReference.keepsLoans op = true := by rfl) : Extends before after := by
  cases op with
  | raw op =>
    apply stable before after
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
  | endBorrow reference => cases checked

theorem issue (before after : State) (mutable : Bool) (input output : NativeSliceLLBC.Value) (element : NativeSliceLLBC.Element)
    (issued : NativeSliceLLBC.issue before mutable input element = some (output,after)) : Extends before after := by
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
    Extends world (NativeByteSliceIndex.index world slice offset).world := by
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


theorem ends_filter (world next : State) (tags : List Nat) (ended : NativeReferenceCleanup.Ends world tags next) :
    next.leases = world.leases.filter (fun lease => decide (lease.tag ∉ tags)) := by
  induction ended with
  | nil world => simp only [List.not_mem_nil,not_false_eq_true,decide_true,List.filter_true]
  | cons actual later ih =>
    rw [ih,NativeReferenceCleanup.endTag_leases _ _ _ actual,List.filter_filter]
    apply List.filter_congr
    intro lease _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true,decide_eq_true_eq,List.mem_cons,not_or,ne_eq]
    tauto

theorem closeScope_filter (entered current : State)
    (complete : (NativeReferenceCleanup.closeScope entered current).pending = []) :
    (NativeReferenceCleanup.closeScope entered current).world.leases =
      current.leases.filter (fun lease => decide (lease.tag < entered.nextTag)) := by
  have partition := NativeReferenceCleanup.release_partition current (NativeReferenceCleanup.scopeTags entered current)
  change (NativeReferenceCleanup.release current (NativeReferenceCleanup.scopeTags entered current)).pending = [] at complete
  rw [complete,List.append_nil] at partition
  rw [NativeReferenceCleanup.closeScope,ends_filter _ _ _ (NativeReferenceCleanup.release_ends _ _),← partition]
  apply List.filter_congr
  intro lease member
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro absent
    by_contra notOlder
    apply absent
    exact List.mem_map.mpr ⟨lease,List.mem_filter.mpr ⟨member,by simpa using Nat.le_of_not_gt notOlder⟩,rfl⟩
  · intro older present
    obtain ⟨other,selected,same⟩ := List.mem_map.mp present
    have bound := of_decide_eq_true (List.mem_filter.mp selected).2
    omega

theorem closeScope_restores (entered current : State) (extended : Extends entered current)
    (valid : NativeByteBorrow.LedgerValid (NativeReferenceMachine.ledger entered))
    (complete : (NativeReferenceCleanup.closeScope entered current).pending = []) :
    (NativeReferenceCleanup.closeScope entered current).world.leases = entered.leases := by
  obtain ⟨newer,same,newAge⟩ := extended.leases
  rw [closeScope_filter entered current complete,same,List.filter_append]
  have newGone : newer.filter (fun lease => decide (lease.tag < entered.nextTag)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro lease member
    have age := newAge lease member
    simpa only [decide_eq_true_eq] using (show ¬ lease.tag < entered.nextTag by omega)
  have oldKept : entered.leases.filter (fun lease => decide (lease.tag < entered.nextTag)) = entered.leases := by
    apply List.filter_eq_self.mpr
    intro lease member
    exact decide_eq_true (valid.1 lease member).1
  rw [newGone,oldKept,List.nil_append]

theorem closeScope_reachable_restores (entered current : State) (extended : Extends entered current)
    (valid : NativeByteBorrow.LedgerValid (NativeReferenceMachine.ledger entered))
    (reachable : NativeReferenceMachine.Reachable current) :
    (NativeReferenceCleanup.closeScope entered current).pending = [] ∧
      (NativeReferenceCleanup.closeScope entered current).world.leases = entered.leases := by
  have complete := NativeReferenceCleanup.closeScope_reachable_complete entered current reachable
  exact ⟨complete,closeScope_restores entered current extended valid complete⟩
end FormalProof4FHE.HasteBoots.NativeScopeRestoration
