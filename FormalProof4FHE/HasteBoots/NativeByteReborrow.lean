module
public import FormalProof4FHE.HasteBoots.NativeByteRangeUpdate
@[expose] public section

/-! Closed local byte replacement through a fresh child lease, followed by
its checked end. This is a model call boundary, not compiler instrumentation. -/
namespace FormalProof4FHE.HasteBoots.NativeByteReborrow
open NativeByteMemory (Byte)
open NativeByteBorrow
open NativeByteRange (loadRange pointerAt)

/-- An outer `none` rejects invalid access; an inner `none` is the source
out-of-bounds return. No callee callback can fabricate a value or skip release. -/
def replaceAt (state : State) (parent index : Nat) (value : Byte) : Option (Option Byte × State) :=
  (lookup state.leases parent).bind (fun lease =>
    if index < lease.layout.size then
      (pointerAt lease.pointer index).bind (fun pointer =>
        (borrow state (some parent) .exclusive pointer ⟨1, 1⟩).bind (fun (child, borrowed) =>
          (read borrowed child 0 1).bind (fun previous =>
            match previous with
            | [old] => (write borrowed child 0 value).bind (fun written =>
                (endBorrow written child).map (fun next => (some old, next)))
            | _ => none)))
    else some (none, state))

theorem outside (state : State) (parent index : Nat) (lease : Lease)
    (found : lookup state.leases parent = some lease) (bound : ¬ index < lease.layout.size) (value : Byte) :
    replaceAt state parent index value = some (none, state) := by
  simp only [replaceAt, found, Option.bind, ite_eq_right bound]

theorem missing (state : State) (parent index : Nat) (absent : lookup state.leases parent = none) (value : Byte) :
    replaceAt state parent index value = none := by
  simp only [replaceAt, absent, Option.bind]

theorem success (state : State) (parent index : Nat) (value old : Byte) (next : State)
    (executed : replaceAt state parent index value = some (some old, next)) :
    ∃ lease pointer child borrowed written,
      lookup state.leases parent = some lease ∧ index < lease.layout.size ∧
      pointerAt lease.pointer index = some pointer ∧
      borrow state (some parent) .exclusive pointer ⟨1, 1⟩ = some (child, borrowed) ∧
      read borrowed child 0 1 = some [old] ∧ write borrowed child 0 value = some written ∧
      endBorrow written child = some next := by
  unfold replaceAt at executed
  cases found : lookup state.leases parent with
  | none => simp only [found, Option.bind] at executed; cases executed
  | some lease =>
    simp only [found, Option.bind] at executed
    split at executed
    next inside =>
      cases advanced : pointerAt lease.pointer index with
      | none => simp only [advanced] at executed; cases executed
      | some pointer =>
        simp only [advanced] at executed
        cases issued : borrow state (some parent) .exclusive pointer ⟨1, 1⟩ with
        | none => simp only [issued] at executed; cases executed
        | some result =>
          obtain ⟨child, borrowed⟩ := result
          simp only [issued] at executed
          cases loaded : read borrowed child 0 1 with
          | none => simp only [loaded] at executed; cases executed
          | some previous =>
            simp only [loaded] at executed
            split at executed
            next previousOld =>
              cases stored : write borrowed child 0 value with
              | none => simp only [stored] at executed; cases executed
              | some written =>
                simp only [stored] at executed
                cases ended : endBorrow written child with
                | none => simp only [ended, Option.map_none] at executed; cases executed
                | some finalState =>
                  simp only [ended, Option.map_some] at executed
                  cases executed
                  exact ⟨lease, pointer, child, borrowed, written, rfl, inside, advanced, issued, loaded, stored, ended⟩
            next => cases executed
    next => cases executed

theorem success_wellFormed (state : State) (valid : WellFormed state) (parent index : Nat)
    (value old : Byte) (next : State) (executed : replaceAt state parent index value = some (some old, next)) :
    WellFormed next := by
  obtain ⟨_, pointer, child, borrowed, written, _, _, _, issued, _, stored, ended⟩ := success state parent index value old next executed
  exact endBorrow_wellFormed written
    (write_wellFormed borrowed (borrow_wellFormed state valid (some parent) .exclusive pointer ⟨1, 1⟩ child borrowed issued)
      child 0 value written stored) child next ended

theorem scope_restored (state : State) (valid : LedgerValid state) (parent index : Nat)
    (value old : Byte) (next : State) (executed : replaceAt state parent index value = some (some old, next)) :
    next.leases = state.leases ∧ next.nextTag = state.nextTag + 1 ∧ lookup next.leases state.nextTag = none := by
  obtain ⟨_, pointer, child, borrowed, written, _, _, _, issued, _, stored, ended⟩ := success state parent index value old next executed
  obtain ⟨fresh, _, counter, leases, _, _⟩ := borrow_success state (some parent) .exclusive pointer ⟨1, 1⟩ child borrowed issued
  obtain ⟨_, _, _, _, _, _, _, _, writeCounter, writeLeases⟩ := write_success borrowed child 0 value written stored
  obtain ⟨_, endCounter, endLeases, revoked, _⟩ := endBorrow_success written child next ended
  have filtered : state.leases.filter (fun lease => decide (lease.tag ≠ child)) = state.leases := by
    apply List.filter_eq_self.mpr
    intro lease member
    exact decide_eq_true (by have before := (valid.1 lease member).1; omega)
  have restored : next.leases = state.leases := by
    rw [endLeases, writeLeases, leases]
    simpa only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false] using filtered
  exact ⟨restored, endCounter.trans (writeCounter.trans counter), by simpa only [fresh] using revoked⟩

theorem success_memory (state : State) (valid : NativeByteMemory.WellFormed state.memory)
    (parent index : Nat) (lease : Lease) (found : lookup state.leases parent = some lease)
    (bytes : List Byte) (view : loadRange state.memory lease.pointer lease.layout = some bytes)
    (value old : Byte) (next : State) (executed : replaceAt state parent index value = some (some old, next)) :
    bytes[index]? = some old ∧ loadRange next.memory lease.pointer lease.layout = some (bytes.set index value) := by
  obtain ⟨actual, pointer, child, borrowed, written, actualFound, inside, advanced, issued, readOld, stored, ended⟩ :=
    success state parent index value old next executed
  have same : actual = lease := Option.some.inj (actualFound.symm.trans found)
  subst actual
  obtain ⟨_, memory, _, leases, _, _⟩ := borrow_success state (some parent) .exclusive pointer ⟨1, 1⟩ child borrowed issued
  let childLease : Lease := ⟨child, some parent, pointer, ⟨1, 1⟩, .exclusive⟩
  have childFound : lookup borrowed.leases child = some childLease := by
    rw [leases]
    simp only [lookup, ite_true]
    rfl
  obtain ⟨readLease, readPointer, readFound, _, readAdvanced, _, loaded⟩ := read_success borrowed child 0 1 [old] readOld
  have sameReadLease : readLease = childLease := Option.some.inj (readFound.symm.trans childFound)
  subst readLease
  change pointerAt pointer 0 = some readPointer at readAdvanced
  rw [NativeByteRangeUpdate.pointerAt_zero] at readAdvanced
  have sameReadPointer : pointer = readPointer := Option.some.inj readAdvanced
  subst readPointer
  rw [memory] at loaded
  obtain ⟨bytePointer, byteAdvanced, byteLoaded⟩ := NativeByteRange.range_agrees_with_byte_load state.memory valid
    pointer ⟨1, 1⟩ [old] loaded 0 (by decide) old rfl
  rw [NativeByteRangeUpdate.pointerAt_zero] at byteAdvanced
  have sameBytePointer : pointer = bytePointer := Option.some.inj byteAdvanced
  subst bytePointer
  have length := NativeByteRange.loadRange_length state.memory lease.pointer lease.layout bytes view
  have bound : index < bytes.length := by omega
  have selected := List.getElem?_eq_getElem bound
  obtain ⟨snapshotPointer, snapshotAdvanced, snapshotLoaded⟩ := NativeByteRange.range_agrees_with_byte_load state.memory valid
    lease.pointer lease.layout bytes view index inside bytes[index] selected
  have sameSnapshotPointer : snapshotPointer = pointer := Option.some.inj (snapshotAdvanced.symm.trans advanced)
  subst snapshotPointer
  have oldValue := Option.some.inj (snapshotLoaded.symm.trans byteLoaded)
  refine ⟨selected.trans (congrArg some oldValue), ?_⟩
  obtain ⟨writeLease, writePointer, writeFound, _, _, writeAdvanced, _, byteStored, _, _⟩ := write_success borrowed child 0 value written stored
  have sameWriteLease : writeLease = childLease := Option.some.inj (writeFound.symm.trans childFound)
  subst writeLease
  change pointerAt pointer 0 = some writePointer at writeAdvanced
  rw [NativeByteRangeUpdate.pointerAt_zero] at writeAdvanced
  have sameWritePointer : pointer = writePointer := Option.some.inj writeAdvanced
  subst writePointer
  rw [memory] at byteStored
  rw [(endBorrow_success written child next ended).1]
  exact NativeByteRangeUpdate.storeByte_range state.memory written.memory valid lease.pointer lease.layout bytes view
    index inside pointer advanced value byteStored

theorem ancestor_fresh_prefix (state : State) (valid : LedgerValid state) (freshLease : Lease)
    (fresh : freshLease.tag = state.nextTag) (fuel older child : Nat) (before : child < state.nextTag) :
    ancestor (freshLease :: state.leases) fuel older child = ancestor state.leases fuel older child := by
  induction fuel generalizing child with
  | zero => rfl
  | succ fuel ih =>
    have different : freshLease.tag ≠ child := by omega
    simp only [ancestor, lookup, ite_eq_right different]
    cases found : lookup state.leases child with
    | none => rfl
    | some lease =>
      cases parental : lease.parent with
      | none => simp only [parental]
      | some parent =>
        simp only [parental]
        obtain ⟨member, same⟩ := lookup_selected state.leases child lease found
        have info := (valid.1 lease member).2.2
        rw [parental] at info
        have parentBefore : parent < state.nextTag := by have lt := info.1; omega
        exact congrArg (fun rest => decide (older = parent) || rest) (ih parent parentBefore)

theorem issued_exclusive_access (state : State) (valid : LedgerValid state) (parent : Nat)
    (pointer : NativePointerStorage.Pointer) (layout : NativeByteMemory.Layout) (child : Nat) (borrowed : State)
    (issued : borrow state (some parent) .exclusive pointer layout = some (child, borrowed)) :
    throughAllowed borrowed child .exclusive pointer layout = true := by
  obtain ⟨fresh, _, counter, leases, allowed, _⟩ := borrow_success state (some parent) .exclusive pointer layout child borrowed issued
  obtain ⟨_, _, parentBefore, _, _, _, _, oldAllowed⟩ := parent_checked state parent .exclusive pointer layout allowed
  apply List.all_eq_true.mpr
  intro lease member
  rw [leases] at member
  rcases List.mem_cons.mp member with same | old
  · subst lease
    simp only [decide_true, Bool.true_or]
  · have permitted := through_selected state parent .exclusive pointer layout oldAllowed lease old
    have lifted : ancestor borrowed.leases borrowed.nextTag lease.tag child =
        (decide (lease.tag = parent) || ancestor state.leases state.nextTag lease.tag parent) := by
      rw [leases, counter]
      simp only [ancestor, lookup, ite_true]
      rw [ancestor_fresh_prefix state valid _ fresh state.nextTag lease.tag parent parentBefore]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    rcases permitted with same | ancestral | compatible
    · exact Or.inl (Or.inr (by rw [lifted]; simp only [same, decide_true, Bool.true_or]))
    · exact Or.inl (Or.inr (by rw [lifted, ancestral, Bool.or_true]))
    · exact Or.inr compatible

theorem exclusive_allows_shared (state : State) (tag : Nat) (pointer : NativePointerStorage.Pointer)
    (layout : NativeByteMemory.Layout) (allowed : throughAllowed state tag .exclusive pointer layout = true) :
    throughAllowed state tag .shared pointer layout = true := by
  apply List.all_eq_true.mpr
  intro lease member
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  rcases through_selected state tag .exclusive pointer layout allowed lease member with same | older | compatible
  · exact Or.inl (Or.inl same)
  · exact Or.inl (Or.inr older)
  · have separated : ¬ Overlap pointer layout lease.pointer lease.layout := by
      rcases compatible with impossible | separate
      · cases impossible.1
      · exact separate
    exact Or.inr (Or.inr separated)

theorem issued_end_after_write (state : State) (valid : WellFormed state) (parent : Nat)
    (pointer : NativePointerStorage.Pointer) (child : Nat) (borrowed written : State)
    (issued : borrow state (some parent) .exclusive pointer ⟨1, 1⟩ = some (child, borrowed))
    (value : Byte) (stored : write borrowed child 0 value = some written) :
    ∃ next, endBorrow written child = some next := by
  obtain ⟨fresh, _, _, leases, allowed, _⟩ := borrow_success state (some parent) .exclusive pointer ⟨1, 1⟩ child borrowed issued
  obtain ⟨_, _, parentBefore, _⟩ := parent_checked state parent .exclusive pointer ⟨1, 1⟩ allowed
  obtain ⟨_, _, _, _, _, _, _, _, _, writeLeases⟩ := write_success borrowed child 0 value written stored
  have childFound : (lookup written.leases child).isSome = true := by
    rw [writeLeases, leases]
    simp only [lookup, ite_true, Option.isSome_some]
  have noChildren : written.leases.all (fun lease => decide (lease.parent ≠ some child)) = true := by
    apply List.all_eq_true.mpr
    intro lease member
    rw [writeLeases, leases] at member
    apply decide_eq_true
    rcases List.mem_cons.mp member with same | old
    · subst lease
      change some parent ≠ some child
      intro equal
      have ids := Option.some.inj equal
      omega
    · have info := valid.2.1 lease old
      cases parental : lease.parent with
      | none => intro equal; cases equal
      | some older =>
        rw [parental] at info
        intro equal
        have ids := Option.some.inj equal
        have previous := info.2.2.1
        have before := info.1
        omega
  refine ⟨{written with leases := written.leases.filter (fun lease => decide (lease.tag ≠ child))}, ?_⟩
  simp only [endBorrow, childFound, noChildren, Bool.true_and, ite_true]

theorem issued_executes (state : State) (valid : WellFormed state) (parent index : Nat) (lease : Lease)
    (found : lookup state.leases parent = some lease) (inside : index < lease.layout.size)
    (pointer : NativePointerStorage.Pointer) (advanced : pointerAt lease.pointer index = some pointer)
    (child : Nat) (borrowed : State)
    (issued : borrow state (some parent) .exclusive pointer ⟨1, 1⟩ = some (child, borrowed)) (value : Byte) :
    ∃ old next, replaceAt state parent index value = some (some old, next) := by
  have borrowedValid := borrow_wellFormed state valid (some parent) .exclusive pointer ⟨1, 1⟩ child borrowed issued
  obtain ⟨_, memory, _, leases, _, bytes, loaded⟩ := borrow_success state (some parent) .exclusive pointer ⟨1, 1⟩ child borrowed issued
  have length := NativeByteRange.loadRange_length state.memory pointer ⟨1, 1⟩ bytes loaded
  have singleton : ∃ old, bytes = [old] := by
    cases bytes with
    | nil => cases length
    | cons old tail =>
      cases tail with
      | nil => exact ⟨old, rfl⟩
      | cons head tail => simp only [List.length_cons] at length; omega
  obtain ⟨old, singleton⟩ := singleton
  subst bytes
  have childFound : lookup borrowed.leases child = some ⟨child, some parent, pointer, ⟨1, 1⟩, .exclusive⟩ := by
    rw [leases]
    simp only [lookup, ite_true]
  have exclusiveAllowed := issued_exclusive_access state valid.2 parent pointer ⟨1, 1⟩ child borrowed issued
  have sharedAllowed := exclusive_allows_shared borrowed child pointer ⟨1, 1⟩ exclusiveAllowed
  have view : loadRange borrowed.memory pointer ⟨1, 1⟩ = some [old] := by rw [memory]; exact loaded
  have childRead : read borrowed child 0 1 = some [old] := by
    simp only [NativeByteBorrow.read, childFound, Option.bind, NativeByteRangeUpdate.pointerAt_zero,
      ite_eq_left sharedAllowed]
    exact view
  obtain ⟨written, stored⟩ := NativeByteRangeUpdate.borrowed_write_of_allowed borrowed borrowedValid.1 child 0
    ⟨child, some parent, pointer, ⟨1, 1⟩, .exclusive⟩ childFound rfl [old] view (by change 0 < 1; decide) pointer
    (NativeByteRangeUpdate.pointerAt_zero pointer) exclusiveAllowed value
  obtain ⟨next, ended⟩ := issued_end_after_write state valid parent pointer child borrowed written issued value stored
  refine ⟨old, next, ?_⟩
  simp only [replaceAt, found, Option.bind, ite_eq_left inside, advanced, issued, childRead, stored, ended, Option.map_some]

theorem success_steps (state : State) (parent index : Nat) (value old : Byte) (next : State)
    (executed : replaceAt state parent index value = some (some old, next)) : Runs state next := by
  obtain ⟨_, pointer, child, borrowed, written, _, _, _, issued, _, stored, ended⟩ := success state parent index value old next executed
  exact Runs.step (Runs.step (Runs.step Runs.refl
    (Step.borrow state (some parent) .exclusive pointer ⟨1, 1⟩ child borrowed issued))
    (Step.write borrowed child 0 value written stored)) (Step.endBorrow written child next ended)

theorem local_tag_never_returns (state : State) (valid : LedgerValid state) (parent index : Nat)
    (value old : Byte) (next future : State)
    (executed : replaceAt state parent index value = some (some old, next)) (continuation : Runs next future) :
    lookup future.leases state.nextTag = none := by
  obtain ⟨_, counter, revoked⟩ := scope_restored state valid parent index value old next executed
  exact (runs_keep_revoked continuation state.nextTag (by omega) revoked).2

end FormalProof4FHE.HasteBoots.NativeByteReborrow
