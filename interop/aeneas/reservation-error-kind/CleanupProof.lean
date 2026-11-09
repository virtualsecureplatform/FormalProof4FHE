namespace HasteBootsReservationErrorKind
open FormalProof4FHE.HasteBoots
open NativeReferenceMachine (State Reference)
open NativeReservationErrorFields (Kind)

theorem old_no_children (world : State) (valid : NativeReferenceMachine.WellFormed world) :
    world.leases.all (fun lease => decide (lease.parent ≠ some world.nextTag)) = true := by
  apply List.all_eq_true.mpr
  intro lease member
  have shape := valid.2.1.1 lease member
  have older : lease.tag < world.nextTag := shape.1
  cases parentEq : lease.parent with
  | none => simp
  | some parent =>
    have parental := shape.2.2
    rw [parentEq] at parental
    have before : parent < lease.tag := parental.1
    have different : parent ≠ world.nextTag := by omega
    simp [different]

theorem close_single_fresh (world final : State) (parent : Reference) (pointer : NativePointerStorage.Pointer)
    (valid : NativeReferenceMachine.WellFormed world) (parentOlder : parent.tag < world.nextTag)
    (same : authority (borrowedWorld world parent pointer) final) :
    NativeReferenceCleanup.closeScope world final = ⟨{final with leases := world.leases},[world.nextTag],[]⟩ := by
  have leases : final.leases = ⟨world.nextTag,some parent.tag,pointer,⟨16,8⟩,.shared⟩ :: world.leases := same.2.1
  have references : final.references = ⟨world.nextTag⟩ :: world.references := same.2.2.1
  have filtered : world.leases.filter (fun lease => decide (world.nextTag ≤ lease.tag)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro lease member
    have older : lease.tag < world.nextTag := (valid.2.1.1 lease member).1
    simp only [decide_eq_true_eq]
    omega
  have scope : NativeReferenceCleanup.scopeTags world final = [world.nextTag] := by
    simp [NativeReferenceCleanup.scopeTags,leases,filtered]
  have different : parent.tag ≠ world.nextTag := by omega
  have noChildren : ∀ lease ∈ world.leases, lease.parent ≠ some world.nextTag := by
    intro lease member
    exact of_decide_eq_true (List.all_eq_true.mp (old_no_children world valid) lease member)
  have noTag : ∀ lease ∈ world.leases, lease.tag ≠ world.nextTag := by
    intro lease member
    have older : lease.tag < world.nextTag := (valid.2.1.1 lease member).1
    omega
  have ended : NativeReferenceCleanup.endTag final world.nextTag = some {final with leases := world.leases} := by
    simp [NativeReferenceCleanup.endTag,references,NativeReferenceMachine.execute,NativeByteBorrow.endBorrow,
      NativeReferenceMachine.ledger,leases,NativeByteBorrow.lookup,different]
    exact ⟨noChildren,noTag⟩
  simp only [NativeReferenceCleanup.closeScope,scope,NativeReferenceCleanup.release,ended]

theorem close_returned_single (world final : State) (parent : Reference) (pointer : NativePointerStorage.Pointer)
    (value : NativeRecordValues.Value) (valid : NativeReferenceMachine.WellFormed world)
    (parentOlder : parent.tag < world.nextTag) (same : authority (borrowedWorld world parent pointer) final) :
    closeReturned world (.returned value final) = .returned value {final with leases := world.leases} := by
  simp only [closeReturned,close_single_fresh world final parent pointer valid parentOlder same,ite_true]

theorem root_ready_closed_complete (world : State) (index : Nat) (kind : Kind) (ready : Ready world index kind)
    (valid : NativeReferenceMachine.WellFormed world) (kindValid : NativeReservationErrorLocal.Valid kind) :
    ∃ final, rootWithCleanup world (.scalar (.reference false ready.descriptor.reference 2)) =
      .returned (NativeReservationErrorLocal.kindValue tags kind) final ∧ final.leases = world.leases := by
  obtain ⟨final,returned,same⟩ := root_ready_complete world index kind ready valid kindValid
  obtain ⟨member,tagEq⟩ := NativeByteBorrow.lookup_selected world.leases ready.descriptor.reference.tag ready.descriptor.lease ready.descriptor.registered
  have older : ready.descriptor.reference.tag < world.nextTag := by
    have age := (valid.2.1.1 ready.descriptor.lease member).1
    change ready.descriptor.lease.tag < world.nextTag at age
    rw [tagEq] at age
    exact age
  refine ⟨{final with leases := world.leases},?_,rfl⟩
  rw [rootWithCleanup,returned,close_returned_single world final ready.descriptor.reference ready.descriptor.lease.pointer _ valid older same]

theorem root_snapshot_complete (world next : State) (base : NativePointerStorage.Address)
    (value result : NativeRecordValues.Value) (valid : NativeReferenceMachine.WellFormed world)
    (executed : NativeReservationErrorLocal.snapshotValue tags world base value = .value result next) :
    ∃ kind final, value = NativeReservationErrorLocal.encode tags kind ∧
      rootWithCleanup next result = .returned (NativeReservationErrorLocal.kindValue tags kind) final ∧ final.leases = next.leases := by
  obtain ⟨kind,same,kindValid,ready,resultEq⟩ := snapshot_ready world next base value result valid executed
  have nextValid := NativeStorageBorrowMachine.runs_wellFormed world next valid
    (by simpa only [executed,NativeRawVecFields.Result.world] using NativeReservationErrorLocal.snapshotValue_projects tags world base value)
  obtain ⟨final,returned,leases⟩ := root_ready_closed_complete next 0 kind ready nextValid kindValid
  exact ⟨kind,final,same,by rw [resultEq]; exact returned,leases⟩

end HasteBootsReservationErrorKind
