module
public import FormalProof4FHE.HasteBoots.NativeRawVecFields
public import FormalProof4FHE.HasteBoots.NativeZstReference
@[expose] public section

/-! Zero-sized local placement and actual shared loan issuance. The placement
address is explicit; native stack placement and lifetime correspondence are open. -/
namespace FormalProof4FHE.HasteBoots.NativeZstBorrow
open NativeReferenceMachine (State)
open NativeRawVecFields (Result)
open NativeWord64Memory (Word)

def placed (world : State) (address : Word) : State :=
  {world with pointers := NativePointerMachine.push world.pointers ⟨address,none⟩}

def granted (world : State) (address : Word) : State :=
  {placed world address with
    nextTag := world.nextTag + 1
    leases := ⟨world.nextTag,none,⟨address,none⟩,⟨0,1⟩,.shared⟩ :: world.leases
    references := ⟨world.nextTag⟩ :: world.references
    births := ⟨world.nextTag,none,⟨address,none⟩,⟨0,1⟩,.shared⟩ :: world.births}

def issue (world : State) (address : Word) : Result NativeSliceLLBC.Value :=
  match NativeReferenceMachine.execute world (.raw (.fromAddress address)) with
  | none => .invalid world
  | some prepared => match NativeReferenceMachine.execute prepared (.borrow 0 .shared ⟨0,1⟩) with
    | none => .invalid prepared
    | some next => .value (.reference false ⟨prepared.nextTag⟩ 0) next

theorem placement_step (world : State) (address : Word) :
    NativeReferenceMachine.execute world (.raw (.fromAddress address)) = some (placed world address) := by
  simp [NativeReferenceMachine.execute,NativeReferenceMachine.rawPermissions,NativePointerMachine.execute,
    NativeReferenceMachine.setPointers,placed]

theorem empty_permission (world : State) (address : Word) :
    NativeByteBorrow.parentAllowed (NativeReferenceMachine.ledger world) none .shared ⟨address,none⟩ ⟨0,1⟩ = true := by
  simp [NativeByteBorrow.parentAllowed,NativeByteBorrow.rawAllowed,NativeByteBorrow.Compatible,NativeByteBorrow.Overlap]

theorem empty_geometry (address : Word) (nonzero : address.val ≠ 0) :
    NativeByteRange.Geometry ⟨address,none⟩ ⟨0,1⟩ := by
  refine ⟨?_,nonzero,?_,?_⟩
  · decide
  · exact Nat.mod_one _
  · simpa only [Nat.add_zero] using address.isLt

theorem grant_step (world : State) (address : Word) (nonzero : address.val ≠ 0) :
    NativeReferenceMachine.execute (placed world address) (.borrow 0 .shared ⟨0,1⟩) = some (granted world address) := by
  have permission := empty_permission (placed world address) address
  have loaded := NativeByteRange.empty_range (NativeReferenceMachine.ledger (placed world address)).memory ⟨address,none⟩ 1 (empty_geometry address nonzero)
  change NativeReferenceMachine.grant (placed world address) none .shared ⟨address,none⟩ ⟨0,1⟩ = _
  unfold NativeReferenceMachine.grant
  rw [NativeByteBorrow.borrow,permission]
  simp only [ite_true,loaded,Option.map_some]
  rfl

theorem issue_complete (world : State) (address : Word) (nonzero : address.val ≠ 0) :
    issue world address = .value (.reference false ⟨world.nextTag⟩ 0) (granted world address) := by
  simp only [issue,placement_step]
  rw [grant_step world address nonzero]
  rfl

theorem issue_projects (world : State) (address : Word) :
    NativeReferenceMachine.Runs world (issue world address).world := by
  cases preparedEq : NativeReferenceMachine.execute world (.raw (.fromAddress address)) with
  | none => simp only [issue,preparedEq,Result.world]; exact .refl _
  | some prepared =>
    have first := NativeReferenceMachine.Runs.step (.refl world) _ preparedEq
    cases issued : NativeReferenceMachine.execute prepared (.borrow 0 .shared ⟨0,1⟩) with
    | none => simpa only [issue,preparedEq,issued,Result.world] using first
    | some next =>
      have later := NativeReferenceMachine.Runs.step (.refl prepared) _ issued
      simpa only [issue,preparedEq,issued,Result.world] using NativeReferenceMachine.runs_trans _ _ _ first later

theorem granted_heap (world : State) (address : Word) :
    (granted world address).pointers.heap = world.pointers.heap := rfl

theorem issue_null (world : State) : issue world 0 = .invalid (placed world 0) := by
  have refused : NativeReferenceMachine.execute (placed world 0) (.borrow 0 .shared ⟨0,1⟩) = none := by
    change NativeReferenceMachine.grant (placed world 0) none .shared ⟨0,none⟩ ⟨0,1⟩ = none
    have loaded := NativeByteRange.null_range (NativeReferenceMachine.ledger (placed world 0)).memory ⟨0,none⟩ rfl ⟨0,1⟩
    unfold NativeReferenceMachine.grant
    rw [NativeByteBorrow.borrow,empty_permission]
    simp only [ite_true,loaded,Option.map_none]
  simp only [issue,placement_step,refused]

theorem granted_decoded (world : State) (address : Word) :
    NativeZstReference.decode (granted world address) 0 = some (.reference false ⟨world.nextTag⟩ 0) := by
  simp [NativeZstReference.decode,granted,NativeByteBorrow.lookup]

theorem granted_reachable (world : State) (address : Word) (nonzero : address.val ≠ 0)
    (reachable : NativeReferenceMachine.Reachable world) : NativeReferenceMachine.Reachable (granted world address) :=
  .step (.step reachable _ (placement_step world address)) _ (grant_step world address nonzero)

theorem issue_heap (world : State) (address : Word) :
    (issue world address).world.pointers.heap = world.pointers.heap := by
  by_cases nonzero : address.val ≠ 0
  · rw [issue_complete world address nonzero]
    rfl
  · have zero : address = 0 := by apply Fin.ext; simpa using nonzero
    subst address
    rw [issue_null]
    rfl

end FormalProof4FHE.HasteBoots.NativeZstBorrow
