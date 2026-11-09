module
public import FormalProof4FHE.HasteBoots.NativeRecordLLBC
public import FormalProof4FHE.HasteBoots.NativeStorageBorrowMachine
public import FormalProof4FHE.HasteBoots.NativeByteRangeCompleteness
@[expose] public section

/-! Marshal a complete logical reservation-error local into checked modeled
storage and issue a shared two-word loan. This is a representation bridge;
native stack placement, local lifetime and typed-reference refinement remain
separate obligations. Failures retain all executed storage operations. -/
namespace FormalProof4FHE.HasteBoots.NativeReservationErrorLocal
open NativeRecordValues (Value)
open NativeReferenceMachine (State)
open NativePointerStorage (Address Pointer)
open NativeWord64Memory (Word)
open NativeRawVecFields (Result)
open NativeReservationErrorFields (Kind)
open NativeStorageBorrowMachine (Op)

structure Tags where
  error : Nat
  kind : Nat
  layout : Nat
  alignment : Nat
  alignmentEnum : Nat
  deriving DecidableEq

def layoutValue (tags : Tags) (size alignment : Word) : Value :=
  .record tags.layout (.pair (.scalar (.usize size))
    (.pair (.record tags.alignment (.pair (.enumeration tags.alignmentEnum alignment) (.scalar .unit))) (.scalar .unit)))

def kindValue (tags : Tags) : Kind → Value
  | .capacityOverflow => .record tags.kind (.choice false (.scalar .unit))
  | .allocationError size alignment => .record tags.kind (.choice true
      (.pair (layoutValue tags size alignment) (.pair (.scalar .unit) (.scalar .unit))))

def encode (tags : Tags) (kind : Kind) : Value := .record tags.error (.pair (kindValue tags kind) (.scalar .unit))

def Valid : Kind → Prop
  | .capacityOverflow => True
  | .allocationError size alignment => alignment ≠ 0 ∧ (NativeAllocatorExecution.request size alignment).Valid

instance (kind : Kind) : Decidable (Valid kind) := by cases kind <;> unfold Valid <;> infer_instance

def decode (tags : Tags) : Value → Option Kind
  | .record error (.pair (.record kind (.choice false (.scalar .unit))) (.scalar .unit)) =>
      if error = tags.error ∧ kind = tags.kind then some .capacityOverflow else none
  | .record error (.pair (.record kind (.choice true (.pair (.record layout (.pair (.scalar (.usize size)) (.pair (.record alignment (.pair (.enumeration alignmentEnum word) (.scalar .unit))) (.scalar .unit)))) (.pair (.scalar .unit) (.scalar .unit))))) (.scalar .unit)) =>
      if error = tags.error ∧ kind = tags.kind ∧ layout = tags.layout ∧ alignment = tags.alignment ∧
          alignmentEnum = tags.alignmentEnum ∧ Valid (.allocationError size word) then some (.allocationError size word) else none
  | _ => none

def bytes : Kind → List NativeByteMemory.Byte
  | .capacityOverflow => NativeWord64Memory.encode 0
  | .allocationError size alignment => NativeWord64Memory.encode alignment ++ NativeWord64Memory.encode size

def steps (base : Address) (kind : Kind) : List Op :=
  [.legacy (.raw (.allocate base ⟨16,8⟩)),.legacy (.raw (.writeBytes 0 8 (bytes kind))),
   .storageBorrow none 0 .shared ⟨16,8⟩]

def executeSteps : State → List Op → Result Unit
  | world, [] => .value () world
  | world, op :: tail => match NativeStorageBorrowMachine.execute world op with
    | none => .invalid world
    | some next => executeSteps next tail

def snapshotValue (tags : Tags) (world : State) (base : Address) (value : Value) : Result Value :=
  match decode tags value with
  | none => .invalid world
  | some kind => match executeSteps world (steps base kind) with
    | .invalid next => .invalid next
    | .value _ next => match NativeRawVecFields.select next 0 with
      | none => .invalid next
      | some reference => .value (.scalar (.reference false reference 2)) next

def snapshotLocal (tags : Tags) (frame : NativeRecordLLBC.Frame) (index : Nat) (base : Address) : Result Value :=
  match NativeRecordLLBC.read frame index [] with
  | none => .invalid frame.world
  | some value => snapshotValue tags frame.world base value

theorem decode_encode (tags : Tags) (kind : Kind) :
    decode tags (encode tags kind) = if Valid kind then some kind else none := by
  cases kind <;> simp [decode,encode,kindValue,layoutValue,Valid]

theorem decode_valid (tags : Tags) (value : Value) (kind : Kind) (decoded : decode tags value = some kind) : Valid kind := by
  unfold decode at decoded
  split at decoded
  next => split at decoded <;> cases decoded; trivial
  next =>
    split at decoded
    next checked => cases decoded; exact checked.2.2.2.2.2
    next => cases decoded
  next => cases decoded

theorem overflow_bytes_length : (bytes .capacityOverflow).length = 8 := NativeWord64Memory.encode_length 0

theorem allocation_bytes_length (size alignment : Word) : (bytes (.allocationError size alignment)).length = 16 := by
  simp [bytes,NativeWord64Memory.encode_length]

theorem executeSteps_projects (world : State) (ops : List Op) :
    NativeStorageBorrowMachine.Runs world (executeSteps world ops).world := by
  induction ops generalizing world with
  | nil => exact .refl _
  | cons op tail ih =>
    cases actual : NativeStorageBorrowMachine.execute world op with
    | none => simp only [executeSteps,actual,Result.world]; exact .refl _
    | some next =>
      simpa only [executeSteps,actual] using NativeStorageBorrowMachine.runs_trans world next _
        (.step (.refl world) op actual) (ih next)

theorem snapshotValue_projects (tags : Tags) (world : State) (base : Address) (value : Value) :
    NativeStorageBorrowMachine.Runs world (snapshotValue tags world base value).world := by
  cases decoded : decode tags value with
  | none => simp only [snapshotValue,decoded,Result.world]; exact .refl _
  | some kind =>
    have run := executeSteps_projects world (steps base kind)
    cases actual : executeSteps world (steps base kind) with
    | invalid next => simpa only [snapshotValue,decoded,actual,Result.world] using run
    | value resultUnit next =>
      cases selected : NativeRawVecFields.select next 0 <;>
        simpa only [snapshotValue,decoded,actual,selected,Result.world] using run

theorem snapshotLocal_projects (tags : Tags) (frame : NativeRecordLLBC.Frame) (index : Nat) (base : Address) :
    NativeStorageBorrowMachine.Runs frame.world (snapshotLocal tags frame index base).world := by
  cases selected : NativeRecordLLBC.read frame index [] with
  | none => simp only [snapshotLocal,selected,Result.world]; exact .refl _
  | some value => simpa only [snapshotLocal,selected] using snapshotValue_projects tags frame.world base value

theorem snapshotLocal_reachable (tags : Tags) (frame : NativeRecordLLBC.Frame) (index : Nat) (base : Address)
    (reachable : NativeStorageBorrowMachine.Reachable frame.world) :
    NativeStorageBorrowMachine.Reachable (snapshotLocal tags frame index base).world :=
  NativeStorageBorrowMachine.runs_trans _ _ _ reachable (snapshotLocal_projects tags frame index base)

theorem snapshotLocal_wellFormed (tags : Tags) (frame : NativeRecordLLBC.Frame) (index : Nat) (base : Address)
    (valid : NativeReferenceMachine.WellFormed frame.world) :
    NativeReferenceMachine.WellFormed (snapshotLocal tags frame index base).world :=
  NativeStorageBorrowMachine.runs_wellFormed _ _ valid (snapshotLocal_projects tags frame index base)

theorem missing_local (tags : Tags) (frame : NativeRecordLLBC.Frame) (index : Nat) (base : Address)
    (missing : NativeRecordLLBC.read frame index [] = none) : snapshotLocal tags frame index base = .invalid frame.world := by
  simp only [snapshotLocal,missing]

theorem local_selected (tags : Tags) (frame : NativeRecordLLBC.Frame) (index : Nat) (base : Address) (value : Value)
    (selected : NativeRecordLLBC.read frame index [] = some value) :
    snapshotLocal tags frame index base = snapshotValue tags frame.world base value := by
  simp only [snapshotLocal,selected]

theorem snapshotValue_success (tags : Tags) (world next : State) (base : Address) (value result : Value)
    (executed : snapshotValue tags world base value = .value result next) :
    ∃ kind reference, decode tags value = some kind ∧ executeSteps world (steps base kind) = .value () next ∧
      NativeRawVecFields.select next 0 = some reference ∧ result = .scalar (.reference false reference 2) := by
  cases decoded : decode tags value with
  | none => simp only [snapshotValue,decoded] at executed; cases executed
  | some kind =>
    cases actual : executeSteps world (steps base kind) with
    | invalid changed => simp only [snapshotValue,decoded,actual] at executed; cases executed
    | value resultUnit changed =>
      cases resultUnit
      cases selected : NativeRawVecFields.select changed 0 with
      | none => simp only [snapshotValue,decoded,actual,selected] at executed; cases executed
      | some reference =>
        simp only [snapshotValue,decoded,actual,selected] at executed
        cases executed
        exact ⟨kind,reference,rfl,actual,selected,rfl⟩

theorem subword (memory : NativeByteMemory.State) (valid : NativeByteMemory.WellFormed memory)
    (header : Pointer) (extent : Nat) (payload : List NativeByteMemory.Byte) (offset : Nat) (word : Word)
    (loaded : NativeByteRange.loadRange memory header ⟨extent,8⟩ = some payload)
    (bounded : offset + 8 ≤ extent) (aligned : offset % 8 = 0)
    (selected : (payload.drop offset).take 8 = NativeWord64Memory.encode word) :
    ∃ slot, NativeByteRange.pointerAt header offset = some slot ∧ NativeWord64Memory.load memory slot = some word := by
  have original := NativeByteRange.loadRange_geometry memory header ⟨extent,8⟩ _ loaded
  have byteGeometry : NativeByteRange.Geometry header ⟨extent,1⟩ :=
    ⟨⟨by change 1 ∈ (List.range 64).map (fun exponent => 2 ^ exponent); decide,by
      have maximum := original.1.2
      change extent + (8-1) ≤ 2^63-1 at maximum
      change extent + (1-1) ≤ 2^63-1
      omega⟩,original.2.1,by exact Nat.mod_one _,original.2.2.2⟩
  have byteRead : NativeByteRange.loadRange memory header ⟨extent,1⟩ = some payload := by
    simpa only [NativeByteRange.loadRange,original,byteGeometry,ite_true] using loaded
  obtain ⟨slot,shifted,read⟩ := NativeByteRangeCompleteness.loadRange_subrange memory valid header extent offset 8 _ byteRead bounded
  have address := (NativeByteRange.pointerAt_fields header offset slot shifted).1
  have subGeometry := NativeByteRange.loadRange_geometry memory slot ⟨8,1⟩ _ read
  have wordGeometry : NativeByteRange.Geometry slot ⟨8,8⟩ := by
    refine ⟨by decide,subGeometry.2.1,?_,subGeometry.2.2.2⟩
    change slot.address.val % 8 = 0
    rw [address,Nat.add_mod,original.2.2.1,aligned]
  have wordRead : NativeByteRange.loadRange memory slot ⟨8,8⟩ = some (NativeWord64Memory.encode word) := by
    rw [selected] at read
    simpa only [NativeByteRange.loadRange,wordGeometry,subGeometry,ite_true] using read
  exact ⟨slot,shifted,by simp only [NativeWord64Memory.load,wordRead,Option.bind_some,NativeWord64Memory.decode_encode]⟩

theorem decode_sound (tags : Tags) (value : Value) (kind : Kind) (decoded : decode tags value = some kind) :
    value = encode tags kind := by
  unfold decode at decoded
  split at decoded
  next =>
    split at decoded
    next checked => obtain ⟨rfl,rfl⟩ := checked; cases decoded; rfl
    next => cases decoded
  next =>
    split at decoded
    next checked => obtain ⟨rfl,rfl,rfl,rfl,rfl,_⟩ := checked; cases decoded; rfl
    next => cases decoded
  next => cases decoded

def Stored (memory : NativeByteMemory.State) (pointer : Pointer) : Kind → Prop
  | .capacityOverflow => NativeWord64Memory.load memory pointer = some 0
  | .allocationError size alignment => NativeWord64Memory.load memory pointer = some alignment ∧
      ∃ slot, NativeByteRange.pointerAt pointer 8 = some slot ∧ NativeWord64Memory.load memory slot = some size

theorem written_overflow (heap next : NativePointerByteMemory.State) (pointer : Pointer)
    (written : NativePointerByteMemory.writeBytes heap pointer 8 (bytes .capacityOverflow) = some next) :
    Stored next.memory pointer .capacityOverflow := by
  have stored := (NativePointerByteMemory.writeBytes_success heap next pointer 8 _ written).1
  have loaded := NativeByteRangeWrite.storeRange_then_load heap.memory pointer 8 _ next.memory stored
  rw [overflow_bytes_length] at loaded
  simp only [Stored,NativeWord64Memory.load,loaded,bytes,Option.bind_some,NativeWord64Memory.decode_encode]

theorem written_allocation (heap next : NativePointerByteMemory.State) (pointer : Pointer) (size alignment : Word)
    (valid : NativeByteMemory.WellFormed heap.memory)
    (written : NativePointerByteMemory.writeBytes heap pointer 8 (bytes (.allocationError size alignment)) = some next) :
    Stored next.memory pointer (.allocationError size alignment) := by
  have stored := (NativePointerByteMemory.writeBytes_success heap next pointer 8 _ written).1
  have afterValid := NativeByteRangeWrite.storeRange_wellFormed heap.memory valid pointer 8 _ next.memory stored
  have loaded := NativeByteRangeWrite.storeRange_then_load heap.memory pointer 8 _ next.memory stored
  rw [allocation_bytes_length] at loaded
  have first : ((bytes (.allocationError size alignment)).drop 0).take 8 = NativeWord64Memory.encode alignment := by
    simp [bytes,NativeWord64Memory.encode_length]
  have second : ((bytes (.allocationError size alignment)).drop 8).take 8 = NativeWord64Memory.encode size := by
    simp [bytes,NativeWord64Memory.encode_length]
  obtain ⟨head,atHead,alignmentStored⟩ := subword next.memory afterValid pointer 16 _ 0 alignment loaded (by decide) (by decide) first
  obtain ⟨tail,atTail,sizeStored⟩ := subword next.memory afterValid pointer 16 _ 8 size loaded (by decide) (by decide) second
  have atZero : NativeByteRange.pointerAt pointer 0 = some pointer := by
    simp [NativeByteRange.pointerAt,pointer.address.isLt]
  have same : head = pointer := Option.some.inj (atHead.symm.trans atZero)
  subst head
  exact ⟨alignmentStored,tail,atTail,sizeStored⟩

theorem written_fields (heap next : NativePointerByteMemory.State) (pointer : Pointer) (kind : Kind)
    (valid : NativeByteMemory.WellFormed heap.memory)
    (written : NativePointerByteMemory.writeBytes heap pointer 8 (bytes kind) = some next) : Stored next.memory pointer kind := by
  cases kind with
  | capacityOverflow => exact written_overflow _ _ _ written
  | allocationError size alignment => exact written_allocation _ _ _ _ _ valid written

theorem executeSteps_runs (world next : State) (ops : List Op) :
    executeSteps world ops = .value () next ↔ NativeStorageBorrowMachine.run world ops = some next := by
  induction ops generalizing world with
  | nil => simp [executeSteps,NativeStorageBorrowMachine.run]
  | cons op tail ih =>
    cases actual : NativeStorageBorrowMachine.execute world op <;>
      simp only [executeSteps,NativeStorageBorrowMachine.run,actual,Option.bind_none,Option.bind_some]
    next => simp
    next middle => exact ih middle

theorem snapshot_trace (tags : Tags) (world next : State) (base : Address) (value result : Value)
    (executed : snapshotValue tags world base value = .value result next) :
    ∃ kind allocated written,
      decode tags value = some kind ∧
      NativeStorageBorrowMachine.execute world (.legacy (.raw (.allocate base ⟨16,8⟩))) = some allocated ∧
      NativeStorageBorrowMachine.execute allocated (.legacy (.raw (.writeBytes 0 8 (bytes kind)))) = some written ∧
      NativeStorageBorrowMachine.execute written (.storageBorrow none 0 .shared ⟨16,8⟩) = some next := by
  obtain ⟨kind,_,decoded,actual,_,_⟩ := snapshotValue_success tags world next base value result executed
  cases allocation : NativeStorageBorrowMachine.execute world (.legacy (.raw (.allocate base ⟨16,8⟩))) with
  | none => simp only [steps,executeSteps,allocation] at actual; cases actual
  | some allocated =>
    cases writing : NativeStorageBorrowMachine.execute allocated (.legacy (.raw (.writeBytes 0 8 (bytes kind)))) with
    | none => simp only [steps,executeSteps,allocation,writing] at actual; cases actual
    | some written =>
      cases borrowing : NativeStorageBorrowMachine.execute written (.storageBorrow none 0 .shared ⟨16,8⟩) with
      | none => simp only [steps,executeSteps,allocation,writing,borrowing] at actual; cases actual
      | some granted =>
        simp only [steps,executeSteps,allocation,writing,borrowing] at actual
        cases actual
        exact ⟨kind,allocated,written,decoded,rfl,writing,borrowing⟩

theorem write_execution_fields (world next : State) (kind : Kind)
    (valid : NativeByteMemory.WellFormed world.pointers.heap.memory)
    (actual : NativeStorageBorrowMachine.execute world (.legacy (.raw (.writeBytes 0 8 (bytes kind)))) = some next) :
    ∃ pointer, world.pointers.registers[0]? = some pointer ∧ next.pointers.registers = world.pointers.registers ∧
      Stored next.pointers.heap.memory pointer kind := by
  simp only [NativeStorageBorrowMachine.execute,NativeReferenceMachine.execute] at actual
  split at actual
  next =>
    obtain ⟨pointers,performed,same⟩ := Option.map_eq_some_iff.mp actual
    simp only [NativePointerMachine.execute,Option.bind_eq_some_iff,Option.map_eq_some_iff] at performed
    obtain ⟨pointer,registered,heap,written,samePointers⟩ := performed
    subst pointers
    subst next
    exact ⟨pointer,registered,rfl,written_fields world.pointers.heap heap pointer kind valid written⟩
  next => cases actual

theorem snapshot_stored (tags : Tags) (world next : State) (base : Address) (value result : Value)
    (valid : NativeReferenceMachine.WellFormed world)
    (executed : snapshotValue tags world base value = .value result next) :
    ∃ kind pointer, decode tags value = some kind ∧ Valid kind ∧ Stored next.pointers.heap.memory pointer kind := by
  obtain ⟨kind,allocated,written,decoded,allocation,writing,borrowing⟩ := snapshot_trace tags world next base value result executed
  have validAllocated := NativeStorageBorrowMachine.execute_wellFormed world allocated valid _ allocation
  obtain ⟨pointer,_,_,stored⟩ := write_execution_fields allocated written kind validAllocated.1.1 writing
  have heap := NativeStorageBorrowMachine.storage_heap written next none 0 .shared ⟨16,8⟩ borrowing
  exact ⟨kind,pointer,decoded,decode_valid tags value kind decoded,by rw [heap]; exact stored⟩

def Resident (world : State) (value : Value) (kind : Kind) : Prop :=
  ∃ reference lease, value = .scalar (.reference false reference 2) ∧
    NativeRawVecFields.select world 0 = some reference ∧
    NativeByteBorrow.lookup world.leases reference.tag = some lease ∧ Stored world.pointers.heap.memory lease.pointer kind

theorem snapshot_resident (tags : Tags) (world next : State) (base : Address) (value result : Value)
    (valid : NativeReferenceMachine.WellFormed world)
    (executed : snapshotValue tags world base value = .value result next) :
    ∃ kind, decode tags value = some kind ∧ Valid kind ∧ Resident next result kind := by
  obtain ⟨kind,allocated,written,decoded,allocation,writing,borrowing⟩ := snapshot_trace tags world next base value result executed
  have validAllocated := NativeStorageBorrowMachine.execute_wellFormed world allocated valid _ allocation
  obtain ⟨pointer,registered,registers,stored⟩ := write_execution_fields allocated written kind validAllocated.1.1 writing
  have finalHeap := NativeStorageBorrowMachine.storage_heap written next none 0 .shared ⟨16,8⟩ borrowing
  simp only [NativeStorageBorrowMachine.execute,NativeStorageBorrowMachine.parentTag,Option.bind_some,Option.bind_eq_some_iff] at borrowing
  obtain ⟨borrowPointer,atBorrow,granted⟩ := borrowing
  have samePointer : borrowPointer = pointer := by
    rw [registers,registered] at atBorrow
    exact Option.some.inj atBorrow.symm
  subst borrowPointer
  obtain ⟨tag,ledger,actual,pointers,counter,leases,references,births⟩ :=
    NativeStorageBorrowMachine.grant_success written next none .shared pointer ⟨16,8⟩ granted
  obtain ⟨_,_,_,newLeases,_,_⟩ := NativeByteBorrowStorage.borrow_success _ _ _ _ _ _ _ actual
  have lookup : NativeByteBorrow.lookup next.leases tag = some ⟨tag,none,pointer,⟨16,8⟩,.shared⟩ := by
    rw [leases,newLeases]
    simp [NativeByteBorrow.lookup]
  have selected : NativeRawVecFields.select next 0 = some ⟨tag⟩ := by
    simp [NativeRawVecFields.select,references,lookup]
  obtain ⟨otherKind,reference,decodedAgain,_,selectedAgain,resultEq⟩ := snapshotValue_success tags world next base value result executed
  have sameKind : otherKind = kind := Option.some.inj (decodedAgain.symm.trans decoded)
  subst otherKind
  have sameReference : reference = ⟨tag⟩ := Option.some.inj (selectedAgain.symm.trans selected)
  subst reference
  refine ⟨kind,decoded,decode_valid tags value kind decoded,⟨⟨tag⟩,⟨tag,none,pointer,⟨16,8⟩,.shared⟩,resultEq,selected,lookup,?_⟩⟩
  change Stored next.pointers.heap.memory pointer kind
  rw [finalHeap]
  exact stored

theorem snapshotLocal_resident (tags : Tags) (frame : NativeRecordLLBC.Frame) (index : Nat) (base : Address)
    (next : State) (result : Value) (valid : NativeReferenceMachine.WellFormed frame.world)
    (executed : snapshotLocal tags frame index base = .value result next) :
    ∃ value kind, NativeRecordLLBC.read frame index [] = some value ∧ value = encode tags kind ∧
      Valid kind ∧ Resident next result kind := by
  cases selected : NativeRecordLLBC.read frame index [] with
  | none => simp only [snapshotLocal,selected] at executed; cases executed
  | some value =>
    simp only [snapshotLocal,selected] at executed
    obtain ⟨kind,decoded,kindValid,resident⟩ := snapshot_resident tags frame.world next base value result valid executed
    exact ⟨value,kind,rfl,decode_sound tags value kind decoded,kindValid,resident⟩

end FormalProof4FHE.HasteBoots.NativeReservationErrorLocal
