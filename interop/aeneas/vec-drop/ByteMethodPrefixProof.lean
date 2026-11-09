namespace HasteBootsVecDrop
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC
open NativeRecordDropCalls (Code)
open NativeReferenceMachine (State Reference)
open NativeResidentVec (Descriptor InitializedElements)
open NativeVecBytePrefix

/-- Extract the real field-read, fat-pointer and slice-borrow preparation stages. -/
def byteMethodStages : Code → Option (Body × Body × Body × Code × Code)
  | .scope (.native fields (.native parts .done)) (.scope (.native borrow call) after) => some (fields,parts,borrow,call,after)
  | _ => none

def byteMethodPieces : Body × Body × Body × Code × Code := (byteMethodStages f2.code).get (by decide)
def byteFieldBody : Body := byteMethodPieces.1
def bytePartsBody : Body := byteMethodPieces.2.1
def byteBorrowBody : Body := byteMethodPieces.2.2.1
def byteCallCode : Code := byteMethodPieces.2.2.2.1
def byteAfterCode : Code := byteMethodPieces.2.2.2.2

theorem byte_method_code : f2.code =
    .scope (.native byteFieldBody (.native bytePartsBody .done)) (.scope (.native byteBorrowBody byteCallCode) byteAfterCode) := by rfl

def byteMethodEntry (world : State) (reference : Reference) : Frame :=
  ⟨f2.types,[.dead,.live (some (.scalar (.reference true reference 3))),.dead,.dead,.dead,.dead,.dead],world⟩

def byteFieldsFrame {world : State} {index : Nat} (descriptor : Descriptor world index) : Frame :=
  ⟨f2.types,[.live (some (.scalar .unit)),.live (some (.scalar (.reference true descriptor.reference 3))),.live none,
    .live (some (.scalar (.raw ⟨descriptor.buffer,none⟩))),.live (some (.scalar (.usize descriptor.length))),.dead,.dead],lengthWorld descriptor⟩

def bytePartsFrame {world : State} {index : Nat} (descriptor : Descriptor world index) : Frame :=
  {byteFieldsFrame descriptor with slots := (byteFieldsFrame descriptor).slots.set 2 (.live (some (.scalar (.raw ⟨descriptor.buffer,some descriptor.length⟩))))}

def byteBorrowCaller {world : State} {index : Nat} (descriptor : Descriptor world index) (next : State) : Frame :=
  ⟨f2.types,[.live (some (.scalar .unit)),.live (some (.scalar (.reference true descriptor.reference 3))),
    .live (some (.scalar (.raw ⟨descriptor.buffer,some descriptor.length⟩))),.dead,.dead,.dead,
    .live (some (.scalar (.reference true ⟨world.nextTag⟩ descriptor.length)))],next⟩

theorem byte_method_initial (world : State) (reference : Reference) :
    initial f2.types f2.argCount [.scalar (.reference true reference 3)] world = some (byteMethodEntry world reference) := by
  simp [initial,f2,byteMethodEntry,NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem byte_fields_complete {world : State} {index : Nat} (descriptor : Descriptor world index)
    (valid : NativeByteBorrow.LedgerValid (NativeReferenceMachine.ledger world))
    (frontier : NativeBorrowFrontier.ExclusiveFrontier (NativeReferenceMachine.ledger world) descriptor.lease) :
    eval byteFieldBody (byteMethodEntry world descriptor.reference) = .normal (byteFieldsFrame descriptor) := by
  have pointerRead := pointer_field_complete descriptor valid frontier
  have lengthRead := length_field_complete descriptor valid frontier
  simp [byteFieldBody,byteMethodPieces,byteMethodStages,f2,byteMethodEntry,byteFieldsFrame,
    eval,evalRvalue,recordResultValue,evalArgs,evalOperand,evalVec,NativeVecReference.eval,storageLive,storageDead,write,
    NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,
    NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits,
    NativeRecordValues.copyable,pointerRead,lengthRead,descriptor.nonnull]

theorem byte_parts_complete {world : State} {index : Nat} (descriptor : Descriptor world index) :
    eval bytePartsBody (byteFieldsFrame descriptor) = .normal (bytePartsFrame descriptor) := by
  simp [bytePartsBody,byteMethodPieces,byteMethodStages,f2,byteFieldsFrame,bytePartsFrame,
    eval,evalRvalue,evalParts,partsValue,NativeSliceLLBC.partsValue,evalArgs,evalOperand,write,NativeRecordLLBC.read,
    NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.fits,NativeRecordValues.complete,
    NativeRecordValues.compatible,NativeSliceLLBC.fits,NativeRecordValues.copyable]

theorem byte_borrow_complete {world : State} {index : Nat} (descriptor : Descriptor world index)
    (reachable : NativeReferenceMachine.Reachable world) (initialized : InitializedElements descriptor)
    (available : Available world descriptor.buffer descriptor.capacity.val)
    (frontier : NativeBorrowFrontier.ExclusiveFrontier (NativeReferenceMachine.ledger world) descriptor.lease) :
    ∃ next, eval byteBorrowBody (bytePartsFrame descriptor) = .normal (byteBorrowCaller descriptor next) ∧
      NativeByteTraversalCompleteness.Ready next ⟨⟨world.nextTag⟩,descriptor.length⟩ := by
  obtain ⟨next,issued,ready⟩ := fields_issue_ready descriptor reachable initialized available frontier
  refine ⟨next,?_,ready⟩
  simp [byteBorrowBody,byteMethodPieces,byteMethodStages,f2,bytePartsFrame,byteFieldsFrame,byteBorrowCaller,
    eval,evalRvalue,evalBorrowSlice,storageLive,storageDead,write,NativeRecordLLBC.read,
    NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.fits,NativeRecordValues.complete,
    NativeRecordValues.compatible,NativeSliceLLBC.fits,issued]

/-- The readonly source scope closes no loans and passes its actual caller
slots to slice preparation. The original scope cutoff is retained. -/
theorem byte_method_prefix {world : State} {index : Nat} (descriptor : Descriptor world index)
    (valid : NativeByteBorrow.LedgerValid (NativeReferenceMachine.ledger world))
    (frontier : NativeBorrowFrontier.ExclusiveFrontier (NativeReferenceMachine.ledger world) descriptor.lease) :
    evalCode f2.code (byteMethodEntry world descriptor.reference) =
      evalCode (.scope (.native byteBorrowBody byteCallCode) byteAfterCode) (bytePartsFrame descriptor) := by
  have prepared : evalCode (.native byteFieldBody (.native bytePartsBody .done)) (byteMethodEntry world descriptor.reference) =
      some (.normal (bytePartsFrame descriptor)) := by
    simp only [evalCode.eq_2,byte_fields_complete descriptor valid frontier,byte_parts_complete descriptor,evalCode.eq_1]
  rw [byte_method_code,evalCode.eq_3,prepared]
  have cleanup : NativeReferenceCleanup.closeScope (byteMethodEntry world descriptor.reference).world
      (bytePartsFrame descriptor).world = ⟨lengthWorld descriptor,[],[]⟩ := length_scope descriptor valid
  simp only [NativeRecordDropCalls.resumeScope,cleanup,List.isEmpty_nil,ite_true]
  rfl

/-- The actual byte-method prefix reaches its first call with a traversal-ready
slice. Callee execution and cleanup keep their original entry threshold. -/
theorem byte_method_ready_prefix {world : State} {index : Nat} (descriptor : Descriptor world index)
    (reachable : NativeReferenceMachine.Reachable world) (initialized : InitializedElements descriptor)
    (available : Available world descriptor.buffer descriptor.capacity.val)
    (frontier : NativeBorrowFrontier.ExclusiveFrontier (NativeReferenceMachine.ledger world) descriptor.lease) :
    ∃ next, NativeByteTraversalCompleteness.Ready next ⟨⟨world.nextTag⟩,descriptor.length⟩ ∧
      evalCode f2.code (byteMethodEntry world descriptor.reference) =
        match evalCode byteCallCode (byteBorrowCaller descriptor next) with
        | none => none
        | some returned => match NativeRecordDropCalls.resumeScope (lengthWorld descriptor) returned with
          | .normal changed => evalCode byteAfterCode changed
          | flow => some flow := by
  obtain ⟨next,borrowed,ready⟩ := byte_borrow_complete descriptor reachable initialized available frontier
  refine ⟨next,ready,?_⟩
  rw [byte_method_prefix descriptor (NativeReferenceMachine.reachable_wellFormed world reachable).2.1 frontier,
    evalCode.eq_3,evalCode.eq_2,borrowed]
  rfl


def byteCallConsumed {world : State} {index : Nat} (descriptor : Descriptor world index) (next : State) : Frame :=
  {byteBorrowCaller descriptor next with slots := (byteBorrowCaller descriptor next).slots.set 6 (.live (some .uninit))}

def byteForeignEntry {world : State} {index : Nat} (descriptor : Descriptor world index) (next : State) : Frame :=
  ⟨f3.types,[.dead,.live (some (.scalar (.reference true ⟨world.nextTag⟩ descriptor.length))),.dead,.dead],next⟩

theorem byte_call_code : byteCallCode =
    .call f3.name f3.classification f3.types f3.argCount 0 [.move 6 []] f3.code
      (.native (.dead 1 .resume) .done) .done := by rfl

theorem byte_call_prepared {world : State} {index : Nat} (descriptor : Descriptor world index) (next : State) :
    NativeRecordDropCalls.prepareCall (byteBorrowCaller descriptor next) f3.types f3.argCount [.move 6 []] =
      some (byteCallConsumed descriptor next,byteForeignEntry descriptor next) := by
  simp [NativeRecordDropCalls.prepareCall,byteBorrowCaller,byteCallConsumed,byteForeignEntry,f2,f3,
    evalArgs,evalOperand,NativeRecordValues.replace,NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,
    NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits,initial]

end HasteBootsVecDrop
