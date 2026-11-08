namespace HasteBootsGlobalDeallocation
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC
open NativeRecordValues (Value)
open NativeReferenceMachine (State Reference)
open NativeSliceLLBC (Raw)
open NativeWord64Memory (Word)

def pointerValue (pointer : Raw) : Value := .record 0 (.pair (.scalar (.raw pointer)) (.scalar .unit))
def alignmentValue (alignment : Word) : Value := .record 3 (.pair (.enumeration 4 alignment) (.scalar .unit))
def layoutValue (size alignment : Word) : Value :=
  .record 1 (.pair (.scalar (.usize size)) (.pair (alignmentValue alignment) (.scalar .unit)))
def selfValue (reference : Reference) : Value := .scalar (.reference false reference ⟨0,by decide⟩)
def entry (world : State) (reference : Reference) (pointer : Raw) (size alignment : Word) : Frame :=
  ⟨f1.types,[.dead,.live (some (selfValue reference)),.live (some (pointerValue pointer)),
    .live (some (layoutValue size alignment)),.dead,.dead],world⟩

theorem classification_preserved : f1.classification = .transparent ∧ f3.classification = .externalBody := by decide

theorem initial_exact (world : State) (reference : Reference) (pointer : Raw) (size alignment : Word)
    (thin : pointer.length = none) (nonnull : pointer.storage.address.val ≠ 0)
    (aligned : alignment ∈ alignmentDiscriminants) :
    initial f1.types f1.argCount [selfValue reference,pointerValue pointer,layoutValue size alignment] world =
      some (entry world reference pointer size alignment) := by
  simp [initial,f1,entry,selfValue,pointerValue,layoutValue,alignmentValue,NativeRecordValues.fits,
    NativeRecordValues.compatible,NativeRecordValues.complete,NativeSliceLLBC.fits,thin,nonnull,aligned]

theorem zero_case (world : State) (reference : Reference) (pointer : Raw) (alignment : Word)
    :
    eval f1.body (entry world reference pointer (0 : Word) alignment) = .returned (.scalar .unit) world := by
  simp [f1,entry,selfValue,pointerValue,layoutValue,alignmentValue,eval,evalOperand,evalRvalue,retag,
    NativeRecordLLBC.storageLive,NativeRecordLLBC.storageDead,NativeRecordLLBC.read,NativeRecordLLBC.write,
    NativeRecordValues.get,NativeRecordValues.typeAt,NativeRecordValues.copyable,NativeRecordValues.complete,
    NativeRecordValues.fits,NativeRecordValues.compatible,NativeSliceLLBC.fits,NativeSliceLLBC.retagValue,
    ]

theorem nonzero_success (world next : State) (reference : Reference) (pointer : Raw) (size alignment : Word)
    (reachable : NativeReferenceMachine.Reachable world)
    (thin : pointer.length = none) (nonnull : pointer.storage.address.val ≠ 0)
    (aligned : alignment ∈ alignmentDiscriminants)
    (freed : NativeByteDeallocation.execute world pointer size alignment = some next) :
    eval f1.body (entry world reference pointer size alignment) = .returned (.scalar .unit) next := by
  have positive := (NativeByteDeallocation.execute_success world next pointer size alignment freed).2.1
  have nonzero : size ≠ (0 : Word) := by
    intro same
    simp only [same,Fin.val_zero,Nat.lt_irrefl] at positive
  have cleanup := HasteBootsAllocatorCaller.free_settle world next pointer size alignment reachable freed
  simp [f1,entry,selfValue,pointerValue,layoutValue,alignmentValue,eval,evalOperand,evalArgs,evalRvalue,retag,initial,
    NativeRecordLLBC.storageLive,NativeRecordLLBC.storageDead,NativeRecordLLBC.read,NativeRecordLLBC.write,
    NativeRecordValues.get,NativeRecordValues.replace,NativeRecordValues.typeAt,NativeRecordValues.copyable,
    NativeRecordValues.complete,NativeRecordValues.fits,NativeRecordValues.compatible,NativeSliceLLBC.fits,
    NativeSliceLLBC.retagValue,deallocate,thin,nonnull,aligned,nonzero,freed,cleanup]

theorem nonzero_failure (world : State) (reference : Reference) (pointer : Raw) (size alignment : Word)
    (thin : pointer.length = none) (nonnull : pointer.storage.address.val ≠ 0)
    (aligned : alignment ∈ alignmentDiscriminants) (nonzero : size ≠ (0 : Word))
    (rejected : NativeByteDeallocation.execute world pointer size alignment = none) :
    eval f1.body (entry world reference pointer size alignment) = .invalid world := by
  simp [f1,entry,selfValue,pointerValue,layoutValue,alignmentValue,eval,evalOperand,evalArgs,evalRvalue,retag,initial,
    NativeRecordLLBC.storageLive,NativeRecordLLBC.read,NativeRecordLLBC.write,
    NativeRecordValues.get,NativeRecordValues.replace,NativeRecordValues.typeAt,NativeRecordValues.copyable,
    NativeRecordValues.complete,NativeRecordValues.fits,NativeRecordValues.compatible,NativeSliceLLBC.fits,
    NativeSliceLLBC.retagValue,deallocate,thin,nonnull,aligned,nonzero,rejected,settle]


def inputs (selfRegister dataRegister : Nat) (size alignment : Word) : List Input :=
  [.zstSharedReference selfRegister,.record 0 (.pair (.scalar (.rawRegister dataRegister)) .unit),
   .record 1 (.pair (.scalar (.usize size)) (.pair (.record 3 (.pair (.enumeration 4 alignment) .unit)) .unit))]

theorem decode_exact (world : State) (selfRegister dataRegister : Nat) (reference : Reference)
    (pointer : Raw) (size alignment : Word)
    (selfSelected : NativeZstReference.decode world selfRegister = some (.reference false reference ⟨0,by decide⟩))
    (selected : world.pointers.registers[dataRegister]? = some pointer.storage) (thin : pointer.length = none) :
    decodeArgs world (inputs selfRegister dataRegister size alignment) =
      some [selfValue reference,pointerValue pointer,layoutValue size alignment] := by
  rcases pointer with ⟨storage,length⟩
  cases thin
  simp [inputs,decodeArgs,decode,NativeSliceLLBC.decodeInput,selfSelected,selected,
    selfValue,pointerValue,layoutValue,alignmentValue]

theorem settle_same (world : State) (reachable : NativeReferenceMachine.Reachable world) :
    settle world (.returned (.scalar .unit) world) = .returned (.scalar .unit) world := by
  have noNew : NativeReferenceCleanup.scopeTags world world = [] := by
    simp only [NativeReferenceCleanup.scopeTags]
    have empty : world.leases.filter (fun lease => decide (world.nextTag ≤ lease.tag)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro lease member
      have older := (NativeReferenceMachine.reachable_wellFormed world reachable).2.1.1 lease member
      simpa [NativeReferenceMachine.ledger] using Nat.not_le_of_gt older.1
    rw [empty]
    rfl
  simp only [settle,NativeReferenceCleanup.settleUnit,NativeReferenceCleanup.closeScope,noNew,NativeReferenceCleanup.release]
  rfl

theorem invocation_zero (world : State) (selfRegister dataRegister : Nat) (reference : Reference)
    (pointer : Raw) (alignment : Word) (reachable : NativeReferenceMachine.Reachable world)
    (selfSelected : NativeZstReference.decode world selfRegister = some (.reference false reference ⟨0,by decide⟩))
    (selected : world.pointers.registers[dataRegister]? = some pointer.storage)
    (thin : pointer.length = none) (nonnull : pointer.storage.address.val ≠ 0)
    (aligned : alignment ∈ alignmentDiscriminants) :
    invoke f1 world (inputs selfRegister dataRegister (0 : Word) alignment) = .returned (.scalar .unit) world := by
  simp only [invoke,decode_exact world selfRegister dataRegister reference pointer _ alignment selfSelected selected thin,
    initial_exact world reference pointer _ alignment thin nonnull aligned,zero_case,settle_same world reachable]

theorem invocation_nonzero (world next : State) (selfRegister dataRegister : Nat) (reference : Reference)
    (pointer : Raw) (size alignment : Word) (reachable : NativeReferenceMachine.Reachable world)
    (selfSelected : NativeZstReference.decode world selfRegister = some (.reference false reference ⟨0,by decide⟩))
    (selected : world.pointers.registers[dataRegister]? = some pointer.storage)
    (thin : pointer.length = none) (nonnull : pointer.storage.address.val ≠ 0)
    (aligned : alignment ∈ alignmentDiscriminants)
    (freed : NativeByteDeallocation.execute world pointer size alignment = some next) :
    invoke f1 world (inputs selfRegister dataRegister size alignment) = .returned (.scalar .unit) next := by
  simp only [invoke,decode_exact world selfRegister dataRegister reference pointer size alignment selfSelected selected thin,
    initial_exact world reference pointer size alignment thin nonnull aligned,
    nonzero_success world next reference pointer size alignment reachable thin nonnull aligned freed,
    HasteBootsAllocatorCaller.free_settle world next pointer size alignment reachable freed]

theorem every_normal_return (world next : State) (reference : Reference) (pointer : Raw) (size alignment : Word)
    (reachable : NativeReferenceMachine.Reachable world)
    (thin : pointer.length = none) (nonnull : pointer.storage.address.val ≠ 0)
    (aligned : alignment ∈ alignmentDiscriminants)
    (returned : eval f1.body (entry world reference pointer size alignment) = .returned (.scalar .unit) next) :
    (size = 0 ∧ next = world) ∨
      (size ≠ 0 ∧ next.pointers.heap.memory.blocks.length + 1 = world.pointers.heap.memory.blocks.length) := by
  by_cases zero : size = 0
  · subst size
    rw [zero_case] at returned
    cases returned
    exact Or.inl ⟨rfl,rfl⟩
  · cases freed : NativeByteDeallocation.execute world pointer size alignment with
    | none => rw [nonzero_failure world reference pointer size alignment thin nonnull aligned zero freed] at returned; cases returned
    | some released =>
      rw [nonzero_success world released reference pointer size alignment reachable thin nonnull aligned freed] at returned
      cases returned
      exact Or.inr ⟨zero,NativeByteDeallocation.execute_frees_one world next pointer size alignment freed⟩

theorem every_invocation_projects (world : State) (args : List Input) :
    NativeReferenceMachine.Runs world (invoke f1 world args).world := invoke_projects f1 world args

theorem every_invocation_reachable (world : State) (args : List Input) (reachable : NativeReferenceMachine.Reachable world) :
    NativeReferenceMachine.Reachable (invoke f1 world args).world := invoke_reachable f1 world args reachable

end HasteBootsGlobalDeallocation
