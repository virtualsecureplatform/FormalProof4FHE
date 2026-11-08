namespace HasteBootsAllocatorCaller
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC
open NativeRecordValues (Value)
open NativeReferenceMachine (State)
open NativeSliceLLBC (Raw)
open NativeWord64Memory (Word)

def alignmentValue (alignment : Word) : Value :=
  .record 1 (.pair (.enumeration 4 alignment) (.scalar .unit))

def layoutValue (size alignment : Word) : Value :=
  .record 0 (.pair (.scalar (.usize size)) (.pair (alignmentValue alignment) (.scalar .unit)))

def nonnullValue (pointer : Raw) : Value :=
  .record 2 (.pair (.scalar (.raw pointer)) (.scalar .unit))

def entry (world : State) (pointer : Raw) (size alignment : Word) : Frame :=
  ⟨f2.types, [.dead,.live (some (.scalar (.raw pointer))),.live (some (layoutValue size alignment)),
    .dead,.dead,.dead,.dead,.dead],world⟩

theorem classification_preserved : f2.classification = .transparent ∧
    f3.classification = .foreignBody ∧ f4.classification = .externalBody := by decide

theorem initial_exact (world : State) (pointer : Raw) (size alignment : Word)
    (thin : pointer.length = none) (aligned : alignment ∈ alignmentDiscriminants) :
    initial f2.types f2.argCount [.scalar (.raw pointer),layoutValue size alignment] world =
      some (entry world pointer size alignment) := by
  simp [initial, f2, NativeRecordValues.fits, NativeRecordValues.complete,
    NativeRecordValues.compatible, NativeSliceLLBC.fits, layoutValue, alignmentValue, thin, aligned, entry]

theorem free_settle (world next : State) (pointer : Raw) (size alignment : Word)
    (reachable : NativeReferenceMachine.Reachable world)
    (freed : NativeByteDeallocation.execute world pointer size alignment = some next) :
    settle world (.returned (.scalar .unit) next) = .returned (.scalar .unit) next := by
  have retained := NativeByteDeallocation.execute_preserves_history world next pointer size alignment freed
  have noNew : NativeReferenceCleanup.scopeTags world next = [] := by
    simp only [NativeReferenceCleanup.scopeTags, retained.2.2.2.1]
    have noEligible : world.leases.filter (fun lease => decide (world.nextTag ≤ lease.tag)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro lease member
      have older := (NativeReferenceMachine.reachable_wellFormed world reachable).2.1.1 lease member
      simpa [NativeReferenceMachine.ledger] using Nat.not_le_of_gt older.1
    rw [noEligible]
    rfl
  simp only [settle, NativeReferenceCleanup.settleUnit, NativeReferenceCleanup.closeScope,
    noNew, NativeReferenceCleanup.release]
  rfl

theorem caller_success (world next : State) (pointer : Raw) (size alignment : Word)
    (reachable : NativeReferenceMachine.Reachable world)
    (thin : pointer.length = none) (nonnull : pointer.storage.address.val ≠ 0)
    (aligned : alignment ∈ alignmentDiscriminants)
    (freed : NativeByteDeallocation.execute world pointer size alignment = some next) :
    eval f2.body (entry world pointer size alignment) = .returned (.scalar .unit) next := by
  have cleanup := free_settle world next pointer size alignment reachable freed
  simp [f2, entry, layoutValue, alignmentValue, eval, evalOperand, evalArgs, initial,
    evalRvalue, retag, NativeRecordLLBC.storageLive, NativeRecordLLBC.storageDead, NativeRecordLLBC.read, NativeRecordLLBC.write, NativeRecordValues.typeAt,
    NativeRecordValues.get, NativeRecordValues.replace, NativeRecordValues.copyable,
    NativeRecordValues.fits, NativeRecordValues.complete, NativeRecordValues.compatible,
    NativeSliceLLBC.fits, NativeSliceLLBC.retagValue, deallocate, thin, nonnull, aligned, freed, cleanup]

theorem caller_failure (world : State) (pointer : Raw) (size alignment : Word)
    (thin : pointer.length = none) (nonnull : pointer.storage.address.val ≠ 0)
    (aligned : alignment ∈ alignmentDiscriminants)
    (rejected : NativeByteDeallocation.execute world pointer size alignment = none) :
    eval f2.body (entry world pointer size alignment) = .invalid world := by
  simp [f2, entry, layoutValue, alignmentValue, eval, evalOperand, evalArgs, initial,
    evalRvalue, retag, NativeRecordLLBC.storageLive, NativeRecordLLBC.read, NativeRecordLLBC.write, NativeRecordValues.typeAt,
    NativeRecordValues.get, NativeRecordValues.replace, NativeRecordValues.copyable,
    NativeRecordValues.fits, NativeRecordValues.complete, NativeRecordValues.compatible,
    NativeSliceLLBC.fits, NativeSliceLLBC.retagValue, deallocate, thin, nonnull, aligned, rejected, settle]


def inputs (register : Nat) (size alignment : Word) : List Input :=
  [.scalar (.rawRegister register), .record 0 (.pair (.scalar (.usize size))
    (.pair (.record 1 (.pair (.enumeration 4 alignment) .unit)) .unit))]

theorem decode_exact (world : State) (register : Nat) (pointer : Raw) (size alignment : Word)
    (selected : world.pointers.registers[register]? = some pointer.storage) (thin : pointer.length = none) :
    decodeArgs world (inputs register size alignment) = some [.scalar (.raw pointer),layoutValue size alignment] := by
  rcases pointer with ⟨storage,length⟩
  cases thin
  simp [inputs, decodeArgs, decode, NativeSliceLLBC.decodeInput, selected, layoutValue, alignmentValue]

theorem invocation_success (world next : State) (register : Nat) (pointer : Raw) (size alignment : Word)
    (reachable : NativeReferenceMachine.Reachable world)
    (selected : world.pointers.registers[register]? = some pointer.storage)
    (thin : pointer.length = none) (nonnull : pointer.storage.address.val ≠ 0)
    (aligned : alignment ∈ alignmentDiscriminants)
    (freed : NativeByteDeallocation.execute world pointer size alignment = some next) :
    invoke f2 world (inputs register size alignment) = .returned (.scalar .unit) next := by
  simp only [invoke, decode_exact world register pointer size alignment selected thin,
    initial_exact world pointer size alignment thin aligned,
    caller_success world next pointer size alignment reachable thin nonnull aligned freed,
    free_settle world next pointer size alignment reachable freed]

theorem every_normal_return_frees_one (world next : State) (pointer : Raw) (size alignment : Word)
    (reachable : NativeReferenceMachine.Reachable world)
    (thin : pointer.length = none) (nonnull : pointer.storage.address.val ≠ 0)
    (aligned : alignment ∈ alignmentDiscriminants)
    (returned : eval f2.body (entry world pointer size alignment) = .returned (.scalar .unit) next) :
    next.pointers.heap.memory.blocks.length + 1 = world.pointers.heap.memory.blocks.length := by
  cases freed : NativeByteDeallocation.execute world pointer size alignment with
  | none => rw [caller_failure world pointer size alignment thin nonnull aligned freed] at returned; cases returned
  | some released =>
    rw [caller_success world released pointer size alignment reachable thin nonnull aligned freed] at returned
    cases returned
    exact NativeByteDeallocation.execute_frees_one world next pointer size alignment freed

theorem every_invocation_projects (world : State) (args : List Input) :
    NativeReferenceMachine.Runs world (invoke f2 world args).world := invoke_projects f2 world args

theorem every_invocation_reachable (world : State) (args : List Input)
    (reachable : NativeReferenceMachine.Reachable world) :
    NativeReferenceMachine.Reachable (invoke f2 world args).world := invoke_reachable f2 world args reachable

end HasteBootsAllocatorCaller
