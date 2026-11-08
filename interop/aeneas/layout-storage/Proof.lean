namespace HasteBootsLayoutStorage
open FormalProof4FHE.HasteBoots
open NativeReferenceMachine (State)
open NativeRecordLLBC (Flow)
open NativeLayoutBytes (Words)

theorem metadata_exact : layoutSize = 16 ∧ layoutAlignment = 8 ∧ sizeOffset = 8 ∧ alignmentOffset = 0 := by decide

theorem alignment_domain : HasteBootsAllocatorCaller.alignmentDiscriminants.map Fin.val =
    (List.range 64).map (fun exponent => 2 ^ exponent) := by decide

theorem alignment_member (value : Words) (valid : value.Valid) :
    value.alignment ∈ HasteBootsAllocatorCaller.alignmentDiscriminants := by
  change value.alignment.val ∈ (List.range 64).map (fun exponent => 2 ^ exponent) at valid
  rw [← alignment_domain] at valid
  obtain ⟨word, member, same⟩ := List.mem_map.mp valid
  have equal : word = value.alignment := Fin.ext same
  rw [← equal]
  exact member

theorem value_exact (value : Words) : value.value layoutTag alignmentTag enumTag =
    HasteBootsAllocatorCaller.layoutValue value.size value.alignment := rfl

/-- Capture the data pointer before the resident descriptor read shifts scratch
registers. Caller operands come from actual checked bytes and that full pointer. -/
def call (world : State) (dataRegister layoutReference : Nat) : Flow :=
  match world.pointers.registers[dataRegister]? with
  | none => .invalid world
  | some pointer => match NativeLayoutBytes.read world layoutReference with
    | .invalid next => .invalid next
    | .value value next =>
      match NativeRecordLLBC.initial HasteBootsAllocatorCaller.f2.types HasteBootsAllocatorCaller.f2.argCount
          [.scalar (.raw ⟨pointer,none⟩), value.value layoutTag alignmentTag enumTag] next with
      | none => .invalid next
      | some frame => NativeRecordLLBC.settle next (NativeRecordLLBC.eval HasteBootsAllocatorCaller.f2.body frame)

theorem call_projects (world : State) (dataRegister layoutReference : Nat) :
    NativeReferenceMachine.Runs world (call world dataRegister layoutReference).world := by
  cases selected : world.pointers.registers[dataRegister]? with
  | none => simp only [call, selected, Flow.world]; exact .refl _
  | some pointer =>
    have first := NativeLayoutBytes.read_projects world layoutReference
    cases loaded : NativeLayoutBytes.read world layoutReference with
    | invalid next => simpa only [call, selected, loaded, NativeLayoutBytes.Result.world, Flow.world] using first
    | value value next =>
      rw [loaded] at first
      simp only [NativeLayoutBytes.Result.world] at first
      cases initialized : NativeRecordLLBC.initial HasteBootsAllocatorCaller.f2.types HasteBootsAllocatorCaller.f2.argCount
          [.scalar (.raw ⟨pointer,none⟩),value.value layoutTag alignmentTag enumTag] next with
      | none => simpa only [call, selected, loaded, initialized, Flow.world] using first
      | some frame =>
        have same := NativeRecordLLBC.initial_world _ _ _ _ frame initialized
        have later := NativeReferenceMachine.runs_trans _ _ _ (NativeRecordLLBC.eval_projects HasteBootsAllocatorCaller.f2.body frame)
          (NativeRecordLLBC.settle_projects next (NativeRecordLLBC.eval HasteBootsAllocatorCaller.f2.body frame))
        conv_lhs at later => rw [same]
        simp only [call, selected, loaded, initialized]
        exact NativeReferenceMachine.runs_trans _ _ _ first later

theorem call_reachable (world : State) (dataRegister layoutReference : Nat)
    (reachable : NativeReferenceMachine.Reachable world) :
    NativeReferenceMachine.Reachable (call world dataRegister layoutReference).world :=
  NativeSliceLLBC.reference_runs_reachable _ _ reachable (call_projects world dataRegister layoutReference)

theorem call_success (world readWorld next : State) (dataRegister layoutReference : Nat)
    (pointer : NativePointerStorage.Pointer) (value : Words)
    (reachable : NativeReferenceMachine.Reachable world)
    (selected : world.pointers.registers[dataRegister]? = some pointer)
    (loaded : NativeLayoutBytes.read world layoutReference = .value value readWorld)
    (freed : NativeByteDeallocation.execute readWorld ⟨pointer,none⟩ value.size value.alignment = some next) :
    call world dataRegister layoutReference = .returned (.scalar .unit) next := by
  have during : NativeReferenceMachine.Reachable readWorld := by
    simpa only [loaded, NativeLayoutBytes.Result.world] using NativeLayoutBytes.read_reachable world layoutReference reachable
  obtain ⟨_, bytes, _, decoded⟩ := NativeLayoutBytes.read_success world readWorld layoutReference value loaded
  have aligned := alignment_member value (NativeLayoutBytes.decode_valid bytes value decoded)
  have nonnull := (NativeByteDeallocation.execute_success readWorld next ⟨pointer,none⟩ value.size value.alignment freed).1.2
  simp only [call, selected, loaded, value_exact,
    HasteBootsAllocatorCaller.initial_exact readWorld ⟨pointer,none⟩ value.size value.alignment rfl aligned,
    HasteBootsAllocatorCaller.caller_success readWorld next ⟨pointer,none⟩ value.size value.alignment during rfl nonnull aligned freed,
    HasteBootsAllocatorCaller.free_settle readWorld next ⟨pointer,none⟩ value.size value.alignment during freed]

end HasteBootsLayoutStorage
