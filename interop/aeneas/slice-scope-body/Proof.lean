namespace HasteBootsSliceScopeBody
open FormalProof4FHE.HasteBoots
open NativeSliceLLBC
open NativeReferenceMachine (State)
open NativeWord64Memory (Word)

def finishIssue (world : State) : Option (Value × State) → Flow
  | none => .invalid world
  | some (value, next) => .returned value next

def finishUnit : Flow → Flow
  | .returned _ world => .returned .unit world
  | flow => flow

theorem byte_layout_exact : g0.val = 1 ∧ g1.val = 1 ∧ g2.val = 1 ∧ g3.val = 1 := by decide

attribute [local simp] f0 f1 f2 f3  NativeSliceLLBC.invoke NativeSliceLLBC.decodeArgs NativeSliceLLBC.decodeInput
  NativeSliceLLBC.initial NativeSliceLLBC.eval NativeSliceLLBC.evalArgs NativeSliceLLBC.evalRvalue
  NativeSliceLLBC.evalOperand NativeSliceLLBC.storageLive NativeSliceLLBC.storageDead
  NativeSliceLLBC.writeLocal NativeSliceLLBC.readLocal NativeSliceLLBC.partsValue NativeSliceLLBC.evalParts
  NativeSliceLLBC.fits NativeSliceLLBC.retagValue finishIssue finishUnit

theorem shared_byte_body (world : State) (index : Nat) (length : Word) :
    invoke f2 world [.rawRegister index, .usize length] = match world.pointers.registers[index]? with
      | none => .invalid world
      | some pointer => finishIssue world (issue world false (.raw ⟨pointer, some length⟩) .byte) := by
  cases selected : world.pointers.registers[index]? with
  | none => simp_all
  | some pointer =>
    cases issued : issue world false (.raw ⟨pointer, some length⟩) .byte with
    | none => simp_all
    | some output =>
      rcases output with ⟨value, next⟩
      obtain ⟨count, same⟩ := issue_returned_tag world next false _ value issued
      subst value
      simp_all

theorem mutable_byte_body (world : State) (index : Nat) (length : Word) :
    invoke f3 world [.rawRegister index, .usize length] = match world.pointers.registers[index]? with
      | none => .invalid world
      | some pointer => finishIssue world (issue world true (.raw ⟨pointer, some length⟩) .byte) := by
  cases selected : world.pointers.registers[index]? with
  | none => simp_all
  | some pointer =>
    cases issued : issue world true (.raw ⟨pointer, some length⟩) .byte with
    | none => simp_all
    | some output =>
      rcases output with ⟨value, next⟩
      obtain ⟨count, same⟩ := issue_returned_tag world next true _ value issued
      subst value
      simp_all

theorem shared_scope (world : State) (index : Nat) (length : Word) :
    invoke f0 world [.rawRegister index, .usize length] = finishUnit (invoke f2 world [.rawRegister index, .usize length]) := by
  cases selected : world.pointers.registers[index]? with
  | none => simp_all
  | some pointer =>
    cases issued : issue world false (.raw ⟨pointer, some length⟩) .byte with
    | none => simp_all
    | some output =>
      rcases output with ⟨value, next⟩
      obtain ⟨count, same⟩ := issue_returned_tag world next false _ value issued
      subst value
      simp_all

theorem mutable_scope (world : State) (index : Nat) (length : Word) :
    invoke f1 world [.rawRegister index, .usize length] = finishUnit (match invoke f3 world [.rawRegister index, .usize length] with
      | .returned value next => finishIssue next (issue next true value .byte)
      | flow => flow) := by
  cases selected : world.pointers.registers[index]? with
  | none => simp_all
  | some pointer =>
    cases issued : issue world true (.raw ⟨pointer, some length⟩) .byte with
    | none => simp_all
    | some output =>
      rcases output with ⟨value, next⟩
      obtain ⟨count, same⟩ := issue_returned_tag world next true _ value issued
      subst value
      cases reborrowed : issue next true (.reference true ⟨world.nextTag⟩ count) .byte with
      | none => simp_all
      | some output =>
        rcases output with ⟨value, final⟩
        obtain ⟨size, same⟩ := issue_returned_tag next final true _ value reborrowed
        subst value
        simp_all

end HasteBootsSliceScopeBody
