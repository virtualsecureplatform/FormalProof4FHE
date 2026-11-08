namespace HasteBootsReferenceRetagBody
open FormalProof4FHE.HasteBoots
open NativeSliceLLBC
open NativeReferenceMachine (State)
open NativeWord64Memory (Word)

def finishIssue (world : State) : Option (Value × State) → Flow
  | none => .invalid world
  | some (value, next) => .returned value next

def relayByte (mutable : Bool) : Flow → Flow
  | .returned value world => finishIssue world (issue world mutable value .byte)
  | flow => flow

def finishUnit : Flow → Flow
  | .returned _ world => .returned .unit world
  | flow => flow

def applyBody (function : Function) (world : State) (args : List Value) : Flow :=
  match initial function.types function.argCount args world with
  | none => .invalid world
  | some frame => eval function.body frame

theorem byte_layout_exact : g0.val = 1 ∧ g1.val = 1 ∧ g2.val = 1 ∧ g3.val = 1 := by decide

attribute [local simp] f0 f1 f2 f3 f4 f5 NativeSliceLLBC.invoke NativeSliceLLBC.decodeArgs NativeSliceLLBC.decodeInput
  NativeSliceLLBC.initial NativeSliceLLBC.eval NativeSliceLLBC.evalArgs NativeSliceLLBC.evalRvalue
  NativeSliceLLBC.evalOperand NativeSliceLLBC.storageLive NativeSliceLLBC.storageDead
  NativeSliceLLBC.writeLocal NativeSliceLLBC.readLocal NativeSliceLLBC.partsValue NativeSliceLLBC.evalParts
  NativeSliceLLBC.fits NativeSliceLLBC.retagValue finishIssue relayByte finishUnit applyBody

theorem shared_byte_body (world : State) (index : Nat) (length : Word) :
    invoke f3 world [.rawRegister index, .usize length] = match world.pointers.registers[index]? with
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
    invoke f4 world [.rawRegister index, .usize length] = match world.pointers.registers[index]? with
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

theorem borrowed_body (world : State) (reference : NativeReferenceMachine.Reference) (length : Word) :
    applyBody f0 world [.reference false reference length] =
      finishIssue world (issue world false (.reference false reference length) .byte) := by
  cases issued : issue world false (.reference false reference length) .byte with
  | none => simp_all
  | some output =>
    rcases output with ⟨value, next⟩
    obtain ⟨count, same⟩ := issue_returned_tag world next false _ value issued
    subst value
    simp_all

theorem identity_body (world : State) (reference : NativeReferenceMachine.Reference) (length : Word) :
    applyBody f5 world [.reference true reference length] =
      finishIssue world (issue world true (.reference true reference length) .byte) := by
  cases issued : issue world true (.reference true reference length) .byte with
  | none => simp_all
  | some output =>
    rcases output with ⟨value, next⟩
    obtain ⟨count, same⟩ := issue_returned_tag world next true _ value issued
    subst value
    simp_all

theorem shared_scope (world : State) (index : Nat) (length : Word) :
    invoke f1 world [.rawRegister index, .usize length] =
      finishUnit (relayByte false (relayByte false (invoke f3 world [.rawRegister index, .usize length]))) := by
  cases selected : world.pointers.registers[index]? with
  | none => simp_all
  | some pointer =>
    cases issued : issue world false (.raw ⟨pointer, some length⟩) .byte with
    | none => simp_all
    | some output =>
      rcases output with ⟨value, next⟩
      obtain ⟨count, same⟩ := issue_returned_tag world next false _ value issued
      subst value
      cases first : issue next false (.reference false ⟨world.nextTag⟩ count) .byte with
      | none => simp_all
      | some output =>
        rcases output with ⟨value, middle⟩
        obtain ⟨size, same⟩ := issue_returned_tag next middle false _ value first
        subst value
        cases second : issue middle false (.reference false ⟨next.nextTag⟩ size) .byte with
        | none => simp_all
        | some output =>
          rcases output with ⟨value, final⟩
          obtain ⟨lastSize, same⟩ := issue_returned_tag middle final false _ value second
          subst value
          simp_all

theorem mutable_scope (world : State) (index : Nat) (length : Word) :
    invoke f2 world [.rawRegister index, .usize length] = finishUnit (relayByte true (relayByte true (relayByte true (invoke f4 world [.rawRegister index, .usize length])))) := by
  cases selected : world.pointers.registers[index]? with
  | none => simp_all
  | some pointer =>
    cases issued : issue world true (.raw ⟨pointer, some length⟩) .byte with
    | none => simp_all
    | some output =>
      rcases output with ⟨value, next⟩
      obtain ⟨count, same⟩ := issue_returned_tag world next true _ value issued
      subst value
      cases first : issue next true (.reference true ⟨world.nextTag⟩ count) .byte with
      | none => simp_all
      | some output =>
        rcases output with ⟨value, afterFirst⟩
        obtain ⟨countFirst, same⟩ := issue_returned_tag next afterFirst true _ value first
        subst value
        cases second : issue afterFirst true (.reference true ⟨next.nextTag⟩ countFirst) .byte with
        | none => simp_all
        | some output =>
          rcases output with ⟨value, afterSecond⟩
          obtain ⟨countSecond, same⟩ := issue_returned_tag afterFirst afterSecond true _ value second
          subst value
          cases third : issue afterSecond true (.reference true ⟨afterFirst.nextTag⟩ countSecond) .byte with
          | none => simp_all
          | some output =>
            rcases output with ⟨value, final⟩
            obtain ⟨countThird, same⟩ := issue_returned_tag afterSecond final true _ value third
            subst value
            simp_all


end HasteBootsReferenceRetagBody
