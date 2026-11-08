namespace HasteBootsSliceReferenceBody
open FormalProof4FHE.HasteBoots
open NativeSliceLLBC
open NativeReferenceMachine (State)
open NativeWord64Memory (Word)

def finishIssue (world : State) : Option (Value × State) → Flow
  | none => .invalid world
  | some (value, next) => .returned value next

def relay (mutable : Bool) : Flow → Flow
  | .returned value world => finishIssue world (issue world mutable value)
  | .continued frame => .invalid frame.world
  | .unwind world => .unwind world
  | .invalid world => .invalid world
  | .unsupported source world => .unsupported source world

def relayByte (mutable : Bool) : Flow → Flow
  | .returned value world => finishIssue world (issue world mutable value .byte)
  | .continued frame => .invalid frame.world
  | .unwind world => .unwind world
  | .invalid world => .invalid world
  | .unsupported source world => .unsupported source world

theorem word_layout_exact : g0.val = 8 ∧ g1.val = 8 ∧ g4.val = 8 ∧ g5.val = 8 := by decide

theorem byte_layout_exact : g2.val = 1 ∧ g3.val = 1 ∧ g6.val = 1 ∧ g7.val = 1 := by decide

attribute [local simp] f0 f1 f2 f3 f4 f5 f6 f7 NativeSliceLLBC.invoke NativeSliceLLBC.decodeArgs NativeSliceLLBC.decodeInput
  NativeSliceLLBC.initial NativeSliceLLBC.eval NativeSliceLLBC.evalArgs NativeSliceLLBC.evalRvalue
  NativeSliceLLBC.evalOperand NativeSliceLLBC.storageLive NativeSliceLLBC.storageDead
  NativeSliceLLBC.writeLocal NativeSliceLLBC.readLocal NativeSliceLLBC.partsValue NativeSliceLLBC.evalParts
  NativeSliceLLBC.fits finishIssue relay relayByte

theorem shared_body (world : State) (index : Nat) (length : Word) :
    invoke f4 world [.rawRegister index, .usize length] = match world.pointers.registers[index]? with
      | none => .invalid world
      | some pointer => finishIssue world (issue world false (.raw ⟨pointer, some length⟩)) := by
  cases selected : world.pointers.registers[index]? with
  | none => simp_all
  | some pointer =>
    cases issued : issue world false (.raw ⟨pointer, some length⟩) with
    | none => simp_all
    | some output =>
      rcases output with ⟨value, next⟩
      obtain ⟨count, same⟩ := issue_returned_tag world next false _ value issued
      subst value
      simp_all

theorem mutable_body (world : State) (index : Nat) (length : Word) :
    invoke f5 world [.rawRegister index, .usize length] = match world.pointers.registers[index]? with
      | none => .invalid world
      | some pointer => finishIssue world (issue world true (.raw ⟨pointer, some length⟩)) := by
  cases selected : world.pointers.registers[index]? with
  | none => simp_all
  | some pointer =>
    cases issued : issue world true (.raw ⟨pointer, some length⟩) with
    | none => simp_all
    | some output =>
      rcases output with ⟨value, next⟩
      obtain ⟨count, same⟩ := issue_returned_tag world next true _ value issued
      subst value
      simp_all

theorem shared_wrapper (world : State) (index : Nat) (length : Word) :
    invoke f0 world [.rawRegister index, .usize length] = relay false (invoke f4 world [.rawRegister index, .usize length]) := by
  cases selected : world.pointers.registers[index]? with
  | none => simp_all
  | some pointer =>
    cases issued : issue world false (.raw ⟨pointer, some length⟩) with
    | none => simp_all
    | some output =>
      rcases output with ⟨value, next⟩
      obtain ⟨count, same⟩ := issue_returned_tag world next false _ value issued
      subst value
      cases reborrowed : issue next false (.reference false ⟨world.nextTag⟩ count) with
      | none => simp_all
      | some output =>
        rcases output with ⟨value, final⟩
        obtain ⟨size, same⟩ := issue_returned_tag next final false _ value reborrowed
        subst value
        simp_all

theorem mutable_wrapper (world : State) (index : Nat) (length : Word) :
    invoke f1 world [.rawRegister index, .usize length] = relay true (relay true (relay true (invoke f5 world [.rawRegister index, .usize length]))) := by
  cases selected : world.pointers.registers[index]? with
  | none => simp_all
  | some pointer =>
    cases issued : issue world true (.raw ⟨pointer, some length⟩) with
    | none => simp_all
    | some output =>
      rcases output with ⟨value, next⟩
      obtain ⟨count, same⟩ := issue_returned_tag world next true _ value issued
      subst value
      cases first : issue next true (.reference true ⟨world.nextTag⟩ count) with
      | none => simp_all
      | some output =>
        rcases output with ⟨value, afterFirst⟩
        obtain ⟨countFirst, same⟩ := issue_returned_tag next afterFirst true _ value first
        subst value
        cases second : issue afterFirst true (.reference true ⟨next.nextTag⟩ countFirst) with
        | none => simp_all
        | some output =>
          rcases output with ⟨value, afterSecond⟩
          obtain ⟨countSecond, same⟩ := issue_returned_tag afterFirst afterSecond true _ value second
          subst value
          cases third : issue afterSecond true (.reference true ⟨afterFirst.nextTag⟩ countSecond) with
          | none => simp_all
          | some output =>
            rcases output with ⟨value, final⟩
            obtain ⟨countThird, same⟩ := issue_returned_tag afterSecond final true _ value third
            subst value
            simp_all

theorem shared_byte_body (world : State) (index : Nat) (length : Word) :
    invoke f6 world [.rawRegister index, .usize length] = match world.pointers.registers[index]? with
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
    invoke f7 world [.rawRegister index, .usize length] = match world.pointers.registers[index]? with
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

theorem shared_byte_wrapper (world : State) (index : Nat) (length : Word) :
    invoke f2 world [.rawRegister index, .usize length] = relayByte false (invoke f6 world [.rawRegister index, .usize length]) := by
  cases selected : world.pointers.registers[index]? with
  | none => simp_all
  | some pointer =>
    cases issued : issue world false (.raw ⟨pointer, some length⟩) .byte with
    | none => simp_all
    | some output =>
      rcases output with ⟨value, next⟩
      obtain ⟨count, same⟩ := issue_returned_tag world next false _ value issued
      subst value
      cases reborrowed : issue next false (.reference false ⟨world.nextTag⟩ count) .byte with
      | none => simp_all
      | some output =>
        rcases output with ⟨value, final⟩
        obtain ⟨size, same⟩ := issue_returned_tag next final false _ value reborrowed
        subst value
        simp_all

theorem mutable_byte_wrapper (world : State) (index : Nat) (length : Word) :
    invoke f3 world [.rawRegister index, .usize length] = relayByte true (relayByte true (relayByte true (invoke f7 world [.rawRegister index, .usize length]))) := by
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

def constructor (element : Element) (mutable : Bool) : Function :=
  match element, mutable with
  | .word, false => f4
  | .word, true => f5
  | .byte, false => f6
  | .byte, true => f7

theorem constructor_body (world : State) (index : Nat) (length : Word) (mutable : Bool) (element : Element) :
    invoke (constructor element mutable) world [.rawRegister index, .usize length] = match world.pointers.registers[index]? with
      | none => .invalid world
      | some pointer => finishIssue world (issue world mutable (.raw ⟨pointer, some length⟩) element) := by
  cases element <;> cases mutable
  · exact shared_byte_body world index length
  · exact mutable_byte_body world index length
  · exact shared_body world index length
  · exact mutable_body world index length

theorem constructor_success (world next : State) (index : Nat) (length : Word) (mutable : Bool) (element : Element) (value : Value)
    (returned : invoke (constructor element mutable) world [.rawRegister index, .usize length] = .returned value next) :
    ∃ pointer, world.pointers.registers[index]? = some pointer ∧
      NativeReferenceMachine.execute world (.borrow index (mode mutable) (layout length element)) = some next ∧
      value = .reference mutable ⟨world.nextTag⟩ length := by
  rw [constructor_body] at returned
  cases selected : world.pointers.registers[index]? with
  | none => simp only [selected] at returned; cases returned
  | some pointer =>
    simp only [selected] at returned
    rw [issue_raw_selected world index pointer selected mutable length element] at returned
    cases actual : NativeReferenceMachine.grant world none (mode mutable) pointer (layout length element) with
    | none => simp only [actual, Option.map_none, finishIssue] at returned; cases returned
    | some final =>
      simp only [actual, Option.map_some, finishIssue] at returned
      cases returned
      refine ⟨pointer, rfl, ?_, rfl⟩
      simpa only [NativeReferenceMachine.execute, selected, Option.bind_some] using actual

theorem constructor_lease (world next : State) (index : Nat) (length : Word) (mutable : Bool) (element : Element) (value : Value)
    (returned : invoke (constructor element mutable) world [.rawRegister index, .usize length] = .returned value next) :
    ∃ pointer, world.pointers.registers[index]? = some pointer ∧ value = .reference mutable ⟨world.nextTag⟩ length ∧
      NativeByteBorrow.lookup next.leases world.nextTag = some ⟨world.nextTag, none, pointer, layout length element, mode mutable⟩ ∧
      (⟨world.nextTag⟩ : NativeReferenceMachine.Reference) ∈ next.references := by
  obtain ⟨pointer, selected, actual, valueEq⟩ := constructor_success world next index length mutable element value returned
  simp only [NativeReferenceMachine.execute, selected, Option.bind_some] at actual
  obtain ⟨tag, borrowed, checked, _, _, leases, references, _⟩ :=
    NativeReferenceMachine.grant_success world next none (mode mutable) pointer (layout length element) actual
  have outcome := NativeByteBorrow.borrow_success (NativeReferenceMachine.ledger world) none (mode mutable) pointer (layout length element) tag borrowed checked
  refine ⟨pointer, selected, valueEq, ?_, ?_⟩
  · rw [leases, outcome.2.2.2.1, outcome.1]
    simp only [NativeReferenceMachine.ledger, NativeByteBorrow.lookup, ite_true]
  · rw [references, outcome.1]
    exact List.mem_cons_self

end HasteBootsSliceReferenceBody
