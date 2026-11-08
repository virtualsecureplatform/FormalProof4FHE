namespace HasteBootsByteLoopBody
open FormalProof4FHE.HasteBoots
open NativeByteLoopLLBC
open NativeReferenceMachine (State)
open NativePointerStorage (Pointer)
open NativeWord64Memory (Word)
open NativeByteSliceIndex (Slice)

def entry (world : State) (slice : Slice) : Frame :=
  ⟨[.unit,.sliceRef,.usize,.usize,.rawByte,.boolean,.sliceRef,.byteRef],
    [.dead,.live (some (.sliceRef slice)),.dead,.dead,.dead,.dead,.dead,.dead],world⟩

def head (world : State) (slice : Slice) (cursor : Word) (last : Option Pointer) (six seven : Slot) : Frame :=
  ⟨[.unit,.sliceRef,.usize,.usize,.rawByte,.boolean,.sliceRef,.byteRef],
    [.live (some .unit),.live (some (.sliceRef slice)),.live (some (.usize slice.length)),.live (some (.usize cursor)),
      .live (last.map Value.rawByte),.live none,six,seven],world⟩

def exit (world : State) : Frame :=
  ⟨[.unit,.sliceRef,.usize,.usize,.rawByte,.boolean,.sliceRef,.byteRef],
    [.live (some .unit),.dead,.dead,.dead,.dead,.dead,.dead,.dead],world⟩

def successor (cursor : Word) : Word := ⟨(cursor.val+1) % (2^64), Nat.mod_lt _ (by decide)⟩

attribute [local simp] f4 entry head exit successor NativeByteLoopLLBC.initial
  NativeByteLoopLLBC.eval NativeByteLoopLLBC.evalRvalue NativeByteLoopLLBC.evalBinary
  NativeByteLoopLLBC.binaryValue NativeByteLoopLLBC.evalOperand NativeByteLoopLLBC.copyAllowed
  NativeByteLoopLLBC.readLocal NativeByteLoopLLBC.writeLocal NativeByteLoopLLBC.storageLive NativeByteLoopLLBC.storageDead
  NativeByteLoopLLBC.fits NativeByteLoopLLBC.retagValue NativeByteLoopLLBC.borrowSlice NativeByteLoopLLBC.evalIndex
  NativeByteLoopLLBC.Flow.world NativeByteLoopLLBC.Flow.frame

theorem initial_exact (world : State) (slice : Slice) : initial f4 world slice = some (entry world slice) := by simp

theorem before_exact (world : State) (slice : Slice) :
    eval f4.before (entry world slice) = .normal (head world slice ⟨0, by decide⟩ none .dead .dead) := by simp

theorem after_exact (world : State) (slice : Slice) (cursor : Word) (last : Option Pointer) (six seven : Slot) :
    eval f4.after (head world slice cursor last six seven) = .returned .unit (exit world) := by simp

theorem body_stop (world : State) (slice : Slice) (last : Option Pointer) (six seven : Slot) :
    eval f4.body (head world slice slice.length last six seven) = .breaking (head world slice slice.length last six seven) := by simp

theorem episode_world (world : State) (slice : Slice) (cursor : Word) (last : Option Pointer) (six seven : Slot)
    (before : cursor.val < slice.length.val) :
    (settle world (eval f4.body (head world slice cursor last six seven))).world =
      (NativeByteDropTraversal.iteration world slice cursor).world := by
  have different : (cursor == slice.length) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro same
    have := congrArg Fin.val same
    omega
  cases issued : NativeSliceLLBC.issue world true (.reference true slice.reference slice.length) .byte with
  | none => simp [different, issued, settle, NativeByteDropTraversal.iteration, NativeByteDropTraversal.Iteration.world]
  | some output =>
    rcases output with ⟨value, borrowed⟩
    have same := issue_slice_shape world borrowed slice value issued
    subst value
    cases indexed : NativeByteSliceIndex.index borrowed ⟨⟨world.nextTag⟩, slice.length⟩ cursor with
    | invalid next => simp [different, issued, indexed, before, settle, NativeByteDropTraversal.iteration, NativeByteDropTraversal.Iteration.world]
    | value child next =>
      cases recovered : NativeByteSliceIndex.rawByte next child with
      | none => simp [different, issued, indexed, recovered, before, settle, NativeByteDropTraversal.iteration, NativeByteDropTraversal.Iteration.world]
      | some pointer =>
        by_cases cleaned : (NativeReferenceCleanup.closeScope world next).pending = [] <;>
          simp [different, issued, indexed, recovered, before, cleaned, settle, settleFrame,
            NativeByteDropTraversal.iteration, NativeByteDropTraversal.Iteration.world]

theorem episode_success (world next : State) (slice : Slice) (cursor : Word) (last : Option Pointer) (six seven : Slot)
    (before : cursor.val < slice.length.val) (pointer : Pointer)
    (successful : NativeByteDropTraversal.iteration world slice cursor = .value pointer next) :
    ∃ newSix newSeven, settle world (eval f4.body (head world slice cursor last six seven)) =
      .continuing (head next slice (successor cursor) (some pointer) newSix newSeven) := by
  have different : (cursor == slice.length) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro same
    have := congrArg Fin.val same
    omega
  cases issued : NativeSliceLLBC.issue world true (.reference true slice.reference slice.length) .byte with
  | none => simp [NativeByteDropTraversal.iteration, issued] at successful
  | some output =>
    rcases output with ⟨value, borrowed⟩
    have same := issue_slice_shape world borrowed slice value issued
    subst value
    cases indexed : NativeByteSliceIndex.index borrowed ⟨⟨world.nextTag⟩, slice.length⟩ cursor with
    | invalid failed => simp [NativeByteDropTraversal.iteration, issued, indexed] at successful
    | value child indexedWorld =>
      cases recovered : NativeByteSliceIndex.rawByte indexedWorld child with
      | none => simp [NativeByteDropTraversal.iteration, issued, indexed, recovered] at successful
      | some raw =>
        by_cases cleaned : (NativeReferenceCleanup.closeScope world indexedWorld).pending = []
        · simp [NativeByteDropTraversal.iteration, issued, indexed, recovered, cleaned] at successful
          obtain ⟨pointerEq, worldEq⟩ := successful
          subst pointer
          subst next
          refine ⟨.live none, .live (some (.byteRef child)), ?_⟩
          simp [different, issued, indexed, recovered, before, cleaned, settle, settleFrame]
        · simp [NativeByteDropTraversal.iteration, issued, indexed, recovered, cleaned] at successful

theorem episode_failure (world next : State) (slice : Slice) (cursor : Word) (last : Option Pointer) (six seven : Slot)
    (before : cursor.val < slice.length.val)
    (failed : NativeByteDropTraversal.iteration world slice cursor = .invalid next) :
    ∃ frame, settle world (eval f4.body (head world slice cursor last six seven)) = .invalid frame ∧ frame.world = next := by
  have different : (cursor == slice.length) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro same
    have := congrArg Fin.val same
    omega
  cases issued : NativeSliceLLBC.issue world true (.reference true slice.reference slice.length) .byte with
  | none =>
    simp [NativeByteDropTraversal.iteration, issued] at failed
    subst next
    simp [different, issued, settle]
  | some output =>
    rcases output with ⟨value, borrowed⟩
    have same := issue_slice_shape world borrowed slice value issued
    subst value
    cases indexed : NativeByteSliceIndex.index borrowed ⟨⟨world.nextTag⟩, slice.length⟩ cursor with
    | invalid indexedWorld =>
      simp [NativeByteDropTraversal.iteration, issued, indexed] at failed
      subst next
      simp [different, issued, indexed, before, settle]
    | value child indexedWorld =>
      cases recovered : NativeByteSliceIndex.rawByte indexedWorld child with
      | none =>
        simp [NativeByteDropTraversal.iteration, issued, indexed, recovered] at failed
        subst next
        simp [different, issued, indexed, recovered, before, settle]
      | some raw =>
        by_cases cleaned : (NativeReferenceCleanup.closeScope world indexedWorld).pending = []
        · simp [NativeByteDropTraversal.iteration, issued, indexed, recovered, cleaned] at failed
        · simp [NativeByteDropTraversal.iteration, issued, indexed, recovered, cleaned] at failed
          subst next
          simp [different, issued, indexed, recovered, before, cleaned, settle, settleFrame]

def observe (flow : Flow) : State × Bool :=
  (flow.world, match flow with | .returned .unit _ => true | _ => false)

theorem loop_witness (slice : Slice) (cursor : Nat) (world : State) (last : Option Pointer)
    (result : NativeByteDropTraversal.Result)
    (ran : NativeByteDropTraversal.Executes slice cursor world last result) (bounded : cursor ≤ slice.length.val)
    (six seven : Slot) :
    ∃ flow, LoopRuns f4.body f4.after
      (head world slice ⟨cursor, Nat.lt_of_le_of_lt bounded slice.length.isLt⟩ last six seven) flow ∧
      observe flow = (result.world, result.complete) := by
  induction ran generalizing six seven with
  | stop cursor world last done =>
    subst cursor
    refine ⟨.returned .unit (exit world), ?_, rfl⟩
    exact .stop _ _ _ (body_stop world slice last six seven) (after_exact world slice slice.length last six seven)
  | fail cursor world next last before failed =>
    obtain ⟨frame, actual, same⟩ := episode_failure world next slice
      ⟨cursor, Nat.lt_trans before slice.length.isLt⟩ last six seven before failed
    refine ⟨.invalid frame, .terminal _ _ actual rfl, ?_⟩
    change (frame.world, false) = (next, false)
    rw [same]
  | next cursor world next last pointer result before actual later ih =>
    obtain ⟨newSix, newSeven, stepped⟩ := episode_success world next slice
      ⟨cursor, Nat.lt_trans before slice.length.isLt⟩ last six seven before pointer actual
    have nextWord : successor ⟨cursor, Nat.lt_trans before slice.length.isLt⟩ =
        (⟨cursor+1, Nat.lt_of_le_of_lt (Nat.succ_le_of_lt before) slice.length.isLt⟩ : Word) := by
      apply Fin.ext
      exact NativeByteDropTraversal.cursor_increment slice.length ⟨cursor, Nat.lt_trans before slice.length.isLt⟩ before
    rw [nextWord] at stepped
    obtain ⟨flow, tail, observed⟩ := ih (Nat.succ_le_of_lt before) newSix newSeven
    exact ⟨flow, .next _ _ _ stepped tail, observed⟩

theorem run_simulation (world : State) (slice : Slice) :
    ∃ flow, Executes f4 (entry world slice) flow ∧
      observe flow = ((NativeByteDropTraversal.run world slice).world, (NativeByteDropTraversal.run world slice).complete) := by
  obtain ⟨flow, loop, observed⟩ := loop_witness slice 0 world none _
    (NativeByteDropTraversal.run_executes world slice) (Nat.zero_le _) .dead .dead
  exact ⟨flow, .start _ _ _ (before_exact world slice) loop, observed⟩

theorem every_execution_agrees (world : State) (slice : Slice) (flow : Flow)
    (executed : Executes f4 (entry world slice) flow) :
    observe flow = ((NativeByteDropTraversal.run world slice).world, (NativeByteDropTraversal.run world slice).complete) := by
  obtain ⟨other, witness, observed⟩ := run_simulation world slice
  have same := executes_deterministic f4 (entry world slice) flow other executed witness
  rw [same]
  exact observed

theorem invoke_simulation (world : State) (register : Nat) (slice : Slice)
    (decoded : decodeSlice world register = some slice) :
    ∃ flow, Invokes f4 world register flow ∧
      observe flow = ((NativeByteDropTraversal.run world slice).world, (NativeByteDropTraversal.run world slice).complete) := by
  obtain ⟨flow, witness, observed⟩ := run_simulation world slice
  exact ⟨flow, .valid slice (entry world slice) flow decoded (initial_exact world slice) witness, observed⟩

theorem every_invocation_agrees (world : State) (register : Nat) (slice : Slice) (flow : Flow)
    (decoded : decodeSlice world register = some slice) (invoked : Invokes f4 world register flow) :
    observe flow = ((NativeByteDropTraversal.run world slice).world, (NativeByteDropTraversal.run world slice).complete) := by
  cases invoked with
  | invalid missing => rw [decoded] at missing; cases missing
  | malformed other found rejected =>
    have same := Option.some.inj (decoded.symm.trans found)
    subst other
    rw [initial_exact] at rejected
    cases rejected
  | valid other frame flow found initialized executed =>
    have same := Option.some.inj (decoded.symm.trans found)
    subst other
    have frameSame := Option.some.inj ((initial_exact world slice).symm.trans initialized)
    subst frame
    exact every_execution_agrees world slice flow executed

theorem invocation_heap_frame (world : State) (register : Nat) (slice : Slice) (flow : Flow)
    (decoded : decodeSlice world register = some slice) (invoked : Invokes f4 world register flow) :
    flow.world.pointers.heap = world.pointers.heap := by
  have same := congrArg Prod.fst (every_invocation_agrees world register slice flow decoded invoked)
  change flow.world = (NativeByteDropTraversal.run world slice).world at same
  rw [same]
  exact NativeByteDropTraversal.run_heap_frame world slice

theorem invocation_returns_unit (world : State) (register : Nat) (slice : Slice) (flow : Flow)
    (decoded : decodeSlice world register = some slice) (invoked : Invokes f4 world register flow)
    (complete : (NativeByteDropTraversal.run world slice).complete = true) :
    ∃ frame, flow = .returned .unit frame := by
  have flag := congrArg Prod.snd (every_invocation_agrees world register slice flow decoded invoked)
  change (observe flow).2 = (NativeByteDropTraversal.run world slice).complete at flag
  rw [complete] at flag
  cases flow with
  | returned value frame =>
    cases value <;> cases flag
    exact ⟨frame,rfl⟩
  | normal frame => cases flag
  | unwind frame => cases flag
  | invalid frame => cases flag
  | breaking frame => cases flag
  | continuing frame => cases flag

end HasteBootsByteLoopBody
