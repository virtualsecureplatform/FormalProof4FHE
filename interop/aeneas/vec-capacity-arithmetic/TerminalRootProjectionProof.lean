namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

theorem effect_handler_eval_projects (base : NativePointerStorage.Address) (tail : Frame → Flow) (tailProjects : ∀ frame, NativeStorageBorrowMachine.Runs frame.world (tail frame).world) (frame : Frame) :
    NativeStorageBorrowMachine.Runs frame.world (effectHandlerEval base tail frame).world := by
  have first := NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects handlerPrefix frame)
  cases prefixed : eval handlerPrefix frame with
  | returned value world => simpa only [effectHandlerEval,prefixed] using first
  | unwind world => simpa only [effectHandlerEval,prefixed] using first
  | invalid world => simpa only [effectHandlerEval,prefixed] using first
  | unsupported source world => simpa only [effectHandlerEval,prefixed] using first
  | normal prepared =>
    simp only [prefixed,Flow.world] at first
    have later := NativeReservationErrorLocal.snapshotLocal_projects reservationErrorTags prepared 1 base
    cases issued : NativeReservationErrorLocal.snapshotLocal reservationErrorTags prepared 1 base with
    | invalid world =>
      simp only [issued,NativeRawVecFields.Result.world] at later
      simpa only [effectHandlerEval,prefixed,issued,Flow.world] using NativeStorageBorrowMachine.runs_trans _ _ _ first later
    | value reference world =>
      simp only [issued,NativeRawVecFields.Result.world] at later
      have entered := NativeStorageBorrowMachine.runs_trans _ _ _ first later
      cases written : write {prepared with world} 3 reference with
      | none => simpa only [effectHandlerEval,prefixed,issued,written,Flow.world] using entered
      | some borrowed =>
        have sameBorrowed := write_world {prepared with world} borrowed 3 reference written
        cases arguments : evalArgs borrowed [.move 3 []] with
        | none => simpa only [effectHandlerEval,prefixed,issued,written,arguments,Flow.world,sameBorrowed] using entered
        | some entry =>
          rcases entry with ⟨values,caller⟩
          have sameCaller := (evalArgs_world borrowed caller [.move 3 []] values arguments).trans sameBorrowed
          cases values with
          | nil => simpa only [effectHandlerEval,prefixed,issued,written,arguments,Flow.world,sameCaller] using entered
          | cons argument rest =>
            cases rest with
            | nil =>
              have called := NativeStorageBorrowMachine.runs_trans _ _ _
                (HasteBootsReservationErrorKind.invoke_projects_for reservationErrorTags caller.world argument)
                (handled_resume_projects caller 2 (eval (handlerCleanup .resume)) tail
                  (fun next => NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects (handlerCleanup .resume) next)) tailProjects
                  (HasteBootsReservationErrorKind.invokeFor reservationErrorTags caller.world argument))
              have enteredCaller : NativeStorageBorrowMachine.Runs frame.world caller.world := by rw [sameCaller]; exact entered
              simpa only [effectHandlerEval,prefixed,issued,written,arguments] using NativeStorageBorrowMachine.runs_trans _ _ _ enteredCaller called
            | cons next tail => simpa only [effectHandlerEval,prefixed,issued,written,arguments,Flow.world,sameCaller] using entered

theorem effect_outer_projects (base : NativePointerStorage.Address) (handler : NativePointerStorage.Address → Frame → Flow)
    (handlerProjects : ∀ placement frame, NativeStorageBorrowMachine.Runs frame.world (handler placement frame).world) (frame : Frame) :
    NativeStorageBorrowMachine.Runs frame.world (effectOuterErrorEval base handler frame).world := by
  exact NativeStorageBorrowMachine.runs_trans _ _ _
    (NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects outerErrorPrefix frame))
    (handled_continue_projects _ (handled_call_projects _ _ _ _ _ _ _
      (handlerProjects base)
      (fun frame => NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects _ frame))
      (fun frame => NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects _ frame))) _)

theorem effect_raw_tail_projects (base : NativePointerStorage.Address) (handler : NativePointerStorage.Address → Frame → Flow)
    (handlerProjects : ∀ placement frame, NativeStorageBorrowMachine.Runs frame.world (handler placement frame).world) (cold : Body) (frame : Frame) :
    NativeStorageBorrowMachine.Runs frame.world (effectRawTail base handler cold frame).world := by
  cases selected : selectChoice frame 4 [] 8 with
  | none => simp only [effectRawTail,selected,Flow.world]; exact .refl _
  | some side =>
    have branch : NativeStorageBorrowMachine.Runs frame.world
        (if side then effectOuterErrorEval base handler frame else .normal frame).world := by
      cases side
      · exact .refl _
      · exact effect_outer_projects base handler handlerProjects frame
    have run := NativeStorageBorrowMachine.runs_trans _ _ _ branch
      (handled_continue_projects (eval (rawSuccessTail cold))
        (fun frame => NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects (rawSuccessTail cold) frame)) _)
    simpa only [effectRawTail,selected] using run

theorem effect_raw_eval_projects (ambient : Frame) (base : NativePointerStorage.Address) (address : NativeWord64Memory.Word)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) (handler : NativePointerStorage.Address → Frame → Flow)
    (handlerProjects : ∀ placement frame, NativeStorageBorrowMachine.Runs frame.world (handler placement frame).world) (frame : Frame) :
    NativeStorageBorrowMachine.Runs frame.world (effectRawEval ambient base address outcome shim handler frame).world :=
  NativeStorageBorrowMachine.runs_trans _ _ _
    (NativeStorageBorrowMachine.legacy_runs _ _ (NativeAllocatorLLBC.eval_projects _ frame))
    (handled_continue_projects _ (effect_raw_tail_projects base handler handlerProjects _) _)

theorem effect_vec_eval_projects (ambient : Frame) (base : NativePointerStorage.Address) (address : NativeWord64Memory.Word)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) (handler : NativePointerStorage.Address → Frame → Flow)
    (handlerProjects : ∀ placement frame, NativeStorageBorrowMachine.Runs frame.world (handler placement frame).world) (frame : Frame) :
    NativeStorageBorrowMachine.Runs frame.world (effectVecEval ambient base address outcome shim handler frame).world :=
  NativeStorageBorrowMachine.runs_trans _ _ _
    (NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects _ frame))
    (handled_continue_projects _ (handled_call_projects _ _ _ _ _ _ _
      (effect_raw_eval_projects _ base address outcome shim handler handlerProjects)
      (fun frame => NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects _ frame))
      (fun frame => NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects _ frame))) _)

theorem effect_root_eval_projects (ambient : Frame) (base : NativePointerStorage.Address) (address : NativeWord64Memory.Word)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) (handler : NativePointerStorage.Address → Frame → Flow)
    (handlerProjects : ∀ placement frame, NativeStorageBorrowMachine.Runs frame.world (handler placement frame).world) (frame : Frame) :
    NativeStorageBorrowMachine.Runs frame.world (effectRootEval ambient base address outcome shim handler frame).world :=
  NativeStorageBorrowMachine.runs_trans _ _ _
    (NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects _ frame))
    (handled_continue_projects _ (handled_call_projects _ _ _ _ _ _ _
      (effect_vec_eval_projects _ base address outcome shim handler handlerProjects)
      (fun frame => NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects _ frame))
      (fun frame => NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects _ frame))) _)

theorem effect_root_invoke_projects (world : NativeReferenceMachine.State) (base : NativePointerStorage.Address)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body)
    (handler : NativePointerStorage.Address → Frame → Flow)
    (handlerProjects : ∀ placement frame, NativeStorageBorrowMachine.Runs frame.world (handler placement frame).world) (capacity : NativeWord64Memory.Word) :
    NativeStorageBorrowMachine.Runs world (effectRootInvoke world base address outcome shim handler capacity).world := by
  unfold effectRootInvoke
  exact handled_invoke_projects (capacityRootTypes (handledAmbient world)) 1
    (effectRootEval (handledAmbient world) base address outcome shim handler)
    (effect_root_eval_projects (handledAmbient world) base address outcome shim handler handlerProjects) world [.scalar (.usize capacity)]


theorem terminal_handler_overflow_projects (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow)
    (formatterProjects : ∀ text world, NativeStorageBorrowMachine.Runs world (formatter text world).world)
    (panicProjects : ∀ name world, NativeStorageBorrowMachine.Runs world (panic name world).world) (frame : Frame) :
    NativeStorageBorrowMachine.Runs frame.world (terminalHandlerOverflowCall fields formatter panic frame).world := by
  unfold terminalHandlerOverflowCall
  exact handled_call_projects (terminalOverflowTypes fields) 0 0 [] (terminalOverflowEval formatter panic)
    (eval (handlerCleanup .resume)) (eval (handlerCleanup .abort))
    (terminal_overflow_projects formatter panic formatterProjects panicProjects)
    (fun caller => NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects (handlerCleanup .resume) caller))
    (fun caller => NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects (handlerCleanup .abort) caller)) frame

theorem terminal_handler_allocation_projects (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow)
    (formatterProjects : ∀ text world, NativeStorageBorrowMachine.Runs world (formatter text world).world)
    (panicProjects : ∀ name world, NativeStorageBorrowMachine.Runs world (panic name world).world) (frame : Frame) :
    NativeStorageBorrowMachine.Runs frame.world (terminalHandlerAllocationCall fields formatter panic frame).world := by
  unfold terminalHandlerAllocationCall
  exact handled_call_projects terminalAllocationTypes 1 0 [(.move 5 [])] (terminalAllocationEval fields formatter panic)
    (eval (handlerCleanup .resume)) (eval (handlerCleanup .abort))
    (terminal_allocation_projects fields formatter panic formatterProjects panicProjects)
    (fun caller => NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects (handlerCleanup .resume) caller))
    (fun caller => NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects (handlerCleanup .abort) caller)) frame

theorem terminal_handler_tail_projects (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow)
    (formatterProjects : ∀ text world, NativeStorageBorrowMachine.Runs world (formatter text world).world)
    (panicProjects : ∀ name world, NativeStorageBorrowMachine.Runs world (panic name world).world) (frame : Frame) :
    NativeStorageBorrowMachine.Runs frame.world (terminalHandlerTail fields formatter panic frame).world := by
  unfold terminalHandlerTail
  apply NativeStorageBorrowMachine.runs_trans _ _ _ (NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects _ frame))
  apply handled_continue_projects
  intro caller
  cases selected : selectChoice caller 2 [] 18 with
  | none => simp only [Flow.world]; exact .refl _
  | some side =>
    have branch : NativeStorageBorrowMachine.Runs caller.world
        (if side then handledContinue (terminalHandlerAllocationCall fields formatter panic)
          (eval (handlerAllocationPrefix .done) caller) else .normal caller).world := by
      cases side
      · exact .refl _
      · exact NativeStorageBorrowMachine.runs_trans _ _ _
          (NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects (handlerAllocationPrefix .done) caller))
          (handled_continue_projects _ (terminal_handler_allocation_projects fields formatter panic formatterProjects panicProjects) _)
    have run := NativeStorageBorrowMachine.runs_trans _ _ _ branch
      (handled_continue_projects _ (terminal_handler_overflow_projects fields formatter panic formatterProjects panicProjects) _)
    simpa only [selected] using run

theorem terminal_handler_eval_projects (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow)
    (formatterProjects : ∀ text world, NativeStorageBorrowMachine.Runs world (formatter text world).world)
    (panicProjects : ∀ name world, NativeStorageBorrowMachine.Runs world (panic name world).world)
    (base : NativePointerStorage.Address) (frame : Frame) :
    NativeStorageBorrowMachine.Runs frame.world (effectHandlerEval base (terminalHandlerTail fields formatter panic) frame).world :=
  effect_handler_eval_projects base _ (terminal_handler_tail_projects fields formatter panic formatterProjects panicProjects) frame

theorem terminal_root_projects (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow)
    (formatterProjects : ∀ text world, NativeStorageBorrowMachine.Runs world (formatter text world).world)
    (panicProjects : ∀ name world, NativeStorageBorrowMachine.Runs world (panic name world).world)
    (world : NativeReferenceMachine.State) (base : NativePointerStorage.Address) (address : NativeWord64Memory.Word)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) (capacity : NativeWord64Memory.Word) :
    NativeStorageBorrowMachine.Runs world (terminalRootInvoke fields formatter panic world base address outcome shim capacity).world := by
  unfold terminalRootInvoke
  exact effect_root_invoke_projects world base address outcome shim _
    (terminal_handler_eval_projects fields formatter panic formatterProjects panicProjects) capacity

theorem terminal_root_reachable (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow)
    (formatterProjects : ∀ text world, NativeStorageBorrowMachine.Runs world (formatter text world).world)
    (panicProjects : ∀ name world, NativeStorageBorrowMachine.Runs world (panic name world).world)
    (world : NativeReferenceMachine.State) (base : NativePointerStorage.Address) (address : NativeWord64Memory.Word)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) (capacity : NativeWord64Memory.Word)
    (reachable : NativeStorageBorrowMachine.Reachable world) :
    NativeStorageBorrowMachine.Reachable (terminalRootInvoke fields formatter panic world base address outcome shim capacity).world :=
  NativeStorageBorrowMachine.runs_trans _ _ _ reachable
    (terminal_root_projects fields formatter panic formatterProjects panicProjects world base address outcome shim capacity)

theorem terminal_root_wellFormed (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow)
    (formatterProjects : ∀ text world, NativeStorageBorrowMachine.Runs world (formatter text world).world)
    (panicProjects : ∀ name world, NativeStorageBorrowMachine.Runs world (panic name world).world)
    (world : NativeReferenceMachine.State) (base : NativePointerStorage.Address) (address : NativeWord64Memory.Word)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) (capacity : NativeWord64Memory.Word)
    (valid : NativeReferenceMachine.WellFormed world) :
    NativeReferenceMachine.WellFormed (terminalRootInvoke fields formatter panic world base address outcome shim capacity).world :=
  NativeStorageBorrowMachine.runs_wellFormed _ _ valid
    (terminal_root_projects fields formatter panic formatterProjects panicProjects world base address outcome shim capacity)

end HasteBootsVecCapacityArithmetic
