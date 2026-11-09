namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

theorem handled_continue_projects (next : Frame → Flow)
    (projects : ∀ frame, NativeStorageBorrowMachine.Runs frame.world (next frame).world) (flow : Flow) :
    NativeStorageBorrowMachine.Runs flow.world (handledContinue next flow).world := by
  cases flow with
  | normal frame => exact projects frame
  | returned value world => exact .refl _
  | invalid world => exact .refl _
  | unwind world => exact .refl _
  | unsupported source world => exact .refl _

theorem handled_resume_projects (caller : Frame) (target : Nat) (unwind next : Frame → Flow)
    (unwindProjects : ∀ frame, NativeStorageBorrowMachine.Runs frame.world (unwind frame).world)
    (nextProjects : ∀ frame, NativeStorageBorrowMachine.Runs frame.world (next frame).world) (flow : Flow) :
    NativeStorageBorrowMachine.Runs flow.world (handledResume caller target unwind next flow).world := by
  cases flow with
  | normal changed => exact .refl _
  | invalid world => exact .refl _
  | unsupported source world => exact .refl _
  | unwind world => exact unwindProjects {caller with world}
  | returned value world =>
    cases written : write {caller with world} target value with
    | none => simp only [handledResume,written,Flow.world]; exact .refl _
    | some changed =>
      have later := nextProjects changed
      rw [write_world {caller with world} changed target value written] at later
      simpa only [handledResume,written,Flow.world] using later

theorem handled_call_projects (types : List NativeRecordValues.Ty) (argCount target : Nat) (args : List Operand)
    (callee unwind next : Frame → Flow)
    (calleeProjects : ∀ frame, NativeStorageBorrowMachine.Runs frame.world (callee frame).world)
    (unwindProjects : ∀ frame, NativeStorageBorrowMachine.Runs frame.world (unwind frame).world)
    (nextProjects : ∀ frame, NativeStorageBorrowMachine.Runs frame.world (next frame).world) (frame : Frame) :
    NativeStorageBorrowMachine.Runs frame.world (handledCall types argCount target args callee unwind next frame).world := by
  cases arguments : evalArgs frame args with
  | none => simp only [handledCall,arguments,Flow.world]; exact .refl _
  | some pair =>
    rcases pair with ⟨values,caller⟩
    have callerWorld := evalArgs_world frame caller args values arguments
    cases initialized : initial types argCount values caller.world with
    | none =>
      simp only [handledCall,arguments,initialized,Flow.world]
      rw [callerWorld]
      exact .refl _
    | some entered =>
      have enteredWorld := (initial_world types argCount values caller.world entered initialized).trans callerWorld
      have returned := NativeStorageBorrowMachine.runs_trans _ _ _ (calleeProjects entered)
        (NativeStorageBorrowMachine.legacy_runs _ _ (settle_projects entered.world (callee entered)))
      have resumed := handled_resume_projects caller target unwind next unwindProjects nextProjects
        (settle entered.world (callee entered))
      have run := NativeStorageBorrowMachine.runs_trans _ _ _ returned resumed
      rw [enteredWorld] at run
      simpa only [handledCall,arguments,initialized,enteredWorld] using run

theorem handled_invoke_projects (types : List NativeRecordValues.Ty) (argCount : Nat) (body : Frame → Flow)
    (projects : ∀ frame, NativeStorageBorrowMachine.Runs frame.world (body frame).world)
    (world : NativeReferenceMachine.State) (values : List NativeRecordValues.Value) :
    NativeStorageBorrowMachine.Runs world (handledInvoke types argCount body world values).world := by
  cases initialized : initial types argCount values world with
  | none => simp only [handledInvoke,initialized,Flow.world]; exact .refl _
  | some entered =>
    have run := NativeStorageBorrowMachine.runs_trans _ _ _ (projects entered)
      (NativeStorageBorrowMachine.legacy_runs _ _ (settle_projects entered.world (body entered)))
    have same := initial_world types argCount values world entered initialized
    rw [same] at run
    simpa only [handledInvoke,initialized,same] using run

theorem outer_error_projects (base : NativePointerStorage.Address) (overflow allocation : Body) (frame : Frame) :
    NativeStorageBorrowMachine.Runs frame.world (outerErrorEval base overflow allocation frame).world := by
  exact NativeStorageBorrowMachine.runs_trans _ _ _
    (NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects outerErrorPrefix frame))
    (handled_continue_projects _ (handled_call_projects _ _ _ _ _ _ _
      (handlerEval_projects base overflow allocation)
      (fun frame => NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects _ frame))
      (fun frame => NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects _ frame))) _)

theorem handled_raw_tail_projects (base : NativePointerStorage.Address) (overflow allocation cold : Body) (frame : Frame) :
    NativeStorageBorrowMachine.Runs frame.world (handledRawTail base overflow allocation cold frame).world := by
  cases selected : selectChoice frame 4 [] 8 with
  | none => simp only [handledRawTail,selected,Flow.world]; exact .refl _
  | some side =>
    have branch : NativeStorageBorrowMachine.Runs frame.world
        (if side then outerErrorEval base overflow allocation frame else .normal frame).world := by
      cases side
      · exact .refl _
      · exact outer_error_projects base overflow allocation frame
    have run := NativeStorageBorrowMachine.runs_trans _ _ _ branch
      (handled_continue_projects (eval (rawSuccessTail cold))
        (fun frame => NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects (rawSuccessTail cold) frame)) _)
    simpa only [handledRawTail,selected] using run

theorem handled_raw_eval_projects (ambient : Frame) (base : NativePointerStorage.Address) (address : NativeWord64Memory.Word)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) (overflow allocation : Body) (frame : Frame) :
    NativeStorageBorrowMachine.Runs frame.world (handledRawEval ambient base address outcome shim overflow allocation frame).world :=
  NativeStorageBorrowMachine.runs_trans _ _ _
    (NativeStorageBorrowMachine.legacy_runs _ _ (NativeAllocatorLLBC.eval_projects _ frame))
    (handled_continue_projects _ (handled_raw_tail_projects base overflow allocation _) _)

theorem handled_vec_eval_projects (ambient : Frame) (base : NativePointerStorage.Address) (address : NativeWord64Memory.Word)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) (overflow allocation : Body) (frame : Frame) :
    NativeStorageBorrowMachine.Runs frame.world (handledVecEval ambient base address outcome shim overflow allocation frame).world :=
  NativeStorageBorrowMachine.runs_trans _ _ _
    (NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects _ frame))
    (handled_continue_projects _ (handled_call_projects _ _ _ _ _ _ _
      (handled_raw_eval_projects _ base address outcome shim overflow allocation)
      (fun frame => NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects _ frame))
      (fun frame => NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects _ frame))) _)

theorem handled_root_eval_projects (ambient : Frame) (base : NativePointerStorage.Address) (address : NativeWord64Memory.Word)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) (overflow allocation : Body) (frame : Frame) :
    NativeStorageBorrowMachine.Runs frame.world (handledRootEval ambient base address outcome shim overflow allocation frame).world :=
  NativeStorageBorrowMachine.runs_trans _ _ _
    (NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects _ frame))
    (handled_continue_projects _ (handled_call_projects _ _ _ _ _ _ _
      (handled_vec_eval_projects _ base address outcome shim overflow allocation)
      (fun frame => NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects _ frame))
      (fun frame => NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects _ frame))) _)

theorem handled_root_invoke_projects (world : NativeReferenceMachine.State) (base : NativePointerStorage.Address)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body)
    (overflow allocation : Body) (capacity : NativeWord64Memory.Word) :
    NativeStorageBorrowMachine.Runs world (handledRootInvoke world base address outcome shim overflow allocation capacity).world := by
  unfold handledRootInvoke
  exact handled_invoke_projects (capacityRootTypes (handledAmbient world)) 1
    (handledRootEval (handledAmbient world) base address outcome shim overflow allocation)
    (handled_root_eval_projects (handledAmbient world) base address outcome shim overflow allocation) world [.scalar (.usize capacity)]

theorem handled_root_reachable (world : NativeReferenceMachine.State) (base : NativePointerStorage.Address)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body)
    (overflow allocation : Body) (capacity : NativeWord64Memory.Word) (reachable : NativeStorageBorrowMachine.Reachable world) :
    NativeStorageBorrowMachine.Reachable (handledRootInvoke world base address outcome shim overflow allocation capacity).world :=
  NativeStorageBorrowMachine.runs_trans _ _ _ reachable
    (handled_root_invoke_projects world base address outcome shim overflow allocation capacity)

theorem handled_root_wellFormed (world : NativeReferenceMachine.State) (base : NativePointerStorage.Address)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body)
    (overflow allocation : Body) (capacity : NativeWord64Memory.Word) (valid : NativeReferenceMachine.WellFormed world) :
    NativeReferenceMachine.WellFormed (handledRootInvoke world base address outcome shim overflow allocation capacity).world :=
  NativeStorageBorrowMachine.runs_wellFormed _ _ valid
    (handled_root_invoke_projects world base address outcome shim overflow allocation capacity)

end HasteBootsVecCapacityArithmetic
