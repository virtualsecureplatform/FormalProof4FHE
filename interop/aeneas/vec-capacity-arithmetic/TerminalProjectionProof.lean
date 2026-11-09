namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

theorem terminal_panic_projects (panic : String → NativeReferenceMachine.State → Flow)
    (projects : ∀ name world, NativeStorageBorrowMachine.Runs world (panic name world).world) (frame : Frame) :
    NativeStorageBorrowMachine.Runs frame.world (terminalPanicEval panic frame).world := by
  have run := projects "core::panicking::panic_fmt" frame.world
  cases actual : panic "core::panicking::panic_fmt" frame.world <;>
    simpa only [terminalPanicEval,actual,Flow.world] using run

theorem terminal_format_projects (target : Nat) (cleanup : Body → Body) (text : String)
    (formatter panic : String → NativeReferenceMachine.State → Flow)
    (formatterProjects : ∀ text world, NativeStorageBorrowMachine.Runs world (formatter text world).world)
    (panicProjects : ∀ name world, NativeStorageBorrowMachine.Runs world (panic name world).world) (frame : Frame) :
    NativeStorageBorrowMachine.Runs frame.world (terminalFormatEval target cleanup text formatter panic frame).world := by
  unfold terminalFormatEval
  apply NativeStorageBorrowMachine.runs_trans _ _ _ (formatterProjects text frame.world)
  apply handled_resume_projects
  · intro caller
    exact NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects (cleanup .resume) caller)
  · intro changed
    exact NativeStorageBorrowMachine.runs_trans _ _ _
      (NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects (cleanup .done) changed))
      (handled_continue_projects (terminalPanicEval panic) (terminal_panic_projects panic panicProjects) _)

theorem terminal_overflow_projects (formatter panic : String → NativeReferenceMachine.State → Flow)
    (formatterProjects : ∀ text world, NativeStorageBorrowMachine.Runs world (formatter text world).world)
    (panicProjects : ∀ name world, NativeStorageBorrowMachine.Runs world (panic name world).world) (frame : Frame) :
    NativeStorageBorrowMachine.Runs frame.world (terminalOverflowEval formatter panic frame).world := by
  unfold terminalOverflowEval
  exact NativeStorageBorrowMachine.runs_trans _ _ _
    (NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects terminalOverflowPrefix frame))
    (handled_continue_projects _ (terminal_format_projects 1 (Body.dead 1) "capacity overflow"
      formatter panic formatterProjects panicProjects) _)

theorem terminal_ct_projects (formatter panic : String → NativeReferenceMachine.State → Flow)
    (formatterProjects : ∀ text world, NativeStorageBorrowMachine.Runs world (formatter text world).world)
    (panicProjects : ∀ name world, NativeStorageBorrowMachine.Runs world (panic name world).world) (frame : Frame) :
    NativeStorageBorrowMachine.Runs frame.world (terminalCtEval formatter panic frame).world := by
  unfold terminalCtEval
  exact NativeStorageBorrowMachine.runs_trans _ _ _
    (NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects terminalCtPrefix frame))
    (handled_continue_projects _ (terminal_format_projects 2 terminalCtCleanup "allocation failed"
      formatter panic formatterProjects panicProjects) _)

theorem terminal_allocation_projects (fields : NativeRecordValues.Ty) (formatter panic : String → NativeReferenceMachine.State → Flow)
    (formatterProjects : ∀ text world, NativeStorageBorrowMachine.Runs world (formatter text world).world)
    (panicProjects : ∀ name world, NativeStorageBorrowMachine.Runs world (panic name world).world) (frame : Frame) :
    NativeStorageBorrowMachine.Runs frame.world (terminalAllocationEval fields formatter panic frame).world := by
  unfold terminalAllocationEval
  exact NativeStorageBorrowMachine.runs_trans _ _ _
    (NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects terminalAllocationPrefix frame))
    (handled_continue_projects _ (handled_call_projects (terminalCtTypes fields) 1 0 [(.move 2 [.left])]
      (terminalCtEval formatter panic) (eval (terminalCtCleanup .resume)) (eval (terminalCtCleanup .abort))
      (terminal_ct_projects formatter panic formatterProjects panicProjects)
      (fun caller => NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects (terminalCtCleanup .resume) caller))
      (fun caller => NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects (terminalCtCleanup .abort) caller))) _)

theorem terminal_overflow_invoke_projects (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow)
    (formatterProjects : ∀ text world, NativeStorageBorrowMachine.Runs world (formatter text world).world)
    (panicProjects : ∀ name world, NativeStorageBorrowMachine.Runs world (panic name world).world)
    (world : NativeReferenceMachine.State) :
    NativeStorageBorrowMachine.Runs world (terminalOverflowInvoke fields formatter panic world).world := by
  unfold terminalOverflowInvoke
  exact handled_invoke_projects (terminalOverflowTypes fields) 0 (terminalOverflowEval formatter panic)
    (terminal_overflow_projects formatter panic formatterProjects panicProjects) world []

theorem terminal_allocation_invoke_projects (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow)
    (formatterProjects : ∀ text world, NativeStorageBorrowMachine.Runs world (formatter text world).world)
    (panicProjects : ∀ name world, NativeStorageBorrowMachine.Runs world (panic name world).world)
    (world : NativeReferenceMachine.State) (layout : NativeRecordValues.Value) :
    NativeStorageBorrowMachine.Runs world (terminalAllocationInvoke fields formatter panic world layout).world := by
  unfold terminalAllocationInvoke
  exact handled_invoke_projects terminalAllocationTypes 1 (terminalAllocationEval fields formatter panic)
    (terminal_allocation_projects fields formatter panic formatterProjects panicProjects) world [layout]

theorem terminal_overflow_reachable (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow)
    (formatterProjects : ∀ text world, NativeStorageBorrowMachine.Runs world (formatter text world).world)
    (panicProjects : ∀ name world, NativeStorageBorrowMachine.Runs world (panic name world).world)
    (world : NativeReferenceMachine.State) (reachable : NativeStorageBorrowMachine.Reachable world) :
    NativeStorageBorrowMachine.Reachable (terminalOverflowInvoke fields formatter panic world).world :=
  NativeStorageBorrowMachine.runs_trans _ _ _ reachable
    (terminal_overflow_invoke_projects fields formatter panic formatterProjects panicProjects world)

theorem terminal_allocation_reachable (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow)
    (formatterProjects : ∀ text world, NativeStorageBorrowMachine.Runs world (formatter text world).world)
    (panicProjects : ∀ name world, NativeStorageBorrowMachine.Runs world (panic name world).world)
    (world : NativeReferenceMachine.State) (layout : NativeRecordValues.Value) (reachable : NativeStorageBorrowMachine.Reachable world) :
    NativeStorageBorrowMachine.Reachable (terminalAllocationInvoke fields formatter panic world layout).world :=
  NativeStorageBorrowMachine.runs_trans _ _ _ reachable
    (terminal_allocation_invoke_projects fields formatter panic formatterProjects panicProjects world layout)

theorem terminal_overflow_wellFormed (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow)
    (formatterProjects : ∀ text world, NativeStorageBorrowMachine.Runs world (formatter text world).world)
    (panicProjects : ∀ name world, NativeStorageBorrowMachine.Runs world (panic name world).world)
    (world : NativeReferenceMachine.State) (valid : NativeReferenceMachine.WellFormed world) :
    NativeReferenceMachine.WellFormed (terminalOverflowInvoke fields formatter panic world).world :=
  NativeStorageBorrowMachine.runs_wellFormed _ _ valid
    (terminal_overflow_invoke_projects fields formatter panic formatterProjects panicProjects world)

theorem terminal_allocation_wellFormed (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow)
    (formatterProjects : ∀ text world, NativeStorageBorrowMachine.Runs world (formatter text world).world)
    (panicProjects : ∀ name world, NativeStorageBorrowMachine.Runs world (panic name world).world)
    (world : NativeReferenceMachine.State) (layout : NativeRecordValues.Value) (valid : NativeReferenceMachine.WellFormed world) :
    NativeReferenceMachine.WellFormed (terminalAllocationInvoke fields formatter panic world layout).world :=
  NativeStorageBorrowMachine.runs_wellFormed _ _ valid
    (terminal_allocation_invoke_projects fields formatter panic formatterProjects panicProjects world layout)

end HasteBootsVecCapacityArithmetic
