namespace HasteBootsReservationErrorKind
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC
open NativeReferenceMachine (State)

theorem live_world (index : Nat) (next : Body) (kept : ∀ frame, (eval next frame).world = frame.world) (frame : Frame) :
    (eval (.live index next) frame).world = frame.world := by
  cases actual : storageLive frame index with
  | none => simp only [eval,actual,Flow.world]
  | some changed =>
    simpa only [eval,actual,kept changed] using storageLive_world frame changed index actual

theorem dead_world (index : Nat) (next : Body) (kept : ∀ frame, (eval next frame).world = frame.world) (frame : Frame) :
    (eval (.dead index next) frame).world = frame.world := by
  cases actual : storageDead frame index with
  | none => simp only [eval,actual,Flow.world]
  | some changed =>
    simpa only [eval,actual,kept changed] using storageDead_world frame changed index actual

theorem ret_world (frame : Frame) : (eval .ret frame).world = frame.world := by
  cases actual : NativeRecordLLBC.read frame 0 [] <;> simp only [eval,actual,Flow.world]

theorem rootPrefix_world (frame : Frame) : (eval rootPrefix frame).world = frame.world :=
  live_world 0 _ (fun changed => live_world 2 .done (fun _ => rfl) changed) frame

theorem rootTail_world (frame : Frame) : (eval rootTail frame).world = frame.world :=
  dead_world 2 _ (fun changed => dead_world 1 .ret ret_world changed) frame

theorem rootUnwind_world (frame : Frame) : (eval rootUnwind frame).world = frame.world :=
  dead_world 1 .resume (fun _ => rfl) frame

theorem rootResume_heap_projects (caller : Frame) (flow : Flow) :
    NativeHeapFrame.Runs flow.world (rootResume caller flow).world := by
  cases flow with
  | normal changed => exact .refl _
  | invalid world => exact .refl _
  | unsupported source world => exact .refl _
  | unwind world => exact ⟨congrArg (fun state : State => state.pointers.heap) (rootUnwind_world {caller with world})⟩
  | returned value world =>
    cases written : write {caller with world} 0 value with
    | none => simp only [rootResume,written,Flow.world]; exact .refl _
    | some changed =>
      have projected := (show NativeHeapFrame.Runs changed.world (eval rootTail changed).world from ⟨congrArg (fun state : State => state.pointers.heap) (rootTail_world changed)⟩)
      rw [write_world {caller with world} changed 0 value written] at projected
      simpa only [rootResume,written,Flow.world] using projected

theorem rootEval_heap_projects (frame : Frame) : NativeHeapFrame.Runs frame.world (rootEval frame).world := by
  have first := (show NativeHeapFrame.Runs frame.world (eval rootPrefix frame).world from ⟨congrArg (fun state : State => state.pointers.heap) (rootPrefix_world frame)⟩)
  cases prefixed : eval rootPrefix frame with
  | returned value world => simpa only [rootEval,prefixed] using first
  | unwind world => simpa only [rootEval,prefixed] using first
  | invalid world => simpa only [rootEval,prefixed] using first
  | unsupported source world => simpa only [rootEval,prefixed] using first
  | normal prepared =>
    simp only [prefixed,Flow.world] at first
    cases selected : NativeRecordLLBC.read prepared 1 [] with
    | none => simpa only [rootEval,prefixed,selected,Flow.world] using first
    | some value =>
      have later := (show NativeHeapFrame.Runs prepared.world (reborrow prepared.world value).world from ⟨reborrow_heap prepared.world value⟩)
      cases issued : reborrow prepared.world value with
      | invalid world =>
        simp only [issued,NativeRawVecFields.Result.world] at later
        simpa only [rootEval,prefixed,selected,issued,Flow.world] using NativeHeapFrame.runs_trans _ _ _ first later
      | value reference world =>
        simp only [issued,NativeRawVecFields.Result.world] at later
        have entered := NativeHeapFrame.runs_trans _ _ _ first later
        cases written : write {prepared with world} 2 reference with
        | none => simpa only [rootEval,prefixed,selected,issued,written,Flow.world] using entered
        | some borrowed =>
          have sameBorrowed := write_world {prepared with world} borrowed 2 reference written
          cases arguments : evalArgs borrowed [.move 2 []] with
          | none => simpa only [rootEval,prefixed,selected,issued,written,arguments,Flow.world,sameBorrowed] using entered
          | some entry =>
            rcases entry with ⟨values,caller⟩
            have sameCaller := (evalArgs_world borrowed caller [.move 2 []] values arguments).trans sameBorrowed
            cases values with
            | nil => simpa only [rootEval,prefixed,selected,issued,written,arguments,Flow.world,sameCaller] using entered
            | cons argument rest =>
              cases rest with
              | nil =>
                have called := NativeHeapFrame.runs_trans _ _ _ (show NativeHeapFrame.Runs caller.world (invoke caller.world argument).world from ⟨invoke_heap caller.world argument⟩)
                  (rootResume_heap_projects caller (invoke caller.world argument))
                have enteredCaller : NativeHeapFrame.Runs frame.world caller.world := by rw [sameCaller]; exact entered
                simpa only [rootEval,prefixed,selected,issued,written,arguments] using NativeHeapFrame.runs_trans _ _ _ enteredCaller called
              | cons next tail => simpa only [rootEval,prefixed,selected,issued,written,arguments,Flow.world,sameCaller] using entered

theorem rootInvoke_heap_projects (world : State) (value : NativeRecordValues.Value) :
    NativeHeapFrame.Runs world (rootInvoke world value).world := by
  cases initialized : initial rootTypes 1 [value] world with
  | none => simp only [rootInvoke,initialized,Flow.world]; exact .refl _
  | some frame =>
    have projected := rootEval_heap_projects frame
    rw [initial_world rootTypes 1 [value] world frame initialized] at projected
    simpa only [rootInvoke,initialized] using projected

theorem closeReturned_heap_projects (entered : State) (flow : Flow) :
    NativeHeapFrame.Runs flow.world (closeReturned entered flow).world := by
  cases flow with
  | normal frame => exact .refl _
  | unwind world => exact .refl _
  | invalid world => exact .refl _
  | unsupported source world => exact .refl _
  | returned value world =>
    have projected := NativeReferenceCleanup.closeScope_heap_projects entered world
    simp only [closeReturned]
    split <;> exact projected

theorem rootWithCleanup_heap_projects (world : State) (value : NativeRecordValues.Value) :
    NativeHeapFrame.Runs world (rootWithCleanup world value).world :=
  NativeHeapFrame.runs_trans _ _ _ (rootInvoke_heap_projects world value) (closeReturned_heap_projects world (rootInvoke world value))

theorem rootWithCleanup_heap (world : State) (value : NativeRecordValues.Value) :
    (rootWithCleanup world value).world.pointers.heap = world.pointers.heap := (rootWithCleanup_heap_projects world value).heap_eq

end HasteBootsReservationErrorKind
