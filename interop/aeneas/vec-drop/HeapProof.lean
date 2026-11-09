namespace HasteBootsVecDrop
open FormalProof4FHE.HasteBoots
open NativeRecordDropCalls
open NativeRecordLLBC (Frame Flow)
open NativeReferenceMachine (State)
open NativeHeapLoss (Loss)

theorem evalCode_normal_budget (code : Code) (frame changed : Frame)
    (computed : evalCode code frame = some (.normal changed)) : (heapBudget code).canContinue = true := by
  induction code generalizing frame changed with
  | done => rfl
  | native body next nextIH =>
    cases actual : NativeRecordLLBC.eval body frame with
    | normal middle =>
      have continued := NativeRecordLLBC.eval_normal_canContinue body frame middle actual
      have later := nextIH middle changed (by simpa only [evalCode, actual] using computed)
      simp only [heapBudget, continued, later, Bool.and_self]
    | returned value world => simp only [evalCode, actual] at computed; cases computed
    | unwind world => simp only [evalCode, actual] at computed; cases computed
    | invalid world => simp only [evalCode, actual] at computed; cases computed
    | unsupported source world => simp only [evalCode, actual] at computed; cases computed
  | scope body next bodyIH nextIH =>
    cases actual : evalCode body frame with
    | none => simp only [evalCode, actual] at computed; cases computed
    | some returned =>
      cases returned with
      | normal middle =>
        have first := bodyIH frame middle actual
        by_cases cleaned : (NativeReferenceCleanup.closeScope frame.world middle.world).pending.isEmpty = true
        · have later := nextIH {middle with world := (NativeReferenceCleanup.closeScope frame.world middle.world).world} changed
            (by simpa only [evalCode, actual, resumeScope, cleaned, ite_true] using computed)
          simp only [heapBudget, first, later, Bool.and_self]
        · simp only [evalCode, actual, resumeScope, cleaned, Bool.false_eq_true, ite_false] at computed; cases computed
      | returned value world => simp only [evalCode, actual, resumeScope] at computed; cases computed
      | unwind world => simp only [evalCode, actual, resumeScope] at computed; cases computed
      | invalid world => simp only [evalCode, actual, resumeScope] at computed; cases computed
      | unsupported source world => simp only [evalCode, actual, resumeScope] at computed; cases computed
  | call name classification types count target args callee unwind next calleeIH unwindIH nextIH =>
    cases prepared : prepareCall frame types count args with
    | none => simp only [evalCode, prepared] at computed; cases computed
    | some pair =>
      rcases pair with ⟨caller,entered⟩
      cases actual : evalCode callee entered with
      | none => simp only [evalCode, prepared, actual] at computed; cases computed
      | some returned =>
        cases resumed : resumeCall entered.world caller target returned with
        | next middle =>
          have later := nextIH middle changed (by simpa only [evalCode, prepared, actual, resumed] using computed)
          simp only [heapBudget, later, Bool.or_true]
        | unwind middle =>
          have later := unwindIH middle changed (by simpa only [evalCode, prepared, actual, resumed] using computed)
          simp only [heapBudget, later, Bool.true_or]
        | invalid world => simp only [evalCode, prepared, actual, resumed] at computed; cases computed
        | unsupported source world => simp only [evalCode, prepared, actual, resumed] at computed; cases computed
  | loop classification function =>
    by_cases same : function = HasteBootsVecByteLoop.f6
    · cases argument : loopArgument frame with
      | none => simp only [evalCode, same, ite_true, argument] at computed; cases computed
      | some slice =>
        simp only [evalCode, same, ite_true, argument, loopOutcome] at computed
        split at computed <;> cases computed
    · simp only [evalCode, same, ite_false] at computed; cases computed

theorem evalCode_loss (code : Code) (frame : Frame) (flow : Flow)
    (computed : evalCode code frame = some flow) :
    Loss frame.world flow.world ((heapBudget code).limit flow) := by
  induction code generalizing frame flow with
  | done => simp only [evalCode, Option.some.injEq] at computed; subst flow; exact .refl _ _
  | native body next nextIH =>
    have first := NativeRecordLLBC.eval_loss body frame
    cases actual : NativeRecordLLBC.eval body frame with
    | normal middle =>
      rw [actual] at first
      have follows := NativeRecordLLBC.eval_normal_canContinue body frame middle actual
      have second := nextIH middle flow (by simpa only [evalCode, actual] using computed)
      exact (first.trans second).mono _ (by cases flow <;> simp only [heapBudget, HeapBudget.limit, follows, ite_true] <;> omega)
    | returned value world =>
      rw [actual] at first
      simp only [evalCode, actual, Option.some.injEq] at computed
      subst flow
      exact first.mono _ (by simp only [heapBudget, HeapBudget.limit]; omega)
    | unwind world =>
      rw [actual] at first
      simp only [evalCode, actual, Option.some.injEq] at computed
      subst flow
      exact first.mono _ (by simp only [heapBudget, HeapBudget.limit]; omega)
    | invalid world =>
      rw [actual] at first
      simp only [evalCode, actual, Option.some.injEq] at computed
      subst flow
      exact first.mono _ (by simp only [heapBudget, HeapBudget.limit]; omega)
    | unsupported source world =>
      rw [actual] at first
      simp only [evalCode, actual, Option.some.injEq] at computed
      subst flow
      exact first.mono _ (by simp only [heapBudget, HeapBudget.limit]; omega)
  | scope body next bodyIH nextIH =>
    cases actual : evalCode body frame with
    | none => simp only [evalCode, actual] at computed; cases computed
    | some returned =>
      have first := bodyIH frame returned actual
      cases returned with
      | normal middle =>
        have follows := evalCode_normal_budget body frame middle actual
        have cleanup := NativeReferenceCleanup.closeScope_heap_projects frame.world middle.world
        by_cases cleaned : (NativeReferenceCleanup.closeScope frame.world middle.world).pending.isEmpty = true
        · have second := nextIH {middle with world := (NativeReferenceCleanup.closeScope frame.world middle.world).world} flow
            (by simpa only [evalCode, actual, resumeScope, cleaned, ite_true] using computed)
          exact ((first.suffix cleanup).trans second).mono _
            (by cases flow <;> simp only [heapBudget, HeapBudget.limit, follows, ite_true] <;> omega)
        · simp only [evalCode, actual, resumeScope, cleaned, Bool.false_eq_true, ite_false, Option.some.injEq] at computed
          subst flow
          exact (first.suffix cleanup).mono _ (by simp only [heapBudget, HeapBudget.limit, follows, ite_true]; omega)
      | returned value world =>
        simp only [evalCode, actual, resumeScope, Option.some.injEq] at computed
        subst flow
        exact first.mono _ (by simp only [heapBudget, HeapBudget.limit]; omega)
      | unwind world =>
        simp only [evalCode, actual, resumeScope, Option.some.injEq] at computed
        subst flow
        exact first.mono _ (by simp only [heapBudget, HeapBudget.limit]; omega)
      | invalid world =>
        simp only [evalCode, actual, resumeScope, Option.some.injEq] at computed
        subst flow
        exact first.mono _ (by simp only [heapBudget, HeapBudget.limit]; omega)
      | unsupported source world =>
        simp only [evalCode, actual, resumeScope, Option.some.injEq] at computed
        subst flow
        exact first.mono _ (by simp only [heapBudget, HeapBudget.limit]; omega)
  | call name classification types count target args callee unwind next calleeIH unwindIH nextIH =>
    cases prepared : prepareCall frame types count args with
    | none =>
      simp only [evalCode, prepared, Option.some.injEq] at computed
      subst flow; exact .refl _ _
    | some pair =>
      rcases pair with ⟨caller,entered⟩
      have before : NativeHeapFrame.Runs frame.world entered.world := by
        rw [(prepareCall_worlds frame caller entered types count args prepared).2]
        exact .refl _
      cases actual : evalCode callee entered with
      | none => simp only [evalCode, prepared, actual] at computed; cases computed
      | some returned =>
        have first := Loss.prefix before ((calleeIH entered returned actual).mono (heapBudget callee).total ((heapBudget callee).limit_le_total returned))
        have resumeFrame := resumeCall_heap_projects entered.world caller target returned
        cases resumed : resumeCall entered.world caller target returned with
        | next middle =>
          rw [resumed] at resumeFrame
          have computedNext : evalCode next middle = some flow := by simpa only [evalCode, prepared, actual, resumed] using computed
          have second := nextIH middle flow computedNext
          apply ((first.suffix resumeFrame).trans second).mono
          cases flow with
          | normal changed =>
            have follows := evalCode_normal_budget next middle changed computedNext
            simp only [heapBudget, HeapBudget.limit, follows, ite_true]
            omega
          | returned value world => simp only [heapBudget, HeapBudget.limit]; omega
          | unwind world => simp only [heapBudget, HeapBudget.limit]; omega
          | invalid world => simp only [heapBudget, HeapBudget.limit]; omega
          | unsupported source world => simp only [heapBudget, HeapBudget.limit]; omega
        | unwind middle =>
          rw [resumed] at resumeFrame
          have computedNext : evalCode unwind middle = some flow := by simpa only [evalCode, prepared, actual, resumed] using computed
          have second := unwindIH middle flow computedNext
          apply ((first.suffix resumeFrame).trans second).mono
          cases flow with
          | normal changed =>
            have follows := evalCode_normal_budget unwind middle changed computedNext
            simp only [heapBudget, HeapBudget.limit, follows, ite_true]
            omega
          | returned value world => simp only [heapBudget, HeapBudget.limit]; omega
          | unwind world => simp only [heapBudget, HeapBudget.limit]; omega
          | invalid world => simp only [heapBudget, HeapBudget.limit]; omega
          | unsupported source world => simp only [heapBudget, HeapBudget.limit]; omega
        | invalid world =>
          rw [resumed] at resumeFrame
          simp only [evalCode, prepared, actual, resumed, Option.some.injEq] at computed
          subst flow
          exact (first.suffix resumeFrame).mono _ (by simp only [heapBudget, HeapBudget.limit]; omega)
        | unsupported source world =>
          rw [resumed] at resumeFrame
          simp only [evalCode, prepared, actual, resumed, Option.some.injEq] at computed
          subst flow
          exact (first.suffix resumeFrame).mono _ (by simp only [heapBudget, HeapBudget.limit]; omega)
  | loop classification function =>
    by_cases same : function = HasteBootsVecByteLoop.f6
    · cases argument : loopArgument frame with
      | none =>
        simp only [evalCode, same, ite_true, argument, Option.some.injEq] at computed
        subst flow; exact .refl _ _
      | some slice =>
        simp only [evalCode, same, ite_true, argument, Option.some.injEq] at computed
        subst flow
        exact Loss.ofFrame ⟨loopOutcome_heap_frame frame.world slice⟩ _
    · simp only [evalCode, same, ite_false] at computed; cases computed

theorem invokeCode_loss (function : Definition) (world : State) (args : List NativeRecordLLBC.Input) (flow : Flow)
    (computed : invokeCode function world args = some flow) :
    Loss world flow.world (heapBudget function.code).total := by
  cases decoded : NativeRecordLLBC.decodeArgs world args with
  | none => simp only [invokeCode, decoded, Option.some.injEq] at computed; subst flow; exact .refl _ _
  | some values =>
    cases initialized : NativeRecordLLBC.initial function.types function.argCount values world with
    | none => simp only [invokeCode, decoded, initialized, Option.some.injEq] at computed; subst flow; exact .refl _ _
    | some entered =>
      simp only [invokeCode, decoded, initialized, Option.map_eq_some_iff] at computed
      obtain ⟨returned,actual,same⟩ := computed
      subst flow
      have before : NativeHeapFrame.Runs world entered.world := by
        rw [NativeRecordLLBC.initial_world function.types function.argCount values world entered initialized]
        exact .refl _
      have first := (evalCode_loss function.code entered returned actual).mono (heapBudget function.code).total ((heapBudget function.code).limit_le_total returned)
      exact Loss.prefix before (first.suffix (NativeRecordLLBC.settle_heap_projects world returned))

theorem invocation_loss (function : Definition) (world : State) (args : List NativeRecordLLBC.Input) (flow : Flow)
    (checked : sourceLoops function.code = true) (invoked : Invokes function world args flow) :
    Loss world flow.world (heapBudget function.code).total := by
  have total := invokeCode_total function world args checked
  cases actual : invokeCode function world args with
  | none => rw [actual] at total; cases total
  | some other =>
    have same := invokes_deterministic function world args flow other invoked (invokeCode_sound function world args other actual)
    subst other
    exact invokeCode_loss function world args flow actual

theorem source_heap_budget_one : (heapBudget f1.code).total = 1 := by decide

theorem execute_loss (world : State) (args : List NativeRecordLLBC.Input) :
    Loss world (execute world args).world 1 := by
  have first := invokeCode_loss f1 world args (execute world args)
    (Option.get_mem (invokeCode_total f1 world args source_loops_checked))
  rw [source_heap_budget_one] at first
  exact first

/-- Every outcome, including rejection/unwind/unsupported prefixes, has the original
live-allocation count or one fewer. This is a count bound, not a valid-Vec postcondition. -/
theorem invocation_live_count (world : State) (args : List NativeRecordLLBC.Input) (flow : Flow)
    (invoked : Invokes f1 world args flow) :
    flow.world.pointers.heap.memory.blocks.length = world.pointers.heap.memory.blocks.length ∨
      flow.world.pointers.heap.memory.blocks.length + 1 = world.pointers.heap.memory.blocks.length := by
  have same := (invocation_iff_execute world args flow).mp invoked
  rw [same]
  have bound := execute_loss world args
  rcases bound with ⟨noGrowth,bounded,_⟩
  dsimp only [NativeHeapLoss.count] at noGrowth bounded
  omega

/-- The complete byte-and-shadow heap is unchanged unless one allocation was
removed. This holds for every source outcome, not only a normal return. -/
theorem invocation_heap_effect (world : State) (args : List NativeRecordLLBC.Input) (flow : Flow)
    (invoked : Invokes f1 world args flow) :
    flow.world.pointers.heap = world.pointers.heap ∨
      flow.world.pointers.heap.memory.blocks.length + 1 = world.pointers.heap.memory.blocks.length := by
  have same := (invocation_iff_execute world args flow).mp invoked
  have bound := execute_loss world args
  rw [← same] at bound
  rcases invocation_live_count world args flow invoked with unchanged | freed
  · exact Or.inl (bound.unchanged unchanged)
  · exact Or.inr freed

theorem byte_method_zero_budget : (heapBudget f2.code).total = 0 := by decide

theorem byte_method_heap_frame (world : State) (args : List NativeRecordLLBC.Input) (flow : Flow)
    (invoked : Invokes f2 world args flow) : flow.world.pointers.heap = world.pointers.heap := by
  have checked : sourceLoops f2.code = true := by decide
  have bound := invocation_loss f2 world args flow checked invoked
  rw [byte_method_zero_budget] at bound
  apply bound.unchanged
  have noGrowth := bound.no_growth
  have bounded := bound.bounded
  omega

end HasteBootsVecDrop
