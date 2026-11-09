module
public import FormalProof4FHE.HasteBoots.NativeHeapRelease
@[expose] public section

/-! Bounds on live-allocation loss in finite retained aggregate bodies. These
counts are heap effects, not physical attacker work or native allocator costs. -/
namespace FormalProof4FHE.HasteBoots.NativeHeapLoss
open NativeReferenceMachine (State)

def count (world : State) : Nat := world.pointers.heap.memory.blocks.length

structure Loss (before after : State) (budget : Nat) : Prop where
  bounded : count before ≤ count after + budget
  released : NativeHeapRelease.Releases before.pointers.heap after.pointers.heap

theorem Loss.no_growth {before after : State} {budget : Nat} (bound : Loss before after budget) : count after ≤ count before :=
  bound.released.no_growth

theorem Loss.unchanged {before after : State} {budget : Nat} (bound : Loss before after budget)
    (same : count after = count before) : after.pointers.heap = before.pointers.heap :=
  bound.released.unchanged same

theorem Loss.refl (world : State) (budget : Nat) : Loss world world budget := ⟨Nat.le_add_right _ _,.refl _⟩

theorem Loss.ofFrame {before after : State} (same : NativeHeapFrame.Runs before after) (budget : Nat) : Loss before after budget := by
  have counts : count after = count before := congrArg (fun heap => heap.memory.blocks.length) same.heap_eq
  constructor
  · rw [counts]; exact Nat.le_add_right _ _
  · rw [same.heap_eq]; exact .refl _

theorem Loss.mono {before after : State} {small : Nat} (first : Loss before after small)
    (large : Nat) (enough : small ≤ large) : Loss before after large := by
  rcases first with ⟨bound,released⟩
  exact ⟨by omega,released⟩

theorem Loss.trans {before middle after : State} {firstBudget secondBudget : Nat}
    (first : Loss before middle firstBudget) (second : Loss middle after secondBudget) :
    Loss before after (firstBudget + secondBudget) := by
  rcases first with ⟨bound,firstRelease⟩
  rcases second with ⟨boundNext,secondRelease⟩
  exact ⟨by omega,firstRelease.trans secondRelease⟩

theorem Loss.prefix {before middle after : State} {budget : Nat}
    (same : NativeHeapFrame.Runs before middle) (later : Loss middle after budget) : Loss before after budget := by
  simpa only [Nat.zero_add] using (Loss.ofFrame same 0).trans later

theorem Loss.suffix {before middle after : State} {budget : Nat}
    (first : Loss before middle budget) (same : NativeHeapFrame.Runs middle after) : Loss before after budget := by
  simpa only [Nat.add_zero] using first.trans (Loss.ofFrame same 0)

end FormalProof4FHE.HasteBoots.NativeHeapLoss

namespace FormalProof4FHE.HasteBoots.NativeRecordLLBC
open NativeReferenceMachine (State)
open NativeHeapLoss (Loss)

/-- A syntax upper bound. A leaf counts one checked free; separate alternatives
are summed conservatively, without assuming any branch is unreachable. -/
def deallocationBudget : Body → Nat
  | .done | .ret | .resume | .abort | .unsupported _ => 0
  | .live _ next | .dead _ next | .assign _ _ next => deallocationBudget next
  | .constIf _ yes no next | .switchUsize _ _ yes no next | .matchChoice _ _ _ yes no next =>
    deallocationBudget yes + deallocationBudget no + deallocationBudget next
  | .deallocate _ _ _ _ => 1
  | .call _ _ _ _ _ _ callee unwind next | .twoPhaseRawVecCall _ _ _ _ _ _ _ _ _ callee unwind next =>
    deallocationBudget callee + (deallocationBudget unwind + deallocationBudget next)

/-- Only a normal continuation reaches a following source body. -/
def canContinue : Body → Bool
  | .done => true
  | .ret | .resume | .abort | .unsupported _ | .deallocate _ _ _ _ => false
  | .live _ next | .dead _ next | .assign _ _ next => canContinue next
  | .constIf _ yes no next | .switchUsize _ _ yes no next | .matchChoice _ _ _ yes no next =>
    (canContinue yes || canContinue no) && canContinue next
  | .call _ _ _ _ _ _ _ unwind next | .twoPhaseRawVecCall _ _ _ _ _ _ _ _ _ _ unwind next =>
    canContinue unwind || canContinue next

theorem deallocate_not_normal (frame changed : Frame) (pointer size alignment : Operand) (tag : Nat)
    (normal : deallocate frame pointer size alignment tag = .normal changed) : False := by
  cases selected : evalArgs frame [pointer,size,alignment] with
  | none => simp only [deallocate, selected] at normal; cases normal
  | some pair =>
    rcases pair with ⟨values,caller⟩
    simp only [deallocate, selected] at normal
    split at normal
    next raw bytes actual align =>
      by_cases matched : actual = tag
      · simp only [matched, ite_true] at normal
        cases freed : NativeByteDeallocation.execute caller.world raw bytes align <;> rw [freed] at normal <;> cases normal
      · simp only [matched, ite_false] at normal; cases normal
    next => cases normal

theorem eval_normal_canContinue (body : Body) (frame changed : Frame)
    (normal : eval body frame = .normal changed) : canContinue body = true := by
  induction body generalizing frame changed <;> simp only [canContinue]
  all_goals simp only [eval] at normal
  all_goals repeat' (first | split at normal | contradiction)
  all_goals (try simp_all)
  all_goals first
    | aesop
    | (exact deallocate_not_normal _ _ _ _ _ _ normal)

theorem deallocate_loss (frame : Frame) (pointer size alignment : Operand) (tag : Nat) :
    Loss frame.world (deallocate frame pointer size alignment tag).world 1 := by
  cases selected : evalArgs frame [pointer,size,alignment] with
  | none => simp only [deallocate, selected, Flow.world]; exact .refl _ _
  | some result =>
    rcases result with ⟨values,caller⟩
    have same := evalArgs_world frame caller [pointer,size,alignment] values selected
    simp only [deallocate, selected]
    split
    next raw bytes actual align =>
      by_cases matched : actual = tag
      · simp only [matched, ite_true]
        cases freed : NativeByteDeallocation.execute caller.world raw bytes align with
        | none => simp only [Flow.world]; rw [same]; exact .refl _ _
        | some world =>
          have countEq := NativeByteDeallocation.execute_frees_one caller.world world raw bytes align freed
          rw [same] at countEq
          change Loss frame.world world 1
          refine ⟨?_,?_⟩
          · dsimp only [NativeHeapLoss.count]; omega
          · obtain ⟨heap,release,snapshot⟩ := NativeByteDeallocation.execute_heap caller.world world raw bytes align freed
            have conditions := NativeByteDeallocation.execute_success caller.world world raw bytes align freed
            have heapEq := congrArg (fun state => state.pointers.heap) snapshot
            rw [heapEq, ← same]
            exact .free (.refl _) raw.storage ⟨bytes.val,align.val⟩ conditions.2.1 conditions.2.2.1 conditions.1.2 release
      · simp only [matched, ite_false, Flow.world]; rw [same]; exact .refl _ _
    next => change Loss frame.world caller.world 1; rw [same]; exact .refl _ _

theorem eval_loss (body : Body) (frame : Frame) :
    Loss frame.world (eval body frame).world (deallocationBudget body) := by
  induction body generalizing frame with
  | done => exact .refl _ _
  | ret => cases selected : read frame 0 [] <;> simp only [eval, selected, Flow.world] <;> exact .refl _ _
  | resume => exact .refl _ _
  | abort => exact .refl _ _
  | unsupported source => exact .refl _ _
  | live index next ih =>
    cases changed : storageLive frame index with
    | none => simp only [eval, changed, Flow.world]; exact .refl _ _
    | some caller =>
      simp only [eval, changed]
      simpa only [deallocationBudget, storageLive_world frame caller index changed] using ih caller
  | dead index next ih =>
    cases changed : storageDead frame index with
    | none => simp only [eval, changed, Flow.world]; exact .refl _ _
    | some caller =>
      simp only [eval, changed]
      simpa only [deallocationBudget, storageDead_world frame caller index changed] using ih caller
  | assign index rvalue next ih =>
    have first := evalRvalue_heap_projects frame rvalue
    cases actual : evalRvalue frame rvalue with
    | invalid world =>
      simpa only [deallocationBudget, eval, actual, Evaluated.world, Flow.world] using Loss.ofFrame first (deallocationBudget next)
    | value value caller =>
      rw [actual] at first
      cases written : write caller index value with
      | none => simpa only [deallocationBudget, eval, actual, written, Evaluated.world, Flow.world] using Loss.ofFrame first (deallocationBudget next)
      | some changed =>
        simp only [eval, actual, written]
        have second := ih changed
        rw [write_world caller changed index value written] at second
        exact Loss.prefix first second
  | constIf condition yes no next yesIH noIH nextIH =>
    have first : Loss frame.world (if condition then eval yes frame else eval no frame).world
        (deallocationBudget yes + deallocationBudget no) := by
      cases condition
      · exact (noIH frame).mono _ (by omega)
      · exact (yesIH frame).mono _ (by omega)
    simp only [eval]
    generalize chosen : (if condition then eval yes frame else eval no frame) = branch at first ⊢
    cases branch with
    | normal changed => exact first.trans (nextIH changed)
    | returned value world => exact first.mono _ (by dsimp only [deallocationBudget]; omega)
    | unwind world => exact first.mono _ (by dsimp only [deallocationBudget]; omega)
    | invalid world => exact first.mono _ (by dsimp only [deallocationBudget]; omega)
    | unsupported source world => exact first.mono _ (by dsimp only [deallocationBudget]; omega)
  | matchChoice index path tag left right next leftIH rightIH nextIH =>
    cases selected : selectChoice frame index path tag with
    | none => simp only [eval, selected, Flow.world]; exact .refl _ _
    | some side =>
      have first : Loss frame.world (if side then eval right frame else eval left frame).world
          (deallocationBudget left + deallocationBudget right) := by
        cases side
        · exact (leftIH frame).mono _ (by omega)
        · exact (rightIH frame).mono _ (by omega)
      simp only [eval, selected]
      generalize chosen : (if side then eval right frame else eval left frame) = branch at first ⊢
      cases branch with
      | normal changed => exact first.trans (nextIH changed)
      | returned value world => exact first.mono _ (by dsimp only [deallocationBudget]; omega)
      | unwind world => exact first.mono _ (by dsimp only [deallocationBudget]; omega)
      | invalid world => exact first.mono _ (by dsimp only [deallocationBudget]; omega)
      | unsupported source world => exact first.mono _ (by dsimp only [deallocationBudget]; omega)
  | switchUsize operand expected yes no next yesIH noIH nextIH =>
    cases selected : evalOperand frame operand with
    | none => simp only [eval, selected, Flow.world]; exact .refl _ _
    | some result =>
      rcases result with ⟨value,caller⟩
      have same := evalOperand_world frame caller operand value selected
      cases value with
      | pair left right => simp only [eval, selected, Flow.world]; exact .refl _ _
      | choice side fields => simp only [eval, selected, Flow.world]; exact .refl _ _
      | record tag fields => simp only [eval, selected, Flow.world]; exact .refl _ _
      | enumeration tag value => simp only [eval, selected, Flow.world]; exact .refl _ _
      | uninit => simp only [eval, selected, Flow.world]; exact .refl _ _
      | scalar value =>
        cases value with
        | unit => simp only [eval, selected, Flow.world]; exact .refl _ _
        | raw pointer => simp only [eval, selected, Flow.world]; exact .refl _ _
        | reference mutable reference length => simp only [eval, selected, Flow.world]; exact .refl _ _
        | usize word =>
          have first : Loss frame.world (if word = expected then eval yes caller else eval no caller).world
              (deallocationBudget yes + deallocationBudget no) := by
            rw [← same]
            split
            · exact (yesIH caller).mono _ (by omega)
            · exact (noIH caller).mono _ (by omega)
          simp only [eval, selected]
          generalize chosen : (if word = expected then eval yes caller else eval no caller) = branch at first ⊢
          cases branch with
          | normal changed => exact first.trans (nextIH changed)
          | returned value world => exact first.mono _ (by dsimp only [deallocationBudget]; omega)
          | unwind world => exact first.mono _ (by dsimp only [deallocationBudget]; omega)
          | invalid world => exact first.mono _ (by dsimp only [deallocationBudget]; omega)
          | unsupported source world => exact first.mono _ (by dsimp only [deallocationBudget]; omega)
  | deallocate pointer size alignment tag => exact deallocate_loss frame pointer size alignment tag
  | twoPhaseRawVecCall parent path reserved name classification types argCount target rest callee unwind next calleeIH unwindIH nextIH =>
    let total := deallocationBudget callee + (deallocationBudget unwind + deallocationBudget next)
    by_cases pending : pendingMutableSlot frame reserved = true
    · have reservedRun := reserveRawVec_heap_projects frame parent path
      cases reservationEq : reserveRawVec frame parent path with
      | invalid world => simpa only [deallocationBudget, eval, pending, ite_true, reservationEq, Flow.world, NativeRawVecFields.Result.world] using Loss.ofFrame reservedRun total
      | value reservation prepared =>
        rw [reservationEq] at reservedRun
        cases argsEq : evalArgs {frame with world := prepared} rest with
        | none => simpa only [deallocationBudget, eval, pending, ite_true, reservationEq, argsEq, Flow.world, NativeRawVecFields.Result.world] using Loss.ofFrame reservedRun total
        | some result =>
          rcases result with ⟨values,caller⟩
          have callerWorld := evalArgs_world {frame with world := prepared} caller rest values argsEq
          have activatedRun := NativeRawVecMutBorrow.activate_heap_projects caller.world reservation
          have activationStart : NativeHeapFrame.Runs frame.world caller.world := by
            simpa only [deallocationBudget, callerWorld, NativeRawVecFields.Result.world] using reservedRun
          cases activated : NativeRawVecMutBorrow.activate caller.world reservation with
          | invalid world =>
            rw [activated] at activatedRun
            simpa only [deallocationBudget, eval, pending, ite_true, reservationEq, argsEq, activated, Flow.world, NativeRawVecFields.Result.world] using
              Loss.ofFrame (NativeHeapFrame.runs_trans _ _ _ activationStart activatedRun) total
          | value reference world =>
            rw [activated] at activatedRun
            have beforeWrite : NativeHeapFrame.Runs frame.world world := NativeHeapFrame.runs_trans _ _ _ activationStart activatedRun
            cases writtenEq : write {caller with world} reserved (.scalar reference) with
            | none => simpa only [deallocationBudget, eval, pending, ite_true, reservationEq, argsEq, activated, writtenEq, Flow.world] using Loss.ofFrame beforeWrite total
            | some written =>
              have writtenWorld := write_world {caller with world} written reserved (.scalar reference) writtenEq
              cases movedEq : evalOperand written (.move reserved []) with
              | none => simpa only [deallocationBudget, eval, pending, ite_true, reservationEq, argsEq, activated, writtenEq, movedEq, Flow.world] using Loss.ofFrame beforeWrite total
              | some moved =>
                rcases moved with ⟨argument,consumed⟩
                have consumedWorld := evalOperand_world written consumed (.move reserved []) argument movedEq
                cases initialized : initial types argCount (argument :: values) consumed.world with
                | none =>
                  have consumedRun : NativeHeapFrame.Runs frame.world consumed.world := by
                    simpa only [consumedWorld, writtenWorld] using beforeWrite
                  simpa only [deallocationBudget, eval, pending, ite_true, reservationEq, argsEq, activated, writtenEq, movedEq, initialized, Flow.world] using Loss.ofFrame consumedRun total
                | some entered =>
                  have entryWorld := initial_world types argCount (argument :: values) consumed.world entered initialized
                  have callStart : NativeHeapFrame.Runs frame.world entered.world := by
                    simpa only [entryWorld, consumedWorld, writtenWorld] using beforeWrite
                  have first := Loss.prefix callStart ((calleeIH entered).suffix (settle_heap_projects entered.world (eval callee entered)))
                  cases returned : settle entered.world (eval callee entered) with
                  | normal changed => simpa only [deallocationBudget, eval, pending, ite_true, reservationEq, argsEq, activated, writtenEq, movedEq, initialized, returned, Flow.world] using first.mono total (by dsimp only [total]; omega)
                  | invalid final => simpa only [deallocationBudget, eval, pending, ite_true, reservationEq, argsEq, activated, writtenEq, movedEq, initialized, returned, Flow.world] using first.mono total (by dsimp only [total]; omega)
                  | unsupported source final => simpa only [deallocationBudget, eval, pending, ite_true, reservationEq, argsEq, activated, writtenEq, movedEq, initialized, returned, Flow.world] using first.mono total (by dsimp only [total]; omega)
                  | unwind final =>
                    rw [returned] at first
                    simp only [eval, pending, ite_true, reservationEq, argsEq, activated, writtenEq, movedEq, initialized, returned]
                    exact first.trans ((unwindIH {consumed with world := final}).mono (deallocationBudget unwind + deallocationBudget next) (by omega))
                  | returned output final =>
                    rw [returned] at first
                    cases stored : write {consumed with world := final} target output with
                    | none => simpa only [deallocationBudget, eval, pending, ite_true, reservationEq, argsEq, activated, writtenEq, movedEq, initialized, returned, stored, Flow.world] using first.mono total (by dsimp only [total]; omega)
                    | some changed =>
                      simp only [eval, pending, ite_true, reservationEq, argsEq, activated, writtenEq, movedEq, initialized, returned, stored]
                      have later := nextIH changed
                      rw [write_world {consumed with world := final} changed target output stored] at later
                      exact first.trans (later.mono (deallocationBudget unwind + deallocationBudget next) (by omega))
    · simp only [eval, pending, Flow.world]; exact .refl _ _
  | call name classification types argCount target args callee unwind next calleeIH unwindIH nextIH =>
    let total := deallocationBudget callee + (deallocationBudget unwind + deallocationBudget next)
    cases selected : evalArgs frame args with
    | none => simp only [eval, selected, Flow.world]; exact .refl _ _
    | some result =>
      rcases result with ⟨values,caller⟩
      have same := evalArgs_world frame caller args values selected
      cases initialized : initial types argCount values caller.world with
      | none => simp only [eval, selected, initialized, Flow.world]; rw [same]; exact .refl _ _
      | some entered =>
        have entryWorld := initial_world types argCount values caller.world entered initialized
        have callPrefix : NativeHeapFrame.Runs frame.world entered.world := by
          rw [entryWorld, same]; exact .refl _
        have first := Loss.prefix callPrefix ((calleeIH entered).suffix (settle_heap_projects entered.world (eval callee entered)))
        cases returned : settle entered.world (eval callee entered) with
        | normal changed => simpa only [deallocationBudget, eval, selected, initialized, returned, Flow.world] using first.mono total (by dsimp only [total]; omega)
        | invalid world => simpa only [deallocationBudget, eval, selected, initialized, returned, Flow.world] using first.mono total (by dsimp only [total]; omega)
        | unsupported source world => simpa only [deallocationBudget, eval, selected, initialized, returned, Flow.world] using first.mono total (by dsimp only [total]; omega)
        | unwind world =>
          rw [returned] at first
          simp only [eval, selected, initialized, returned]
          exact first.trans ((unwindIH {caller with world}).mono (deallocationBudget unwind + deallocationBudget next) (by omega))
        | returned output world =>
          rw [returned] at first
          cases written : write {caller with world} target output with
          | none => simpa only [deallocationBudget, eval, selected, initialized, returned, written, Flow.world] using first.mono total (by dsimp only [total]; omega)
          | some changed =>
            have second := nextIH changed
            rw [write_world {caller with world} changed target output written] at second
            simp only [eval, selected, initialized, returned, written]
            exact first.trans (second.mono (deallocationBudget unwind + deallocationBudget next) (by omega))

end FormalProof4FHE.HasteBoots.NativeRecordLLBC

namespace FormalProof4FHE.HasteBoots.NativeRecordDropCalls
open NativeReferenceMachine (State)
open NativeRecordLLBC (Frame Flow)
theorem resumeCall_heap_projects (entered : State) (caller : Frame) (target : Nat) (flow : Flow) :
    NativeHeapFrame.Runs flow.world (resumeCall entered caller target flow).world := by
  cases flow with
  | returned value current =>
    have first := NativeRecordLLBC.settle_heap_projects entered (.returned value current)
    simp only [resumeCall]
    cases actual : NativeRecordLLBC.settle entered (.returned value current) with
    | returned output world =>
      rw [actual] at first
      simp only []
      cases written : NativeRecordLLBC.write {caller with world} target output with
      | none => exact first
      | some frame =>
        have same := NativeRecordLLBC.write_world {caller with world} frame target output written
        change NativeHeapFrame.Runs current frame.world
        rw [same]
        exact first
    | invalid world => simpa only [actual, NativeRecordLLBC.Flow.world, Resume.world] using first
    | normal frame => simpa only [actual, NativeRecordLLBC.Flow.world, Resume.world] using first
    | unwind world => simpa only [actual, NativeRecordLLBC.Flow.world, Resume.world] using first
    | unsupported source world => simpa only [actual, NativeRecordLLBC.Flow.world, Resume.world] using first
  | unwind world => exact .refl _
  | invalid world => exact .refl _
  | unsupported source world => exact .refl _
  | normal frame => exact .refl _

theorem resumeScope_heap_projects (entered : State) (flow : Flow) :
    NativeHeapFrame.Runs flow.world (resumeScope entered flow).world := by
  cases flow with
  | normal frame =>
    have first := NativeReferenceCleanup.closeScope_heap_projects entered frame.world
    simp only [resumeScope]
    split <;> exact first
  | returned value world => exact .refl _
  | unwind world => exact .refl _
  | invalid world => exact .refl _
  | unsupported source world => exact .refl _


structure HeapBudget where
  normal : Nat
  terminal : Nat
  canContinue : Bool
  deriving DecidableEq

def HeapBudget.total (budget : HeapBudget) : Nat := max budget.normal budget.terminal

def HeapBudget.limit (budget : HeapBudget) : Flow → Nat
  | .normal _ => budget.normal
  | _ => budget.terminal

theorem HeapBudget.limit_le_total (budget : HeapBudget) (flow : Flow) : budget.limit flow ≤ budget.total := by
  cases flow <;> simp only [HeapBudget.limit, HeapBudget.total] <;> omega

/-- Normal and terminal paths are tracked separately. A completed unwind cannot
also reach the source's normal successor and charge its free a second time. -/
def heapBudget : Code → HeapBudget
  | .done => ⟨0,0,true⟩
  | .loop _ _ => ⟨0,0,false⟩
  | .native body next =>
    let budget := heapBudget next
    let reads := NativeRecordLLBC.deallocationBudget body
    let follows := NativeRecordLLBC.canContinue body
    ⟨reads + budget.normal,reads + (if follows then budget.terminal else 0),follows && budget.canContinue⟩
  | .scope body next =>
    let first := heapBudget body
    let later := heapBudget next
    ⟨first.normal + later.normal,
      max first.terminal (if first.canContinue then first.normal + later.terminal else 0),
      first.canContinue && later.canContinue⟩
  | .call _ _ _ _ _ _ callee unwind next =>
    let first := (heapBudget callee).total
    let failed := heapBudget unwind
    let later := heapBudget next
    ⟨first + max (if failed.canContinue then failed.normal else 0) (if later.canContinue then later.normal else 0),
      first + max failed.terminal later.terminal, failed.canContinue || later.canContinue⟩

end FormalProof4FHE.HasteBoots.NativeRecordDropCalls
