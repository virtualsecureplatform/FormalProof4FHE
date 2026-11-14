module
public import FormalProof4FHE.HasteBoots.DependentStageContinuation
@[expose] public section

/-! Exact projection of dependent reached-or-skipped continuations. The child
projection is an execution identity under the same handler and incoming state. -/
namespace FormalProof4FHE.HasteBoots.DependentStageContinuationProjection
open OracleSpec OracleComp
noncomputable section
variable {ι Before Erased Index ErasedIndex State : Type} {spec : OracleSpec ι}
  {Result : Index → Type} {ErasedResult : ErasedIndex → Type}
variable (erase : Before → Erased) (eraseIndex : Index → ErasedIndex)
  (eraseChild : ∀ index, Result index → ErasedResult (eraseIndex index))
  (select : Before → Option Index) (selectErased : Erased → Option ErasedIndex)
  (start : Before → State) (finish : ∀ index, Result index → State)
  (child : ∀ index, State → ProbComp (Result index))
  (childProgram : ∀ index, OracleComp spec (ErasedResult index))

def eraseOutcome (outcome : Before × Option (Sigma Result)) : Erased × Option (Sigma ErasedResult) :=
  (erase outcome.1,outcome.2.map fun chosen => ⟨eraseIndex chosen.1,eraseChild chosen.1 chosen.2⟩)

def program (before : Erased) : OracleComp spec (Erased × Option (Sigma ErasedResult)) :=
  match selectErased before with
  | none => pure (before,none)
  | some index => do
    let returned ← childProgram index
    pure (before,some ⟨index,returned⟩)

/-- Preserve the actual gate, selected index, child return and final state. -/
theorem project_finish (impl : QueryImpl spec (StateT State ProbComp))
    (law : ∀ before, selectErased (erase before) = (select before).map eraseIndex)
    (projection : ∀ index state,
      (fun returned => (eraseChild index returned,finish index returned)) <$> child index state =
      (simulateQ impl (childProgram (eraseIndex index))).run state)
    (before : Before) :
    (fun outcome => (eraseOutcome erase eraseIndex eraseChild outcome,
      DependentStageContinuation.finalState start finish outcome)) <$>
      DependentStageContinuation.program select start child before =
    (simulateQ impl (program selectErased childProgram (erase before))).run (start before) := by
  simp only [program,law,DependentStageContinuation.program]
  cases selected : select before with
  | none =>
    simp only [Option.map_none,map_pure,simulateQ_pure,StateT.run_pure,
      eraseOutcome,DependentStageContinuation.finalState]
  | some index =>
    simp only [Option.map_some,map_bind,map_pure,simulateQ_bind,StateT.run_bind,
      simulateQ_pure,StateT.run_pure,eraseOutcome,DependentStageContinuation.finalState]
    rw [←projection index (start before)]
    simp only [bind_pure_comp,Functor.map_map]

/-- The predecessor and continuation execute once under the same state handler. -/
theorem project_bind (impl : QueryImpl spec (StateT State ProbComp))
    (law : ∀ before, selectErased (erase before) = (select before).map eraseIndex)
    (projection : ∀ index state,
      (fun returned => (eraseChild index returned,finish index returned)) <$> child index state =
      (simulateQ impl (childProgram (eraseIndex index))).run state)
    (prior : ProbComp Before) (priorProgram : OracleComp spec Erased) (initial : State)
    (priorProjection : (fun before => (erase before,start before)) <$> prior =
      (simulateQ impl priorProgram).run initial) :
    (fun outcome => (eraseOutcome erase eraseIndex eraseChild outcome,
      DependentStageContinuation.finalState start finish outcome)) <$>
      (prior >>= DependentStageContinuation.program select start child) =
    (simulateQ impl (priorProgram >>= program selectErased childProgram)).run initial := by
  rw [simulateQ_bind,StateT.run_bind,←priorProjection]
  simp only [map_bind,bind_map_left]
  apply bind_congr
  intro before
  exact project_finish erase eraseIndex eraseChild select selectErased start finish child childProgram impl law projection before

/-- Every terminal state event has the same probability in the raw program. -/
theorem terminal_event_eq (impl : QueryImpl spec (StateT State ProbComp))
    (law : ∀ before, selectErased (erase before) = (select before).map eraseIndex)
    (projection : ∀ index state,
      (fun returned => (eraseChild index returned,finish index returned)) <$> child index state =
      (simulateQ impl (childProgram (eraseIndex index))).run state)
    (prior : ProbComp Before) (priorProgram : OracleComp spec Erased) (initial : State)
    (priorProjection : (fun before => (erase before,start before)) <$> prior =
      (simulateQ impl priorProgram).run initial) (event : State → Prop) :
    Pr{let outcome ← (prior >>= DependentStageContinuation.program select start child)}[
      event (DependentStageContinuation.finalState start finish outcome)] =
    Pr{let outcome ← (simulateQ impl (priorProgram >>= program selectErased childProgram)).run initial}[
      event outcome.2] := by
  rw [←project_bind erase eraseIndex eraseChild select selectErased start finish child childProgram
    impl law projection prior priorProgram initial priorProjection,prEvent_map]

end
end FormalProof4FHE.HasteBoots.DependentStageContinuationProjection
