module
public import FormalProof4FHE.HasteBoots.LookupTupleTest
public import FormalProof4FHE.HasteBoots.LookupBatchCollectorTrace
@[expose] public section

/-! An original attained lookup source candidate has one fixed whole
compression test and an all-budget native scalar kernel. The primitive causal
bound has no union over source positions and retains zero-event classes. -/
namespace FormalProof4FHE.HasteBoots.LookupCompressionKernel
open InputIndexedOracle (Input World law)
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
open LookupSourceCandidate (Candidate)
open OracleProgram (Program run runPrefix)
open MeasureTheory ProbabilityTheory
noncomputable section

def Event {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) (dummy : NativeRootMessage.Digest) : World → Prop :=
  LookupScalarKernel.Event candidate.draw.coefficients.phase.pending.input (LookupTupleTest.test candidate dummy)

theorem draw_value {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) :
    candidate.draw.value = TypedFieldRequest.scalarValue goldilocksBasis candidate.draw.coefficients.values := by
  let transcript := LookupExecutionOrigin.childStart NativeGoldBlockCode.description.row candidate.ctx.registry candidate.ctx.helper candidate.ctx.parent
    candidate.ctx.requests candidate.ctx.proof world
  have completed := (NativeLookupBatch.execute_valid goldilocksBasis 7 candidate.ctx.lookupFuel _ world
    (NativeLookupBatch.initial_valid goldilocksBasis _ transcript)).2 candidate.job.view.producer candidate.job.producerMember
  exact ((completed.1.1).2 candidate.draw candidate.member).2.2

/-- The actual retained original draw supplies an attained kernel event when
its complete fixed source test holds. No independent scalar is sampled. -/
theorem of_test {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) (dummy : NativeRootMessage.Digest)
    (occurred : LookupTupleTest.test candidate dummy candidate.draw.value) : Event candidate dummy world := by
  let transcript := LookupExecutionOrigin.childStart NativeGoldBlockCode.description.row candidate.ctx.registry candidate.ctx.helper candidate.ctx.parent
    candidate.ctx.requests candidate.ctx.proof world
  have traced := (LookupBatchCollectorTrace.initialized candidate.ctx.lookupFuel
    (NativeLookupBatch.schedule candidate.ctx.requests.property.le (fun i => (NativeSharedLookupParent.models candidate.ctx.requests i).sampling))
    transcript world).2 candidate.job.view.producer candidate.job.producerMember
  have source := traced.2 candidate.draw candidate.member
  obtain ⟨budget,collected⟩ := LookupScalarKernel.source_value candidate.draw.coefficients world _ source.1 source.2
  rw [← draw_value candidate] at collected
  exact ⟨budget,by rw [collected]; exact occurred⟩

theorem event_fixed {A : Type} (program : Program A) (position : ℕ) (world other : World)
    (left : Candidate program position world) (right : Candidate program position other) (dummy : NativeRootMessage.Digest)
    (input : left.draw.coefficients.phase.pending.input = right.draw.coefficients.phase.pending.input)
    (ordinal : left.index.val = right.index.val)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run)
    (good : JobReferenceFixation.Good program position world dummy) (safe : ¬JobReferenceFixation.CounterBad program other) :
    Event left dummy = Event right dummy := by
  unfold Event
  rw [input,LookupTupleTest.test_fixed program position world other left right dummy input ordinal same good safe]

theorem conditional_bound {S B A : Type} (step : S → OracleMachine.Command S B)
    {past : World → NativeTranscript.Execution (S ⊕ B)} (replay : ObservationReplay.Replayable past) (reference : World)
    {program : Program A} {position : ℕ} {world : World} (candidate : Candidate program position world) (dummy : NativeRootMessage.Digest)
    (selected : CausalStreamExposure.firstRead step (past reference).run = some candidate.draw.coefficients.phase.pending.input) :
    (law[|{other | (past other).run = (past reference).run}]) {other | Event candidate dummy other} ≤
      ((candidate.origin.ready.jobs.get candidate.index).tag.request.table.length : ENNReal)*
        ((((candidate.origin.ready.jobs.get candidate.index).tag.request.columns-1 : ℕ) : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ)) := by
  classical
  let request := (candidate.origin.ready.jobs.get candidate.index).tag.request
  let source := LookupTupleTest.tuples request (NativeScalarQueryShape.checked_power _ _ _ candidate.job.view.shape)
    candidate.job.view.enough (LookupSourceCandidate.sources candidate dummy)
  by_cases bad : ∃ position, ∀ row, source position ≠ LookupTupleTest.publicRows request row
  · have included : {other | Event candidate dummy other} ⊆
        {other | LookupScalarKernel.Event candidate.draw.coefficients.phase.pending.input
          (fun y => ∀ position, ∃ row, TupleHash.hash y (source position) = TupleHash.hash y (LookupTupleTest.publicRows request row)) other} := by
      rintro other ⟨budget,occurred⟩
      refine ⟨budget,?_⟩
      cases found : GoldScalarChallengeLaw.values budget (LookupScalarKernel.phase candidate.draw.coefficients.phase.pending.input) other with
      | none => rw [found] at occurred; exact occurred.elim
      | some y => rw [found] at occurred; exact occurred.2
    exact (measure_mono included).trans (LookupPairChallengeBounds.tuple_family step replay reference dummy _ selected
      source (LookupTupleTest.publicRows request) bad)
  · have empty : {other | Event candidate dummy other} ⊆ ∅ := by
      rintro other ⟨budget,occurred⟩
      cases found : GoldScalarChallengeLaw.values budget (LookupScalarKernel.phase candidate.draw.coefficients.phase.pending.input) other with
      | none => rw [found] at occurred; exact occurred.elim
      | some y => rw [found] at occurred; exact (bad occurred.1).elim
    exact (measure_mono empty).trans (by simp)

theorem first_bound {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) (dummy : NativeRootMessage.Digest) :
    (law[|{other | (runPrefix position program other).run = (runPrefix position program world).run}]) {other | Event candidate dummy other} ≤
      ((candidate.origin.ready.jobs.get candidate.index).tag.request.table.length : ENNReal)*
        ((((candidate.origin.ready.jobs.get candidate.index).tag.request.columns-1 : ℕ) : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ)) := by
  have selected := candidate.first.selected
  rw [candidate.first_position] at selected
  exact conditional_bound OracleProgramMachine.step (OracleProgram.prefix_replay position program) world candidate dummy selected

end
end FormalProof4FHE.HasteBoots.LookupCompressionKernel
