module
public import FormalProof4FHE.HasteBoots.LookupOffsetCompressionFixation
public import FormalProof4FHE.HasteBoots.RefinedCompressionKernel
@[expose] public section

/-! The original reciprocal kernel is fixed and bounded on the same refined
fiber. The active-count characteristic guard remains explicit; validated
caller execution supplies it. No union over adaptive classes is claimed. -/
namespace FormalProof4FHE.HasteBoots.LookupOffsetKernel
open InputIndexedOracle (World law)
open NativeRootMessage (Digest)
open NativeFields (goldilocksModulus)
open OracleProgram (Program runPrefix)
open LookupOffsetCompressionFixation (Candidate)
open RefinedScalarSourceKernel (retained retained_replay retained_packet pending)
open MeasureTheory ProbabilityTheory
noncomputable section

def complexity {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) : ℕ :=
  (candidate.source.origin.ready.jobs.get candidate.source.index).tag.request.terminal.logicalLength.val +
    (candidate.source.origin.ready.jobs.get candidate.source.index).tag.request.table.length-1

def Event {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) (dummy : Digest) : World → Prop :=
  LookupScalarKernel.Event candidate.source.draw.coefficients.phase.pending.input
    (LookupReciprocalStatement.test candidate.toCandidate dummy
      (NativeFieldWire.goldExtensionValue (candidate.source.origin.ready.jobs.get candidate.source.index).output.y))

theorem event_fixed {A : Type} (program : Program A) (position : ℕ) (world other : World)
    (left : Candidate program position world) (right : Candidate program position other) (dummy : Digest)
    (input : left.source.draw.coefficients.phase.pending.input = right.source.draw.coefficients.phase.pending.input)
    (ordinal : left.source.index.val = right.source.index.val)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run)
    (good : JobReferenceFixation.Good program position world dummy) (safe : ¬JobReferenceFixation.CounterBad program other) :
    Event left dummy = Event right dummy := by
  unfold Event
  rw [input,LookupOffsetCompressionFixation.test_fixed program position world other left right dummy input ordinal same good safe]

theorem complexity_fixed {A : Type} (program : Program A) (position : ℕ) (world other : World)
    (left : Candidate program position world) (right : Candidate program position other) (dummy : Digest)
    (input : left.source.draw.coefficients.phase.pending.input = right.source.draw.coefficients.phase.pending.input)
    (ordinal : left.source.index.val = right.source.index.val)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run)
    (good : JobReferenceFixation.Good program position world dummy) (safe : ¬JobReferenceFixation.CounterBad program other) :
    complexity left = complexity right := by
  obtain ⟨_,requests,_,_⟩ := LookupMultiplicityFixation.fixed program position world other left.toCandidate right.toCandidate dummy input ordinal same good safe
  exact congrArg (fun request : NativeSharedLookupStatement.Request => request.terminal.logicalLength.val + request.table.length-1)
    (OriginalJobOrdinal.request left.source.origin right.source.origin requests left.source.index right.source.index ordinal)

theorem conditional_bound {S B A : Type} (step : S → OracleMachine.Command S B)
    {past : World → NativeTranscript.Execution (S ⊕ B)} (replay : ObservationReplay.Replayable past) (reference : World)
    {program : Program A} {position : ℕ} {world : World} (candidate : Candidate program position world) (dummy : Digest)
    (selected : CausalStreamExposure.firstRead step (past reference).run = some candidate.source.draw.coefficients.phase.pending.input)
    (small : (candidate.source.origin.ready.jobs.get candidate.source.index).tag.request.terminal.logicalLength.val < goldilocksModulus) :
    (law[|{other | (past other).run = (past reference).run}]) {other | Event candidate dummy other} ≤
      (complexity candidate : ENNReal)/(goldilocksModulus^3 : ℕ) := by
  exact LookupReciprocalKernel.conditional_bound step replay reference dummy _ selected _ _ _ small

theorem bound {A : Type} (program : Program A) (position : ℕ) (world : World)
    (candidate : Candidate program position world) (dummy : Digest)
    (small : (candidate.source.origin.ready.jobs.get candidate.source.index).tag.request.terminal.logicalLength.val < goldilocksModulus) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}])
      {other | Event candidate dummy other} ≤ (complexity candidate : ENNReal)/(goldilocksModulus^3 : ℕ) := by
  have primitive := conditional_bound (pending candidate.source.draw.coefficients.phase.pending.input)
    (retained_replay (ParentFactorFiber.replay (OracleProgram.prefix_replay position program))) world candidate dummy
    (RefinedCompressionKernel.selected program position world candidate.source) small
  simpa only [retained_packet] using primitive

end
end FormalProof4FHE.HasteBoots.LookupOffsetKernel
