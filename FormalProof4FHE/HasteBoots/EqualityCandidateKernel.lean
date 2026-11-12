module
public import FormalProof4FHE.HasteBoots.EqualityCollectorInputCongruence
@[expose] public section

/-! Fixed-reference equality events use the original stream input with a
canonical collector phase. Whole residual fixation preserves the event, and
first exposure supplies dimension/cardinality loss over all collector budgets. -/
namespace FormalProof4FHE.HasteBoots.EqualityCandidateKernel
open InputIndexedOracle (Input World law)
open OracleProgram (Program)
open NativeRootMessage (Digest)
open NativeExtensionFields (Goldilocks3)
open EqualityFactorCandidate (Candidate)
open EqualityCandidateResidual (test residual)
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

def Event {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) (dummy : Digest) (other : World) : Prop :=
  ∃ budget, (GoldEqualityPointLaw.values candidate.family.selection.origin.geometry.geometry.1.val budget
    (EqualityCollectorInputCongruence.phase candidate.family.selection.family.input) other).elim False (test candidate dummy)

/-- If the original stored equality point misses this residual, the same
initialized native collector witnesses the all-budget kernel event. -/
theorem of_test {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) (dummy : Digest)
    (failed : test candidate dummy candidate.family.draw.point) : Event candidate dummy world := by
  have contract := NativeSharedLookupPrelude.protocol_contract candidate.family.selection.ctx.requests.property.le
    (NativeSharedLookupParent.models candidate.family.selection.ctx.requests) candidate.family.selection.origin.geometry.geometry.1
    candidate.family.selection.ctx.proof.values.multiplicities candidate.family.selection.ctx.proof.values.roots
    candidate.family.selection.ctx.proof.roots.property 7 candidate.family.selection.ctx.lookupFuel candidate.family.selection.ctx.equalityFuel
    _ world candidate.family.selection.origin.ready candidate.family.selection.origin.prepared
  obtain ⟨transcript,_,machine,_⟩ := contract.lookup
  have member := List.mem_of_getElem? candidate.family.drawAt
  simp only [machine,NativeLookupEquality.request,NativeLookupEquality.run_steps] at member
  obtain ⟨budget,collected⟩ := EqualityCollectorTrace.draw_point candidate.family.selection.ctx.equalityFuel transcript
    candidate.family.selection.ctx.proof.values.roots candidate.family.selection.ctx.proof.roots.property world candidate.family.draw member
  rw [EqualityCollectorInputCongruence.original_values] at collected
  have named := Eq.mp (congrArg (fun key : Input =>
    GoldEqualityPointLaw.values candidate.family.selection.origin.geometry.geometry.1.val budget
      (EqualityCollectorInputCongruence.phase key) world = some candidate.family.draw.point) candidate.family.input.symm) collected
  refine ⟨budget,?_⟩
  rw [named]
  exact failed

theorem event_congr {ln rn : ℕ} (dimension : ln = rn)
    (left : (Fin ln → Goldilocks3) → Prop) (right : (Fin rn → Goldilocks3) → Prop) (tests : HEq left right)
    (leftInput rightInput : Input) (input : leftInput = rightInput) :
    (fun other => ∃ budget, (GoldEqualityPointLaw.values ln budget (EqualityCollectorInputCongruence.phase leftInput) other).elim False left) =
      (fun other => ∃ budget, (GoldEqualityPointLaw.values rn budget (EqualityCollectorInputCongruence.phase rightInput) other).elim False right) := by
  cases dimension
  cases tests
  cases input
  rfl

theorem event_fixed {A : Type} {program : Program A} {position : ℕ} {world other : World}
    (left : Candidate program position world) (right : Candidate program position other) (dummy : Digest)
    (input : left.family.selection.family.input = right.family.selection.family.input)
    (ordinal : left.family.selection.index.val = right.family.selection.index.val)
    (same : (ParentFactorFiber.extend (OracleProgram.runPrefix position program) other).run =
      (ParentFactorFiber.extend (OracleProgram.runPrefix position program) world).run)
    (good : JobReferenceFixation.Good program position world dummy) (safe : ¬JobReferenceFixation.CounterBad program other) :
    Event left dummy = Event right dummy :=
  event_congr (EqualityCandidateResidual.alignment left right dummy input ordinal same good safe).nativeDimension
    (test left dummy) (test right dummy) (EqualityCandidateResidual.test_fixed left right dummy input ordinal same good safe)
    _ _ input

theorem conditional_bound {S B A : Type} (step : S → OracleMachine.Command S B)
    {past : World → NativeTranscript.Execution (S ⊕ B)} (replay : ObservationReplay.Replayable past)
    (reference : World) {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) (dummy : Digest)
    (selected : CausalStreamExposure.firstRead step (past reference).run = some candidate.family.selection.family.input) :
    (law[|{other | (past other).run = (past reference).run}]) {other | Event candidate dummy other} ≤
      (candidate.family.selection.origin.geometry.geometry.1.val : ENNReal) / (NativeFields.goldilocksModulus^3 : ℕ) := by
  by_cases bad : ∃ cell, residual candidate dummy cell ≠ 0
  · have included : {other | Event candidate dummy other} ⊆
        {other | ∃ budget, (GoldEqualityPointLaw.values candidate.family.selection.origin.geometry.geometry.1.val budget
          (EqualityCollectorInputCongruence.phase candidate.family.selection.family.input) other).elim False
          (fun point => (∑ cell, PackedEqualityCube.weight point cell * residual candidate dummy cell) = 0)} := by
      rintro other ⟨budget,failed⟩
      refine ⟨budget,?_⟩
      cases found : GoldEqualityPointLaw.values candidate.family.selection.origin.geometry.geometry.1.val budget
        (EqualityCollectorInputCongruence.phase candidate.family.selection.family.input) other with
      | none => rw [found] at failed; exact failed.elim
      | some point => rw [found] at failed; exact failed.2
    exact (measure_mono included).trans
      (GoldEqualityPointLaw.eventual_residual_bound step replay reference dummy _ _ selected (residual candidate dummy) bad)
  · have included : {other | Event candidate dummy other} ⊆ ∅ := by
      rintro other ⟨budget,failed⟩
      cases found : GoldEqualityPointLaw.values candidate.family.selection.origin.geometry.geometry.1.val budget
        (EqualityCollectorInputCongruence.phase candidate.family.selection.family.input) other with
      | none => rw [found] at failed; exact failed.elim
      | some point => rw [found] at failed; exact (bad failed.1).elim
    exact (measure_mono included).trans (by simp)

/-- The candidate's stored first-read position supplies the primitive causal
selector. Pricing after auxiliary refinement still needs its fresh-input proof. -/
theorem first_bound {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) (dummy : Digest) :
    (law[|{other | (OracleProgram.runPrefix position program other).run = (OracleProgram.runPrefix position program world).run}])
      {other | Event candidate dummy other} ≤
      (candidate.family.selection.origin.geometry.geometry.1.val : ENNReal) / (NativeFields.goldilocksModulus^3 : ℕ) := by
  have selected := candidate.family.first.selected
  rw [candidate.family.first_position] at selected
  exact conditional_bound OracleProgramMachine.step (OracleProgram.prefix_replay position program) world candidate dummy selected

end
end FormalProof4FHE.HasteBoots.EqualityCandidateKernel
