module
public import FormalProof4FHE.HasteBoots.FirstCompressionCandidate
public import FormalProof4FHE.HasteBoots.OffsetWorkPosition
@[expose] public section

/-! All admitted original first-compression candidates at one first read
share its input and original job ordinal. The selected key bytes price their
whole tuple test without summing source positions, jobs or parent reuses. -/
namespace FormalProof4FHE.HasteBoots.FirstCompressionWorkPosition
open InputIndexedOracle (World law)
open OracleProgram (Program runPrefix)
open NativeRootMessage (Digest)
open FirstCompressionCandidate (Candidate)
open MeasureTheory ProbabilityTheory
noncomputable section

def Event {A : Type} (program : Program A) (position : ℕ) (dummy : Digest) (world : World) : Prop :=
  ∃ candidate : Candidate program position world, LookupCompressionKernel.Event candidate.toCandidate dummy world

def SafeEvent {A : Type} (program : Program A) (position : ℕ) (dummy : Digest) (world : World) : Prop :=
  Event program position dummy world ∧ ¬GlobalReferenceBad.Bad program dummy world

theorem input_fixed {A : Type} (program : Program A) (position : ℕ) (world other : World)
    (left : Candidate program position world) (right : Candidate program position other)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run) :
    left.draw.coefficients.phase.pending.input = right.draw.coefficients.phase.pending.input := by
  have leftSelected := left.first.selected
  have rightSelected := right.first.selected
  rw [left.first_position] at leftSelected
  rw [right.first_position,ParentFactorFiber.old_packet (runPrefix position program) world other same] at rightSelected
  exact Option.some.inj (leftSelected.symm.trans rightSelected)

theorem budget_rate : (FirstCompressionCandidate.budget : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) ≤
    64*LookupStreamWorkRate.rate := by
  have degrees : FirstCompressionCandidate.budget ≤ OffsetDegreeBudget.budget := by
    norm_num [FirstCompressionCandidate.budget,OffsetDegreeBudget.budget]
  exact (ENNReal.div_le_div_right (Nat.cast_le.mpr degrees) _).trans LookupStreamWorkRate.budget_rate

theorem conditional {A : Type} (program : Program A) (position : ℕ) (world : World) (dummy : Digest) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}]) {other | SafeEvent program position dummy other} ≤
        OffsetWorkPosition.charge program position world := by
  let replay := ParentFactorFiber.replay (OracleProgram.prefix_replay position program)
  by_cases attained : ∃ reference, (ParentFactorFiber.extend (runPrefix position program) reference).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run ∧ SafeEvent program position dummy reference
  · obtain ⟨reference,same,⟨⟨candidate,_⟩,safe⟩⟩ := attained
    have good := GlobalReferenceBad.good program position dummy reference safe
    have included := FactorPosteriorMismatch.conditional_mono replay world (SafeEvent program position dummy)
      (fun other => LookupCompressionKernel.Event candidate.toCandidate dummy other) (by
        intro other fiber ⟨⟨otherCandidate,event⟩,otherSafe⟩
        have otherGood := GlobalReferenceBad.good program position dummy other otherSafe
        have counterSafe : ¬JobReferenceFixation.CounterBad program other := by
          rintro (receipt | context)
          · exact otherGood.receipt receipt
          · exact otherGood.context context
        have inputs := input_fixed program position reference other candidate otherCandidate (fiber.trans same.symm)
        have fixed := LookupCompressionKernel.event_fixed program position reference other candidate.toCandidate otherCandidate.toCandidate dummy
          inputs (FirstCompressionCandidate.ordinal_unique candidate otherCandidate inputs) (fiber.trans same.symm) good counterSafe
        rw [fixed]
        exact event)
    have bounded := RefinedCompressionKernel.bound_of_complexity program position reference candidate.toCandidate dummy
      FirstCompressionCandidate.budget candidate.bounded
    have fiberEq : {other | (ParentFactorFiber.extend (runPrefix position program) other).run =
        (ParentFactorFiber.extend (runPrefix position program) reference).run} =
      {other | (ParentFactorFiber.extend (runPrefix position program) other).run =
        (ParentFactorFiber.extend (runPrefix position program) world).run} := by
      ext other
      rw [same]
    rw [fiberEq] at bounded
    apply (included.trans bounded).trans
    have selected := candidate.first.selected
    rw [candidate.first_position,ParentFactorFiber.old_packet (runPrefix position program) world reference same] at selected
    have priced := budget_rate.trans (mul_le_mul' (Nat.cast_le.mpr (LookupStreamWorkRate.key_length candidate.toCandidate)) le_rfl)
    simpa only [OffsetWorkPosition.charge,OffsetWorkPosition.score,ScalarEquationWork.selectedBytes,selected] using priced
  · have included := FactorPosteriorMismatch.conditional_mono replay world (SafeEvent program position dummy) (fun _ => False)
      (fun other fiber occurred => attained ⟨other,fiber,occurred⟩)
    exact included.trans (by simp)

theorem bound {A : Type} (program : Program A) (position : ℕ) (dummy : Digest) :
    law {world | SafeEvent program position dummy world} ≤ ∫⁻ world, OffsetWorkPosition.charge program position world ∂law := by
  apply OracleFiberOuterBound.score_bound (ParentFactorFiber.replay (OracleProgram.prefix_replay position program))
    {world | SafeEvent program position dummy world} (fun packet => OffsetWorkPosition.score packet.1.1.1.1)
  intro world
  exact conditional program position world dummy

end
end FormalProof4FHE.HasteBoots.FirstCompressionWorkPosition
