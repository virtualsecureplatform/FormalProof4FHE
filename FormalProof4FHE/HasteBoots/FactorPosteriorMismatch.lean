module
public import FormalProof4FHE.HasteBoots.ProgramFactorFixation
@[expose] public section

/-! Conditional mass of any original-position factor disagreeing with a
good reference factor is bounded by the existing fresh-receipt bad event.
The counterfactual sample is existential, so no measurable chooser or matching
certificate for complete executions is assumed. -/
namespace FormalProof4FHE.HasteBoots.FactorPosteriorMismatch
open InputIndexedOracle (World law)
open OracleProgram (Program runPrefix)
open LookupFactorFixation (Scalar Point)
open ProgramFactorFixation (Observed)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section

def ScalarMismatch {A : Type} (program : Program A) (left : Scalar) (other : World) : Prop :=
  ∃ right : Scalar, right.view.reader.world = other ∧ Observed program right.toSample ∧
    left.view.reader.entry.coefficients.phase.pending.input = right.view.reader.entry.coefficients.phase.pending.input ∧
    left.position = right.position ∧ right.word ≠ left.word

def PointMismatch {A : Type} (program : Program A) (left : Point) (other : World) : Prop :=
  ∃ right : Point, right.view.reader.world = other ∧ Observed program right.toSample ∧
    left.view.reader.entry.coefficients.phase.pending.input = right.view.reader.entry.coefficients.phase.pending.input ∧
    left.position = right.position ∧ right.point ≠ left.point

theorem scalar_cover {A : Type} (program : Program A) (left : Scalar)
    (first : ProgramFirstStreamRead.First program left.view.reader.world left.view.reader.entry.coefficients.phase.pending.input)
    (observed : Observed program left.toSample)
    (freshSafe : ¬ ProgramReceiptCoverage.Bad program left.view.reader.world)
    (collisionSafe : ¬ ProgramReceiptCollision.Bad program left.view.reader.world) (other : World)
    (fiber : (ReceiptCandidateCompletion.extend (runPrefix first.position program) other).run =
      (ReceiptCandidateCompletion.extend (runPrefix first.position program) left.view.reader.world).run)
    (mismatch : ScalarMismatch program left other) : ProgramReceiptCoverage.Bad program other := by
  obtain ⟨right,sameWorld,rightObserved,sameInput,samePosition,different⟩ := mismatch
  subst other
  rcases ProgramFactorFixation.scalar_on_fiber program left right sameInput samePosition first observed rightObserved fiber with equal | bad
  · exact False.elim (different equal)
  · rcases bad with old | bad | collision
    · exact False.elim (freshSafe old)
    · exact bad
    · exact False.elim (collisionSafe collision)

theorem point_cover {A : Type} (program : Program A) (left : Point)
    (first : ProgramFirstStreamRead.First program left.view.reader.world left.view.reader.entry.coefficients.phase.pending.input)
    (observed : Observed program left.toSample)
    (freshSafe : ¬ ProgramReceiptCoverage.Bad program left.view.reader.world)
    (collisionSafe : ¬ ProgramReceiptCollision.Bad program left.view.reader.world) (other : World)
    (fiber : (ReceiptCandidateCompletion.extend (runPrefix first.position program) other).run =
      (ReceiptCandidateCompletion.extend (runPrefix first.position program) left.view.reader.world).run)
    (mismatch : PointMismatch program left other) : ProgramReceiptCoverage.Bad program other := by
  obtain ⟨right,sameWorld,rightObserved,sameInput,samePosition,different⟩ := mismatch
  subst other
  rcases ProgramFactorFixation.point_on_fiber program left right sameInput samePosition first observed rightObserved fiber with equal | bad
  · exact False.elim (different equal)
  · rcases bad with old | bad | collision
    · exact False.elim (freshSafe old)
    · exact bad
    · exact False.elim (collisionSafe collision)

/-- Event containment on a replay fiber lifts to its conditional law, even
when an existential counterfactual sample has not been chosen measurably. -/
theorem conditional_mono {T : Type} {past : World → NativeTranscript.Execution T}
    (replay : ObservationReplay.Replayable past) (world : World) (left right : World → Prop)
    (cover : ∀ other, (past other).run = (past world).run → left other → right other) :
    (law[|{other | (past other).run = (past world).run}]) {other | left other} ≤
      (law[|{other | (past other).run = (past world).run}]) {other | right other} := by
  rw [cond_apply (ObservationReplay.fiber_measurable replay world),cond_apply (ObservationReplay.fiber_measurable replay world)]
  have included : {other | (past other).run = (past world).run} ∩ {other | left other} ⊆
      {other | (past other).run = (past world).run} ∩ {other | right other} := by
    rintro other ⟨same,yes⟩
    exact ⟨same,cover other same yes⟩
  exact mul_le_mul_right (measure_mono included) _

theorem scalar_le {A : Type} (program : Program A) (left : Scalar)
    (first : ProgramFirstStreamRead.First program left.view.reader.world left.view.reader.entry.coefficients.phase.pending.input)
    (observed : Observed program left.toSample)
    (freshSafe : ¬ ProgramReceiptCoverage.Bad program left.view.reader.world)
    (collisionSafe : ¬ ProgramReceiptCollision.Bad program left.view.reader.world) :
    (law[|{other | (ReceiptCandidateCompletion.extend (runPrefix first.position program) other).run =
      (ReceiptCandidateCompletion.extend (runPrefix first.position program) left.view.reader.world).run}])
      {other | ScalarMismatch program left other} ≤
    (law[|{other | (ReceiptCandidateCompletion.extend (runPrefix first.position program) other).run =
      (ReceiptCandidateCompletion.extend (runPrefix first.position program) left.view.reader.world).run}])
      {other | ProgramReceiptCoverage.Bad program other} :=
  conditional_mono (ReceiptCandidateCompletion.replay (OracleProgram.prefix_replay first.position program)) left.view.reader.world _ _
    (scalar_cover program left first observed freshSafe collisionSafe)

theorem point_le {A : Type} (program : Program A) (left : Point)
    (first : ProgramFirstStreamRead.First program left.view.reader.world left.view.reader.entry.coefficients.phase.pending.input)
    (observed : Observed program left.toSample)
    (freshSafe : ¬ ProgramReceiptCoverage.Bad program left.view.reader.world)
    (collisionSafe : ¬ ProgramReceiptCollision.Bad program left.view.reader.world) :
    (law[|{other | (ReceiptCandidateCompletion.extend (runPrefix first.position program) other).run =
      (ReceiptCandidateCompletion.extend (runPrefix first.position program) left.view.reader.world).run}])
      {other | PointMismatch program left other} ≤
    (law[|{other | (ReceiptCandidateCompletion.extend (runPrefix first.position program) other).run =
      (ReceiptCandidateCompletion.extend (runPrefix first.position program) left.view.reader.world).run}])
      {other | ProgramReceiptCoverage.Bad program other} :=
  conditional_mono (ReceiptCandidateCompletion.replay (OracleProgram.prefix_replay first.position program)) left.view.reader.world _ _
    (point_cover program left first observed freshSafe collisionSafe)

end
end FormalProof4FHE.HasteBoots.FactorPosteriorMismatch
