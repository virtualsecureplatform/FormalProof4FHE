module
public import FormalProof4FHE.HasteBoots.FirstReadFiber
public import FormalProof4FHE.HasteBoots.ProgramReceiptCollision
@[expose] public section

/-! Original receipt-bound factors are fixed on the completed actual
pre-read fiber, outside the already bounded program-wide receipt events.
Named-payload and first-read witnesses are derived from actual observations;
no posterior equality of complete executions is supplied. -/
namespace FormalProof4FHE.HasteBoots.ProgramFactorFixation
open InputIndexedOracle (World)
open OracleProgram (Program run runPrefix)
open LookupFactorFixation (Sample Scalar Point)
open ProgramFirstStreamRead (First)
noncomputable section

def Observed {A : Type} (program : Program A) (sample : Sample) : Prop :=
  NativeTranscript.Observation.output (NativeReceiptPrefixView.key sample.state.phase.consumed) 0
    (InputIndexedOracle.bytes sample.view.reader.world (NativeReceiptPrefixView.key sample.state.phase.consumed) 0 64) ∈
      (run program sample.view.reader.world).run.2

def Bad {A : Type} (program : Program A) (left right : Sample) : Prop :=
  ProgramReceiptCoverage.Bad program left.view.reader.world ∨
    ProgramReceiptCoverage.Bad program right.view.reader.world ∨
      ProgramReceiptCollision.Bad program left.view.reader.world

theorem named_on_fiber {A : Type} (program : Program A) (left right : Sample)
    (sameInput : left.view.reader.entry.coefficients.phase.pending.input = right.view.reader.entry.coefficients.phase.pending.input)
    (first : First program left.view.reader.world left.view.reader.entry.coefficients.phase.pending.input)
    (leftObserved : Observed program left) (rightObserved : Observed program right)
    (fiber : (ReceiptCandidateCompletion.extend (runPrefix first.position program) right.view.reader.world).run =
      (ReceiptCandidateCompletion.extend (runPrefix first.position program) left.view.reader.world).run)
    (leftSafe : ¬ ProgramReceiptCoverage.Bad program left.view.reader.world)
    (rightSafe : ¬ ProgramReceiptCoverage.Bad program right.view.reader.world) :
    left.state.phase.consumed ∈ ReceiptPayloadView.payloads (runPrefix first.position program left.view.reader.world).run.2 ∧
      right.state.phase.consumed ∈ ReceiptPayloadView.payloads (runPrefix first.position program right.view.reader.world).run.2 := by
  have same := ReceiptCandidateCompletion.old_packet (runPrefix first.position program) left.view.reader.world right.view.reader.world fiber
  let other := FirstReadFiber.transport first right.view.reader.world same
  exact ⟨ProgramReceiptCoverage.named left program first leftObserved leftSafe,
    ProgramReceiptCoverage.named_at right program other rfl sameInput.symm rightObserved rightSafe⟩

theorem coefficients {A : Type} (program : Program A) (left right : Sample)
    (sameInput : left.view.reader.entry.coefficients.phase.pending.input = right.view.reader.entry.coefficients.phase.pending.input)
    (samePosition : left.position = right.position)
    (first : First program left.view.reader.world left.view.reader.entry.coefficients.phase.pending.input)
    (leftObserved : Observed program left) (rightObserved : Observed program right)
    (fiber : (ReceiptCandidateCompletion.extend (runPrefix first.position program) right.view.reader.world).run =
      (ReceiptCandidateCompletion.extend (runPrefix first.position program) left.view.reader.world).run) :
    right.state.values = left.state.values ∨ Bad program left right := by
  by_cases leftSafe : ProgramReceiptCoverage.Bad program left.view.reader.world
  · exact Or.inr (Or.inl leftSafe)
  by_cases rightSafe : ProgramReceiptCoverage.Bad program right.view.reader.world
  · exact Or.inr (Or.inr (Or.inl rightSafe))
  have named := named_on_fiber program left right sameInput first leftObserved rightObserved fiber leftSafe rightSafe
  rcases LookupFactorFixation.coefficients (OracleProgram.prefix_replay first.position program) left right sameInput samePosition named.1 named.2 fiber with equal | collision
  · exact Or.inl equal
  · exact Or.inr (Or.inr (Or.inr (ProgramReceiptCollision.prefix_covers program left.view.reader.world first.position collision)))

theorem scalar_on_fiber {A : Type} (program : Program A) (left right : Scalar)
    (sameInput : left.view.reader.entry.coefficients.phase.pending.input = right.view.reader.entry.coefficients.phase.pending.input)
    (samePosition : left.position = right.position)
    (first : First program left.view.reader.world left.view.reader.entry.coefficients.phase.pending.input)
    (leftObserved : Observed program left.toSample) (rightObserved : Observed program right.toSample)
    (fiber : (ReceiptCandidateCompletion.extend (runPrefix first.position program) right.view.reader.world).run =
      (ReceiptCandidateCompletion.extend (runPrefix first.position program) left.view.reader.world).run) :
    right.word = left.word ∨ Bad program left.toSample right.toSample := by
  rcases coefficients program left.toSample right.toSample sameInput samePosition first leftObserved rightObserved fiber with equal | bad
  · exact Or.inl (Option.some.inj (right.decoded.symm.trans ((congrArg NativeGoldLookupProducer.decode equal).trans left.decoded)))
  · exact Or.inr bad

theorem point_on_fiber {A : Type} (program : Program A) (left right : Point)
    (sameInput : left.view.reader.entry.coefficients.phase.pending.input = right.view.reader.entry.coefficients.phase.pending.input)
    (samePosition : left.position = right.position)
    (first : First program left.view.reader.world left.view.reader.entry.coefficients.phase.pending.input)
    (leftObserved : Observed program left.toSample) (rightObserved : Observed program right.toSample)
    (fiber : (ReceiptCandidateCompletion.extend (runPrefix first.position program) right.view.reader.world).run =
      (ReceiptCandidateCompletion.extend (runPrefix first.position program) left.view.reader.world).run) :
    right.point = left.point ∨ Bad program left.toSample right.toSample := by
  by_cases leftSafe : ProgramReceiptCoverage.Bad program left.view.reader.world
  · exact Or.inr (Or.inl leftSafe)
  by_cases rightSafe : ProgramReceiptCoverage.Bad program right.view.reader.world
  · exact Or.inr (Or.inr (Or.inl rightSafe))
  have named := named_on_fiber program left.toSample right.toSample sameInput first leftObserved rightObserved fiber leftSafe rightSafe
  rcases LookupFactorFixation.point_on_fiber (OracleProgram.prefix_replay first.position program) left right sameInput samePosition named.1 named.2 fiber with equal | collision
  · exact Or.inl equal
  · exact Or.inr (Or.inr (Or.inr (ProgramReceiptCollision.prefix_covers program left.view.reader.world first.position collision)))

end
end FormalProof4FHE.HasteBoots.ProgramFactorFixation
