module
public import FormalProof4FHE.HasteBoots.LookupSourceCandidate
@[expose] public section

/-! The original parent binds every grouped multiplicity row before the
child seed. Matching an original lookup stream fixes these raw rows with
only the existing parent-seed collision alternative. -/
namespace FormalProof4FHE.HasteBoots.LookupMultiplicityFixation
open InputIndexedOracle (World)
open NativeRootMessage (Digest)
open OracleProgram (Program runPrefix)
noncomputable section

structure Candidate {A : Type} (program : Program A) (position : ℕ) (world : World) where
  source : LookupSourceCandidate.Candidate program position world
  grouped : source.parent.parent.grouped = NativeLookupMultiplicityWire.grouped source.ctx.proof.multiplicities

theorem compare {A : Type} (program : Program A) (position : ℕ) (world other : World)
    (left : Candidate program position world) (right : Candidate program position other)
    (input : left.source.draw.coefficients.phase.pending.input = right.source.draw.coefficients.phase.pending.input)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run) :
    left.source.ctx.proof.values.multiplicities = right.source.ctx.proof.values.multiplicities ∨
      ProgramParentSeedCollision.Bad program world := by
  have leftQuote : NativeChildSeedView.quote left.source.draw.coefficients.phase.pending.input =
      some (InputIndexedOracle.block world left.source.parent.input 0 64) := by
    rw [left.source.parentInput]
    exact LookupDrawSeedQuote.quote left.source.origin left.source.job left.source.draw left.source.member
  have rightQuote : NativeChildSeedView.quote left.source.draw.coefficients.phase.pending.input =
      some (InputIndexedOracle.block other right.source.parent.input 0 64) := by
    rw [input,right.source.parentInput]
    exact LookupDrawSeedQuote.quote right.source.origin right.source.job right.source.draw right.source.member
  rcases OriginalSharedParent.compare_on_fiber program position world other _ _ _
      left.source.parent.parent right.source.parent.parent _ _ left.source.parent.known right.source.parent.known
      left.source.parent.parsed right.source.parent.parsed leftQuote rightQuote same with parents | bad
  · apply Or.inl
    exact NativeLookupMultiplicityWire.grouped_injective _ _
      (left.grouped.symm.trans ((congrArg SharedParentInputView.View.grouped parents).trans right.grouped))
  · exact Or.inr bad

def row {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) :=
  candidate.source.ctx.proof.values.multiplicities[
    (candidate.source.origin.ready.jobs.get candidate.source.index).tag.ordinal.val]?.getD []

/-- Select the same original request ordinal after prepared-job order has
been recovered. Repetitions never select a fresh independently chosen row. -/
theorem row_fixed {A : Type} (program : Program A) (position : ℕ) (world other : World)
    (left : Candidate program position world) (right : Candidate program position other)
    (input : left.source.draw.coefficients.phase.pending.input = right.source.draw.coefficients.phase.pending.input)
    (ordinal : left.source.index.val = right.source.index.val)
    (requests : left.source.ctx.requests = right.source.ctx.requests)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run)
    (safe : ¬ProgramParentSeedCollision.Bad program world) : row left = row right := by
  have counts := (compare program position world other left right input same).resolve_right safe
  have tags := OriginalJobOrdinal.tag left.source.origin right.source.origin requests left.source.index right.source.index ordinal
  unfold row
  rw [counts,tags]

/-- Source columns, selected request and its entire original raw count row
are fixed together on the existing good parent fiber. No per-row exception
or independently selected multiplicity witness is added. -/
theorem fixed {A : Type} (program : Program A) (position : ℕ) (world other : World)
    (left : Candidate program position world) (right : Candidate program position other) (dummy : Digest)
    (input : left.source.draw.coefficients.phase.pending.input = right.source.draw.coefficients.phase.pending.input)
    (ordinal : left.source.index.val = right.source.index.val)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run)
    (good : JobReferenceFixation.Good program position world dummy) (safe : ¬JobReferenceFixation.CounterBad program other) :
    left.source.ctx.registry = right.source.ctx.registry ∧
      left.source.ctx.requests = right.source.ctx.requests ∧
      HEq (LookupSourceCandidate.sources left.source dummy) (LookupSourceCandidate.sources right.source dummy) ∧
      row left = row right := by
  obtain ⟨registry,_,requests,sources⟩ := (LookupSourceCandidate.compare program position world other left.source right.source dummy input ordinal same).resolve_right
    (JobReferenceFixation.family_bad_false program position world other dummy good safe)
  exact ⟨registry,requests,sources,row_fixed program position world other left right input ordinal requests same good.parent⟩

end
end FormalProof4FHE.HasteBoots.LookupMultiplicityFixation
