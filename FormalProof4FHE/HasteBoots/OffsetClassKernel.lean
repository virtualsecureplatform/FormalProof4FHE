module
public import FormalProof4FHE.HasteBoots.LookupOffsetKernel
@[expose] public section

/-! Attained original accepted-offset classes are indexed by actual reciprocal
degree complexity as well as input and job ordinal. Their safe adaptive bound has
no reference-choice normalization or successful-world probability floor.
The union of all complexity indices retains every original candidate. -/
namespace FormalProof4FHE.HasteBoots.OffsetClassKernel
open InputIndexedOracle (Input World law)
open OracleProgram (Program runPrefix)
open NativeRootMessage (Digest)
open MeasureTheory ProbabilityTheory
noncomputable section

abbrev Class {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal cost : ℕ) (world : World) :=
  {candidate : LookupOffsetCompressionFixation.Candidate program position world //
    candidate.source.draw.coefficients.phase.pending.input = input ∧ candidate.source.index.val = ordinal ∧
      LookupOffsetKernel.complexity candidate = cost ∧
      (candidate.source.origin.ready.jobs.get candidate.source.index).tag.request.terminal.logicalLength.val < NativeFields.goldilocksModulus}

def Event {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal cost : ℕ) (dummy : Digest) (world : World) : Prop :=
  ∃ candidate : Class program position input ordinal cost world, LookupOffsetKernel.Event candidate.val dummy world

def SafeEvent {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal cost : ℕ) (dummy : Digest) (world : World) : Prop :=
  Event program position input ordinal cost dummy world ∧ ¬GlobalReferenceBad.Bad program dummy world

def Lifetime {A : Type} (program : Program A) (dummy : Digest) (world : World) : Prop :=
  ∃ position input ordinal cost, Event program position input ordinal cost dummy world

theorem of_candidate {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : LookupOffsetCompressionFixation.Candidate program position world) (dummy : Digest)
    (small : (candidate.source.origin.ready.jobs.get candidate.source.index).tag.request.terminal.logicalLength.val < NativeFields.goldilocksModulus)
    (occurred : LookupOffsetKernel.Event candidate dummy world) : Lifetime program dummy world :=
  ⟨position,candidate.source.draw.coefficients.phase.pending.input,candidate.source.index.val,LookupOffsetKernel.complexity candidate,
    ⟨⟨candidate,rfl,rfl,rfl,small⟩,occurred⟩⟩

theorem cost_unique {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal leftCost rightCost : ℕ)
    (world other : World) (left : Class program position input ordinal leftCost world) (right : Class program position input ordinal rightCost other)
    (dummy : Digest)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run)
    (good : JobReferenceFixation.Good program position world dummy) (safe : ¬JobReferenceFixation.CounterBad program other) :
    leftCost = rightCost := by
  have fixed := LookupOffsetKernel.complexity_fixed program position world other left.val right.val dummy
    (left.property.1.trans right.property.1.symm) (left.property.2.1.trans right.property.2.1.symm) same good safe
  exact left.property.2.2.1.symm.trans (fixed.trans right.property.2.2.1)

theorem covered_conditional {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal cost : ℕ)
    (world : World) (dummy : Digest) (event : Set World)
    (witness : ∀ other, (ParentFactorFiber.extend (runPrefix position program) other).run =
        (ParentFactorFiber.extend (runPrefix position program) world).run → other ∈ event → SafeEvent program position input ordinal cost dummy other) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}]) event ≤
        (cost : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) := by
  let replay := ParentFactorFiber.replay (OracleProgram.prefix_replay position program)
  by_cases attained : ∃ reference, (ParentFactorFiber.extend (runPrefix position program) reference).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run ∧ reference ∈ event
  · obtain ⟨reference,same,occurred⟩ := attained
    obtain ⟨⟨packet,_⟩,safe⟩ := witness reference same occurred
    have good := GlobalReferenceBad.good program position dummy reference safe
    have included := FactorPosteriorMismatch.conditional_mono replay world (fun other => other ∈ event)
      (fun other => LookupOffsetKernel.Event packet.val dummy other) (by
        intro other fiber occurred
        obtain ⟨⟨otherPacket,healing⟩,otherSafe⟩ := witness other fiber occurred
        have otherGood := GlobalReferenceBad.good program position dummy other otherSafe
        have counterSafe : ¬JobReferenceFixation.CounterBad program other := by
          rintro (receipt | context)
          · exact otherGood.receipt receipt
          · exact otherGood.context context
        have fixed := LookupOffsetKernel.event_fixed program position reference other packet.val otherPacket.val dummy
          (packet.property.1.trans otherPacket.property.1.symm) (packet.property.2.1.trans otherPacket.property.2.1.symm)
          (fiber.trans same.symm) good counterSafe
        rw [fixed]
        exact healing)
    have bounded := LookupOffsetKernel.bound program position reference packet.val dummy packet.property.2.2.2
    rw [packet.property.2.2.1] at bounded
    have fiberEq : {other | (ParentFactorFiber.extend (runPrefix position program) other).run =
        (ParentFactorFiber.extend (runPrefix position program) reference).run} =
      {other | (ParentFactorFiber.extend (runPrefix position program) other).run =
        (ParentFactorFiber.extend (runPrefix position program) world).run} := by
      ext other
      rw [same]
    rw [fiberEq] at bounded
    exact included.trans bounded
  · have included := FactorPosteriorMismatch.conditional_mono replay world (fun other => other ∈ event) (fun _ => False)
      (fun other fiber occurred => attained ⟨other,fiber,occurred⟩)
    have zero : (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
        (ParentFactorFiber.extend (runPrefix position program) world).run}]) event ≤ 0 := by simpa using included
    exact zero.trans (by exact zero_le)

theorem conditional {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal cost : ℕ)
    (world : World) (dummy : Digest) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}]) {other | SafeEvent program position input ordinal cost dummy other} ≤
        (cost : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) :=
  covered_conditional program position input ordinal cost world dummy _ (fun _ _ occurred => occurred)

/-- An event containing any complexity classes is either null on this fiber,
or priced by the actual unique cost of an attained safe reference. There is
no extra countable union or loss over possible complexity values. -/
theorem cost_alternative {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal : ℕ)
    (world : World) (dummy : Digest) (event : Set World)
    (witness : ∀ other, (ParentFactorFiber.extend (runPrefix position program) other).run =
        (ParentFactorFiber.extend (runPrefix position program) world).run → other ∈ event →
      ∃ cost, SafeEvent program position input ordinal cost dummy other) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}]) event = 0 ∨
      ∃ reference, (ParentFactorFiber.extend (runPrefix position program) reference).run =
        (ParentFactorFiber.extend (runPrefix position program) world).run ∧ reference ∈ event ∧
        ∃ cost, SafeEvent program position input ordinal cost dummy reference ∧
          (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
            (ParentFactorFiber.extend (runPrefix position program) world).run}]) event ≤
              (cost : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) := by
  let replay := ParentFactorFiber.replay (OracleProgram.prefix_replay position program)
  by_cases attained : ∃ reference, (ParentFactorFiber.extend (runPrefix position program) reference).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run ∧ reference ∈ event
  · obtain ⟨reference,same,occurred⟩ := attained
    obtain ⟨cost,referenceSafe⟩ := witness reference same occurred
    obtain ⟨⟨packet,kernel⟩,safe⟩ := referenceSafe
    have good := GlobalReferenceBad.good program position dummy reference safe
    right
    refine ⟨reference,same,occurred,cost,⟨⟨packet,kernel⟩,safe⟩,?_⟩
    apply (FactorPosteriorMismatch.conditional_mono replay world (fun other => other ∈ event)
      (SafeEvent program position input ordinal cost dummy) ?_).trans
      (conditional program position input ordinal cost world dummy)
    intro other fiber occurred
    obtain ⟨otherCost,otherSafe⟩ := witness other fiber occurred
    obtain ⟨⟨otherPacket,healing⟩,otherGood⟩ := otherSafe
    have otherFacts := GlobalReferenceBad.good program position dummy other otherGood
    have counterSafe : ¬JobReferenceFixation.CounterBad program other := by
      rintro (receipt | context)
      · exact otherFacts.receipt receipt
      · exact otherFacts.context context
    have costs := cost_unique program position input ordinal cost otherCost reference other packet otherPacket dummy
      (fiber.trans same.symm) good counterSafe
    subst otherCost
    exact ⟨⟨otherPacket,healing⟩,otherGood⟩
  · left
    have included := FactorPosteriorMismatch.conditional_mono replay world (fun other => other ∈ event) (fun _ => False)
      (fun other fiber occurred => attained ⟨other,fiber,occurred⟩)
    exact le_antisymm (by simpa using included) (by exact zero_le)

theorem bound {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal cost : ℕ) (dummy : Digest) :
    law {world | SafeEvent program position input ordinal cost dummy world} ≤ (cost : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) :=
  OracleFiberOuterBound.uniform (ParentFactorFiber.replay (OracleProgram.prefix_replay position program)) _ _
    (fun world => conditional program position input ordinal cost world dummy)

end
end FormalProof4FHE.HasteBoots.OffsetClassKernel
