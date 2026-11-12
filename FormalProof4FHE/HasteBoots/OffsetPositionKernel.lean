module
public import FormalProof4FHE.HasteBoots.LookupOffsetOrdinal
public import FormalProof4FHE.HasteBoots.OffsetClassKernel
@[expose] public section

/-! At one original first-read position, the prefix fixes the input and the
input fixes the job ordinal. All attained degree classes aggregate without
an input/ordinal/cost union multiplier. A degree budget is still explicit. -/
namespace FormalProof4FHE.HasteBoots.OffsetPositionKernel
open InputIndexedOracle (Input World law)
open OracleProgram (Program runPrefix)
open NativeRootMessage (Digest)
open MeasureTheory ProbabilityTheory
noncomputable section

def SafeEvent {A : Type} (program : Program A) (position : ℕ) (dummy : Digest) (world : World) : Prop :=
  ∃ input ordinal cost, OffsetClassKernel.SafeEvent program position input ordinal cost dummy world

def Event {A : Type} (program : Program A) (position budget : ℕ) (dummy : Digest) (world : World) : Prop :=
  ∃ input ordinal cost, cost ≤ budget ∧ OffsetClassKernel.Event program position input ordinal cost dummy world

def BoundedEvent {A : Type} (program : Program A) (position budget : ℕ) (dummy : Digest) (world : World) : Prop :=
  ∃ input ordinal cost, cost ≤ budget ∧ OffsetClassKernel.SafeEvent program position input ordinal cost dummy world

theorem safe_iff {A : Type} (program : Program A) (position budget : ℕ) (dummy : Digest) (world : World) :
    BoundedEvent program position budget dummy world ↔ Event program position budget dummy world ∧ ¬GlobalReferenceBad.Bad program dummy world := by
  constructor
  · rintro ⟨input,ordinal,cost,bounded,event,safe⟩
    exact ⟨⟨input,ordinal,cost,bounded,event⟩,safe⟩
  · rintro ⟨⟨input,ordinal,cost,bounded,event⟩,safe⟩
    exact ⟨input,ordinal,cost,bounded,event,safe⟩

theorem input_fixed {A : Type} (program : Program A) (position : ℕ) (world other : World)
    (left : LookupOffsetCompressionFixation.Candidate program position world)
    (right : LookupOffsetCompressionFixation.Candidate program position other)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run) :
    left.source.draw.coefficients.phase.pending.input = right.source.draw.coefficients.phase.pending.input := by
  have leftSelected := left.source.first.selected
  have rightSelected := right.source.first.selected
  rw [left.source.first_position] at leftSelected
  rw [right.source.first_position,ParentFactorFiber.old_packet (runPrefix position program) world other same] at rightSelected
  exact Option.some.inj (leftSelected.symm.trans rightSelected)

theorem indices_fixed {A : Type} (program : Program A) (position : ℕ)
    (leftInput rightInput : Input) (leftOrdinal rightOrdinal leftCost rightCost : ℕ) (world other : World)
    (left : OffsetClassKernel.Class program position leftInput leftOrdinal leftCost world)
    (right : OffsetClassKernel.Class program position rightInput rightOrdinal rightCost other) (dummy : Digest)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run)
    (good : JobReferenceFixation.Good program position world dummy) (safe : ¬JobReferenceFixation.CounterBad program other) :
    leftInput = rightInput ∧ leftOrdinal = rightOrdinal ∧ leftCost = rightCost := by
  have inputs := input_fixed program position world other left.val right.val same
  have ordinals := LookupOffsetOrdinal.unique left.val right.val inputs
  have costs := LookupOffsetKernel.complexity_fixed program position world other left.val right.val dummy inputs ordinals same good safe
  exact ⟨left.property.1.symm.trans (inputs.trans right.property.1),
    left.property.2.1.symm.trans (ordinals.trans right.property.2.1),
    left.property.2.2.1.symm.trans (costs.trans right.property.2.2.1)⟩

theorem cost_alternative {A : Type} (program : Program A) (position : ℕ) (world : World) (dummy : Digest) (event : Set World)
    (witness : ∀ other, (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run → other ∈ event → SafeEvent program position dummy other) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}]) event = 0 ∨
      ∃ reference, (ParentFactorFiber.extend (runPrefix position program) reference).run =
        (ParentFactorFiber.extend (runPrefix position program) world).run ∧ reference ∈ event ∧
        ∃ input ordinal cost, OffsetClassKernel.SafeEvent program position input ordinal cost dummy reference ∧
          (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
            (ParentFactorFiber.extend (runPrefix position program) world).run}]) event ≤
              (cost : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) := by
  let replay := ParentFactorFiber.replay (OracleProgram.prefix_replay position program)
  by_cases attained : ∃ reference, (ParentFactorFiber.extend (runPrefix position program) reference).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run ∧ reference ∈ event
  · obtain ⟨reference,same,occurred⟩ := attained
    obtain ⟨input,ordinal,cost,referenceSafe⟩ := witness reference same occurred
    obtain ⟨⟨packet,kernel⟩,safe⟩ := referenceSafe
    have good := GlobalReferenceBad.good program position dummy reference safe
    right
    refine ⟨reference,same,occurred,input,ordinal,cost,⟨⟨packet,kernel⟩,safe⟩,?_⟩
    apply (FactorPosteriorMismatch.conditional_mono replay world (fun other => other ∈ event)
      (OffsetClassKernel.SafeEvent program position input ordinal cost dummy) ?_).trans
      (OffsetClassKernel.conditional program position input ordinal cost world dummy)
    intro other fiber occurred
    obtain ⟨otherInput,otherOrdinal,otherCost,otherSafe⟩ := witness other fiber occurred
    obtain ⟨⟨otherPacket,healing⟩,otherGood⟩ := otherSafe
    have otherFacts := GlobalReferenceBad.good program position dummy other otherGood
    have counterSafe : ¬JobReferenceFixation.CounterBad program other := by
      rintro (receipt | context)
      · exact otherFacts.receipt receipt
      · exact otherFacts.context context
    obtain ⟨rfl,rfl,rfl⟩ := indices_fixed program position input otherInput ordinal otherOrdinal cost otherCost reference other
      packet otherPacket dummy (fiber.trans same.symm) good counterSafe
    exact ⟨⟨otherPacket,healing⟩,otherGood⟩
  · left
    have included := FactorPosteriorMismatch.conditional_mono replay world (fun other => other ∈ event) (fun _ => False)
      (fun other fiber occurred => attained ⟨other,fiber,occurred⟩)
    exact le_antisymm (by simpa using included) (by exact zero_le)

theorem conditional {A : Type} (program : Program A) (position budget : ℕ) (world : World) (dummy : Digest) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}])
      {other | BoundedEvent program position budget dummy other} ≤ (budget : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) := by
  rcases cost_alternative program position world dummy {other | BoundedEvent program position budget dummy other}
      (fun other _ ⟨input,ordinal,cost,_,safe⟩ => ⟨input,ordinal,cost,safe⟩) with zero | attained
  · rw [zero]; exact zero_le
  · obtain ⟨reference,same,⟨otherInput,otherOrdinal,otherCost,small,otherSafe⟩,input,ordinal,cost,referenceSafe,bounded⟩ := attained
    obtain ⟨⟨packet,_⟩,safe⟩ := referenceSafe
    obtain ⟨⟨otherPacket,_⟩,otherGood⟩ := otherSafe
    have good := GlobalReferenceBad.good program position dummy reference safe
    have otherFacts := GlobalReferenceBad.good program position dummy reference otherGood
    have counterSafe : ¬JobReferenceFixation.CounterBad program reference := by
      rintro (receipt | context)
      · exact otherFacts.receipt receipt
      · exact otherFacts.context context
    have costs := (indices_fixed program position input otherInput ordinal otherOrdinal cost otherCost reference reference packet otherPacket dummy rfl good counterSafe).2.2
    have numeric : (cost : ENNReal) ≤ budget := by exact_mod_cast costs.trans_le small
    exact bounded.trans (ENNReal.div_le_div_right numeric _)

theorem bound {A : Type} (program : Program A) (position budget : ℕ) (dummy : Digest) :
    law {world | BoundedEvent program position budget dummy world} ≤ (budget : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) :=
  OracleFiberOuterBound.uniform (ParentFactorFiber.replay (OracleProgram.prefix_replay position program)) _ _
    (fun world => conditional program position budget world dummy)

end
end FormalProof4FHE.HasteBoots.OffsetPositionKernel
