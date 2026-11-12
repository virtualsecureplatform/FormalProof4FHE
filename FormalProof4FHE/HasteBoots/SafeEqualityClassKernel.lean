module
public import FormalProof4FHE.HasteBoots.EqualityClassKernel
@[expose] public section

/-! Adaptive equality classes outside the existing shared global reference
bad event have a uniform 63/q^3 bound. Only attained successful classes supply
references; empty classes contribute zero without a normalization premise. -/
namespace FormalProof4FHE.HasteBoots.SafeEqualityClassKernel
open InputIndexedOracle (Input World law)
open OracleProgram (Program runPrefix)
open NativeRootMessage (Digest)
open MeasureTheory ProbabilityTheory
noncomputable section

def Event {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal : ℕ)
    (dummy : Digest) (world : World) : Prop :=
  EqualityClassKernel.Event program position input ordinal dummy world ∧ ¬GlobalReferenceBad.Bad program dummy world

theorem covered_conditional {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal : ℕ)
    (world : World) (dummy : Digest) (event : Set World)
    (witness : ∀ other, (ParentFactorFiber.extend (runPrefix position program) other).run =
        (ParentFactorFiber.extend (runPrefix position program) world).run → other ∈ event → Event program position input ordinal dummy other) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}]) event ≤ (63 : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) := by
  let replay := ParentFactorFiber.replay (OracleProgram.prefix_replay position program)
  by_cases attained : ∃ reference, (ParentFactorFiber.extend (runPrefix position program) reference).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run ∧ reference ∈ event
  · obtain ⟨reference,same,occurred⟩ := attained
    obtain ⟨⟨packet,_⟩,safe⟩ := witness reference same occurred
    have good := GlobalReferenceBad.good program position dummy reference safe
    have included := FactorPosteriorMismatch.conditional_mono replay world (fun other => other ∈ event)
      (fun other => EqualityCandidateKernel.Event packet.val dummy other) (by
        intro other fiber occurred
        obtain ⟨⟨otherPacket,healing⟩,otherSafe⟩ := witness other fiber occurred
        have otherGood := GlobalReferenceBad.good program position dummy other otherSafe
        have counterSafe : ¬JobReferenceFixation.CounterBad program other := by
          rintro (receipt | context)
          · exact otherGood.receipt receipt
          · exact otherGood.context context
        have fixed := EqualityCandidateKernel.event_fixed packet.val otherPacket.val dummy
          (packet.property.1.trans otherPacket.property.1.symm) (packet.property.2.trans otherPacket.property.2.symm)
          (fiber.trans same.symm) good counterSafe
        rw [fixed]
        exact healing)
    have bounded := RefinedEqualityKernel.bound_63 program position reference packet.val dummy
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

theorem conditional {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal : ℕ)
    (world : World) (dummy : Digest) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}]) {other | Event program position input ordinal dummy other} ≤
      (63 : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) :=
  covered_conditional program position input ordinal world dummy _ (fun _ _ occurred => occurred)

/-- Outer-measure averaging needs no measurability assumption on the
existential attained class or on its reference choice. -/
theorem bound {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal : ℕ) (dummy : Digest) :
    law {world | Event program position input ordinal dummy world} ≤ (63 : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) :=
  OracleFiberOuterBound.uniform (ParentFactorFiber.replay (OracleProgram.prefix_replay position program)) _ _
    (fun world => conditional program position input ordinal world dummy)

end
end FormalProof4FHE.HasteBoots.SafeEqualityClassKernel
