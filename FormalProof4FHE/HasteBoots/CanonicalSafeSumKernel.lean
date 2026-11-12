module
public import FormalProof4FHE.HasteBoots.CanonicalSumAttainableEvent
public import FormalProof4FHE.HasteBoots.OracleFiberOuterBound
@[expose] public section

/-! Safe attained sum classes pay degree-one conditional loss after canonical
helper fixation. Global reference bad mass is excluded once for the class. -/
namespace FormalProof4FHE.HasteBoots.CanonicalSafeSumKernel
open InputIndexedOracle (Input World law)
open OracleProgram (Program runPrefix)
open NativeRootMessage (Digest)
open MeasureTheory ProbabilityTheory
noncomputable section

def Event {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal : ℕ)
    (dummy : Digest) (world : World) : Prop :=
  CanonicalSumAttainableEvent.Event program position input ordinal dummy world ∧ ¬GlobalReferenceBad.Bad program dummy world

theorem covered_conditional {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal : ℕ)
    (world : World) (dummy : Digest) (event : Set World)
    (witness : ∀ other, (ParentFactorFiber.extend (runPrefix position program) other).run =
        (ParentFactorFiber.extend (runPrefix position program) world).run → other ∈ event → Event program position input ordinal dummy other) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}]) event ≤ (1 : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) := by
  let replay := ParentFactorFiber.replay (OracleProgram.prefix_replay position program)
  by_cases attained : ∃ reference, (ParentFactorFiber.extend (runPrefix position program) reference).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run ∧ reference ∈ event
  · obtain ⟨reference,same,occurred⟩ := attained
    obtain ⟨⟨packet,_⟩,safe⟩ := witness reference same occurred
    have good := GlobalReferenceBad.good program position dummy reference safe
    have included := FactorPosteriorMismatch.conditional_mono replay world (fun other => other ∈ event)
      (fun other => CanonicalSumAttainableEvent.occurs packet dummy other) (by
        intro other fiber occurred
        obtain ⟨⟨otherPacket,healing⟩,otherSafe⟩ := witness other fiber occurred
        have otherGood := GlobalReferenceBad.good program position dummy other otherSafe
        have fixed := CanonicalCandidateFixation.class_fixed program position input ordinal world reference other packet.classed otherPacket.classed
          same fiber dummy good (fun bad => bad otherGood)
        exact (CanonicalSumAttainableEvent.transport packet otherPacket dummy fixed other).mpr healing)
    have bounded := CanonicalSumAttainableEvent.kernel_bound program position input ordinal reference packet dummy
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
      (1 : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) :=
  covered_conditional program position input ordinal world dummy _ (fun _ _ occurred => occurred)

theorem conditional_le_four {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal : ℕ)
    (world : World) (dummy : Digest) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}]) {other | Event program position input ordinal dummy other} ≤
      (4 : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) :=
  (conditional program position input ordinal world dummy).trans
    (ENNReal.div_le_div_right (by norm_num : (1 : ENNReal) ≤ 4) _)

/-- Outer-measure averaging needs no measurability assumption on the
existential attained class or on its reference choice. -/
theorem bound {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal : ℕ) (dummy : Digest) :
    law {world | Event program position input ordinal dummy world} ≤ (1 : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) :=
  OracleFiberOuterBound.uniform (ParentFactorFiber.replay (OracleProgram.prefix_replay position program)) _ _
    (fun world => conditional program position input ordinal world dummy)

end
end FormalProof4FHE.HasteBoots.CanonicalSafeSumKernel
