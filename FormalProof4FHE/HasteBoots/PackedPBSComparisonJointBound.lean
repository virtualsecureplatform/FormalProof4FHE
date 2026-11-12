module
public import FormalProof4FHE.HasteBoots.PackedPBSComparisonSharedExecution
@[expose] public section

/-! Earlier and comparison arithmetic risks share the extended final exception.
Stopping or nonreturning continuations need no losslessness assumption. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSComparisonJointBound
open PackedPBSFirstComparisons (erasePrior priorState finalState)
open OracleSpec OracleComp
open NativeRootMessage (Digest)
open PackedPBSHadamardNTT (HadamardOutcome LoopOutcome)
open PackedPBSFirstReconstruction (Before LinearOutcome beforeState reconstruction)
noncomputable section
/-- Union arithmetic events under one shared exception predicate. -/
theorem safe_union {A : Type} (experiment : ProbComp A)
    (left right clear : A → Prop) (leftRate rightRate : ENNReal)
    (left_bound : Pr{let outcome ← experiment}[left outcome ∧ clear outcome] ≤ leftRate)
    (right_bound : Pr{let outcome ← experiment}[right outcome ∧ clear outcome] ≤ rightRate) :
    Pr{let outcome ← experiment}[(left outcome ∨ right outcome) ∧ clear outcome] ≤ leftRate + rightRate := by
  have equal : Pr{let outcome ← experiment}[(left outcome ∨ right outcome) ∧ clear outcome] =
      Pr{let outcome ← experiment}[(left outcome ∧ clear outcome) ∨ (right outcome ∧ clear outcome)] := by
    apply prEvent_congr
    intro outcome
    exact or_and_right
  rw [equal]
  exact (prEvent_or_le _ _ _).trans (add_le_add left_bound right_bound)

variable {q log d b c r k n front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory FirstMessage Message : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points (ZMod q) n b)] [SampleableType (Fin b → Fin b → ZMod q)]
abbrev Outcome := Before (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k) (n := n) (d := d)
    (front := front) (queries := queries) (height := height) ×
  Option (LinearOutcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (d := d) (front := front) (suffix := suffix)
    (queries := queries) (height := height))

variable (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
  (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : PackedPBSDecompositionReferences.Inputs)
  (base : Fin (2*d+1) → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    b c r k front suffix m queries height)
  (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor (2*d)) (PBSHadamard.Term (2*d))
    FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
  (nodesEnough : 2*b ≤ q) (radix : ZMod q)
  (linearBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) b front suffix m queries height)


local notation "Prior" => Outcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
  (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k) (n := n) (d := d)
  (front := front) (suffix := suffix) (queries := queries) (height := height)

variable {Helper Result : Type}


omit [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points (ZMod q) n b)] [SampleableType (Fin b → Fin b → ZMod q)] in
/-- The comparison continuation never substitutes a different predecessor. -/
theorem finish_prior (dummy : Digest) (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Result d)
    (prior : Prior) (outcome : Prior × Option (PackedPBSComparisonStage.Outcome s))
    (supported : outcome ∈ support (PackedPBSFirstComparisons.finish hs dummy s prior)) : outcome.1 = prior := by
  cases equal : prior.2 with
  | none =>
    simp only [PackedPBSFirstComparisons.finish,equal,support_pure,Set.mem_singleton_iff] at supported
    exact congrArg Prod.fst supported
  | some child =>
    by_cases passed : AuthenticatedLinear.accepted child.2.1 = true
    · simp only [PackedPBSFirstComparisons.finish,equal,passed,ite_true,support_bind,support_pure,
        Set.mem_iUnion,Set.mem_singleton_iff] at supported
      obtain ⟨compared,_,same⟩ := supported
      exact congrArg Prod.fst same
    · simp [PackedPBSFirstComparisons.finish,equal,passed] at supported
      exact congrArg Prod.fst supported

/-- A safe earlier event cannot become more likely after adaptive comparison
work, even when that work has no returning branch. Old exceptions persist. -/
theorem earlier_safe_event_le (dummy : Digest) (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Result d)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (event : Prior → Prop) :
    Pr{let outcome ← (PackedPBSFirstComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s initial)}[
      event outcome.1 ∧ ¬CheckpointCollision.Bad _ (finalState s outcome)] ≤
    Pr{let prior ← (PackedPBSFirstReconstruction.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial)}[
      event prior ∧ ¬CheckpointCollision.Bad _ (priorState prior)] := by
  unfold PackedPBSFirstComparisons.witness
  apply prEvent_bind_le_prEvent_of_forall_eq_zero _ _
    (fun prior => event prior ∧ ¬CheckpointCollision.Bad _ (priorState prior)) _
  intro prior outside
  apply prEvent_eq_zero_of_forall_mem_support
  intro outcome supported accepted
  have same := finish_prior hs dummy s prior outcome supported
  apply outside
  refine ⟨same ▸ accepted.1,?_⟩
  intro bad
  exact accepted.2 (PackedPBSFirstComparisons.finish_bad_persistent hs dummy s prior bad outcome supported)

/-- The two arithmetic rates add outside the SAME extended final exception. -/
theorem safe_joint_bound (dummy : Digest) (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Result d)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (earlier : Prior → Prop) (comparison : PackedPBSComparisonStage.Outcome s → Prop)
    (earlierRate comparisonRate : ENNReal)
    (earlier_bound : Pr{let prior ← (PackedPBSFirstReconstruction.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial)}[
      earlier prior ∧ ¬CheckpointCollision.Bad _ (priorState prior)] ≤ earlierRate)
    (comparison_bound : Pr{let outcome ← (PackedPBSFirstComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s initial)}[
      ∃ compared, outcome.2 = some compared ∧ comparison compared ∧ ¬CheckpointCollision.Bad _ (finalState s outcome)] ≤ comparisonRate) :
    Pr{let outcome ← (PackedPBSFirstComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s initial)}[
      (earlier outcome.1 ∨ ∃ compared, outcome.2 = some compared ∧ comparison compared) ∧
        ¬CheckpointCollision.Bad _ (finalState s outcome)] ≤ earlierRate + comparisonRate := by
  have predecessor := (earlier_safe_event_le length psi primitive family inputs base hs nodesEnough radix linearBase dummy s initial earlier).trans earlier_bound
  refine safe_union _ _ _ _ earlierRate comparisonRate predecessor ?_
  convert comparison_bound using 1
  apply prEvent_congr
  intro outcome
  constructor
  · rintro ⟨⟨compared,equal,risk⟩,clear⟩
    exact ⟨compared,equal,risk,clear⟩
  · rintro ⟨compared,equal,risk,clear⟩
    exact ⟨⟨compared,equal,risk⟩,clear⟩

end
end FormalProof4FHE.HasteBoots.PackedPBSComparisonJointBound
