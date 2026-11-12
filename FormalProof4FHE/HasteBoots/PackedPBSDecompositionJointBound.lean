module
public import FormalProof4FHE.HasteBoots.PackedPBSSecondComparisonProbability
public import FormalProof4FHE.HasteBoots.PackedPBSComparisonJointBound
@[expose] public section

/-! Compose both reconstruction/comparison halves under a single final exception. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSDecompositionJointBound
open OracleSpec OracleComp
open NativeRootMessage (Digest)
open PackedPBSSecondComparisons (sharedScheme beforeState finalState)
noncomputable section
variable {q log d b c r k n front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory FirstMessage Message : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points (ZMod q) n b)] [SampleableType (Fin b → Fin b → ZMod q)]
abbrev Outcome := PackedPBSFirstReconstruction.Before (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k) (n := n) (d := d)
    (front := front) (queries := queries) (height := height) ×
  Option (PackedPBSFirstReconstruction.LinearOutcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
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

variable {Helper Selection Root Data : Type}


abbrev ComparisonReturn := Selection × ShortCircuitSequence.Outcome Root Data Memory

local notation "Return" => ComparisonReturn (Selection := Selection) (Root := Root) (Data := Data) (Memory := Memory)

abbrev Before (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d) :=
  Prior × Option (PackedPBSComparisonStage.Outcome s)

local notation "Reached" => Before (q := q) (Response := Response) (CommitMemory := CommitMemory)
  (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix)
  (queries := queries) (height := height)

abbrev LinearOutcome (heights : Cfg → ℕ) :=
  AmbientLinear.Prefix heights (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) (count := 2*d+2) ×
  AmbientLinear.RunResult heights (F := ZMod q) (Input := Input) (Digest := Digest) (Response := Response)
    (Memory := Memory) (count := 2*d+2) (b := b) (front := front) (suffix := suffix) (height := height) (queries := queries)


local notation "Child" => LinearOutcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
  (Memory := Memory) (CommitMemory := CommitMemory) (d := d) (b := b) (front := front) (suffix := suffix)
  (queries := queries) (height := height)

abbrev SecondBefore (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d) :=
  Reached first × Option (Child first.heights)

local notation "Previous" => SecondBefore (q := q) (Response := Response) (CommitMemory := CommitMemory)
  (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix)
  (queries := queries) (height := height)

variable {SecondHelper SecondResult : Type}


abbrev ComparisonOutcome (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper SecondResult d) :=
  PackedPBSComparisonStage.Outcome (sharedScheme first.heights second)



/-- Earlier first-half risks and second-half reconstruction risks survive the
last comparison with the same final exception. Each input rate is used once. -/
theorem safe_joint_bound (dummy : Digest)
    (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper SecondResult d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (earlier : Reached first → Prop) (linear : Previous first → Prop)
    (comparison : ComparisonOutcome first second → Prop)
    (earlierRate linearRate comparisonRate : ENNReal)
    (earlier_bound : Pr{let before ← (PackedPBSFirstComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first initial)}[
      earlier before ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (PackedPBSFirstComparisons.finalState first before)] ≤ earlierRate)
    (linear_bound : Pr{let before ← (PackedPBSSecondReconstruction.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first secondBase initial)}[
      linear before ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (beforeState first before)] ≤ linearRate)
    (comparison_bound : Pr{let outcome ← (PackedPBSSecondComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial)}[
      ∃ compared, outcome.2 = some compared ∧ comparison compared ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState first second outcome)] ≤ comparisonRate) :
    Pr{let outcome ← (PackedPBSSecondComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial)}[
      ((earlier outcome.1.1 ∨ linear outcome.1) ∨ ∃ compared, outcome.2 = some compared ∧ comparison compared) ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState first second outcome)] ≤
      (earlierRate + linearRate) + comparisonRate := by
  have previous := (PackedPBSSecondReconstructionProbability.earlier_safe_event_le length psi primitive family inputs base hs
    nodesEnough radix linearBase dummy first secondBase initial earlier).trans earlier_bound
  have earlierFinal := (PackedPBSSecondComparisonProbability.earlier_safe_event_le length psi primitive family inputs base hs
    nodesEnough radix linearBase dummy first second secondBase initial (fun before => earlier before.1)).trans previous
  have linearFinal := (PackedPBSSecondComparisonProbability.earlier_safe_event_le length psi primitive family inputs base hs
    nodesEnough radix linearBase dummy first second secondBase initial linear).trans linear_bound
  have combined := PackedPBSComparisonJointBound.safe_union _ _ _ _ earlierRate linearRate earlierFinal linearFinal
  refine PackedPBSComparisonJointBound.safe_union _ _ _ _ (earlierRate + linearRate) comparisonRate combined ?_
  convert comparison_bound using 1
  apply prEvent_congr
  intro outcome
  constructor
  · rintro ⟨⟨compared,equal,risk⟩,clear⟩
    exact ⟨compared,equal,risk,clear⟩
  · rintro ⟨compared,equal,risk,clear⟩
    exact ⟨⟨compared,equal,risk⟩,clear⟩

/-- Add one charge for the complete actual prefix, including both halves and
rejected paths. No local comparison or reconstruction charge is added. -/
theorem risk_or_bad_bound [Fintype Digest] (dummy : Digest)
    (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper SecondResult d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (first.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase))
    (risk : Previous first × Option (ComparisonOutcome first second) → Prop) (epsilon : ENNReal)
    (safe_bound : Pr{let outcome ← (PackedPBSSecondComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      risk outcome ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState first second outcome)] ≤ epsilon) :
    Pr{let outcome ← (PackedPBSSecondComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      risk outcome ∨ CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState first second outcome)] ≤ epsilon +
      ExpectedHazard.charge (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
        (AmbientMatrixSource.Shape first.heights))
        (CheckpointCollision.loss unifSpec (AmbientMatrixSource.Shape first.heights))
        (PackedPBSSecondComparisons.program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase)
        (CheckpointExecution.empty (AmbientMatrixSource.Shape first.heights)) := by
  have failure := PackedPBSSecondComparisons.final_bad_le_charge length psi primitive family inputs base hs nodesEnough radix linearBase
    dummy first second secondBase restricted
  refine (prEvent_mono _ _ (fun outcome =>
    (risk outcome ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState first second outcome)) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState first second outcome)) ?_).trans
    ((prEvent_or_le _ _ _).trans (add_le_add safe_bound failure))
  intro outcome event
  obtain arithmetic | bad := event
  · by_cases bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState first second outcome)
    · exact Or.inr bad
    · exact Or.inl ⟨arithmetic,bad⟩
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.PackedPBSDecompositionJointBound
