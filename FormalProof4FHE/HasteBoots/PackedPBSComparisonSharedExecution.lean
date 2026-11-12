module
public import FormalProof4FHE.HasteBoots.PackedPBSFirstComparisons
public import FormalProof4FHE.HasteBoots.CheckpointScopedTransport
@[expose] public section

/-! A structural record scope turns the first reconstruction/comparison boundary
into one full shared execution, including its monitor and one collision charge. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSComparisonSharedExecution
open PackedPBSFirstComparisons (erasePrior priorState finalState)
open OracleSpec OracleComp
open NativeRootMessage (Digest)
open PackedPBSHadamardNTT (HadamardOutcome LoopOutcome)
open PackedPBSFirstReconstruction (Before LinearOutcome beforeState reconstruction)
noncomputable section
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


/-- Scoped syntax discharges the terminal geometry condition on actual returns. -/
theorem prefix_compatible (dummy : Digest) (newShape : Cfg → BinaryTree.Skeleton)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height) newShape initial.checkpoints)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = newShape tag)
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase))
    (prior : Prior)
    (supported : prior ∈ support
      (PackedPBSFirstReconstruction.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial)) :
    CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height) newShape (priorState prior).checkpoints := by
  have actual : (erasePrior prior,priorState prior) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
        (RecordedSourceCoherence.Shape Cfg height))
        (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)).run initial) := by
    rw [←PackedPBSFirstReconstruction.project_witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointRecordScope.compatible_run (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy _ _
    _ restricted initial compatible _ actual

/-- The full predecessor state agrees with the later handler's geometry. -/
theorem project_prior (dummy : Digest) (newShape : Cfg → BinaryTree.Skeleton)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height) newShape initial.checkpoints)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = newShape tag)
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)) :
    (fun prior => (erasePrior prior,CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) newShape (priorState prior))) <$>
      PackedPBSFirstReconstruction.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy newShape)
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)).run
      (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) newShape initial) := by
  have projected := congrArg (fun experiment =>
    Prod.map id (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) newShape) <$> experiment)
    (PackedPBSFirstReconstruction.project_witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial)
  rw [Functor.map_map,CheckpointScopedTransport.run (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
    _ _ _ restricted initial compatible] at projected
  exact projected

/-- Erasure recovers the complete extended shared state, not just its cache. -/
theorem project_witness (dummy : Digest) (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Result d)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (fun cfg => BinaryTree.Skeleton.perfect (s.heights cfg)) initial.checkpoints)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (s.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)) :
    (fun outcome => ((erasePrior outcome.1,outcome.2.map (PackedPBSComparisonStage.erase s)),finalState s outcome)) <$>
      PackedPBSFirstComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s initial =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
      (fun cfg => BinaryTree.Skeleton.perfect (s.heights cfg)))
      (PackedPBSFirstComparisons.program length psi primitive family inputs base hs nodesEnough radix linearBase s)).run
      (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height)
        (fun cfg => BinaryTree.Skeleton.perfect (s.heights cfg)) initial) := by
  simp only [PackedPBSFirstComparisons.program,simulateQ_bind,StateT.run_bind]
  rw [←project_prior length psi primitive family inputs base hs nodesEnough radix linearBase dummy _ initial compatible restricted]
  simp only [PackedPBSFirstComparisons.witness,map_bind,bind_map_left]
  congr 1
  funext prior
  cases equal : prior.2 with
  | none => simp [PackedPBSFirstComparisons.finish,erasePrior,finalState,priorState,
      PackedPBSReconstructionJointBound.finalState,equal,map_pure,simulateQ_pure,StateT.run_pure]
  | some child =>
    simp only [erasePrior,equal,Option.map_some]
    by_cases passed : AuthenticatedLinear.accepted child.2.1 = true
    · simp only [PackedPBSFirstComparisons.finish,equal,passed,ite_true,map_bind,map_pure,
        simulateQ_bind,StateT.run_bind,simulateQ_pure,StateT.run_pure,Option.map_some,finalState]
      have projected := PackedPBSComparisonStage.project_witness hs.encoding dummy s child.1.1.1 child.2.1.2.memory
        (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height)
          (fun cfg => BinaryTree.Skeleton.perfect (s.heights cfg)) child.2.2)
      simp only [priorState,PackedPBSReconstructionJointBound.finalState,equal]
      rw [←projected]
      simp only [bind_map_left]
      rfl
    · simp [PackedPBSFirstComparisons.finish,equal,passed,finalState,priorState,
        PackedPBSReconstructionJointBound.finalState,map_pure,simulateQ_pure,StateT.run_pure]

/-- From the empty shared state, all availability/collision exceptions across
Hadamard, the NTT loop, reconstruction and comparisons pay one whole-run charge. -/
theorem final_bad_le_charge [Fintype Digest] (dummy : Digest)
    (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Result d)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (s.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)) :
    Pr{let outcome ← (PackedPBSFirstComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      CheckpointCollision.Bad _ (finalState s outcome)] ≤
    ExpectedHazard.charge (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
      (fun cfg => BinaryTree.Skeleton.perfect (s.heights cfg)))
      (CheckpointCollision.loss unifSpec (fun cfg => BinaryTree.Skeleton.perfect (s.heights cfg)))
      (PackedPBSFirstComparisons.program length psi primitive family inputs base hs nodesEnough radix linearBase s)
      (CheckpointExecution.empty (fun cfg => BinaryTree.Skeleton.perfect (s.heights cfg))) := by
  have emptyCompatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (fun cfg => BinaryTree.Skeleton.perfect (s.heights cfg))
      (CheckpointExecution.empty (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)).checkpoints := by
    intro tag entry member
    cases member
  have projected := project_witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s
    (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)) emptyCompatible restricted
  have emptyState : CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height)
      (fun cfg => BinaryTree.Skeleton.perfect (s.heights cfg))
      (CheckpointExecution.empty (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) =
      CheckpointExecution.empty (fun cfg => BinaryTree.Skeleton.perfect (s.heights cfg)) := rfl
  rw [emptyState] at projected
  have bound := CheckpointCollision.failure_from_empty_le_charge (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
    (fun cfg => BinaryTree.Skeleton.perfect (s.heights cfg))
    (PackedPBSFirstComparisons.program length psi primitive family inputs base hs nodesEnough radix linearBase s)
  rw [←projected,prEvent_map] at bound
  exact bound


/-- Arithmetic risks outside the single final exception combine with its one
whole-program charge, without any additional local authentication charge. -/
theorem risk_or_bad_bound [Fintype Digest] (dummy : Digest)
    (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Result d)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (s.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase))
    (risk : Prior × Option (PackedPBSComparisonStage.Outcome s) → Prop) (epsilon : ENNReal)
    (safe_bound : Pr{let outcome ← (PackedPBSFirstComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      risk outcome ∧ ¬CheckpointCollision.Bad _ (finalState s outcome)] ≤ epsilon) :
    Pr{let outcome ← (PackedPBSFirstComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      risk outcome ∨ CheckpointCollision.Bad _ (finalState s outcome)] ≤ epsilon +
      ExpectedHazard.charge (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
      (fun cfg => BinaryTree.Skeleton.perfect (s.heights cfg)))
      (CheckpointCollision.loss unifSpec (fun cfg => BinaryTree.Skeleton.perfect (s.heights cfg)))
      (PackedPBSFirstComparisons.program length psi primitive family inputs base hs nodesEnough radix linearBase s)
      (CheckpointExecution.empty (fun cfg => BinaryTree.Skeleton.perfect (s.heights cfg))) := by
  have failure := final_bad_le_charge length psi primitive family inputs base hs nodesEnough radix linearBase dummy s restricted
  refine (prEvent_mono _ _ (fun outcome =>
    (risk outcome ∧ ¬CheckpointCollision.Bad _ (finalState s outcome)) ∨
      CheckpointCollision.Bad _ (finalState s outcome)) ?_).trans
    ((prEvent_or_le _ _ _).trans (add_le_add safe_bound failure))
  intro outcome event
  obtain arithmetic | bad := event
  · by_cases bad : CheckpointCollision.Bad _ (finalState s outcome)
    · exact Or.inr bad
    · exact Or.inl ⟨arithmetic,bad⟩
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.PackedPBSComparisonSharedExecution
