module
public import FormalProof4FHE.HasteBoots.PackedPBSReconstructionJointBound
public import FormalProof4FHE.HasteBoots.PackedPBSComparisonStage
@[expose] public section

/-! The first comparison call is reached only after all reconstruction checks.
It keeps the actual digit/borrow registry, post-opening memory and shared cache.
Changing ghost geometry requires explicit compatibility for inherited audits. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSFirstComparisons
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

def erasePrior (prior : Prior) :=
  (PackedPBSFirstReconstruction.eraseBefore prior.1,
    prior.2.map (fun child => (child.1.1,child.2.1)))

def priorState (prior : Prior) := PackedPBSReconstructionJointBound.finalState prior

/-- The actual call uses the complete reconstruction verifier result and its
last opening memory. It does not proceed after algebra or opening rejection. -/
def program (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Result d) := do
  let prior ← PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase
  match prior.2 with
  | none => pure (prior,none)
  | some child =>
    if AuthenticatedLinear.accepted child.2 then
      let compared ← PackedPBSComparisonStage.program s child.1.1 child.2.2.memory
      pure (prior,some compared)
    else pure (prior,none)

def finish (dummy : Digest) (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Result d)
    (prior : Prior) : ProbComp (Prior × Option (PackedPBSComparisonStage.Outcome s)) := do
  match prior.2 with
  | none => pure (prior,none)
  | some child =>
    if AuthenticatedLinear.accepted child.2.1 then
      let compared ← PackedPBSComparisonStage.witness hs.encoding dummy s child.1.1.1 child.2.1.2.memory
        (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height)
          (fun cfg => BinaryTree.Skeleton.perfect (s.heights cfg)) child.2.2)
      pure (prior,some compared)
    else pure (prior,none)

def witness (dummy : Digest) (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Result d)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) := do
  let prior ← PackedPBSFirstReconstruction.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial
  finish hs dummy s prior

def finalState (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Result d)
    (outcome : Prior × Option (PackedPBSComparisonStage.Outcome s)) : PackedPBSComparisonStage.State s :=
  match outcome.2 with
  | none => CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height)
      (fun cfg => BinaryTree.Skeleton.perfect (s.heights cfg)) (priorState outcome.1)
  | some compared => compared.2.2.2


/-- The reached predecessor is exactly the original shared-cache program. -/
theorem project_prior (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) :
    (fun prior => (erasePrior prior,(priorState prior).hash.cache)) <$>
      PackedPBSFirstReconstruction.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial =
    (simulateQ (CheckpointExecution.canonical (Cfg := Cfg) (QueryImpl.ofLift unifSpec ProbComp))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)).run initial.hash.cache := by
  have projected := congrArg (fun experiment =>
    Prod.map id (fun current : CheckpointExecution.State (Input := Input) (Digest := Digest)
      (RecordedSourceCoherence.Shape Cfg height) => current.hash.cache) <$> experiment)
    (PackedPBSFirstReconstruction.project_witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial)
  rw [Functor.map_map,CheckpointExecution.project_run] at projected
  exact projected

/-- The geometry switch is passive: every real answer, rejection branch and
cache entry agrees with the actual program, even without geometry compatibility. -/
theorem project_witness (dummy : Digest) (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Result d)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) :
    (fun outcome => ((erasePrior outcome.1,outcome.2.map (PackedPBSComparisonStage.erase s)),
      (finalState s outcome).hash.cache)) <$>
      witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s initial =
    (simulateQ (CheckpointExecution.canonical (Cfg := Cfg) (QueryImpl.ofLift unifSpec ProbComp))
      (program length psi primitive family inputs base hs nodesEnough radix linearBase s)).run initial.hash.cache := by
  simp only [program,simulateQ_bind,StateT.run_bind]
  rw [←project_prior length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial]
  simp only [witness,map_bind,bind_map_left]
  congr 1
  funext prior
  cases equal : prior.2 with
  | none => simp [finish,erasePrior,finalState,priorState,PackedPBSReconstructionJointBound.finalState,
      equal,CheckpointShapeTransport.state,map_pure,simulateQ_pure,StateT.run_pure]
  | some child =>
    simp only [erasePrior,equal,Option.map_some]
    by_cases passed : AuthenticatedLinear.accepted child.2.1 = true
    · simp only [finish,equal,passed,ite_true,map_bind,map_pure,simulateQ_bind,StateT.run_bind,
        simulateQ_pure,StateT.run_pure,Option.map_some,finalState]
      have projected := PackedPBSComparisonStage.project_canonical hs.encoding dummy s child.1.1.1 child.2.1.2.memory
        (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height)
          (fun cfg => BinaryTree.Skeleton.perfect (s.heights cfg)) child.2.2)
      simp only [CheckpointShapeTransport.state] at projected
      simp only [priorState,PackedPBSReconstructionJointBound.finalState,equal]
      rw [←projected]
      simp only [bind_map_left]
      rfl
    · simp [finish,equal,passed,finalState,priorState,PackedPBSReconstructionJointBound.finalState,
        CheckpointShapeTransport.state,map_pure,simulateQ_pure,StateT.run_pure]


/-- Reaching comparisons derives acceptance of the FULL reconstruction and
exposes the exact transported history, roots and final opening memory. -/
theorem reached_comparisons (dummy : Digest) (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Result d)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (prior : Prior) (compared : PackedPBSComparisonStage.Outcome s)
    (supported : (prior,some compared) ∈ support
      (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s initial)) :
    ∃ child, prior.2 = some child ∧ AuthenticatedLinear.accepted child.2.1 = true ∧
      prior ∈ support (PackedPBSFirstReconstruction.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial) ∧
      compared ∈ support (PackedPBSComparisonStage.witness hs.encoding dummy s child.1.1.1 child.2.1.2.memory
        (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height)
          (fun cfg => BinaryTree.Skeleton.perfect (s.heights cfg)) child.2.2)) := by
  simp only [witness,support_bind,Set.mem_iUnion] at supported
  obtain ⟨selected,selectedSupported,remainder⟩ := supported
  cases equal : selected.2 with
  | none => simp [finish,equal] at remainder
  | some child =>
    by_cases passed : AuthenticatedLinear.accepted child.2.1 = true
    · simp only [finish,equal,passed,ite_true,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at remainder
      obtain ⟨actual,actualSupported,same⟩ := remainder
      have samePrior : prior = selected := congrArg Prod.fst same
      have sameCompared : compared = actual := Option.some.inj (congrArg Prod.snd same)
      subst selected
      subst actual
      exact ⟨child,equal,passed,selectedSupported,actualSupported⟩
    · simp [finish,equal,passed] at remainder

/-- Every supported predecessor inherits the audit at its actual final state. -/
theorem prior_audited (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (valid : CheckpointExecution.Audited hs.encoding dummy _ initial)
    (prior : Prior)
    (supported : prior ∈ support
      (PackedPBSFirstReconstruction.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial)) :
    CheckpointExecution.Audited hs.encoding dummy _ (priorState prior) := by
  have actual : (erasePrior prior,priorState prior) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
        (RecordedSourceCoherence.Shape Cfg height))
        (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)).run initial) := by
    rw [←PackedPBSFirstReconstruction.project_witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy _
    (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase) initial valid _ actual

/-- The reached comparison source tuple is fixed by the successful linear
registry and its actual final opening memory, before any pair/helper work. -/
theorem comparison_sources (dummy : Digest) (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Result d)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (prior : Prior) (compared : PackedPBSComparisonStage.Outcome s)
    (supported : (prior,some compared) ∈ support
      (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s initial)) :
    ∃ child, prior.2 = some child ∧ AuthenticatedLinear.accepted child.2.1 = true ∧
      compared.1.1 = PackedPBSComparisonStage.sources child.1.1.1 child.2.1.2.memory := by
  obtain ⟨child,equal,passed,_,present⟩ := reached_comparisons length psi primitive family inputs base hs
    nodesEnough radix linearBase dummy s initial prior compared supported
  exact ⟨child,equal,passed,(PackedPBSComparisonStage.source_eq hs.encoding dummy s _ _ _ compared present).1⟩


/-- The actual first-half digit roots are inherited from the original PBS
coefficient family, rather than supplied afresh by the comparison prover. -/
theorem comparison_digit_roots (dummy : Digest) (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Result d)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (prior : Prior) (compared : PackedPBSComparisonStage.Outcome s)
    (supported : (prior,some compared) ∈ support
      (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s initial))
    (level : Fin d) :
    compared.1.1.1 (PackedPBSComparisonReferences.digitSlot level) =
      family.coefficients (PackedPBSDecompositionReferences.digitSlot false level) := by
  obtain ⟨child,equal,_,priorSupported,present⟩ := reached_comparisons length psi primitive family inputs base hs
    nodesEnough radix linearBase dummy s initial prior compared supported
  have childSupport : (prior.1,some child) ∈ support
      (PackedPBSFirstReconstruction.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial) := by
    rw [←equal]
    exact priorSupported
  have roots := (PackedPBSFirstReconstruction.reconstruction_roots length psi primitive family inputs base hs nodesEnough
    radix linearBase dummy initial prior.1 child childSupport).2 level
  have fixed := (PackedPBSComparisonStage.source_eq hs.encoding dummy s _ _ _ compared present).1
  have source := congrArg (fun first => first.1 (PackedPBSComparisonReferences.digitSlot level)) fixed
  simpa only [PackedPBSComparisonStage.sources,PackedPBSComparisonReferences.linear_digit] using source.trans roots

omit [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points (ZMod q) n b)] [SampleableType (Fin b → Fin b → ZMod q)] in
/-- The phase change preserves the inherited audit precisely when all recorded
contexts keep their geometry. No source truth is assumed by this condition. -/
theorem finish_audited (dummy : Digest) (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Result d)
    (prior : Prior)
    (valid : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) (priorState prior))
    (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (fun cfg => BinaryTree.Skeleton.perfect (s.heights cfg)) (priorState prior).checkpoints)
    (outcome : Prior × Option (PackedPBSComparisonStage.Outcome s))
    (supported : outcome ∈ support (finish hs dummy s prior)) :
    CheckpointExecution.Audited hs.encoding dummy _ (finalState s outcome) := by
  have incoming := CheckpointShapeTransport.audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
    (fun cfg => BinaryTree.Skeleton.perfect (s.heights cfg)) (priorState prior) compatible valid
  cases equal : prior.2 with
  | none =>
    simp only [finish,equal,support_pure,Set.mem_singleton_iff] at supported
    subst outcome
    exact incoming
  | some child =>
    by_cases passed : AuthenticatedLinear.accepted child.2.1 = true
    · simp only [finish,equal,passed,ite_true,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at supported
      obtain ⟨compared,present,same⟩ := supported
      subst outcome
      have childAudit : CheckpointExecution.Audited hs.encoding dummy _
          (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height)
            (fun cfg => BinaryTree.Skeleton.perfect (s.heights cfg)) child.2.2) := by
        simpa only [priorState,PackedPBSReconstructionJointBound.finalState,equal] using incoming
      exact PackedPBSComparisonStage.audited hs.encoding dummy s _ _ _ childAudit compared present
    · simp [finish,equal,passed] at supported
      subst outcome
      exact incoming

/-- All supported extended returns retain an audit, including rejected stages. -/
theorem final_audited (dummy : Digest) (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Result d)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (valid : CheckpointExecution.Audited hs.encoding dummy _ initial)
    (compatible : ∀ prior ∈ support
      (PackedPBSFirstReconstruction.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial),
      CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
        (fun cfg => BinaryTree.Skeleton.perfect (s.heights cfg)) (priorState prior).checkpoints)
    (outcome : Prior × Option (PackedPBSComparisonStage.Outcome s))
    (supported : outcome ∈ support
      (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s initial)) :
    CheckpointExecution.Audited hs.encoding dummy _ (finalState s outcome) := by
  simp only [witness,support_bind,Set.mem_iUnion] at supported
  obtain ⟨prior,priorSupported,present⟩ := supported
  exact finish_audited hs dummy s prior
    (prior_audited length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial valid prior priorSupported)
    (compatible prior priorSupported) outcome present

omit [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points (ZMod q) n b)] [SampleableType (Fin b → Fin b → ZMod q)] in
/-- No phase transition or rejected path erases an earlier collision event. -/
theorem finish_bad_persistent (dummy : Digest) (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Result d)
    (prior : Prior)
    (bad : CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) (priorState prior))
    (outcome : Prior × Option (PackedPBSComparisonStage.Outcome s))
    (supported : outcome ∈ support (finish hs dummy s prior)) :
    CheckpointCollision.Bad _ (finalState s outcome) := by
  have incoming := (CheckpointShapeTransport.bad_iff (RecordedSourceCoherence.Shape Cfg height)
    (fun cfg => BinaryTree.Skeleton.perfect (s.heights cfg)) (priorState prior)).mpr bad
  cases equal : prior.2 with
  | none =>
    simp only [finish,equal,support_pure,Set.mem_singleton_iff] at supported
    subst outcome
    exact incoming
  | some child =>
    by_cases passed : AuthenticatedLinear.accepted child.2.1 = true
    · simp only [finish,equal,passed,ite_true,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at supported
      obtain ⟨compared,present,same⟩ := supported
      subst outcome
      have childBad : CheckpointCollision.Bad _
          (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height)
            (fun cfg => BinaryTree.Skeleton.perfect (s.heights cfg)) child.2.2) := by
        simpa only [priorState,PackedPBSReconstructionJointBound.finalState,equal] using incoming
      exact PackedPBSComparisonStage.bad_persistent hs.encoding dummy s _ _ _ childBad compared present
    · simp [finish,equal,passed] at supported
      subst outcome
      exact incoming


/-- A conditional comparison bound is averaged over the actually reached
reconstruction returns, retaining inherited audits and rejected paths. -/
theorem safe_comparison_bound (dummy : Digest) (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Result d)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (valid : CheckpointExecution.Audited hs.encoding dummy _ initial)
    (compatible : ∀ prior ∈ support
      (PackedPBSFirstReconstruction.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial),
      CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
        (fun cfg => BinaryTree.Skeleton.perfect (s.heights cfg)) (priorState prior).checkpoints)
    (event : Prior → PackedPBSComparisonStage.Outcome s → Prop) (epsilon : ENNReal)
    (conditional : ∀ prior child,
      prior ∈ support (PackedPBSFirstReconstruction.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial) →
      prior.2 = some child → AuthenticatedLinear.accepted child.2.1 = true →
      CheckpointExecution.Audited hs.encoding dummy _
        (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height)
          (fun cfg => BinaryTree.Skeleton.perfect (s.heights cfg)) child.2.2) →
      Pr{let compared ← (PackedPBSComparisonStage.witness hs.encoding dummy s child.1.1.1 child.2.1.2.memory
        (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height)
          (fun cfg => BinaryTree.Skeleton.perfect (s.heights cfg)) child.2.2))}[
        event prior compared ∧ ¬CheckpointCollision.Bad _ compared.2.2.2] ≤ epsilon) :
    Pr{let outcome ← (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s initial)}[
      ∃ compared, outcome.2 = some compared ∧ event outcome.1 compared ∧
        ¬CheckpointCollision.Bad _ (finalState s outcome)] ≤ epsilon := by
  unfold witness
  apply prEvent_bind_le_of_forall_le_of_support
  intro prior supported
  cases equal : prior.2 with
  | none => simp [finish,equal,prEvent_norm]
  | some child =>
    by_cases passed : AuthenticatedLinear.accepted child.2.1 = true
    · have incoming := CheckpointShapeTransport.audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
        (fun cfg => BinaryTree.Skeleton.perfect (s.heights cfg)) (priorState prior)
        (compatible prior supported)
        (prior_audited length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial valid prior supported)
      have childAudit : CheckpointExecution.Audited hs.encoding dummy _
          (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height)
            (fun cfg => BinaryTree.Skeleton.perfect (s.heights cfg)) child.2.2) := by
        simpa only [priorState,PackedPBSReconstructionJointBound.finalState,equal] using incoming
      have bound := conditional prior child supported equal passed childAudit
      simp only [finish,equal,passed,ite_true,prEvent_norm,Option.some.injEq,finalState]
      convert bound using 1
      apply prEvent_congr
      intro compared
      simp
    · simp [finish,equal,passed,prEvent_norm]


/-- Every comparison return retains each exact original owner from
reconstruction, including its pre-comparison snapshot rather than a replacement. -/
theorem comparison_retains (dummy : Digest) (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Result d)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (prior : Prior) (compared : PackedPBSComparisonStage.Outcome s)
    (supported : (prior,some compared) ∈ support
      (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s initial))
    (tag : Cfg)
    (entry : MerkleTreeMultiExtractability.Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (RecordedSourceCoherence.Shape Cfg height)) tag)
    (recorded : ⟨tag,entry⟩ ∈ (priorState prior).checkpoints.checkpoints) :
    ⟨tag,CheckpointShapeTransport.checkpoint (RecordedSourceCoherence.Shape Cfg height)
      (fun cfg => BinaryTree.Skeleton.perfect (s.heights cfg)) tag entry⟩ ∈
        compared.2.2.2.checkpoints.checkpoints := by
  obtain ⟨child,equal,_,_,present⟩ := reached_comparisons length psi primitive family inputs base hs
    nodesEnough radix linearBase dummy s initial prior compared supported
  have original : ⟨tag,entry⟩ ∈ child.2.2.checkpoints.checkpoints := by
    simpa only [priorState,PackedPBSReconstructionJointBound.finalState,equal] using recorded
  have transported := (CheckpointShapeTransport.recorded_iff (RecordedSourceCoherence.Shape Cfg height)
    (fun cfg => BinaryTree.Skeleton.perfect (s.heights cfg)) child.2.2.checkpoints tag entry).mpr original
  exact PackedPBSComparisonStage.retains hs.encoding dummy s _ _ _ tag _ transported compared present

end
end FormalProof4FHE.HasteBoots.PackedPBSFirstComparisons
