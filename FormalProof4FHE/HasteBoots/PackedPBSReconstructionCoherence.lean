module
public import FormalProof4FHE.HasteBoots.PackedPBSFirstReconstruction
@[expose] public section

/-! The original NTT coefficient and reached reconstruction digit are compared
at the same actual final state, using retained original roots and checkpoints. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSReconstructionCoherence
open OracleSpec OracleComp
open NativeRootMessage (Digest)
open PackedPBSHadamardNTT (HadamardOutcome LoopOutcome)
open PackedPBSFirstReconstruction (LinearOutcome reconstruction)
open CommittedJointMatrixOpening (snapshots)
noncomputable section
variable {q log d b c r k n front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory FirstMessage Message : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points (ZMod q) n b)] [SampleableType (Fin b → Fin b → ZMod q)]
variable (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
  (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : PackedPBSDecompositionReferences.Inputs)
  (base : Fin (2*d+1) → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    b c r k front suffix m queries height)
  (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor (2*d)) (PBSHadamard.Term (2*d))
    FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
  (nodesEnough : 2*b ≤ q) (radix : ZMod q)
  (linearBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) b front suffix m queries height)

variable (dummy : Digest)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
  (first : HadamardOutcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (n := n) (count := 2*d)
    (front := front) (queries := queries) (height := height))
  (later : LoopOutcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k) (count := 2*d)
    (front := front) (queries := queries) (height := height))
  (child : LinearOutcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (d := d) (front := front) (suffix := suffix)
    (queries := queries) (height := height))
  (supported : ((first,some later),some child) ∈ support
    (PackedPBSFirstReconstruction.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial))

include supported in
/-- Supports expose exactly the reached predecessor and actual reconstruction state. -/
theorem child_support :
    later.1.accepted = true ∧
    (first,some later) ∈ support (PackedPBSHadamardNTT.witness length psi primitive family base hs dummy initial) ∧
    child ∈ support (MultiCommitmentPrefix.witness hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
      (CommittedJointMatrixOpening.requests
        (reconstruction family inputs nodesEnough radix linearBase false later.1.memory).tag
        (AuthenticatedLinear.factors (2*d+2)))
      (reconstruction family inputs nodesEnough radix linearBase false later.1.memory).commit
      (AuthenticatedLinear.continuation (reconstruction family inputs nodesEnough radix linearBase false later.1.memory)) later.2) := by
  obtain ⟨actual,equal,passed,prefixSupport,childSupport⟩ := PackedPBSFirstReconstruction.reached_reconstruction
    length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial (first,some later) child supported
  have same : later = actual := Option.some.inj equal
  subst actual
  exact ⟨passed,prefixSupport,childSupport⟩

include supported in
/-- The reconstruction audit is inherited from the actual accepted NTT loop. -/
theorem final_audited
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial) :
    CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) child.2.2 := by
  have supports := child_support length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial first later child supported
  have beforeAudit := PackedPBSLoopEnforcement.final_audited length psi primitive family base hs dummy initial
    first later supports.2.1 audited
  let l := reconstruction family inputs nodesEnough radix linearBase false later.1.memory
  have projected : ((child.1.1,child.2.1),child.2.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
        (RecordedSourceCoherence.Shape Cfg height)) (AuthenticatedLinear.program l)).run later.2) := by
    unfold AuthenticatedLinear.program
    rw [←MultiCommitmentPrefix.project_witness hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
      (CommittedJointMatrixOpening.requests l.tag (AuthenticatedLinear.factors (2*d+2))) l.commit
      (AuthenticatedLinear.continuation l) later.2,support_map]
    exact Set.mem_image_of_mem _ supports.2.2
  exact CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
    (RecordedSourceCoherence.Shape Cfg height) (AuthenticatedLinear.program l) later.2 beforeAudit _ projected

include supported in
/-- The child records every actual reconstruction column in its final history. -/
theorem linear_recorded (factor : Fin (2*d+2)) :
    ⟨(linearBase later.1.memory).tag factor,snapshots (linearBase later.1.memory).tag child.1 factor⟩ ∈
      child.2.2.checkpoints.checkpoints := by
  have supports := child_support length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial first later child supported
  let l := reconstruction family inputs nodesEnough radix linearBase false later.1.memory
  exact SequentialStageHistory.witness_recorded hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
    (CommittedJointMatrixOpening.requests l.tag (AuthenticatedLinear.factors (2*d+2))) l.commit
    (AuthenticatedLinear.continuation l) later.2 child supports.2.2
    ((linearBase later.1.memory).tag factor,child.1.1.1 factor)
    (List.mem_map_of_mem (AuthenticatedLinear.factors_complete factor))

variable (entry : Fin (2*d+1) × Memory × NTTSequence.Child (F := ZMod q) (Input := Input) (Digest := Digest)
    (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory)
    (b := b) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height))
  (member : entry ∈ later.1.results)

include supported member in
/-- Earlier NTT coefficient snapshots survive reconstruction, even on rejection. -/
theorem coefficient_recorded :
    ⟨(base entry.1 entry.2.1).tag false,snapshots (base entry.1 entry.2.1).tag entry.2.2.1 false⟩ ∈
      child.2.2.checkpoints.checkpoints := by
  have supports := child_support length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial first later child supported
  have earlier := PackedPBSLoopEnforcement.child_recorded_final length psi primitive family base hs dummy initial first later
    supports.2.1 entry member false
  let l := reconstruction family inputs nodesEnough radix linearBase false later.1.memory
  exact SequentialStageHistory.witness_retains hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
    (CommittedJointMatrixOpening.requests l.tag (AuthenticatedLinear.factors (2*d+2))) l.commit
    (AuthenticatedLinear.continuation l) later.2 child supports.2.2
    ((base entry.1 entry.2.1).tag false) (snapshots (base entry.1 entry.2.1).tag entry.2.2.1 false) earlier

include supported member in
/-- A reconstruction digit and its original NTT coefficient have one decoded
interpretation outside the same final collision event. Root facts are derived,
while encoding/domain/context/decoder conditions remain explicit. -/
theorem digit_source_association (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (level : Fin d) (slot : entry.1 = PackedPBSDecompositionReferences.digitSlot false level)
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial)
    (nttEncoding : (base entry.1 entry.2.1).encoding = hs.encoding)
    (linearEncoding : (linearBase later.1.memory).encoding = hs.encoding)
    (domain : (base entry.1 entry.2.1).domain = (linearBase later.1.memory).domain)
    (tags : (base entry.1 entry.2.1).tag false = (linearBase later.1.memory).tag (DecompositionLinear.digit level)) :
    AuthenticatedNTT.sources (base entry.1 entry.2.1) dummy capacity radius entry.2.2.1 false =
      QueryReindex.source (base entry.1 entry.2.1).dimensions
        (AuthenticatedLinear.sources (linearBase later.1.memory) dummy capacity radius child.1 (DecompositionLinear.digit level)) ∨
    CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) child.2.2 := by
  have supports := child_support length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial first later child supported
  have reached := PackedPBSHadamardNTT.reached_loop length psi primitive family base hs dummy initial first later supports.2.1
  have nttRoots := PackedPBSNTTLoop.retained_roots length psi primitive family base hs.encoding dummy
    first.2.1.2.memory first.2.2 later reached.2.2 entry member
  have linearRoots := PackedPBSFirstReconstruction.reconstruction_roots length psi primitive family inputs base hs nodesEnough
    radix linearBase dummy initial (first,some later) child supported
  have roots : (snapshots (base entry.1 entry.2.1).tag entry.2.2.1 false).root =
      (snapshots (linearBase later.1.memory).tag child.1 (DecompositionLinear.digit level)).root := by
    change entry.2.2.1.1.1 false = child.1.1.1 (DecompositionLinear.digit level)
    have coefficient : entry.2.2.1.1.1 false = family.coefficients (PackedPBSDecompositionReferences.digitSlot false level) := by
      simpa only [slot,Bool.false_eq_true,ite_false] using congrFun nttRoots false
    exact coefficient.trans (linearRoots.2 level).symm
  have same := CrossStageSourceCoherence.tables_eq_or_bad hs.encoding dummy (base entry.1 entry.2.1).domain capacity radius
    child.2.2 (final_audited length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial first later child supported audited)
    (base entry.1 entry.2.1).dimensions (base entry.1 entry.2.1).dimensions
    ((base entry.1 entry.2.1).tag false) ((linearBase later.1.memory).tag (DecompositionLinear.digit level))
    (snapshots (base entry.1 entry.2.1).tag entry.2.2.1 false)
    (snapshots (linearBase later.1.memory).tag child.1 (DecompositionLinear.digit level))
    (coefficient_recorded length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial first later child supported entry member)
    (linear_recorded length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial first later child supported _)
    tags roots
  rcases same with same | bad
  · left
    change QueryReindex.source (base entry.1 entry.2.1).dimensions
      (RecordedSourceCoherence.source hs.encoding dummy (base entry.1 entry.2.1).domain capacity radius
        ((base entry.1 entry.2.1).tag false) (snapshots (base entry.1 entry.2.1).tag entry.2.2.1 false)) = _ at same
    change QueryReindex.source (base entry.1 entry.2.1).dimensions
      (RecordedSourceCoherence.source (base entry.1 entry.2.1).encoding dummy (base entry.1 entry.2.1).domain capacity radius
        ((base entry.1 entry.2.1).tag false) (snapshots (base entry.1 entry.2.1).tag entry.2.2.1 false)) =
      QueryReindex.source (base entry.1 entry.2.1).dimensions
      (RecordedSourceCoherence.source (linearBase later.1.memory).encoding dummy (linearBase later.1.memory).domain capacity radius
        ((linearBase later.1.memory).tag (DecompositionLinear.digit level))
        (snapshots (linearBase later.1.memory).tag child.1 (DecompositionLinear.digit level)))
    rw [nttEncoding,linearEncoding,←domain]
    exact same
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.PackedPBSReconstructionCoherence
