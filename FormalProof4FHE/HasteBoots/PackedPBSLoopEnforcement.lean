module
public import FormalProof4FHE.HasteBoots.PackedPBSHadamardNTTJointBound
public import FormalProof4FHE.HasteBoots.NTTSequenceHistory
public import FormalProof4FHE.HasteBoots.CrossStageSourceCoherence
@[expose] public section

/-! Every reached NTT child is related to its original Hadamard factor through
the actual final history. Wrong row transforms expose retained original risks
or the one shared final collision event. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSLoopEnforcement
open OracleSpec OracleComp
open NativeRootMessage (Digest)
open PackedPBSHadamardNTT (HadamardOutcome LoopOutcome)
open CommittedJointMatrixOpening (snapshots)
noncomputable section
variable {q log count b c r k n front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory FirstMessage Message : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points (ZMod q) n b)] [SampleableType (Fin b → Fin b → ZMod q)]
variable (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
  (family : PackedPBSOriginalReferences.Family count)
  (base : Fin (count+1) → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    b c r k front suffix m queries height)
  (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor count) (PBSHadamard.Term count)
    FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)

variable (dummy : Digest)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
  (first : HadamardOutcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (n := n) (count := count)
    (front := front) (queries := queries) (height := height))
  (later : LoopOutcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k) (count := count)
    (front := front) (queries := queries) (height := height))
  (supported : (first,some later) ∈ support (PackedPBSHadamardNTT.witness length psi primitive family base hs dummy initial))


include supported in
/-- Actual prefix and loop executions inherit the caller's audit. -/
theorem final_audited
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial) :
    CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) later.2 := by
  have reached := PackedPBSHadamardNTT.reached_loop length psi primitive family base hs dummy initial first later supported
  have prefixAudit := ZeroCheckConditionalSoundness.audited_witness (PackedPBSHadamardNTT.hadamard family hs)
    dummy initial audited first reached.2.1
  exact NTTSequenceHistory.audited (PackedPBSNTTLoop.factory length psi primitive family base) hs.encoding dummy
    (List.finRange (count+1)) first.2.1.2.memory first.2.2 later reached.2.2 prefixAudit

include supported in
/-- Every original Hadamard factor remains recorded after the complete loop. -/
theorem hadamard_recorded (factor : PBSHadamard.Factor count) :
    ⟨hs.tag factor,snapshots hs.tag first.1 factor⟩ ∈ later.2.checkpoints.checkpoints := by
  have reached := PackedPBSHadamardNTT.reached_loop length psi primitive family base hs dummy initial first later supported
  have recorded := ZeroCheckConditionalSoundness.fresh_recorded (PackedPBSHadamardNTT.hadamard family hs)
    dummy PBSHadamard.factors_complete initial first reached.2.1 factor
  exact NTTSequenceHistory.retains (PackedPBSNTTLoop.factory length psi primitive family base) hs.encoding dummy
    (List.finRange (count+1)) first.2.1.2.memory first.2.2 later reached.2.2 (hs.tag factor)
    (snapshots hs.tag first.1 factor) recorded

variable
    (entry : Fin (count+1) × Memory × NTTSequence.Child (F := ZMod q) (Input := Input) (Digest := Digest)
      (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory)
      (b := b) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height))
    (member : entry ∈ later.1.results)

include supported member in
/-- Each child records both of its own original sources before later reuse. -/
theorem child_recorded (side : Bool) :
    ⟨(base entry.1 entry.2.1).tag side,snapshots (base entry.1 entry.2.1).tag entry.2.2.1 side⟩ ∈
      entry.2.2.2.2.checkpoints.checkpoints := by
  have reached := PackedPBSHadamardNTT.reached_loop length psi primitive family base hs dummy initial first later supported
  obtain ⟨before,present⟩ := NTTSequenceSoundness.retained_child_support
    (PackedPBSNTTLoop.factory length psi primitive family base) hs.encoding dummy (List.finRange (count+1))
    first.2.1.2.memory first.2.2 later reached.2.2 entry member
  exact SequentialStageHistory.witness_recorded hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
    (CommittedJointMatrixOpening.requests (base entry.1 entry.2.1).tag [false,true])
    (PackedPBSNTTLoop.factory length psi primitive family base entry.1 entry.2.1).commit
    (AuthenticatedNTT.continuation (PackedPBSNTTLoop.factory length psi primitive family base entry.1 entry.2.1))
    before entry.2.2 present ((base entry.1 entry.2.1).tag side,entry.2.2.1.1.1 side)
    (List.mem_map_of_mem (by cases side <;> simp))

include supported member in
/-- A retained child's recording is present in the same final history as the Hadamard prefix. -/
theorem child_recorded_final (side : Bool) :
    ⟨(base entry.1 entry.2.1).tag side,snapshots (base entry.1 entry.2.1).tag entry.2.2.1 side⟩ ∈
      later.2.checkpoints.checkpoints := by
  have reached := PackedPBSHadamardNTT.reached_loop length psi primitive family base hs dummy initial first later supported
  exact NTTSequenceHistory.child_recorded (PackedPBSNTTLoop.factory length psi primitive family base) hs.encoding dummy
    (List.finRange (count+1)) first.2.1.2.memory first.2.2 later reached.2.2 entry member
    ((base entry.1 entry.2.1).tag side) (snapshots (base entry.1 entry.2.1).tag entry.2.2.1 side)
    (child_recorded length psi primitive family base hs dummy initial first later supported entry member side)

include supported member in
/-- Original roots are derived from actual retained support; equal decoding
geometry and context identify the same source outside the final collision event. -/
theorem source_association (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial)
    (encoding : (base entry.1 entry.2.1).encoding = hs.encoding)
    (domain : hs.domain = (base entry.1 entry.2.1).domain)
    (tags : (base entry.1 entry.2.1).tag true = hs.tag (PackedPBSOriginalReferences.evaluationFactor entry.1)) :
    AuthenticatedNTT.sources (PackedPBSNTTLoop.factory length psi primitive family base entry.1 entry.2.1)
      dummy capacity radius entry.2.2.1 true =
    QueryReindex.source ((base entry.1 entry.2.1).dimensions.trans hs.dimensions.symm)
      (AuthenticatedZeroCheck.sources hs dummy capacity radius first.1
        (PackedPBSOriginalReferences.evaluationFactor entry.1)) ∨
    CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) later.2 := by
  let t := PackedPBSNTTLoop.factory length psi primitive family base entry.1 entry.2.1
  have reached := PackedPBSHadamardNTT.reached_loop length psi primitive family base hs dummy initial first later supported
  have childRoots := PackedPBSNTTLoop.retained_roots length psi primitive family base hs.encoding dummy
    first.2.1.2.memory first.2.2 later reached.2.2 entry member
  have firstRoots := PackedPBSHadamardNTT.hadamard_roots length psi primitive family base hs dummy initial first later supported
  have roots : (snapshots t.tag entry.2.2.1 true).root =
      (snapshots hs.tag first.1 (PackedPBSOriginalReferences.evaluationFactor entry.1)).root := by
    change entry.2.2.1.1.1 true = first.1.1.1 _
    rw [firstRoots]
    exact (congrFun childRoots true).trans
      (congrArg NativeGoldParameterStore.Reference.root
        (PackedPBSOriginalReferences.evaluation_reference family entry.1)).symm
  have audit : CheckpointExecution.Audited t.encoding dummy (RecordedSourceCoherence.Shape Cfg height) later.2 := by
    change CheckpointExecution.Audited (base entry.1 entry.2.1).encoding dummy _ _
    rw [encoding]
    exact final_audited length psi primitive family base hs dummy initial first later supported audited
  exact CrossStageSourceCoherence.ntt_hadamard_eq_or_bad t hs family.keys dummy capacity radius later.2 audit
    (snapshots t.tag entry.2.2.1) (snapshots hs.tag first.1)
    (PackedPBSOriginalReferences.evaluationFactor entry.1)
    (child_recorded_final length psi primitive family base hs dummy initial first later supported entry member true)
    (hadamard_recorded length psi primitive family base hs dummy initial first later supported _)
    encoding.symm domain tags roots

include supported member in
/-- A wrong transform at any retained row is covered by one original child
risk or the final shared collision event. Child acceptance comes from the loop. -/
theorem false_transform_coverage (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial)
    (encoding : (base entry.1 entry.2.1).encoding = hs.encoding)
    (domain : hs.domain = (base entry.1 entry.2.1).domain)
    (tags : (base entry.1 entry.2.1).tag true = hs.tag (PackedPBSOriginalReferences.evaluationFactor entry.1))
    (accepted : later.1.accepted = true)
    (wrong : ∃ row : MatrixFold.Cube r,
      BlindRotationNTT.transform log psi
        (PackedNTTBinding.row length (AuthenticatedNTT.sources (base entry.1 entry.2.1)
          dummy capacity radius entry.2.2.1 false) row) ≠
      PackedNTTBinding.row length
        (QueryReindex.source ((base entry.1 entry.2.1).dimensions.trans hs.dimensions.symm)
          (AuthenticatedZeroCheck.sources hs dummy capacity radius first.1
            (PackedPBSOriginalReferences.evaluationFactor entry.1))) row) :
    NTTLoopProbability.AnyRisk (PackedPBSNTTLoop.factory length psi primitive family base)
      dummy capacity (fun _ => radius) later.1 ∨
    CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) later.2 := by
  let t := PackedPBSNTTLoop.factory length psi primitive family base entry.1 entry.2.1
  have reached := PackedPBSHadamardNTT.reached_loop length psi primitive family base hs dummy initial first later supported
  rcases source_association length psi primitive family base hs dummy initial first later supported entry member
      capacity radius audited encoding domain tags with same | bad
  · have passes := NTTSequenceHistory.accepted_children (PackedPBSNTTLoop.factory length psi primitive family base)
      hs.encoding dummy (List.finRange (count+1)) first.2.1.2.memory first.2.2 later reached.2.2 entry member accepted
    refine Or.inl ⟨entry,member,snapshots t.tag entry.2.2.1,?_,?_,passes⟩
    · intro side
      exact ⟨rfl,child_recorded length psi primitive family base hs dummy initial first later supported entry member side⟩
    · intro holds
      have relation : PackedNTT.Relation length psi
          (NTTCompression.sourceRows c r (AuthenticatedNTT.sources t dummy capacity radius entry.2.2.1 false))
          (NTTCompression.sourceRows c r (AuthenticatedNTT.sources t dummy capacity radius entry.2.2.1 true)) := holds
      obtain ⟨row,different⟩ := wrong
      have transformed := PackedNTTBinding.transform_of_relation length psi primitive _ _ relation row
      have projected := congrArg (fun table => PackedNTTBinding.row length table row) same
      exact different (transformed.trans projected)
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.PackedPBSLoopEnforcement
