module
public import FormalProof4FHE.HasteBoots.HadamardNTTComposition
@[expose] public section

/-! Source association for reached children in the actual short-circuit
Hadamard/NTT witness. Both root binding and common-history membership are
recovered from support, with no standalone child-from-empty witnesses. -/
namespace FormalProof4FHE.HasteBoots.HadamardNTTSourceAssociation
open OracleSpec OracleComp
noncomputable section
variable {F Input Digest Cfg Response Memory CommitMemory FirstMessage Message : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {b c r k n count front suffix m queries height : ℕ} [SampleableType Digest]

omit [Field F] [DecidableEq F] in
/-- A fixed public commitment survives arbitrary incoming shared state,
requests and continuation; all original commitment calls remain in the run. -/
theorem fixed_roots {Roots Emission Result : Type}
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (roots : Roots) (commit : OracleComp (SharedSequence.Shared Cfg Input Digest) (Roots × Emission))
    (requests : Roots × Emission → List (Cfg × Digest))
    (next : Roots × Emission → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest)
      (RecordedSourceCoherence.Shape Cfg height))
    (outcome : ((Roots × Emission) × CheckpointExecution.State (Input := Input) (Digest := Digest)
        (RecordedSourceCoherence.Shape Cfg height)) × Result ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (supported : outcome ∈ support (MultiCommitmentPrefix.witness enc dummy (RecordedSourceCoherence.Shape Cfg height)
      requests (do let original ← commit; pure (roots,original.2)) next initial)) :
    outcome.1.1.1 = roots := by
  simp only [MultiCommitmentPrefix.witness,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at supported
  obtain ⟨first,firstSupported,last,_,equal⟩ := supported
  subst outcome
  simp only [simulateQ_bind,StateT.run_bind,simulateQ_pure,StateT.run_pure,
    support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at firstSupported
  obtain ⟨emission,_,equal⟩ := firstSupported
  subst first
  rfl

abbrev FirstOutcome :=
  AuthenticatedZeroCheck.Prefix (Factor := PBSHadamard.Factor count) (Digest := Digest)
      (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) ×
    AuthenticatedZeroCheck.RunResult (F := F) (Factor := PBSHadamard.Factor count) (Memory := Memory)
      (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
      (b := b) (n := n) (front := front) (queries := queries) (height := height)

abbrev SecondOutcome :=
  AuthenticatedNTT.Prefix (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input)
      (Cfg := Cfg) (height := height) ×
    AuthenticatedNTT.RunResult (F := F) (Memory := Memory) (Response := Response)
      (Input := Input) (Digest := Digest) (Cfg := Cfg) (b := b) (c := c) (r := r)
      (k := k) (front := front) (queries := queries) (height := height)

variable [SampleableType (Fin k → Fin r → F)] [SampleableType (Fin b → F)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix F (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points F n b)] [SampleableType (Fin b → Fin b → F)]
variable (coefficient : Digest) (expected : Fin count → Digest)
  (publicRoots : PBSHadamard.Factor count → Digest) (factor : PBSHadamard.Factor count)
  (ns : AuthenticatedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
  (hs : AuthenticatedZeroCheck.Scheme F (PBSHadamard.Factor count) (PBSHadamard.Term count)
    FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)

/-- Recover both actual child supports. The second starts at the first's final
state, even when the enclosing caller started from a nonempty history. -/
theorem child_supports (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (first : FirstOutcome (F := F) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (n := n) (count := count)
      (front := front) (queries := queries) (height := height))
    (second : SecondOutcome (F := F) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k)
      (front := front) (queries := queries) (height := height))
    (supported : (first,some second) ∈ support
      (HadamardNTTComposition.witness coefficient expected publicRoots factor ns hs dummy initial)) :
    let h := CallerBoundStageRoots.hadamard expected publicRoots hs
    let t := CallerBoundStageRoots.ntt coefficient (OwnedHadamardSoundness.roots expected publicRoots factor) ns
    first ∈ support (MultiCommitmentPrefix.witness hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
      (CommittedJointMatrixOpening.requests h.tag h.factors) h.commit (AuthenticatedZeroCheck.continuation h) initial) ∧
    second ∈ support (MultiCommitmentPrefix.witness hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
      (CommittedJointMatrixOpening.requests t.tag [false,true]) t.commit (AuthenticatedNTT.continuation t) first.2.2) := by
  let h := CallerBoundStageRoots.hadamard expected publicRoots hs
  let t := CallerBoundStageRoots.ntt coefficient (OwnedHadamardSoundness.roots expected publicRoots factor) ns
  have reached := ShortCircuitStageHistory.reached_second hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
    (CommittedJointMatrixOpening.requests h.tag h.factors) h.commit (AuthenticatedZeroCheck.continuation h)
    (fun entry => AuthenticatedZeroCheck.accepted entry.2)
    (fun _ => CommittedJointMatrixOpening.requests t.tag [false,true])
    (fun _ => t.commit) (fun _ => AuthenticatedNTT.continuation t) initial first second supported
  have joined := reached.2
  simp only [SequentialStageHistory.witness,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at joined
  obtain ⟨actualFirst,firstSupported,actualSecond,secondSupported,equal⟩ := joined
  have firstEq : first = actualFirst := congrArg Prod.fst equal
  have secondEq : second = actualSecond := congrArg Prod.snd equal
  subst actualFirst
  subst actualSecond
  exact ⟨firstSupported,secondSupported⟩

/-- Both public root functions are recovered from the same reached composed
run, without child-from-empty support or separate root certificates. -/
theorem root_functions (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (first : FirstOutcome (F := F) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (n := n) (count := count)
      (front := front) (queries := queries) (height := height))
    (second : SecondOutcome (F := F) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k)
      (front := front) (queries := queries) (height := height))
    (supported : (first,some second) ∈ support
      (HadamardNTTComposition.witness coefficient expected publicRoots factor ns hs dummy initial)) :
    first.1.1.1 = OwnedHadamardSoundness.roots expected publicRoots ∧
    second.1.1.1 = (fun side : Bool => if side then OwnedHadamardSoundness.roots expected publicRoots factor else coefficient) := by
  let h := CallerBoundStageRoots.hadamard expected publicRoots hs
  let t := CallerBoundStageRoots.ntt coefficient (OwnedHadamardSoundness.roots expected publicRoots factor) ns
  have supports := child_supports coefficient expected publicRoots factor ns hs dummy initial first second supported
  have hcommit : h.commit = (do
      let emission ← hs.commit
      pure (OwnedHadamardSoundness.roots expected publicRoots,emission.2)) := by
    simp only [h,CallerBoundStageRoots.hadamard,OwnedHadamardSoundness.stage,PBSHadamard.stage,bind_assoc,pure_bind]
  constructor
  · apply fixed_roots hs.encoding dummy (OwnedHadamardSoundness.roots expected publicRoots) hs.commit
      (CommittedJointMatrixOpening.requests h.tag h.factors) (AuthenticatedZeroCheck.continuation h) initial first
    rw [←hcommit]
    exact supports.1
  · exact fixed_roots hs.encoding dummy
      (fun side : Bool => if side then OwnedHadamardSoundness.roots expected publicRoots factor else coefficient)
      ns.commit (CommittedJointMatrixOpening.requests t.tag [false,true]) (AuthenticatedNTT.continuation t)
      first.2.2 second supports.2

/-- Source equality for the actual reached pair. Root binding, both recorded
checkpoints and the final audit are all derived from this one composed run. -/
theorem source_association (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (first : FirstOutcome (F := F) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (n := n) (count := count)
      (front := front) (queries := queries) (height := height))
    (second : SecondOutcome (F := F) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k)
      (front := front) (queries := queries) (height := height))
    (supported : (first,some second) ∈ support
      (HadamardNTTComposition.witness coefficient expected publicRoots factor ns hs dummy initial))
    (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial)
    (encoding : hs.encoding = ns.encoding) (domain : hs.domain = ns.domain)
    (tags : ns.tag true = hs.tag factor) :
    AuthenticatedNTT.sources ns dummy capacity radius second.1 true =
      QueryReindex.source (ns.dimensions.trans hs.dimensions.symm)
        (AuthenticatedZeroCheck.sources hs dummy capacity radius first.1 factor) ∨
    CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) second.2.2 := by
  let h := CallerBoundStageRoots.hadamard expected publicRoots hs
  let t := CallerBoundStageRoots.ntt coefficient (OwnedHadamardSoundness.roots expected publicRoots factor) ns
  have supports := child_supports coefficient expected publicRoots factor ns hs dummy initial first second supported
  have roots := root_functions coefficient expected publicRoots factor ns hs dummy initial first second supported
  have firstMember : (hs.tag factor,first.1.1.1 factor) ∈
      CommittedJointMatrixOpening.requests h.tag h.factors first.1.1 :=
    List.mem_map_of_mem (PBSHadamard.factors_complete factor)
  have secondMember : (ns.tag true,second.1.1.1 true) ∈
      CommittedJointMatrixOpening.requests t.tag [false,true] second.1.1 :=
    List.mem_map_of_mem (by simp)
  have firstRecorded := SequentialStageHistory.witness_recorded hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
    (CommittedJointMatrixOpening.requests h.tag h.factors) h.commit (AuthenticatedZeroCheck.continuation h)
    initial first supports.1 (hs.tag factor,first.1.1.1 factor) firstMember
  have retained := SequentialStageHistory.witness_retains hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
    (CommittedJointMatrixOpening.requests t.tag [false,true]) t.commit (AuthenticatedNTT.continuation t)
    first.2.2 second supports.2 (hs.tag factor) _ firstRecorded
  have secondRecorded := SequentialStageHistory.witness_recorded hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
    (CommittedJointMatrixOpening.requests t.tag [false,true]) t.commit (AuthenticatedNTT.continuation t)
    first.2.2 second supports.2 (ns.tag true,second.1.1.1 true) secondMember
  have joined : (first,second) ∈ support (SequentialStageHistory.witness hs.encoding dummy
      (RecordedSourceCoherence.Shape Cfg height)
      (CommittedJointMatrixOpening.requests h.tag h.factors) h.commit (AuthenticatedZeroCheck.continuation h)
      (fun _ => CommittedJointMatrixOpening.requests t.tag [false,true])
      (fun _ => t.commit) (fun _ => AuthenticatedNTT.continuation t) initial) := by
    simp only [SequentialStageHistory.witness,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff]
    exact ⟨first,supports.1,second,supports.2,rfl⟩
  have finalAudit := SequentialStageHistory.audited_final hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
    (CommittedJointMatrixOpening.requests h.tag h.factors) h.commit (AuthenticatedZeroCheck.continuation h)
    (fun _ => CommittedJointMatrixOpening.requests t.tag [false,true])
    (fun _ => t.commit) (fun _ => AuthenticatedNTT.continuation t) initial (first,second) joined audited
  have sameRoot : second.1.1.1 true = first.1.1.1 factor := by
    rw [roots.1,roots.2]
    rfl
  rw [encoding] at finalAudit
  exact CrossStageSourceCoherence.ntt_hadamard_eq_or_bad ns hs expected dummy capacity radius second.2.2 finalAudit
    (CommittedJointMatrixOpening.snapshots ns.tag second.1)
    (CommittedJointMatrixOpening.snapshots hs.tag first.1) factor secondRecorded retained
    encoding domain tags sameRoot


/-- The actual composed caller pays one whole-program collision charge for
all reached source-association failures, with no independent alias certificate. -/
theorem source_drift_bound [Fintype Digest] (dummy : Digest)
    (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (encoding : hs.encoding = ns.encoding) (domain : hs.domain = ns.domain)
    (tags : ns.tag true = hs.tag factor) :
    Pr{let outcome ← (HadamardNTTComposition.witness coefficient expected publicRoots factor ns hs dummy
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      ∃ second, outcome.2 = some second ∧
        AuthenticatedNTT.sources ns dummy capacity radius second.1 true ≠
          QueryReindex.source (ns.dimensions.trans hs.dimensions.symm)
            (AuthenticatedZeroCheck.sources hs dummy capacity radius outcome.1.1 factor)] ≤
    ExpectedHazard.charge
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height))
      (CheckpointCollision.loss unifSpec (RecordedSourceCoherence.Shape Cfg height))
      (HadamardNTTComposition.program coefficient expected publicRoots factor ns hs)
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)) := by
  have bound := CheckpointCollision.failure_from_empty_le_charge (QueryImpl.ofLift unifSpec ProbComp)
    hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
    (HadamardNTTComposition.program coefficient expected publicRoots factor ns hs)
  rw [←HadamardNTTComposition.project_witness coefficient expected publicRoots factor ns hs dummy
    (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)),prEvent_map] at bound
  refine le_trans (prEvent_mono_of_support _ _
    (fun outcome => match outcome.2 with
      | none => CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) outcome.1.2.2
      | some second => CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) second.2.2) ?_) ?_
  · intro outcome supported drift
    rcases outcome with ⟨first,optional⟩
    obtain ⟨second,reached,different⟩ := drift
    change optional = some second at reached
    subst optional
    have initial := CheckpointExecution.good_empty hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
    rcases source_association coefficient expected publicRoots factor ns hs dummy _ first second supported
        capacity radius ⟨initial.1,fun _ => initial.2.2⟩ encoding domain tags with equal | bad
    · exact False.elim (different equal)
    · exact bad
  · convert bound using 1
    apply prEvent_congr
    intro outcome
    cases outcome.2 <;> rfl

end
end FormalProof4FHE.HasteBoots.HadamardNTTSourceAssociation
