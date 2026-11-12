module
public import FormalProof4FHE.HasteBoots.AmbientCommittedOpeningSafeBound
public import FormalProof4FHE.HasteBoots.MatrixCompression
public import FormalProof4FHE.HasteBoots.PrivateSampling
public import FormalProof4FHE.HasteBoots.QueryReindex
public import FormalProof4FHE.HasteBoots.QueryHighZeroPadding
@[expose] public section

/-! A caller-owned input root is compared with a fixed verifier table by a
fresh native packed query and ONE private single opening. The public value
is computed by the verifier. Fixed high-zero query pairs select only the
logical view of the same physical decoded source; private padding is retained. -/
namespace FormalProof4FHE.HasteBoots.AmbientKnownInput
open OracleSpec OracleComp BinaryTree Matrix
open InteractiveAuthenticatedOpening CommittedJointMatrixOpening
noncomputable section

structure Scheme (F Input Digest Cfg Response Memory CommitMemory : Type) [Field F]
    (b n front suffix m queries height : ℕ) where
  padding : ℕ
  dimensions : padding+n = front+suffix
  encoding : MerkleOracle.Encoding Input Digest (List F)
  domain : Fin (2^height) ↪ F
  tag : Cfg
  nodes : PackedSumcheckRound.Node b ↪ F
  table : MatrixFold.Cube n → Fin b → F
  commit : OracleComp (SharedSequence.Shared Cfg Input Digest) ((Unit → Digest) × CommitMemory)
  initial : ((Unit → Digest) × CommitMemory) → Memory
  bindKnown : ((Unit → Digest) × CommitMemory) → (MatrixFold.Cube n → Fin b → F) → Memory →
    OracleComp (SharedSequence.Shared Cfg Input Digest) Memory
  build : ((Unit → Digest) × CommitMemory) → (PackedSumcheckSubclaim.Query F b n × Memory) →
    NativeMatrixVerifier.Protocol F Unit Input Digest Cfg Response Memory (2^front) b m (2^suffix) queries height

variable {F K Input Digest Cfg Response Memory CommitMemory : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {b n front suffix m queries height : ℕ}

local notation "S" => Scheme F Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height

abbrev Prefix (heights : Cfg → ℕ) := ((Unit → Digest) × CommitMemory) ×
  CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)
abbrev RunResult (heights : Cfg → ℕ) :=
  ((PackedSumcheckSubclaim.Query F b n × Memory) ×
    ShortCircuitSequence.Outcome Unit (JointMatrixOpening.Data F Digest Response (2^front) b height queries) Memory) ×
  CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)

local notation "Pfx" => Prefix (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory)
local notation "Result" => RunResult (F := F) (Input := Input) (Digest := Digest) (Response := Response) (Memory := Memory)
  (b := b) (n := n) (front := front) (queries := queries) (height := height)

def source (heights : Cfg → ℕ) (s : S) (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (first : Pfx heights) :=
  QueryHighZeroPadding.source s.padding (QueryReindex.source s.dimensions (SubclaimSourceLayout.decodedSource s.domain capacity radius
    (AmbientCommittedBatchSafeBound.frozen s.encoding dummy heights (fun _ : Unit => s.tag) first ())))

def originalSource (heights : Cfg → ℕ) (s : S) (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (owner : AmbientMatrixSource.Snapshot Input Digest heights s.tag) :=
  QueryHighZeroPadding.source s.padding (QueryReindex.source s.dimensions (AmbientMatrixSource.source (front := front) s.encoding dummy heights s.domain capacity radius s.tag owner))

def TruthRisk (heights : Cfg → ℕ) (s : S) (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (outcome : Pfx heights × Result heights) : Prop :=
  source heights s dummy capacity radius outcome.1 ≠ s.table ∧
    outcome.2.1.1.1.fold (source heights s dummy capacity radius outcome.1) = outcome.2.1.1.1.fold s.table

def OpeningRisk (heights : Cfg → ℕ) (s : S) (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (outcome : Pfx heights × Result heights) : Prop :=
  outcome.2.1.2.accepted = true ∧
    outcome.2.1.1.1.fold s.table ≠ outcome.2.1.1.1.fold (source heights s dummy capacity radius outcome.1)

def OriginalRisk (heights : Cfg → ℕ) (s : S) (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (outcome : Pfx heights × Result heights) : Prop :=
  ∃ owner : AmbientMatrixSource.Snapshot Input Digest heights s.tag,
    owner.root = outcome.1.1.1 () ∧ ⟨s.tag,owner⟩ ∈ outcome.2.2.checkpoints.checkpoints ∧
      originalSource heights s dummy capacity radius owner ≠ s.table ∧ outcome.2.1.2.accepted = true

def left (s : S) (packet : PackedSumcheckSubclaim.Query F b n × Memory) (_ : Unit) :=
  SubclaimSourceLayout.leftWeights (front := front) (suffix := suffix) (QueryReindex.query s.dimensions (QueryHighZeroPadding.query s.padding packet.1))
def right (s : S) (packet : PackedSumcheckSubclaim.Query F b n × Memory) (_ : Unit) :=
  SubclaimSourceLayout.rightWeights (front := front) (suffix := suffix) (QueryReindex.query s.dimensions (QueryHighZeroPadding.query s.padding packet.1))

/-- No prover-supplied terminal value is used for this known-input opening. -/
def build (s : S) (emission : (Unit → Digest) × CommitMemory) (packet : PackedSumcheckSubclaim.Query F b n × Memory) :
    NativeMatrixVerifier.Protocol F Unit Input Digest Cfg Response Memory (2^front) b m (2^suffix) queries height :=
  {s.build emission packet with value := fun _ => packet.1.fold s.table}

variable [SampleableType (Fin b → F)] [SampleableType Digest]
  [SampleableType (TestMatrix F (2^front) b)] [SampleableType (Fin queries → Fin (2^height))]

/-- The known table/root context is bound before sampling the fresh query. -/
def select (s : S) (emission : (Unit → Digest) × CommitMemory) := do
  let memory ← s.bindKnown emission s.table (s.initial emission)
  let query ← PrivateSampling.embed Cfg Input Digest (MatrixCompression.sample s.nodes n)
  pure (query,memory)

def continuation (s : S) := NativeCommittedOpening.continuation s.encoding s.domain
  (left s) (right s) (build s) (select s) (fun _ _ => true) (fun _ packet => packet.2) [()]
def program (s : S) := MultiCommitmentPrefix.program (requests (fun _ : Unit => s.tag) [()]) s.commit (continuation s)
def witness (heights : Cfg → ℕ) (s : S) (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :=
  MultiCommitmentPrefix.witness s.encoding dummy (AmbientMatrixSource.Shape heights)
    (requests (fun _ : Unit => s.tag) [()]) s.commit (continuation s) initial

/-- Full-state erasure includes binding, private sampling and actual workers. -/
theorem project_witness (heights : Cfg → ℕ) (s : S) (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :
    (fun outcome => ((outcome.1.1,outcome.2.1),outcome.2.2)) <$> witness heights s dummy initial =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (AmbientMatrixSource.Shape heights))
      (program s)).run initial :=
  MultiCommitmentPrefix.project_witness s.encoding dummy (AmbientMatrixSource.Shape heights)
    (requests (fun _ : Unit => s.tag) [()]) s.commit (continuation s) initial

/-- The fixed source is recorded before either context binding or query draws. -/
theorem fresh_recorded (heights : Cfg → ℕ) (s : S) (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : Pfx heights × Result heights) (supported : outcome ∈ support (witness heights s dummy initial)) :
    ⟨s.tag,AmbientCommittedBatchSafeBound.snapshots heights (fun _ : Unit => s.tag) outcome.1 ()⟩ ∈ outcome.2.2.checkpoints.checkpoints :=
  SequentialStageHistory.witness_recorded s.encoding dummy (AmbientMatrixSource.Shape heights)
    (requests (fun _ : Unit => s.tag) [()]) s.commit (continuation s) initial outcome supported
    (s.tag,outcome.1.1.1 ()) (by simp [requests])

/-- All earlier original owners remain available after this single opening. -/
theorem retains (heights : Cfg → ℕ) (s : S) (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : Pfx heights × Result heights) (supported : outcome ∈ support (witness heights s dummy initial))
    (tag : Cfg) (saved : AmbientMatrixSource.Snapshot Input Digest heights tag)
    (recorded : ⟨tag,saved⟩ ∈ initial.checkpoints.checkpoints) :
    ⟨tag,saved⟩ ∈ outcome.2.2.checkpoints.checkpoints :=
  SequentialStageHistory.witness_retains s.encoding dummy (AmbientMatrixSource.Shape heights)
    (requests (fun _ : Unit => s.tag) [()]) s.commit (continuation s) initial outcome supported tag saved recorded

/-- Earlier exceptions persist on the same full ambient state. -/
theorem bad_persistent (heights : Cfg → ℕ) (s : S) (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : Pfx heights × Result heights) (supported : outcome ∈ support (witness heights s dummy initial))
    (bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) initial) :
    CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2 := by
  have actual : ((outcome.1.1,outcome.2.1),outcome.2.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (AmbientMatrixSource.Shape heights)) (program s)).run initial) := by
    rw [←project_witness heights s dummy initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointCollision.bad_persistent_run (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy
    (AmbientMatrixSource.Shape heights) (program s) initial bad _ actual

/-- Actual execution derives the final audit, even if the opening rejects. -/
theorem audited_witness (heights : Cfg → ℕ) (s : S) (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) initial)
    (outcome : Pfx heights × Result heights) (supported : outcome ∈ support (witness heights s dummy initial)) :
    CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) outcome.2.2 := by
  have actual : ((outcome.1.1,outcome.2.1),outcome.2.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (AmbientMatrixSource.Shape heights)) (program s)).run initial) := by
    rw [←project_witness heights s dummy initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy
    (AmbientMatrixSource.Shape heights) (program s) initial audited _ actual


/-- Fixed unequal source/public tables can agree only within the fresh packed
compression bound. Binding and opening calls retain their actual shared state. -/
theorem truth_risk_bound [Fintype F] (heights : Cfg → ℕ) (s : S) (dummy : Digest)
    (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :
    Pr{let outcome ← (witness heights s dummy initial)}[TruthRisk heights s dummy capacity radius outcome] ≤
      (n : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card F)^b)) := by
  unfold witness MultiCommitmentPrefix.witness
  apply prEvent_bind_le_of_forall_le
  intro first
  by_cases different : source heights s dummy capacity radius first ≠ s.table
  · let state := RecordRoots.state (AmbientMatrixSource.Shape heights) (requests (fun _ : Unit => s.tag) [()] first.1) first.2
    have afterOpening := SharedContinuation.earlier_event_le s.encoding dummy (AmbientMatrixSource.Shape heights)
      (select s first.1)
      (fun packet => if true then ShortCircuitSequence.program
        (NativeMatrixVerifier.step (NativeCommittedOpening.protocol s.encoding s.domain (left s) (right s) (build s) first.1 packet))
        [()] packet.2 else pure ⟨[],packet.2,false⟩) state
      (fun packet => packet.1.fold (source heights s dummy capacity radius first) = packet.1.fold s.table)
    have sampled : Pr{let packet ← ((simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (AmbientMatrixSource.Shape heights))
        (select s first.1)).run state)}[
          packet.1.1.fold (source heights s dummy capacity radius first) = packet.1.1.fold s.table] ≤
        (n : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card F)^b)) := by
      simp only [select,simulateQ_bind,StateT.run_bind]
      apply prEvent_bind_le_of_forall_le
      intro bound
      simpa only [simulateQ_bind,StateT.run_bind,simulateQ_pure,StateT.run_pure,PrivateSampling.run_probComp,
        bind_map_left,pure_bind,prEvent_norm] using MatrixCompression.agreement_bound s.nodes
          (source heights s dummy capacity radius first) s.table different
    simpa [continuation,NativeCommittedOpening.continuation,SharedContinuation.program,TruthRisk,
      different,state,prEvent_norm] using afterOpening.trans sampled
  · simp [TruthRisk,different,prEvent_norm]

variable [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq K]
  [SampleableType ((Fin (2^front) × Fin b) → K)]

/-- A single native PCS error authenticates the verifier-computed known value.
The enclosing final bad event is excluded, with no local hash charge. -/
theorem opening_safe_bound [NeZero m] [NeZero b] (heights : Cfg → ℕ) (s : S)
    (geometry : heights s.tag = height) (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m : Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (witness heights s dummy initial)}[OpeningRisk heights s dummy capacity radius outcome ∧
      ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2] ≤
      JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius := by
  have bound := AmbientCommittedOpeningSafeBound.soundness basis s.encoding dummy heights (fun _ : Unit => s.tag) [()]
    (fun factor => by cases factor; exact List.mem_singleton_self ()) (fun _ => geometry)
    s.domain enough capacity radius (left s) (right s) (build s) s.commit (select s)
    (fun _ _ => true) (fun _ packet => packet.2) small initial audited
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] at bound
  apply le_trans (prEvent_mono _ _ _ ?_) bound
  intro outcome risk
  refine ⟨?_,risk.2⟩
  obtain ⟨passed,different⟩ := risk.1
  refine ⟨passed,(),?_⟩
  change outcome.2.1.1.1.fold s.table ≠ _
  rw [source,QueryHighZeroPadding.fold,QueryReindex.fold,SubclaimSourceLayout.fold_decodedSource] at different
  exact different

/-- Original owners may be selected after execution. Outside the final bad
event, acceptance of an incorrect known-input root costs fresh compression
plus ONE native single-opening error. -/
theorem original_safe_bound [NeZero m] [NeZero b] (heights : Cfg → ℕ) (s : S)
    (geometry : heights s.tag = height) (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m : Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (witness heights s dummy initial)}[OriginalRisk heights s dummy capacity radius outcome ∧
      ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2] ≤
      (n : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card F)^b)) +
      JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius := by
  have arithmetic := truth_risk_bound heights s dummy capacity radius initial
  have opening := opening_safe_bound heights s geometry basis dummy enough capacity radius small initial audited
  apply le_trans (prEvent_mono_of_support (witness heights s dummy initial) _
    (fun outcome => TruthRisk heights s dummy capacity radius outcome ∨
      (OpeningRisk heights s dummy capacity radius outcome ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2)) ?_)
    ((prEvent_or_le _ _ _).trans (add_le_add arithmetic opening))
  intro outcome supported event
  obtain ⟨⟨owner,root,recorded,different,passed⟩,clear⟩ := event
  have audit := audited_witness heights s dummy initial audited outcome supported
  have same : originalSource heights s dummy capacity radius owner = source heights s dummy capacity radius outcome.1 := by
    rcases AmbientMatrixSource.source_eq_or_bad s.encoding dummy heights s.tag geometry s.domain capacity radius outcome.2.2 audit
        owner (AmbientCommittedBatchSafeBound.snapshots heights (fun _ : Unit => s.tag) outcome.1 ()) recorded
        (fresh_recorded heights s dummy initial outcome supported) root with equal | bad
    · exact congrArg (fun physical => QueryHighZeroPadding.source s.padding (QueryReindex.source s.dimensions physical)) equal
    · exact False.elim (clear bad)
  have wrong : source heights s dummy capacity radius outcome.1 ≠ s.table := by
    simpa only [same] using different
  by_cases agrees : outcome.2.1.1.1.fold (source heights s dummy capacity radius outcome.1) = outcome.2.1.1.1.fold s.table
  · exact Or.inl ⟨wrong,agrees⟩
  · exact Or.inr ⟨⟨passed,Ne.symm agrees⟩,clear⟩

end
end FormalProof4FHE.HasteBoots.AmbientKnownInput
