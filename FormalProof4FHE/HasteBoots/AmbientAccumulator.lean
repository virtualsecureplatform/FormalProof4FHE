module
public import FormalProof4FHE.HasteBoots.PackedAccumulatorOracle
public import FormalProof4FHE.HasteBoots.AmbientDependentBatchOpening
public import FormalProof4FHE.HasteBoots.SequentialStageHistory
@[expose] public section

/-! Seven native accumulator source batches execute in the inherited ambient
history. Trusted query/value/root fields override the behavior factory. -/
namespace FormalProof4FHE.HasteBoots.AmbientAccumulator
open OracleSpec OracleComp BinaryTree Matrix
open PackedSumcheckSubclaim (Query)
open InteractiveAuthenticatedOpening CommittedJointMatrixOpening
open PackedAccumulatorOracle (Context Packet)
noncomputable section

structure Scheme (F Input Digest Cfg Response Memory CommitMemory : Type) [Field F]
    (b c r front suffix m queries height : ℕ) where
  encoding : MerkleOracle.Encoding Input Digest (List F)
  domain : Fin (2^height) ↪ F
  tag : Fin 7 → Cfg
  layout : front+suffix = (1+r)+c
  context : Context F b c r
  nodes : PackedSumcheckRound.Node b ↪ F
  commit : OracleComp (SharedSequence.Shared Cfg Input Digest) ((Fin 7 → Digest) × CommitMemory)
  initial : ((Fin 7 → Digest) × CommitMemory) → Memory
  bindContext : ((Fin 7 → Digest) × CommitMemory) → Memory → OracleComp (SharedSequence.Shared Cfg Input Digest) Memory
  receive : ((Fin 7 → Digest) × CommitMemory) → Memory → Query F b ((1+r)+c) →
    OracleComp (SharedSequence.Shared Cfg Input Digest) (PackedAccumulatorOracle.Values F b × Memory)
  build : ((Fin 7 → Digest) × CommitMemory) → (packet : Packet F Memory b c r) → (factor : Fin 7) →
    NativeBatchVerifier.Protocol F Input Digest Cfg Response Memory b front suffix
      (PackedAccumulatorOracle.queries context packet.query factor).length m queries height

variable {F K Input Digest Cfg Response Memory CommitMemory : Type}
  [Field F] [DecidableEq F] [Fintype F] [DecidableEq Input] [DecidableEq Digest]
  {b c r front suffix m queries height : ℕ}

/-- Transport changes only the trusted dimension index, preserving query order. -/
def queryCast (length : front+suffix = (1+r)+c) (query : Query F b ((1+r)+c)) : Query F b (front+suffix) :=
  length.symm ▸ query

/-- The one table transport is fixed before sampling; it does not depend on
which base, selected-half, endpoint or shift query is later opened. -/
def tableCast (length : front+suffix = (1+r)+c) (table : MatrixFold.Cube (front+suffix) → Fin b → F) :
    AccumulatorMatrixSoundness.Table F b c r := fun cell => table (length.symm ▸ cell)

omit [DecidableEq F] [Fintype F] in
theorem fold_cast {a z : ℕ} (length : a = z) (query : Query F b z)
    (table : MatrixFold.Cube a → Fin b → F) :
    (length.symm ▸ query).fold table = query.fold (fun cell => table (length.symm ▸ cell)) := by
  cases length
  rfl

def preflight : Bool :=
  decide (0 < b ∧ 2*b < Fintype.card F)

/-- All original sources use the actual native list order. -/
def factors : List (Fin 7) := List.ofFn id

theorem factors_complete (factor : Fin 7) : factor ∈ factors := List.mem_ofFn.mpr ⟨factor,rfl⟩

def build (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r front suffix m queries height)
    (emission : (Fin 7 → Digest) × CommitMemory) (packet : Packet F Memory b c r) (factor : Fin 7) :
    NativeBatchVerifier.Protocol F Input Digest Cfg Response Memory b front suffix
      (PackedAccumulatorOracle.queries s.context packet.query factor).length m queries height :=
  {s.build emission packet factor with
    encoding := s.encoding,domain := s.domain,root := emission.1 factor,
    query := fun (claim : Fin (PackedAccumulatorOracle.queries s.context packet.query factor).length) =>
      queryCast s.layout ((PackedAccumulatorOracle.queries s.context packet.query factor).get claim),
    values := fun claim => PackedAccumulatorOracle.value packet.values factor claim.val}

variable [SampleableType (Fin b → F)]

def select (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r front suffix m queries height)
    (emission : (Fin 7 → Digest) × CommitMemory) :=
  PackedAccumulatorOracle.program s.nodes s.context (preflight (F := F) (b := b))
    (s.bindContext emission (s.initial emission)) (s.receive emission) (s.initial emission)

variable [SampleableType (TestMatrix F (2^front) b)] [SampleableType (Fin queries → Fin (2^height))]

def continuation (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r front suffix m queries height) :=
  AmbientDependentBatchOpening.continuation s.encoding s.domain (build s) (select s)
    (fun _ packet => packet.accepted) (fun _ packet => packet.memory) factors

def program (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r front suffix m queries height) :=
  MultiCommitmentPrefix.program (requests s.tag factors) s.commit (continuation s)

abbrev Prefix (heights : Cfg → ℕ) := ((Fin 7 → Digest) × CommitMemory) ×
  CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)
abbrev RunResult (heights : Cfg → ℕ) :=
  (Packet F Memory b c r × ShortCircuitSequence.Outcome (Fin 7)
    (JointMatrixOpening.Data F Digest Response (2^front) b height queries) Memory) ×
  CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)

def tables (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (first : Prefix heights (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory)) :=
  fun factor => tableCast s.layout (SubclaimSourceLayout.decodedSource (front := front) (suffix := suffix) s.domain capacity radius
    (AmbientDependentBatchOpening.frozen s.encoding dummy heights s.tag first factor))

def sources (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (first : Prefix heights (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory)) :
    AccumulatorMatrixSoundness.Sources F b c r where
  input := tables heights s dummy capacity radius first 0
  product := tables heights s dummy capacity radius first 1
  difference := tables heights s dummy capacity radius first 2
  output := tables heights s dummy capacity radius first 3
  external := tables heights s dummy capacity radius first 4
  duplicateA := tables heights s dummy capacity radius first 5
  duplicateB := tables heights s dummy capacity radius first 6
  initial := s.context.initial
  final := s.context.final
  start := s.context.start
  finish := s.context.finish

omit [Fintype F] [DecidableEq Input] [SampleableType (Fin b → F)]
  [SampleableType (TestMatrix F (2^front) b)] [SampleableType (Fin queries → Fin (2^height))] in
@[simp] theorem sources_context (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (first : Prefix heights (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory)) :
    PackedAccumulatorOracle.context (sources heights s dummy capacity radius first) = s.context := rfl

omit [Fintype F] [DecidableEq Input] [SampleableType (Fin b → F)]
  [SampleableType (TestMatrix F (2^front) b)] [SampleableType (Fin queries → Fin (2^height))] in
theorem source_tables (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (first : Prefix heights (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory)) (factor : Fin 7) :
    PackedAccumulatorOracle.source (sources heights s dummy capacity radius first) factor =
      tables heights s dummy capacity radius first factor := by
  fin_cases factor <;> rfl

omit [Fintype F] [DecidableEq Input] [SampleableType (Fin b → F)]
  [SampleableType (TestMatrix F (2^front) b)] [SampleableType (Fin queries → Fin (2^height))] in
theorem fold_table (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (first : Prefix heights (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory))
    (factor : Fin 7) (query : Query F b ((1+r)+c)) :
    query.fold (tables heights s dummy capacity radius first factor) =
      matrixEvaluation (SubclaimSourceLayout.leftWeights (queryCast s.layout query))
        (SubclaimSourceLayout.rightWeights (queryCast s.layout query))
        (MatrixOpeningSecurity.extract s.domain capacity radius
          (AmbientDependentBatchOpening.frozen s.encoding dummy heights s.tag first factor)) :=
  (fold_cast s.layout query _).symm.trans
    (SubclaimSourceLayout.fold_decodedSource s.domain capacity radius _ (queryCast s.layout query))

omit [Fintype F] [DecidableEq Input] [SampleableType (Fin b → F)]
  [SampleableType (TestMatrix F (2^front) b)] [SampleableType (Fin queries → Fin (2^height))] in
/-- All positions in every returned value list follow from the trusted batch
values. Equal queries at different positions need no consistency assumption. -/
theorem values_truthful (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (first : Prefix heights (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory))
    (packet : Packet F Memory b c r)
    (checked : PackedAccumulatorOracle.check s.context packet.query packet.values = true)
    (correct : ∀ factor claim, (build s first.1 packet factor).values claim =
      matrixEvaluation (NativeBatchChecks.left (front := front) (suffix := suffix) (build s first.1 packet factor).query claim)
        (NativeBatchChecks.right (front := front) (suffix := suffix) (build s first.1 packet factor).query claim)
        (MatrixOpeningSecurity.extract s.domain capacity radius
          (AmbientDependentBatchOpening.frozen s.encoding dummy heights s.tag first factor))) :
    ∀ factor, packet.values factor = (PackedAccumulatorOracle.queries s.context packet.query factor).map
      (fun query => query.fold (PackedAccumulatorOracle.source (sources heights s dummy capacity radius first) factor)) := by
  have lengths : ∀ factor, (packet.values factor).length = (PackedAccumulatorOracle.queries s.context packet.query factor).length :=
    (of_decide_eq_true checked : PackedAccumulatorOracle.Check s.context packet.query packet.values).1
  intro factor
  apply PackedAccumulatorOracle.values_eq _ _ ((lengths factor).trans (List.length_map ..).symm)
  intro index
  let selected : Fin (PackedAccumulatorOracle.queries s.context packet.query factor).length :=
    ⟨index.val,by simpa only [List.length_map] using index.isLt⟩
  have equal := correct factor selected
  change PackedAccumulatorOracle.value packet.values factor selected.val =
    matrixEvaluation (SubclaimSourceLayout.leftWeights (queryCast s.layout _))
      (SubclaimSourceLayout.rightWeights (queryCast s.layout _)) _ at equal
  rw [←fold_table heights s dummy capacity radius first factor] at equal
  simpa only [PackedAccumulatorOracle.value,source_tables,List.get_eq_getElem,List.getElem_map] using equal

variable [SampleableType Digest]

def witness (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r front suffix m queries height) (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :=
  MultiCommitmentPrefix.witness s.encoding dummy (AmbientMatrixSource.Shape heights)
    (requests s.tag factors) s.commit (continuation s) initial

theorem project_witness (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r front suffix m queries height) (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :
    (fun outcome => ((outcome.1.1,outcome.2.1),outcome.2.2)) <$> witness heights s dummy initial =
      (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy
        (AmbientMatrixSource.Shape heights)) (program s)).run initial :=
  MultiCommitmentPrefix.project_witness s.encoding dummy (AmbientMatrixSource.Shape heights)
    (requests s.tag factors) s.commit (continuation s) initial

/-- Acceptance uses the accumulator packet's computed flag on its actual
supported query/receive path; an arbitrary factory cannot substitute a flag. -/
theorem witness_checked (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r front suffix m queries height) (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : Prefix heights (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) ×
      RunResult heights (F := F) (Input := Input) (Digest := Digest) (Response := Response) (Memory := Memory)
        (b := b) (c := c) (r := r) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness heights s dummy initial))
    (accepted : outcome.2.1.1.accepted = true) :
    PackedAccumulatorOracle.check s.context outcome.2.1.1.query outcome.2.1.1.values = true := by
  simp only [witness,MultiCommitmentPrefix.witness,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at supported
  obtain ⟨first,_,last,reached,same⟩ := supported
  subst outcome
  obtain ⟨selected,selectedSupported,opened,_,equal⟩ :=
    (SharedContinuation.support_program s.encoding dummy (AmbientMatrixSource.Shape heights)
      (select s first.1) (fun packet => if packet.accepted then
        ShortCircuitSequence.program
          (fun factor => NativeBatchVerifier.step (AmbientDependentBatchOpening.protocol s.encoding s.domain (build s) first.1 packet factor))
          factors packet.memory else pure ⟨[],packet.memory,false⟩)
      (RecordRoots.state _ (requests s.tag factors first.1) first.2) last).mp reached
  subst last
  exact PackedAccumulatorOracle.program_checked s.encoding dummy (AmbientMatrixSource.Shape heights)
    s.nodes s.context (preflight (F := F) (b := b)) (s.bindContext first.1 (s.initial first.1))
    (s.receive first.1) (s.initial first.1) _ selected selectedSupported accepted

/-- A later stage receives the entire inherited history, even on rejection. -/
theorem retains (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r front suffix m queries height) (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : Prefix heights (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) ×
      RunResult heights (F := F) (Input := Input) (Digest := Digest) (Response := Response) (Memory := Memory)
        (b := b) (c := c) (r := r) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness heights s dummy initial))
    (tag : Cfg) (saved : AmbientMatrixSource.Snapshot Input Digest heights tag)
    (recorded : ⟨tag,saved⟩ ∈ initial.checkpoints.checkpoints) :
    ⟨tag,saved⟩ ∈ outcome.2.2.checkpoints.checkpoints :=
  SequentialStageHistory.witness_retains s.encoding dummy (AmbientMatrixSource.Shape heights)
    (requests s.tag factors) s.commit (continuation s) initial outcome supported tag saved recorded

theorem audited_witness (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r front suffix m queries height) (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) initial)
    (outcome : Prefix heights (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) ×
      RunResult heights (F := F) (Input := Input) (Digest := Digest) (Response := Response) (Memory := Memory)
        (b := b) (c := c) (r := r) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness heights s dummy initial)) :
    CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) outcome.2.2 := by
  have actual : ((outcome.1.1,outcome.2.1),outcome.2.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy
        (AmbientMatrixSource.Shape heights)) (program s)).run initial) := by
    rw [←project_witness heights s dummy initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy
    (AmbientMatrixSource.Shape heights) (program s) initial audited ((outcome.1.1,outcome.2.1),outcome.2.2) actual

/-- All rejected and successful branches preserve an inherited exception. -/
theorem bad_persistent (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r front suffix m queries height) (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) initial)
    (outcome : Prefix heights (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) ×
      RunResult heights (F := F) (Input := Input) (Digest := Digest) (Response := Response) (Memory := Memory)
        (b := b) (c := c) (r := r) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness heights s dummy initial)) :
    CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2 := by
  have actual : ((outcome.1.1,outcome.2.1),outcome.2.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy
        (AmbientMatrixSource.Shape heights)) (program s)).run initial) := by
    rw [←project_witness heights s dummy initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointCollision.bad_persistent_run (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy
    (AmbientMatrixSource.Shape heights) (program s) initial bad _ actual

/-- Each of the seven actual commitment roots has its frozen checkpoint in
the final registry, without an honesty or acceptance premise. -/
theorem fresh_recorded (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r front suffix m queries height) (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : Prefix heights (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) ×
      RunResult heights (F := F) (Input := Input) (Digest := Digest) (Response := Response) (Memory := Memory)
        (b := b) (c := c) (r := r) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness heights s dummy initial)) (factor : Fin 7) :
    ⟨s.tag factor,AmbientDependentBatchOpening.snapshots heights s.tag outcome.1 factor⟩ ∈ outcome.2.2.checkpoints.checkpoints :=
  SequentialStageHistory.witness_recorded s.encoding dummy (AmbientMatrixSource.Shape heights)
    (requests s.tag factors) s.commit (continuation s) initial outcome supported
    (s.tag factor,outcome.1.1.1 factor) (List.mem_map_of_mem (factors_complete factor))

/-- The common-query arithmetic rate is averaged over the actual frozen
seven-source prefix, before any adaptive value or opening work. -/
theorem truth_risk_bound (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :
    Pr{let outcome ← (witness heights s dummy initial)}[
      ¬AccumulatorEndpointSoundness.FullHolds (sources heights s dummy capacity radius outcome.1) ∧
        PackedAccumulatorOracle.Truthful (sources heights s dummy capacity radius outcome.1) outcome.2.1.1] ≤
      ((((1+r)+c : ℕ) : ENNReal) * (((((2*b-1 : ℕ) : ENNReal)/Fintype.card F)^b))) := by
  unfold witness MultiCommitmentPrefix.witness
  apply prEvent_bind_le_of_forall_le
  intro first
  by_cases falseClaim : ¬AccumulatorEndpointSoundness.FullHolds (sources heights s dummy capacity radius first)
  · let initial := RecordRoots.state (AmbientMatrixSource.Shape heights) (requests s.tag factors first.1) first.2
    have retained := SharedContinuation.earlier_event_le s.encoding dummy (AmbientMatrixSource.Shape heights)
      (select s first.1) (fun packet => if packet.accepted then
        ShortCircuitSequence.program
          (fun factor => NativeBatchVerifier.step (AmbientDependentBatchOpening.protocol s.encoding s.domain (build s) first.1 packet factor))
          factors packet.memory else pure ⟨[],packet.memory,false⟩) initial
      (PackedAccumulatorOracle.Truthful (sources heights s dummy capacity radius first))
    have arithmetic := PackedAccumulatorOracle.truthful_bound s.encoding dummy (AmbientMatrixSource.Shape heights)
      s.nodes (sources heights s dummy capacity radius first) (preflight (F := F) (b := b))
      (s.bindContext first.1 (s.initial first.1)) (s.receive first.1) (s.initial first.1) initial falseClaim
    simpa [continuation,AmbientDependentBatchOpening.continuation,initial,prEvent_norm,falseClaim]
      using retained.trans arithmetic
  · simp [falseClaim,prEvent_norm]

variable [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
  [SampleableType ((Fin (2^front) × Fin b) → K)]

/-- Every source has its own native batch and computed worker flags, even
though their batch lengths differ. No query-count factor or local hash charge. -/
theorem opening_safe_bound [NeZero m] [NeZero b] (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r front suffix m queries height)
    (geometry : ∀ factor, heights (s.tag factor) = height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m : Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (witness heights s dummy initial)}[
      AmbientDependentBatchOpening.Wrong s.encoding dummy heights s.tag s.domain capacity radius (build s) outcome.1 outcome.2 ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2] ≤
      7 * JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius := by
  have bound := AmbientDependentBatchOpening.soundness basis s.encoding dummy heights s.tag factors factors_complete geometry
    s.domain enough capacity radius (build s) s.commit (select s) (fun _ packet => packet.accepted)
    (fun _ packet => packet.memory) small initial audited
  have rate : (factors.map (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius)).sum =
      7 * JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius := by
    simp only [factors,List.map_ofFn,List.sum_ofFn,Function.comp_apply,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    norm_num
  rw [rate] at bound
  exact bound

/-- A false fixed-source accumulator family accepted by both its computed
arithmetic check and actual native openings has the compression plus seven-PCS
rate outside the caller's one shared final exception. -/
theorem false_acceptance_safe_bound [NeZero m] [NeZero b] (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r front suffix m queries height)
    (geometry : ∀ factor, heights (s.tag factor) = height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m : Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (witness heights s dummy initial)}[
      (¬AccumulatorEndpointSoundness.FullHolds (sources heights s dummy capacity radius outcome.1) ∧
        outcome.2.1.1.accepted = true ∧ outcome.2.1.2.accepted = true) ∧
      ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2] ≤
      ((((1+r)+c : ℕ) : ENNReal) * (((((2*b-1 : ℕ) : ENNReal)/Fintype.card F)^b))) +
        7 * JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius := by
  have arithmetic := truth_risk_bound heights s dummy capacity radius initial
  have opening := opening_safe_bound heights s geometry basis dummy enough capacity radius small initial audited
  apply le_trans (prEvent_mono_of_support (witness heights s dummy initial) _
    (fun outcome =>
      (¬AccumulatorEndpointSoundness.FullHolds (sources heights s dummy capacity radius outcome.1) ∧
        PackedAccumulatorOracle.Truthful (sources heights s dummy capacity radius outcome.1) outcome.2.1.1) ∨
      (AmbientDependentBatchOpening.Wrong s.encoding dummy heights s.tag s.domain capacity radius (build s) outcome.1 outcome.2 ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2)) ?_)
    ((prEvent_or_le _ _ _).trans (add_le_add arithmetic opening))
  intro outcome supported event
  by_cases wrong : AmbientDependentBatchOpening.Wrong s.encoding dummy heights s.tag s.domain capacity radius (build s) outcome.1 outcome.2
  · exact Or.inr ⟨wrong,event.2⟩
  · have checked := witness_checked heights s dummy initial outcome supported event.1.2.1
    have truth := values_truthful heights s dummy capacity radius outcome.1 outcome.2.1.1 checked (by
      intro factor claim
      by_contra different
      exact wrong ⟨event.1.2.2,factor,claim,different⟩)
    refine Or.inl ⟨event.1.1,event.1.2.1,?_⟩
    simpa only [sources_context] using truth

end
end FormalProof4FHE.HasteBoots.AmbientAccumulator
