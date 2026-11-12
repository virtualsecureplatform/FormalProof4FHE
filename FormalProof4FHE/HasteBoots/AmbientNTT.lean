module
public import FormalProof4FHE.HasteBoots.NTTConditionalSoundness
public import FormalProof4FHE.HasteBoots.AmbientCommittedBatchSafeBound
@[expose] public section

/-! Original-source NTT verification on an arbitrary inherited mixed-height
history. Only its two opened contexts require the local matrix height. -/
namespace FormalProof4FHE.HasteBoots.AmbientNTT
open OracleSpec OracleComp BinaryTree Matrix
open InteractiveAuthenticatedOpening CommittedJointMatrixOpening AuthenticatedNTT
noncomputable section
variable {F K Input Digest Cfg Response Memory CommitMemory : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {b c r k front suffix m queries height : ℕ}

abbrev Prefix (heights : Cfg → ℕ) := ((Bool → Digest) × CommitMemory) ×
  CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)

abbrev RunResult (heights : Cfg → ℕ) := (Packet F Memory c b r k ×
  ShortCircuitSequence.Outcome Bool (JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries) Memory) ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)

def sources (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (first : Prefix heights (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg)) :=
  fun side => QueryReindex.source s.dimensions
    (SubclaimSourceLayout.decodedSource (front := front) (suffix := suffix) s.domain capacity radius
      (AmbientCommittedBatchSafeBound.frozen s.encoding dummy heights s.tag first side))

def FalseRelation (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (first : Prefix heights (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg)) : Prop :=
  ¬NTTRowCheck.Relation s.transform
    (NTTCompression.sourceRows c r (sources heights s dummy capacity radius first false))
    (NTTCompression.sourceRows c r (sources heights s dummy capacity radius first true))

def accepted (result : Packet F Memory c b r k ×
    ShortCircuitSequence.Outcome Bool (JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries) Memory) : Bool :=
  enabled result.1 && result.2.accepted

def TruthRisk (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (outcome : Prefix heights (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) ×
      RunResult heights (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height)) : Prop :=
  FalseRelation heights s dummy capacity radius outcome.1 ∧
    NTTCompression.TruthfulTerminals (sources heights s dummy capacity radius outcome.1 false)
      (sources heights s dummy capacity radius outcome.1 true) outcome.2.1.1

def OpeningRisk (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (outcome : Prefix heights (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) ×
      RunResult heights (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height)) : Prop :=
  AmbientCommittedBatchSafeBound.Wrong s.encoding dummy heights s.tag s.domain capacity radius (build s) outcome.1 outcome.2

omit [DecidableEq Input] in
/-- Every original-source compressed row value is exactly its native batch
matrix evaluation. This equality also fixes the low-coefficient/high-row order. -/
theorem source_evaluation (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (first : Prefix heights (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg))
    (packet : Packet F Memory c b r k) (side : Bool) (repetition : Fin k) :
    (NTTCompression.sourceQuery packet.1 (compressionQuery packet) (side, repetition)).fold
      (sources heights s dummy capacity radius first side) =
      matrixEvaluation (NativeBatchChecks.left (front := front) (suffix := suffix) (query s packet) repetition)
        (NativeBatchChecks.right (front := front) (suffix := suffix) (query s packet) repetition)
        (MatrixOpeningSecurity.extract s.domain capacity radius
          (AmbientCommittedBatchSafeBound.frozen s.encoding dummy heights s.tag first side)) := by
  rw [sources, QueryReindex.fold, SubclaimSourceLayout.fold_decodedSource]
  rfl

omit [DecidableEq Input] in
/-- A successful batch loop against a false fixed-source relation has either
truthful NTT terminals or a wrong native batch value; no flag is supplied. -/
theorem accepted_implies_risks (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (outcome : Prefix heights (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) ×
      RunResult heights (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height))
    (falseClaim : FalseRelation heights s dummy capacity radius outcome.1)
    (passes : accepted outcome.2.1 = true) :
    TruthRisk heights s dummy capacity radius outcome ∨ OpeningRisk heights s dummy capacity radius outcome := by
  classical
  by_cases wrong : OpeningRisk heights s dummy capacity radius outcome
  · exact Or.inr wrong
  · left
    refine ⟨falseClaim, ?_⟩
    have flags := Bool.and_eq_true_iff.mp passes
    have gate := Bool.and_eq_true_iff.mp flags.1
    refine ⟨gate.1, ?_⟩
    cases terminal : outcome.2.1.1.2 with
    | none => simp [terminal] at gate
    | some entry =>
      intro row
      have correct : ∀ side repetition,
          values outcome.2.1.1 side repetition =
            (NTTCompression.sourceQuery outcome.2.1.1.1 (compressionQuery outcome.2.1.1) (side, repetition)).fold
              (sources heights s dummy capacity radius outcome.1 side) := by
        intro side repetition
        by_contra different
        apply wrong
        refine ⟨flags.2, side, repetition, ?_⟩
        change values outcome.2.1.1 side repetition ≠ _
        rwa [source_evaluation heights s dummy capacity radius outcome.1 outcome.2.1.1 side repetition] at different
      have same := correct row.1 row.2
      cases row with
      | mk side repetition =>
        cases side <;>
          simpa only [values, compressionQuery, terminal, NTTCompression.source, Bool.false_eq_true,
            reduceIte] using same

def originalSources (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (owner : ∀ side, AmbientMatrixSource.Snapshot Input Digest heights (s.tag side)) :=
  fun side => QueryReindex.source s.dimensions
    (AmbientMatrixSource.source (front := front) s.encoding dummy heights s.domain capacity radius (s.tag side) (owner side))

def OriginalRisk (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (outcome : Prefix heights (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) ×
      RunResult heights (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height)) : Prop :=
  ∃ owner : ∀ side, AmbientMatrixSource.Snapshot Input Digest heights (s.tag side),
    (∀ side, (owner side).root = outcome.1.1.1 side ∧ ⟨s.tag side,owner side⟩ ∈ outcome.2.2.checkpoints.checkpoints) ∧
    ¬NTTRowCheck.Relation s.transform
      (NTTCompression.sourceRows c r (originalSources heights s dummy capacity radius owner false))
      (NTTCompression.sourceRows c r (originalSources heights s dummy capacity radius owner true)) ∧
    accepted outcome.2.1 = true

variable [SampleableType (Fin k → Fin r → F)] [SampleableType (Fin b → F)]
  [SampleableType (TestMatrix F (2^front) b)] [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType Digest]

def witness (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :=
  MultiCommitmentPrefix.witness s.encoding dummy (AmbientMatrixSource.Shape heights)
    (requests s.tag [false,true]) s.commit (AuthenticatedNTT.continuation s) initial

theorem project_witness (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :
    (fun outcome => ((outcome.1.1,outcome.2.1),outcome.2.2)) <$> witness heights s dummy initial =
      (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy
        (AmbientMatrixSource.Shape heights)) (AuthenticatedNTT.program s)).run initial :=
  MultiCommitmentPrefix.project_witness s.encoding dummy (AmbientMatrixSource.Shape heights)
    (requests s.tag [false,true]) s.commit (AuthenticatedNTT.continuation s) initial

/-- Original recording is retained from the actual arbitrary incoming state. -/
theorem fresh_recorded (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : Prefix heights (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) ×
      RunResult heights (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness heights s dummy initial)) (side : Bool) :
    ⟨s.tag side,AmbientCommittedBatchSafeBound.snapshots heights s.tag outcome.1 side⟩ ∈ outcome.2.2.checkpoints.checkpoints :=
  SequentialStageHistory.witness_recorded s.encoding dummy (AmbientMatrixSource.Shape heights)
    (requests s.tag [false,true]) s.commit (AuthenticatedNTT.continuation s) initial outcome supported
    (s.tag side,outcome.1.1.1 side) (List.mem_map_of_mem (by cases side <;> simp))

theorem audited_witness (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) initial)
    (outcome : Prefix heights (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) ×
      RunResult heights (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness heights s dummy initial)) :
    CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) outcome.2.2 := by
  have projected : ((outcome.1.1,outcome.2.1),outcome.2.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy
        (AmbientMatrixSource.Shape heights)) (AuthenticatedNTT.program s)).run initial) := by
    unfold AuthenticatedNTT.program
    rw [←MultiCommitmentPrefix.project_witness s.encoding dummy (AmbientMatrixSource.Shape heights)
      (requests s.tag [false,true]) s.commit (AuthenticatedNTT.continuation s) initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy
    (AmbientMatrixSource.Shape heights) (AuthenticatedNTT.program s) initial audited _ projected

/-- Earlier owners remain recorded on successful and rejected NTT paths. -/
theorem retains (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : Prefix heights (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) ×
      RunResult heights (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness heights s dummy initial))
    (tag : Cfg) (saved : AmbientMatrixSource.Snapshot Input Digest heights tag)
    (recorded : ⟨tag,saved⟩ ∈ initial.checkpoints.checkpoints) :
    ⟨tag,saved⟩ ∈ outcome.2.2.checkpoints.checkpoints :=
  SequentialStageHistory.witness_retains s.encoding dummy (AmbientMatrixSource.Shape heights)
    (requests s.tag [false,true]) s.commit (AuthenticatedNTT.continuation s) initial outcome supported tag saved recorded

/-- No part of the native row/compression/opening execution clears a failure. -/
theorem bad_persistent (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : Prefix heights (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) ×
      RunResult heights (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness heights s dummy initial))
    (bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) initial) :
    CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2 := by
  have actual : ((outcome.1.1,outcome.2.1),outcome.2.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy
        (AmbientMatrixSource.Shape heights)) (AuthenticatedNTT.program s)).run initial) := by
    rw [←project_witness heights s dummy initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointCollision.bad_persistent_run (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy
    (AmbientMatrixSource.Shape heights) (AuthenticatedNTT.program s) initial bad _ actual

/-- Choosing the freshly recorded two owners includes every accepted false
prefix-frozen source relation in the original-owner event. -/
theorem fresh_risk_implies_original (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : Prefix heights (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) ×
      RunResult heights (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness heights s dummy initial))
    (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (falseClaim : FalseRelation heights s dummy capacity radius outcome.1)
    (passes : accepted outcome.2.1 = true) : OriginalRisk heights s dummy capacity radius outcome :=
  ⟨AmbientCommittedBatchSafeBound.snapshots heights s.tag outcome.1,
    fun side => ⟨rfl,fresh_recorded heights s dummy initial outcome supported side⟩,falseClaim,passes⟩

/-- Arithmetic sampling is bounded uniformly over all actual commitment prefixes. -/
theorem truth_risk_bound [Fintype F] [SampleableType F] [SampleableType (Fin r → F)]
    (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :
    Pr{let outcome ← (witness heights s dummy initial)}[TruthRisk heights s dummy capacity radius outcome] ≤
      (((r : ENNReal) / Fintype.card F) ^ k) +
        (c : ENNReal) * (((((2 * b - 1 : ℕ) : ENNReal) / Fintype.card F) ^ b)) := by
  unfold witness MultiCommitmentPrefix.witness
  apply prEvent_bind_le_of_forall_le
  intro first
  by_cases falseClaim : FalseRelation heights s dummy capacity radius first
  · let initial := RecordRoots.state (AmbientMatrixSource.Shape heights) (requests s.tag [false, true] first.1) first.2
    have retained := SharedContinuation.earlier_event_le s.encoding dummy (AmbientMatrixSource.Shape heights)
      (select s first.1) (fun packet => if enabled packet then
        ShortCircuitSequence.program
          (fun side => NativeBatchVerifier.step (CommittedBatchOpening.protocol s.encoding s.domain (build s) first.1 packet side))
          [false, true] (memory packet) else pure ⟨[], memory packet, false⟩) initial
      (fun packet => NTTCompression.TruthfulTerminals (sources heights s dummy capacity radius first false)
        (sources heights s dummy capacity radius first true) packet)
    have arithmetic := NTTCompression.truthful_bound s.encoding dummy (AmbientMatrixSource.Shape heights)
      s.nodes s.transform (sources heights s dummy capacity radius first false) (sources heights s dummy capacity radius first true)
      (s.receive first.1) (s.bindRows first.1) (s.initial first.1) (s.afterQuery first.1) initial falseClaim
    simpa [AuthenticatedNTT.continuation, CommittedBatchOpening.continuation, initial, prEvent_norm, TruthRisk, falseClaim]
      using retained.trans arithmetic
  · simp [TruthRisk, falseClaim, prEvent_norm]

variable [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq K]
  [SampleableType ((Fin (2^front) × Fin b) → K)]

/-- Each original NTT root pays once for its whole PCS batch, outside the
shared final collision event; there is no per-claim or extra hash term. -/
theorem opening_safe_bound [NeZero m] [NeZero b]
    (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (geometry : ∀ side, heights (s.tag side) = height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (witness heights s dummy initial)}[
      OpeningRisk heights s dummy capacity radius outcome ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2] ≤
      JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius +
        JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius := by
  have complete : ∀ side : Bool, side ∈ [false,true] := by intro side; cases side <;> simp
  have bound := AmbientCommittedBatchSafeBound.soundness basis s.encoding dummy heights s.tag [false,true] complete geometry s.domain enough
    capacity radius (build s) s.commit (select s) (fun _ => enabled) (fun _ => memory) small initial audited
  simpa only [witness,AuthenticatedNTT.continuation,OpeningRisk,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using bound

/-- Original-owner reuse, row detection, compression and both PCS batches
share the caller's final collision exclusion from any audited incoming state. -/
theorem original_safe_bound [NeZero m] [NeZero b] [SampleableType F] [SampleableType (Fin r → F)]
    (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (geometry : ∀ side, heights (s.tag side) = height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (witness heights s dummy initial)}[
      OriginalRisk heights s dummy capacity radius outcome ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2] ≤
      ((((r : ENNReal)/Fintype.card F)^k) +
        (c : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card F)^b))) +
      (JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius +
        JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius) := by
  have arithmetic := truth_risk_bound heights s dummy capacity radius initial
  have opening := opening_safe_bound heights s geometry basis dummy enough capacity radius small initial audited
  apply le_trans (prEvent_mono_of_support _ _
    (fun outcome => TruthRisk heights s dummy capacity radius outcome ∨
      (OpeningRisk heights s dummy capacity radius outcome ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2)) ?_)
  · exact (prEvent_or_le _ _ _).trans (add_le_add arithmetic opening)
  · intro outcome supported event
    obtain ⟨risk,safe⟩ := event
    obtain ⟨owner,recorded,falseOriginal,passes⟩ := risk
    have audit := audited_witness heights s dummy initial audited outcome supported
    have same : originalSources heights s dummy capacity radius owner =
        sources heights s dummy capacity radius outcome.1 := by
      funext side
      rcases AmbientMatrixSource.source_eq_or_bad s.encoding dummy heights (s.tag side) (geometry side)
          s.domain capacity radius outcome.2.2 audit (owner side) (AmbientCommittedBatchSafeBound.snapshots heights s.tag outcome.1 side) (recorded side).2
          (fresh_recorded heights s dummy initial outcome supported side) (recorded side).1 with equal | bad
      · exact congrArg (QueryReindex.source s.dimensions) equal
      · exact False.elim (safe bad)
    have falseFresh : FalseRelation heights s dummy capacity radius outcome.1 := by
      intro relation
      exact falseOriginal (same.symm ▸ relation)
    rcases accepted_implies_risks heights s dummy capacity radius outcome falseFresh passes with truth | wrong
    · exact Or.inl truth
    · exact Or.inr ⟨wrong,safe⟩

end
end FormalProof4FHE.HasteBoots.AmbientNTT
