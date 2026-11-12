module
public import FormalProof4FHE.HasteBoots.CommittedBatchSafeBound
public import FormalProof4FHE.HasteBoots.OwnedNTTSoundness
@[expose] public section

/-! Original-source NTT errors from an arbitrary audited incoming history,
conditional on excluding the final shared collision event. No child restart
or extra hash charge is used; the enclosing caller charges that event once. -/
namespace FormalProof4FHE.HasteBoots.NTTConditionalSoundness
open OracleSpec OracleComp BinaryTree Matrix
open InteractiveAuthenticatedOpening CommittedJointMatrixOpening
open AuthenticatedNTT
noncomputable section
variable {F K Input Digest Cfg Response Memory CommitMemory : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {b c r k front suffix m queries height : ℕ}
  [SampleableType (Fin k → Fin r → F)] [SampleableType (Fin b → F)]
  [SampleableType (TestMatrix F (2^front) b)] [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType Digest]

def witness
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height)) :=
  MultiCommitmentPrefix.witness s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
    (requests s.tag [false,true]) s.commit (AuthenticatedNTT.continuation s) initial

/-- Original recording is retained from the actual arbitrary incoming state. -/
theorem fresh_recorded
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (outcome : Prefix (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) ×
      RunResult (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness s dummy initial)) (side : Bool) :
    ⟨s.tag side,snapshots s.tag outcome.1 side⟩ ∈ outcome.2.2.checkpoints.checkpoints :=
  SequentialStageHistory.witness_recorded s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
    (requests s.tag [false,true]) s.commit (AuthenticatedNTT.continuation s) initial outcome supported
    (s.tag side,outcome.1.1.1 side) (List.mem_map_of_mem (by cases side <;> simp))

theorem audited_witness
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (audited : CheckpointExecution.Audited s.encoding dummy (fun _ : Cfg => Skeleton.perfect height) initial)
    (outcome : Prefix (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) ×
      RunResult (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness s dummy initial)) :
    CheckpointExecution.Audited s.encoding dummy (fun _ : Cfg => Skeleton.perfect height) outcome.2.2 := by
  have projected : ((outcome.1.1,outcome.2.1),outcome.2.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy
        (fun _ : Cfg => Skeleton.perfect height)) (AuthenticatedNTT.program s)).run initial) := by
    unfold AuthenticatedNTT.program
    rw [←MultiCommitmentPrefix.project_witness s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
      (requests s.tag [false,true]) s.commit (AuthenticatedNTT.continuation s) initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy
    (fun _ : Cfg => Skeleton.perfect height) (AuthenticatedNTT.program s) initial audited _ projected

/-- Arithmetic sampling is bounded uniformly over all actual commitment prefixes. -/
theorem truth_risk_bound [Fintype F] [SampleableType F] [SampleableType (Fin r → F)]
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height)) :
    Pr{let outcome ← (witness s dummy initial)}[TruthRisk s dummy capacity radius outcome] ≤
      (((r : ENNReal) / Fintype.card F) ^ k) +
        (c : ENNReal) * (((((2 * b - 1 : ℕ) : ENNReal) / Fintype.card F) ^ b)) := by
  unfold witness MultiCommitmentPrefix.witness
  apply prEvent_bind_le_of_forall_le
  intro first
  by_cases falseClaim : FalseRelation s dummy capacity radius first
  · let initial := RecordRoots.state (fun _ : Cfg => Skeleton.perfect height) (requests s.tag [false, true] first.1) first.2
    have retained := SharedContinuation.earlier_event_le s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
      (select s first.1) (fun packet => if enabled packet then
        ShortCircuitSequence.program
          (fun side => NativeBatchVerifier.step (CommittedBatchOpening.protocol s.encoding s.domain (build s) first.1 packet side))
          [false, true] (memory packet) else pure ⟨[], memory packet, false⟩) initial
      (fun packet => NTTCompression.TruthfulTerminals (sources s dummy capacity radius first false)
        (sources s dummy capacity radius first true) packet)
    have arithmetic := NTTCompression.truthful_bound s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
      s.nodes s.transform (sources s dummy capacity radius first false) (sources s dummy capacity radius first true)
      (s.receive first.1) (s.bindRows first.1) (s.initial first.1) (s.afterQuery first.1) initial falseClaim
    simpa [AuthenticatedNTT.continuation, CommittedBatchOpening.continuation, initial, prEvent_norm, TruthRisk, falseClaim]
      using retained.trans arithmetic
  · simp [TruthRisk, falseClaim, prEvent_norm]

variable [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq K]
  [SampleableType ((Fin (2^front) × Fin b) → K)]

/-- Each original NTT root pays once for its whole PCS batch, outside the
shared final collision event; there is no per-claim or extra hash term. -/
theorem opening_safe_bound [NeZero m] [NeZero b]
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (audited : CheckpointExecution.Audited s.encoding dummy (fun _ : Cfg => Skeleton.perfect height) initial) :
    Pr{let outcome ← (witness s dummy initial)}[
      OpeningRisk s dummy capacity radius outcome ∧ ¬CheckpointCollision.Bad (fun _ : Cfg => Skeleton.perfect height) outcome.2.2] ≤
      JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius +
        JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius := by
  have complete : ∀ side : Bool, side ∈ [false,true] := by intro side; cases side <;> simp
  have bound := CommittedBatchSafeBound.soundness basis s.encoding dummy s.tag [false,true] complete s.domain enough
    capacity radius (build s) s.commit (select s) (fun _ => enabled) (fun _ => memory) small initial audited
  simpa only [witness,AuthenticatedNTT.continuation,OpeningRisk,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using bound

/-- Original-owner reuse, row detection, compression and both PCS batches
share the caller's final collision exclusion from any audited incoming state. -/
theorem original_safe_bound [NeZero m] [NeZero b] [SampleableType F] [SampleableType (Fin r → F)]
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (audited : CheckpointExecution.Audited s.encoding dummy (fun _ : Cfg => Skeleton.perfect height) initial) :
    Pr{let outcome ← (witness s dummy initial)}[
      OwnedNTTSoundness.OriginalRisk s dummy capacity radius outcome ∧
        ¬CheckpointCollision.Bad (fun _ : Cfg => Skeleton.perfect height) outcome.2.2] ≤
      ((((r : ENNReal)/Fintype.card F)^k) +
        (c : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card F)^b))) +
      (JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius +
        JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius) := by
  have arithmetic := truth_risk_bound s dummy capacity radius initial
  have opening := opening_safe_bound s basis dummy enough capacity radius small initial audited
  apply le_trans (prEvent_mono_of_support _ _
    (fun outcome => TruthRisk s dummy capacity radius outcome ∨
      (OpeningRisk s dummy capacity radius outcome ∧ ¬CheckpointCollision.Bad (fun _ : Cfg => Skeleton.perfect height) outcome.2.2)) ?_)
  · exact (prEvent_or_le _ _ _).trans (add_le_add arithmetic opening)
  · intro outcome supported event
    obtain ⟨risk,safe⟩ := event
    obtain ⟨owner,recorded,falseOriginal,passes⟩ := risk
    have audit := audited_witness s dummy initial audited outcome supported
    have same : OwnedNTTSoundness.originalSources s dummy capacity radius owner =
        sources s dummy capacity radius outcome.1 := by
      funext side
      rcases RecordedSourceCoherence.source_eq_or_bad s.encoding dummy s.domain capacity radius outcome.2.2 audit
          (s.tag side) (owner side) (snapshots s.tag outcome.1 side) (recorded side).2
          (fresh_recorded s dummy initial outcome supported side) (recorded side).1 with equal | bad
      · exact congrArg (QueryReindex.source s.dimensions) equal
      · exact False.elim (safe bad)
    have falseFresh : FalseRelation s dummy capacity radius outcome.1 := by
      intro relation
      exact falseOriginal (same.symm ▸ relation)
    rcases accepted_implies_risks s dummy capacity radius outcome falseFresh passes with truth | wrong
    · exact Or.inl truth
    · exact Or.inr ⟨wrong,safe⟩

end
end FormalProof4FHE.HasteBoots.NTTConditionalSoundness
