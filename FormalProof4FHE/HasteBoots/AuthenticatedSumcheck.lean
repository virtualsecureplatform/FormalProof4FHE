module

public import FormalProof4FHE.HasteBoots.PreparedTerminal
public import FormalProof4FHE.HasteBoots.NativeCommittedOpening

@[expose] public section

/-!
# Authenticated packed sumcheck with native interleaved openings

One program commits the root family, runs packed sumcheck, receives/checks/binds
terminal values and executes the concrete native factor loop. Source extraction
uses only the earlier commitment snapshot and trusted PCS parameters. Private
verifier coins, all prover/scheduler work and all native hashes share the same
handler. The final bound has sumcheck arithmetic error, PCS arithmetic error
and one whole-run expected hash charge, with no residual wrong-opening event.
This is an interactive typed theorem; shared ZeroCheck/stage composition,
Fiat--Shamir, honest scheduling completion and Rust/work refinement remain open.
-/

open OracleSpec OracleComp BinaryTree Matrix
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.CommittedJointMatrixOpening

namespace FormalProof4FHE.HasteBoots.AuthenticatedSumcheck

noncomputable section

structure Scheme (F Factor Term Message Input Digest Cfg Response Memory CommitMemory : Type) [Field F]
    (b front suffix m queries height : ℕ) where
  encoding : MerkleOracle.Encoding Input Digest (List F)
  domain : Fin (2 ^ height) ↪ F
  tag : Factor → Cfg
  factors : List Factor
  nodes : PackedSumcheckRound.Node b ↪ F
  arity : Term → ℕ
  coefficient : Term → F
  indices : (term : Term) → Fin (arity term) → Factor
  interpret : Message → Polynomial F
  claimed : Fin b → F
  commit : OracleComp (SharedSequence.Shared Cfg Input Digest) ((Factor → Digest) × CommitMemory)
  initial : ((Factor → Digest) × CommitMemory) → Memory
  send : ((Factor → Digest) × CommitMemory) → ℕ → Memory → (Fin b → F) →
    OracleComp (SharedSequence.Shared Cfg Input Digest) (Message × Memory)
  afterChallenge : ((Factor → Digest) × CommitMemory) → Memory → (Fin b → F) →
    OracleComp (SharedSequence.Shared Cfg Input Digest) Memory
  receiveValues : ((Factor → Digest) × CommitMemory) → PackedSumcheckSubclaim.Subclaim F b (front + suffix) → Memory →
    OracleComp (SharedSequence.Shared Cfg Input Digest) ((Factor → Fin b → F) × Memory)
  bindValues : ((Factor → Digest) × CommitMemory) → PackedSumcheckSubclaim.Subclaim F b (front + suffix) →
    (Factor → Fin b → F) → Memory → OracleComp (SharedSequence.Shared Cfg Input Digest) Memory
  build : ((Factor → Digest) × CommitMemory) → PreparedTerminal.Packet F Factor Memory b (front + suffix) →
    NativeMatrixVerifier.Protocol F Factor Input Digest Cfg Response Memory (2 ^ front) b m (2 ^ suffix) queries height

variable {F K Factor Term Message Input Digest Cfg Response Memory CommitMemory : Type}
  [Field F] [DecidableEq F] [Fintype Term] [DecidableEq Input] [DecidableEq Digest]
  {b front suffix m queries height : ℕ}

/-- The returned query controls only evaluation weights, never source layout. -/
def left (packet : PreparedTerminal.Packet F Factor Memory b (front + suffix)) (_factor : Factor) :=
  SubclaimSourceLayout.leftWeights (front := front) (suffix := suffix) (PreparedTerminal.query packet)

def right (packet : PreparedTerminal.Packet F Factor Memory b (front + suffix)) (_factor : Factor) :=
  SubclaimSourceLayout.rightWeights (front := front) (suffix := suffix) (PreparedTerminal.query packet)

/-- The actual checked values override any different values in an opening
factory. Trusted context overrides encoding/domain/roots/query separately. -/
def build (s : Scheme F Factor Term Message Input Digest Cfg Response Memory CommitMemory b front suffix m queries height)
    (emission : (Factor → Digest) × CommitMemory) (packet : PreparedTerminal.Packet F Factor Memory b (front + suffix)) :
    NativeMatrixVerifier.Protocol F Factor Input Digest Cfg Response Memory (2 ^ front) b m (2 ^ suffix) queries height :=
  { s.build emission packet with value := packet.data.values }

variable [SampleableType (Fin b → F)]

def select (s : Scheme F Factor Term Message Input Digest Cfg Response Memory CommitMemory b front suffix m queries height)
    (emission : (Factor → Digest) × CommitMemory) :=
  PreparedTerminal.select
    (PackedSumcheckOracle.program s.nodes s.interpret (s.send emission) (s.afterChallenge emission)
      (front + suffix) s.claimed (s.initial emission))
    s.arity s.coefficient s.indices (s.receiveValues emission) (s.bindValues emission) (s.initial emission)

variable [SampleableType (TestMatrix F (2 ^ front) b)]
  [SampleableType (Fin queries → Fin (2 ^ height))]

def continuation (s : Scheme F Factor Term Message Input Digest Cfg Response Memory CommitMemory b front suffix m queries height) :=
  NativeCommittedOpening.continuation s.encoding s.domain left right (build s) (select s)
    (fun _ packet => packet.data.enabled) (fun _ packet => packet.data.memory) s.factors

def program (s : Scheme F Factor Term Message Input Digest Cfg Response Memory CommitMemory b front suffix m queries height) :=
  MultiCommitmentPrefix.program (requests s.tag s.factors) s.commit (continuation s)

variable [SampleableType Digest]

def witness (s : Scheme F Factor Term Message Input Digest Cfg Response Memory CommitMemory b front suffix m queries height) (dummy : Digest) :=
  MultiCommitmentPrefix.witness s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
    (requests s.tag s.factors) s.commit (continuation s) (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height))

/-- All factors use one pre-query decoded source per public root/context. -/
def sources (s : Scheme F Factor Term Message Input Digest Cfg Response Memory CommitMemory b front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (first : ((Factor → Digest) × CommitMemory) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height)) :=
  fun factor => SubclaimSourceLayout.decodedSource (front := front) (suffix := suffix) s.domain capacity radius
    (JointMatrixOpening.frozen s.encoding dummy s.tag (snapshots s.tag first) factor)

abbrev Prefix := ((Factor → Digest) × CommitMemory) ×
  CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height)

abbrev RunResult := (PreparedTerminal.Packet F Factor Memory b (front + suffix) ×
  ShortCircuitSequence.Outcome Factor (JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries) Memory) ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height)

/-- Terminal checking and the complete native factor loop both succeed. -/
def accepted (result : PreparedTerminal.Packet F Factor Memory b (front + suffix) ×
    ShortCircuitSequence.Outcome Factor (JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries) Memory) : Bool :=
  result.1.data.enabled && result.2.accepted

/-- Earlier arithmetic risk, restricted to prefixes whose fixed decoded sum
really contradicts the public claim. No false-prefix certificate is supplied. -/
def TruthRisk
    (s : Scheme F Factor Term Message Input Digest Cfg Response Memory CommitMemory b front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (outcome : Prefix (Factor := Factor) (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) ×
      RunResult (F := F) (Factor := Factor) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (front := front) (suffix := suffix) (queries := queries) (height := height)) : Prop :=
  s.claimed ≠ PackedSumcheckExecution.sum s.arity s.coefficient s.indices (sources s dummy capacity radius outcome.1) ∧
  PackedSumcheckOracle.TruthfulResult s.arity s.coefficient s.indices (sources s dummy capacity radius outcome.1)
    outcome.2.1.1.earlier

/-- Accepted wrong supplied values on the actual native factor loop. -/
def OpeningRisk
    (s : Scheme F Factor Term Message Input Digest Cfg Response Memory CommitMemory b front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (outcome : Prefix (Factor := Factor) (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) ×
      RunResult (F := F) (Factor := Factor) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (front := front) (suffix := suffix) (queries := queries) (height := height)) : Prop :=
  outcome.2.1.2.accepted = true ∧ ∃ factor, outcome.2.1.1.data.values factor ≠
    (PreparedTerminal.query outcome.2.1.1).fold (sources s dummy capacity radius outcome.1 factor)

/-- Every accepted false fixed-source sum exposes one of the two actual
arithmetic events. Source selection uses the prefix snapshot throughout. -/
theorem accepted_implies_risks
    (s : Scheme F Factor Term Message Input Digest Cfg Response Memory CommitMemory b front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (outcome : Prefix (Factor := Factor) (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) ×
      RunResult (F := F) (Factor := Factor) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (front := front) (suffix := suffix) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness s dummy))
    (falseClaim : s.claimed ≠ PackedSumcheckExecution.sum s.arity s.coefficient s.indices
      (sources s dummy capacity radius outcome.1))
    (passes : accepted outcome.2.1 = true) :
    TruthRisk s dummy capacity radius outcome ∨ OpeningRisk s dummy capacity radius outcome := by
  simp only [witness, MultiCommitmentPrefix.witness, support_bind, support_pure, Set.mem_iUnion,
    Set.mem_singleton_iff] at supported
  obtain ⟨first, _, last, lastSupported, equal⟩ := supported
  subst outcome
  obtain ⟨selected, selectedSupported, opened, _, lastEqual⟩ :=
    (SharedContinuation.support_program s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
      (select s first.1) (fun packet => if packet.data.enabled then
        ShortCircuitSequence.program (NativeMatrixVerifier.step
          (NativeCommittedOpening.protocol s.encoding s.domain left right (build s) first.1 packet))
          s.factors packet.data.memory else pure ⟨[], packet.data.memory, false⟩)
      (RecordRoots.state _ (requests s.tag s.factors first.1) first.2) last).mp lastSupported
  subst last
  have flags := Bool.and_eq_true_iff.mp passes
  obtain ⟨entry, earlier, checked⟩ := PreparedTerminal.select_sound s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
    (PackedSumcheckOracle.program s.nodes s.interpret (s.send first.1) (s.afterChallenge first.1)
      (front + suffix) s.claimed (s.initial first.1))
    s.arity s.coefficient s.indices (s.receiveValues first.1) (s.bindValues first.1) (s.initial first.1)
    (RecordRoots.state _ (requests s.tag s.factors first.1) first.2) selected selectedSupported flags.1
  obtain truthful | wrong := PreparedTerminal.checked_truthful_or_wrong s.arity s.coefficient s.indices
    (sources s dummy capacity radius first) selected.1 entry earlier checked
  · exact Or.inl ⟨falseClaim, truthful⟩
  · exact Or.inr ⟨flags.2, wrong⟩

/-- The earlier sumcheck error is averaged over actual commitment outcomes,
including arbitrary private commitment memory and the real root-recorded state. -/
theorem truth_risk_bound [Fintype F]
    (s : Scheme F Factor Term Message Input Digest Cfg Response Memory CommitMemory b front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius productDegree : ℕ)
    (bounded : ∀ term, s.arity term ≤ productDegree)
    (messageDegree : ∀ message, (s.interpret message).natDegree ≤ (2 * b - 1) * productDegree) :
    Pr{let outcome ← (witness s dummy)}[TruthRisk s dummy capacity radius outcome] ≤
      ((front + suffix : ℕ) : ENNReal) *
        ((((((2 * b - 1) * productDegree : ℕ) : ENNReal) / Fintype.card F) ^ b)) := by
  unfold witness MultiCommitmentPrefix.witness
  apply prEvent_bind_le_of_forall_le
  intro first
  by_cases falseClaim : s.claimed ≠ PackedSumcheckExecution.sum s.arity s.coefficient s.indices
      (sources s dummy capacity radius first)
  · let initial := RecordRoots.state (fun _ : Cfg => Skeleton.perfect height) (requests s.tag s.factors first.1) first.2
    have afterNative := SharedContinuation.earlier_event_le s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
      (select s first.1) (fun packet => if packet.data.enabled then
        ShortCircuitSequence.program (NativeMatrixVerifier.step
          (NativeCommittedOpening.protocol s.encoding s.domain left right (build s) first.1 packet))
          s.factors packet.data.memory else pure ⟨[], packet.data.memory, false⟩) initial
      (fun packet => PackedSumcheckOracle.TruthfulResult s.arity s.coefficient s.indices
        (sources s dummy capacity radius first) packet.earlier)
    have afterPrepare := PreparedTerminal.earlier_event_le s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
      (PackedSumcheckOracle.program s.nodes s.interpret (s.send first.1) (s.afterChallenge first.1)
        (front + suffix) s.claimed (s.initial first.1))
      s.arity s.coefficient s.indices (s.receiveValues first.1) (s.bindValues first.1) (s.initial first.1) initial
      (PackedSumcheckOracle.TruthfulResult s.arity s.coefficient s.indices (sources s dummy capacity radius first))
    have arithmetic := PackedSumcheckSharedSoundness.soundness_bound s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
      s.nodes s.arity s.coefficient s.indices s.interpret productDegree bounded messageDegree
      (s.send first.1) (s.afterChallenge first.1) (front + suffix) (sources s dummy capacity radius first)
      s.claimed (s.initial first.1) initial falseClaim
    have bound := afterNative.trans (afterPrepare.trans arithmetic)
    simpa [continuation, NativeCommittedOpening.continuation, initial, prEvent_norm, TruthRisk, falseClaim] using bound
  · simp [TruthRisk, falseClaim, prEvent_norm]

variable [Fintype Digest] [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq K]
  [SampleableType ((Fin (2 ^ front) × Fin b) → K)]

/-- Concrete PCS soundness removes the accepted wrong-factor event, with one
charge on this same complete committed/guarded/native-worker execution. -/
theorem opening_risk_bound [NeZero m] [NeZero b]
    (s : Scheme F Factor Term Message Input Digest Cfg Response Memory CommitMemory b front suffix m queries height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (complete : ∀ factor, factor ∈ s.factors) (enough : m ≤ Fintype.card (Fin (2 ^ height)))
    (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← (witness s dummy)}[OpeningRisk s dummy capacity radius outcome] ≤
      (s.factors.map (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius)).sum +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (fun _ : Cfg => Skeleton.perfect height))
        (CheckpointCollision.loss unifSpec (fun _ : Cfg => Skeleton.perfect height)) (program s)
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) := by
  have bound := NativeCommittedOpening.soundness_from_empty basis s.encoding dummy s.tag s.factors complete
    s.domain enough capacity radius left right (build s) s.commit (select s)
    (fun _ packet => packet.data.enabled) (fun _ packet => packet.data.memory) small
  apply le_trans (prEvent_mono _ _ _ ?_) bound
  intro outcome risk
  obtain ⟨accepted, factor, different⟩ := risk
  refine ⟨accepted, factor, ?_⟩
  change outcome.2.1.1.data.values factor ≠ _
  rw [sources, SubclaimSourceLayout.fold_decodedSource] at different
  exact different

/-- Authenticated packed-sumcheck soundness on one complete native-worker
execution: sumcheck error plus PCS arithmetic error plus one expected hash
charge. No wrong-opening, safety or replay certificate remains in the result. -/
theorem soundness_from_empty [NeZero m] [NeZero b]
    (s : Scheme F Factor Term Message Input Digest Cfg Response Memory CommitMemory b front suffix m queries height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (complete : ∀ factor, factor ∈ s.factors) (enough : m ≤ Fintype.card (Fin (2 ^ height)))
    (capacity : 2 ^ suffix ≤ m * b) (radius productDegree : ℕ)
    (bounded : ∀ term, s.arity term ≤ productDegree)
    (messageDegree : ∀ message, (s.interpret message).natDegree ≤ (2 * b - 1) * productDegree)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← (witness s dummy)}[
      s.claimed ≠ PackedSumcheckExecution.sum s.arity s.coefficient s.indices (sources s dummy capacity radius outcome.1) ∧
      accepted outcome.2.1 = true] ≤
      (((front + suffix : ℕ) : ENNReal) *
        ((((((2 * b - 1) * productDegree : ℕ) : ENNReal) / Fintype.card F) ^ b)) +
      (s.factors.map (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius)).sum) +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (fun _ : Cfg => Skeleton.perfect height))
        (CheckpointCollision.loss unifSpec (fun _ : Cfg => Skeleton.perfect height)) (program s)
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) := by
  have arithmetic := truth_risk_bound s dummy capacity radius productDegree bounded messageDegree
  have opening := opening_risk_bound s basis dummy complete enough capacity radius small
  apply le_trans (prEvent_mono_of_support _ _ (fun outcome =>
    TruthRisk s dummy capacity radius outcome ∨ OpeningRisk s dummy capacity radius outcome) ?_)
  · exact (prEvent_or_le _ _ _).trans ((add_le_add arithmetic opening).trans_eq (add_assoc _ _ _).symm)
  · intro outcome supported event
    exact accepted_implies_risks s dummy capacity radius outcome supported event.1 event.2

/-- Native evaluation vectors fix the nodes and interpreter; their message
polynomials have the required degree by the proved interpolation theorem. -/
def nativeScheme (characteristic productDegree : ℕ) [CharP F characteristic]
    (small : (2 * b - 1) * productDegree + 1 ≤ characteristic)
    (enough : 2 * b ≤ (2 * b - 1) * productDegree + 1)
    (s : Scheme F Factor Term (Fin ((2 * b - 1) * productDegree + 1) → F)
      Input Digest Cfg Response Memory CommitMemory b front suffix m queries height) :
    Scheme F Factor Term (Fin ((2 * b - 1) * productDegree + 1) → F)
      Input Digest Cfg Response Memory CommitMemory b front suffix m queries height :=
  { s with
    nodes := NativePackedInterpolation.nodes characteristic (enough.trans small)
    interpret := NativePackedInterpolation.messagePolynomial (NativePackedInterpolation.consecutive characteristic small) }

/-- Authenticated native-message packed sumcheck, with no degree, opening,
replay or safe-prefix security certificate supplied by the prover. -/
theorem native_soundness_from_empty [NeZero m] [NeZero b]
    (characteristic productDegree : ℕ) [CharP F characteristic]
    (nodeSmall : (2 * b - 1) * productDegree + 1 ≤ characteristic)
    (nodesEnough : 2 * b ≤ (2 * b - 1) * productDegree + 1)
    (s : Scheme F Factor Term (Fin ((2 * b - 1) * productDegree + 1) → F)
      Input Digest Cfg Response Memory CommitMemory b front suffix m queries height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (complete : ∀ factor, factor ∈ s.factors) (enough : m ≤ Fintype.card (Fin (2 ^ height)))
    (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (bounded : ∀ term, s.arity term ≤ productDegree)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← (witness (nativeScheme characteristic productDegree nodeSmall nodesEnough s) dummy)}[
      s.claimed ≠ PackedSumcheckExecution.sum s.arity s.coefficient s.indices (sources s dummy capacity radius outcome.1) ∧
      accepted outcome.2.1 = true] ≤
      (((front + suffix : ℕ) : ENNReal) *
        ((((((2 * b - 1) * productDegree : ℕ) : ENNReal) / Fintype.card F) ^ b)) +
      (s.factors.map (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius)).sum) +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (fun _ : Cfg => Skeleton.perfect height))
        (CheckpointCollision.loss unifSpec (fun _ : Cfg => Skeleton.perfect height))
        (program (nativeScheme characteristic productDegree nodeSmall nodesEnough s))
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) :=
  soundness_from_empty (nativeScheme characteristic productDegree nodeSmall nodesEnough s) basis dummy complete enough
    capacity radius productDegree bounded (fun _ => NativePackedInterpolation.messagePolynomial_degree _ _) small

end

end FormalProof4FHE.HasteBoots.AuthenticatedSumcheck
