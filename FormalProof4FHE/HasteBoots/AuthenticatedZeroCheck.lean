module

public import FormalProof4FHE.HasteBoots.PreparedZeroTerminal
public import FormalProof4FHE.HasteBoots.PackedZeroSharedSoundness
public import FormalProof4FHE.HasteBoots.QueryReindex
public import FormalProof4FHE.HasteBoots.NativeCommittedOpening

@[expose] public section

/-!
# Authenticated ZeroCheck with original-factor native openings

One actual shared execution commits only the original factors, runs adaptive
packed ZeroCheck, checks its verifier-computed public EQ terminal and opens
original-factor values with the concrete interleaved native worker loop. The
false decoded-source zero relation is an event on the actual commitment prefix.
The bound contains all three ZeroCheck arithmetic terms, the PCS arithmetic sum
and one expected hash charge for this complete stopped execution. Native static
preflight/transcript order, full PBS composition, honest scheduling completion,
Fiat--Shamir and Rust/physical-work refinement remain separate obligations.
-/

open OracleSpec OracleComp BinaryTree Matrix
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.CommittedJointMatrixOpening

namespace FormalProof4FHE.HasteBoots.AuthenticatedZeroCheck

noncomputable section

structure Scheme (F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory : Type) [Field F]
    (b n front suffix m queries height : ℕ) where
  dimensions : n + 1 = front + suffix
  encoding : MerkleOracle.Encoding Input Digest (List F)
  domain : Fin (2 ^ height) ↪ F
  tag : Factor → Cfg
  factors : List Factor
  nodes : PackedSumcheckRound.Node b ↪ F
  arity : Term → ℕ
  coefficient : Term → F
  indices : (term : Term) → Fin (arity term) → Factor
  interpretFirst : FirstMessage → Fin b → Polynomial F
  interpret : Message → Polynomial F
  commit : OracleComp (SharedSequence.Shared Cfg Input Digest) ((Factor → Digest) × CommitMemory)
  initial : ((Factor → Digest) × CommitMemory) → Memory
  firstRespond : ((Factor → Digest) × CommitMemory) → PackedZeroReduction.Points F n b → Memory →
    OracleComp (SharedSequence.Shared Cfg Input Digest) (FirstMessage × Memory)
  afterFirst : ((Factor → Digest) × CommitMemory) → PackedZeroReduction.Points F n b → FirstMessage × Memory →
    PackedZeroReduction.Coins F b → OracleComp (SharedSequence.Shared Cfg Input Digest) Memory
  send : ((Factor → Digest) × CommitMemory) → ℕ → Memory → (Fin b → F) →
    OracleComp (SharedSequence.Shared Cfg Input Digest) (Message × Memory)
  afterChallenge : ((Factor → Digest) × CommitMemory) → Memory → (Fin b → F) →
    OracleComp (SharedSequence.Shared Cfg Input Digest) Memory
  receiveValues : ((Factor → Digest) × CommitMemory) → PackedZeroOracle.Subclaim F b n → Memory →
    OracleComp (SharedSequence.Shared Cfg Input Digest) ((Factor → Fin b → F) × Memory)
  bindValues : ((Factor → Digest) × CommitMemory) → PackedZeroOracle.Subclaim F b n →
    (Factor → Fin b → F) → Memory → OracleComp (SharedSequence.Shared Cfg Input Digest) Memory
  build : ((Factor → Digest) × CommitMemory) → PreparedZeroTerminal.Packet F Factor Memory b n →
    NativeMatrixVerifier.Protocol F Factor Input Digest Cfg Response Memory (2 ^ front) b m (2 ^ suffix) queries height

variable {F K Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory : Type}
  [Field F] [DecidableEq F] [Fintype Term] [DecidableEq Input] [DecidableEq Digest]
  {b n front suffix m queries height : ℕ}

/-- Trusted total-dimension equality changes neither the matrix order nor the
source. The PCS split remains fixed before every verifier challenge. -/
def query (s : Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (packet : PreparedZeroTerminal.Packet F Factor Memory b n) :=
  QueryReindex.query s.dimensions (PreparedZeroTerminal.query s.nodes packet)

def left (s : Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (packet : PreparedZeroTerminal.Packet F Factor Memory b n) (_factor : Factor) :=
  SubclaimSourceLayout.leftWeights (front := front) (suffix := suffix) (query s packet)

def right (s : Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (packet : PreparedZeroTerminal.Packet F Factor Memory b n) (_factor : Factor) :=
  SubclaimSourceLayout.rightWeights (front := front) (suffix := suffix) (query s packet)

/-- The actual checked values override any different values in an opening
factory. Trusted context overrides encoding/domain/roots/query separately. -/
def build (s : Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (emission : (Factor → Digest) × CommitMemory) (packet : PreparedZeroTerminal.Packet F Factor Memory b n) :
    NativeMatrixVerifier.Protocol F Factor Input Digest Cfg Response Memory (2 ^ front) b m (2 ^ suffix) queries height :=
  { s.build emission packet with value := packet.data.values }

variable [SampleableType (Fin b → F)] [SampleableType F] [SampleableType (Fin n → F)]
  [SampleableType (PackedZeroReduction.Points F n b)] [SampleableType (Fin b → Fin b → F)]
  [SampleableType (Fin b → ((Fin b → F) × F))]

def select (s : Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (emission : (Factor → Digest) × CommitMemory) :=
  PreparedZeroTerminal.select
    (PackedZeroOracle.program s.nodes s.interpretFirst s.interpret (s.firstRespond emission) (s.afterFirst emission)
      (s.send emission) (s.afterChallenge emission) (s.initial emission))
    s.arity s.coefficient s.indices (s.receiveValues emission) (s.bindValues emission) (s.initial emission)

variable [SampleableType (TestMatrix F (2 ^ front) b)]
  [SampleableType (Fin queries → Fin (2 ^ height))]

def continuation (s : Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height) :=
  NativeCommittedOpening.continuation s.encoding s.domain (left s) (right s) (build s) (select s)
    (fun _ packet => packet.data.enabled) (fun _ packet => packet.data.memory) s.factors

def program (s : Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height) :=
  MultiCommitmentPrefix.program (requests s.tag s.factors) s.commit (continuation s)

variable [SampleableType Digest]

def witness (s : Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height) (dummy : Digest) :=
  MultiCommitmentPrefix.witness s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
    (requests s.tag s.factors) s.commit (continuation s) (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height))

omit [SampleableType F] [SampleableType (Fin n → F)] [SampleableType (Fin b → ((Fin b → F) × F))] in
/-- Erasing the analysis-only prefix reproduces the actual shared program,
including every rejected-path call and its final cache and log. -/
theorem project_witness
    (s : Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) :
    (fun outcome => ((outcome.1.1, outcome.2.1), outcome.2.2)) <$> witness s dummy =
      (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy
        (fun _ : Cfg => Skeleton.perfect height)) (program s)).run
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) :=
  MultiCommitmentPrefix.project_witness s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
    (requests s.tag s.factors) s.commit (continuation s) (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height))

/-- All factors use one pre-query decoded source per public root/context. -/
def sources (s : Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (first : ((Factor → Digest) × CommitMemory) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height)) :=
  fun factor => QueryReindex.source s.dimensions (SubclaimSourceLayout.decodedSource (front := front) (suffix := suffix) s.domain capacity radius
    (JointMatrixOpening.frozen s.encoding dummy s.tag (snapshots s.tag first) factor))

abbrev Prefix := ((Factor → Digest) × CommitMemory) ×
  CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height)

abbrev RunResult := (PreparedZeroTerminal.Packet F Factor Memory b n ×
  ShortCircuitSequence.Outcome Factor (JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries) Memory) ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height)

/-- Terminal checking and the complete native factor loop both succeed. -/
def accepted (result : PreparedZeroTerminal.Packet F Factor Memory b n ×
    ShortCircuitSequence.Outcome Factor (JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries) Memory) : Bool :=
  result.1.data.enabled && result.2.accepted

/-- Earlier arithmetic risk, restricted to prefixes whose fixed decoded sources
violate the original zero relation. No false-prefix certificate is supplied. -/
def TruthRisk
    (s : Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (outcome : Prefix (Factor := Factor) (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) ×
      RunResult (F := F) (Factor := Factor) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (n := n) (front := front) (queries := queries) (height := height)) : Prop :=
  ¬PackedZeroCube.Vanishes s.arity s.coefficient s.indices (sources s dummy capacity radius outcome.1) ∧
  PackedZeroOracle.TruthfulResult s.nodes s.arity s.coefficient s.indices (sources s dummy capacity radius outcome.1)
    outcome.2.1.1.earlier

/-- Accepted wrong supplied values on the actual native factor loop. -/
def OpeningRisk
    (s : Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (outcome : Prefix (Factor := Factor) (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) ×
      RunResult (F := F) (Factor := Factor) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (n := n) (front := front) (queries := queries) (height := height)) : Prop :=
  outcome.2.1.2.accepted = true ∧ ∃ factor, outcome.2.1.1.data.values factor ≠
    (PreparedZeroTerminal.query s.nodes outcome.2.1.1).fold (sources s dummy capacity radius outcome.1 factor)

omit [SampleableType F] [SampleableType (Fin n → F)] [SampleableType (Fin b → ((Fin b → F) × F))] in
/-- Every accepted false fixed-source zero relation exposes one of the two actual
arithmetic events. Source selection uses the prefix snapshot throughout. -/
theorem accepted_implies_risks
    (s : Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (outcome : Prefix (Factor := Factor) (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) ×
      RunResult (F := F) (Factor := Factor) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (n := n) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness s dummy))
    (falseClaim : ¬PackedZeroCube.Vanishes s.arity s.coefficient s.indices
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
          (NativeCommittedOpening.protocol s.encoding s.domain (left s) (right s) (build s) first.1 packet))
          s.factors packet.data.memory else pure ⟨[], packet.data.memory, false⟩)
      (RecordRoots.state _ (requests s.tag s.factors first.1) first.2) last).mp lastSupported
  subst last
  have flags := Bool.and_eq_true_iff.mp passes
  obtain ⟨entry, earlier, checked⟩ := PreparedZeroTerminal.select_sound s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
    (PackedZeroOracle.program s.nodes s.interpretFirst s.interpret (s.firstRespond first.1) (s.afterFirst first.1)
      (s.send first.1) (s.afterChallenge first.1) (s.initial first.1))
    s.arity s.coefficient s.indices (s.receiveValues first.1) (s.bindValues first.1) (s.initial first.1)
    (RecordRoots.state _ (requests s.tag s.factors first.1) first.2) selected selectedSupported flags.1
  obtain truthful | wrong := PreparedZeroTerminal.checked_truthful_or_wrong s.nodes s.arity s.coefficient s.indices
    (sources s dummy capacity radius first) selected.1 entry earlier checked
  · exact Or.inl ⟨falseClaim, truthful⟩
  · exact Or.inr ⟨flags.2, wrong⟩

/-- The earlier ZeroCheck error is averaged over actual commitment outcomes,
including arbitrary private commitment memory and the real root-recorded state. -/
theorem truth_risk_bound [Fintype F]
    (s : Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius productDegree : ℕ)
    (bounded : ∀ term, s.arity term ≤ productDegree)
    (firstDegree : ∀ message point, (s.interpretFirst message point).natDegree ≤ (2 * b - 1) * productDegree)
    (messageDegree : ∀ message, (s.interpret message).natDegree ≤ (2 * b - 1) * (productDegree + 1)) :
    Pr{let outcome ← (witness s dummy)}[TruthRisk s dummy capacity radius outcome] ≤
      ((n : ENNReal) / Fintype.card F) ^ b +
        ((((((2 * b - 1) * productDegree + 1 : ℕ) : ENNReal) / Fintype.card F) ^ b)) +
        (n : ENNReal) * ((((((2 * b - 1) * (productDegree + 1) : ℕ) : ENNReal) / Fintype.card F) ^ b)) := by
  unfold witness MultiCommitmentPrefix.witness
  apply prEvent_bind_le_of_forall_le
  intro first
  by_cases falseClaim : ¬PackedZeroCube.Vanishes s.arity s.coefficient s.indices
      (sources s dummy capacity radius first)
  · let initial := RecordRoots.state (fun _ : Cfg => Skeleton.perfect height) (requests s.tag s.factors first.1) first.2
    have afterNative := SharedContinuation.earlier_event_le s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
      (select s first.1) (fun packet => if packet.data.enabled then
        ShortCircuitSequence.program (NativeMatrixVerifier.step
          (NativeCommittedOpening.protocol s.encoding s.domain (left s) (right s) (build s) first.1 packet))
          s.factors packet.data.memory else pure ⟨[], packet.data.memory, false⟩) initial
      (fun packet => PackedZeroOracle.TruthfulResult s.nodes s.arity s.coefficient s.indices
        (sources s dummy capacity radius first) packet.earlier)
    have afterPrepare := PreparedZeroTerminal.earlier_event_le s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
      (PackedZeroOracle.program s.nodes s.interpretFirst s.interpret (s.firstRespond first.1) (s.afterFirst first.1)
        (s.send first.1) (s.afterChallenge first.1) (s.initial first.1))
      s.arity s.coefficient s.indices (s.receiveValues first.1) (s.bindValues first.1) (s.initial first.1) initial
      (PackedZeroOracle.TruthfulResult s.nodes s.arity s.coefficient s.indices (sources s dummy capacity radius first))
    have arithmetic := PackedZeroSharedSoundness.soundness_bound s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
      s.nodes s.arity s.coefficient s.indices (sources s dummy capacity radius first) productDegree bounded
      s.interpretFirst s.interpret firstDegree messageDegree (s.firstRespond first.1) (s.afterFirst first.1)
      (s.send first.1) (s.afterChallenge first.1) (s.initial first.1) initial falseClaim
    have bound := afterNative.trans (afterPrepare.trans arithmetic)
    simpa [continuation, NativeCommittedOpening.continuation, initial, prEvent_norm, TruthRisk, falseClaim] using bound
  · have valid := Classical.not_not.mp falseClaim
    simp [TruthRisk, valid, prEvent_norm]

variable [Fintype Digest] [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq K]
  [SampleableType ((Fin (2 ^ front) × Fin b) → K)]

omit [SampleableType F] [SampleableType (Fin n → F)] [SampleableType (Fin b → ((Fin b → F) × F))] in
/-- Concrete PCS soundness removes the accepted wrong-factor event, with one
charge on this same complete committed/guarded/native-worker execution. -/
theorem opening_risk_bound [NeZero m] [NeZero b]
    (s : Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
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
    s.domain enough capacity radius (left s) (right s) (build s) s.commit (select s)
    (fun _ packet => packet.data.enabled) (fun _ packet => packet.data.memory) small
  apply le_trans (prEvent_mono _ _ _ ?_) bound
  intro outcome risk
  obtain ⟨accepted, factor, different⟩ := risk
  refine ⟨accepted, factor, ?_⟩
  change outcome.2.1.1.data.values factor ≠ _
  rw [sources, QueryReindex.fold, SubclaimSourceLayout.fold_decodedSource] at different
  exact different

/-- Authenticated packed-ZeroCheck soundness on one complete native-worker
execution: ZeroCheck error plus PCS arithmetic error plus one expected hash
charge. No wrong-opening, safety or replay certificate remains in the result. -/
theorem soundness_from_empty [NeZero m] [NeZero b]
    (s : Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (complete : ∀ factor, factor ∈ s.factors) (enough : m ≤ Fintype.card (Fin (2 ^ height)))
    (capacity : 2 ^ suffix ≤ m * b) (radius productDegree : ℕ)
    (bounded : ∀ term, s.arity term ≤ productDegree)
    (firstDegree : ∀ message point, (s.interpretFirst message point).natDegree ≤ (2 * b - 1) * productDegree)
    (messageDegree : ∀ message, (s.interpret message).natDegree ≤ (2 * b - 1) * (productDegree + 1))
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← (witness s dummy)}[
      ¬PackedZeroCube.Vanishes s.arity s.coefficient s.indices (sources s dummy capacity radius outcome.1) ∧
      accepted outcome.2.1 = true] ≤
      (((n : ENNReal) / Fintype.card F) ^ b +
        ((((((2 * b - 1) * productDegree + 1 : ℕ) : ENNReal) / Fintype.card F) ^ b)) +
        (n : ENNReal) * ((((((2 * b - 1) * (productDegree + 1) : ℕ) : ENNReal) / Fintype.card F) ^ b)) +
      (s.factors.map (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius)).sum) +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (fun _ : Cfg => Skeleton.perfect height))
        (CheckpointCollision.loss unifSpec (fun _ : Cfg => Skeleton.perfect height)) (program s)
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) := by
  have arithmetic := truth_risk_bound s dummy capacity radius productDegree bounded firstDegree messageDegree
  have opening := opening_risk_bound s basis dummy complete enough capacity radius small
  apply le_trans (prEvent_mono_of_support _ _ (fun outcome =>
    TruthRisk s dummy capacity radius outcome ∨ OpeningRisk s dummy capacity radius outcome) ?_)
  · exact (prEvent_or_le _ _ _).trans ((add_le_add arithmetic opening).trans_eq (add_assoc _ _ _).symm)
  · intro outcome supported event
    exact accepted_implies_risks s dummy capacity radius outcome supported event.1 event.2

/-- Native typed evaluation vectors supply both degree bounds by interpolation;
only original-factor roots appear in the committed family. -/
def nativeScheme (characteristic productDegree : ℕ) [CharP F characteristic]
    (firstSmall : (2 * b - 1) * productDegree + 1 ≤ characteristic)
    (roundSmall : (2 * b - 1) * (productDegree + 1) + 1 ≤ characteristic)
    (nodesEnough : 2 * b ≤ (2 * b - 1) * productDegree + 1)
    (s : Scheme F Factor Term (Fin b → Fin ((2 * b - 1) * productDegree + 1) → F)
      (Fin ((2 * b - 1) * (productDegree + 1) + 1) → F) Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height) :
    Scheme F Factor Term (Fin b → Fin ((2 * b - 1) * productDegree + 1) → F)
      (Fin ((2 * b - 1) * (productDegree + 1) + 1) → F) Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height :=
  { s with
    nodes := NativePackedInterpolation.nodes characteristic (nodesEnough.trans firstSmall)
    interpretFirst := fun message point => NativePackedInterpolation.messagePolynomial
      (NativePackedInterpolation.consecutive characteristic firstSmall) (message point)
    interpret := NativePackedInterpolation.messagePolynomial
      (NativePackedInterpolation.consecutive characteristic roundSmall) }

/-- Complete authenticated native-message ZeroCheck: no degree, wrong-opening,
replay, safe-prefix or supplied EQ security certificate is assumed. -/
theorem native_soundness_from_empty [NeZero m] [NeZero b]
    (characteristic productDegree : ℕ) [CharP F characteristic]
    (firstSmall : (2 * b - 1) * productDegree + 1 ≤ characteristic)
    (roundSmall : (2 * b - 1) * (productDegree + 1) + 1 ≤ characteristic)
    (nodesEnough : 2 * b ≤ (2 * b - 1) * productDegree + 1)
    (s : Scheme F Factor Term (Fin b → Fin ((2 * b - 1) * productDegree + 1) → F)
      (Fin ((2 * b - 1) * (productDegree + 1) + 1) → F) Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (complete : ∀ factor, factor ∈ s.factors) (enough : m ≤ Fintype.card (Fin (2 ^ height)))
    (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (bounded : ∀ term, s.arity term ≤ productDegree)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← (witness (nativeScheme characteristic productDegree firstSmall roundSmall nodesEnough s) dummy)}[
      ¬PackedZeroCube.Vanishes s.arity s.coefficient s.indices (sources s dummy capacity radius outcome.1) ∧
      accepted outcome.2.1 = true] ≤
      (((n : ENNReal) / Fintype.card F) ^ b +
        ((((((2 * b - 1) * productDegree + 1 : ℕ) : ENNReal) / Fintype.card F) ^ b)) +
        (n : ENNReal) * ((((((2 * b - 1) * (productDegree + 1) : ℕ) : ENNReal) / Fintype.card F) ^ b)) +
      (s.factors.map (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius)).sum) +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (fun _ : Cfg => Skeleton.perfect height))
        (CheckpointCollision.loss unifSpec (fun _ : Cfg => Skeleton.perfect height)) (program (nativeScheme characteristic productDegree firstSmall roundSmall nodesEnough s))
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) :=
  soundness_from_empty (nativeScheme characteristic productDegree firstSmall roundSmall nodesEnough s) basis dummy complete enough capacity radius productDegree bounded
    (fun _ _ => NativePackedInterpolation.messagePolynomial_degree _ _)
    (fun _ => NativePackedInterpolation.messagePolynomial_degree _ _) small

end

end FormalProof4FHE.HasteBoots.AuthenticatedZeroCheck
