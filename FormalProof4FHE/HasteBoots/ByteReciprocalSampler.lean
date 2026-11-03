module

public import FormalProof4FHE.HasteBoots.CanonicalExtensionSampler
public import FormalProof4FHE.HasteBoots.OptionalRejectionWork

@[expose] public section

/-!
# Reciprocal retries driven by canonical byte-backed extension draws

Each outer trial retains its whole extension/coefficient observation. A
completed zero or public-table pole is retried; an unfinished inner field
sample suspends with its partial bytes retained. The native test is direct,
not enumeration of the field. Prefix lengths are analysis approximations.
Fresh ideal bytes, a proved coordinate basis and trusted profile checks remain
explicit; XOF/transcript/Rust and primitive-hash refinement are separate.
-/

open OracleSpec OracleComp MeasureTheory
open scoped Classical BigOperators

namespace FormalProof4FHE.HasteBoots.ByteReciprocalSampler

noncomputable section

def singletonEquiv (K : Type) : (Fin 1 → K) ≃ K where
  toFun values := values 0
  invFun value := fun _ => value
  left_inv values := by funext index; rw [Subsingleton.elim index 0]
  right_inv _ := rfl

theorem singleton_uniform {K : Type} [SampleableType K] (event : K → Prop) :
    Pr{let values ← $ᵗ (Fin 1 → K)}[event (values 0)] = Pr{let value ← $ᵗ K}[event value] :=
  SampleableType.prEvent_uniformSample_equiv (singletonEquiv K) event

variable {p degree size : ℕ} {K : Type} [Field K] [Module (ZMod p) K]
  [DecidableEq K] [Fintype K] [SampleableType K] [NeZero p]

abbrev Trial (p degree : ℕ) (K : Type) :=
  Option (Fin 1 → K) × CanonicalCoefficientVector.Result p (1 * degree)

def candidate (trial : Trial p degree K) : Option K := trial.1.map (fun values => values 0)

def cost (trial : Trial p degree K) : ℕ := CanonicalCoefficientWork.consumedBytes p trial.2

def step (basis : Module.Basis (Fin degree) (ZMod p) K) (inner : ℕ) : ProbComp (Trial p degree K) :=
  CanonicalExtensionSampler.program basis inner 1

def completion (p degree inner : ℕ) : ENNReal := CanonicalCoefficientVector.completion p inner ^ (1 * degree)

@[reducible] def allow (table : Fin size → K) (value : K) : Prop := value ≠ 0 ∧ ∀ index, value + table index ≠ 0

omit [SampleableType K] in
theorem accepted_eq (table : Fin size → K) :
    OptionalRejectionLoop.accepted (allow table) = ReciprocalDetection.allowed table := by
  ext value
  simp [OptionalRejectionLoop.accepted, allow, ReciprocalDetection.mem_allowed]

omit [DecidableEq K] [Fintype K] in
/-- The optional field-trial law is derived from the actual canonical byte
program, with its true incomplete mass and full raw observations intact. -/
theorem candidate_law (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K) (inner : ℕ) (event : K → Prop) :
    Pr{let trial ← step basis inner}[(candidate trial).elim False event] =
      completion p degree inner * Pr{let value ← $ᵗ K}[event value] := by
  have sampled := CanonicalExtensionSampler.probability valid basis inner 1 (fun values => event (values 0))
  have same := prEvent_congr (step basis inner)
    (fun trial => (candidate trial).elim False event) (fun trial => trial.1.elim False (fun values => event (values 0)))
    (by intro trial; unfold candidate; cases trial.1 <;> rfl)
  exact same.trans (sampled.trans (congrArg (completion p degree inner * ·) (singleton_uniform event)))

def program (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → K) (inner outer : ℕ) :
    ProbComp (OptionalRejectionLoop.Result K (Trial p degree K)) :=
  OptionalRejectionLoop.program (step basis inner) candidate (allow table) outer

omit [Fintype K] [SampleableType K] [NeZero p] in
/-- Every returned offset passed both actual native exclusion tests. -/
theorem returned_allowed (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → K) (inner outer : ℕ)
    (result : OptionalRejectionLoop.Result K (Trial p degree K)) (supported : result ∈ support (program basis table inner outer))
    (value : K) (returned : result.value = some value) : value ≠ 0 ∧ ∀ index, value + table index ≠ 0 :=
  OptionalRejectionLoop.returned_accept _ _ _ outer result supported value returned

/-- Exact successful mass for every nested operational approximation. Inner
suspension is not treated as a completed rejected field candidate. -/
theorem probability (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → K)
    (inner outer : ℕ) (event : K → Prop) :
    Pr{let result ← program basis table inner outer}[result.value.elim False event] =
      (∑ attempt ∈ Finset.range outer,
        (completion p degree inner * RejectionSampling.reject (ReciprocalDetection.allowed table)) ^ attempt) *
      (completion p degree inner * RejectionSampling.hit (ReciprocalDetection.allowed table) event) := by
  have law := OptionalRejectionLoop.probability (step basis inner) candidate (completion p degree inner)
    (candidate_law valid basis inner) (allow table) outer event
  simpa only [accepted_eq, program] using law

/-- The entire real finite approximation is dominated by the ideal accepted
reciprocal-domain law. Incomplete mass is kept, with no retry cap assumption. -/
theorem event_le_ideal (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → K)
    (enough : size + 1 < Fintype.card K) (inner outer : ℕ) (event : K → Prop) :
    Pr{let result ← program basis table inner outer}[result.value.elim False event] ≤
      Pr{let value ← ReciprocalDetection.sample table}[event value] := by
  have nonempty : (OptionalRejectionLoop.accepted (allow table)).Nonempty := by
    rw [accepted_eq]
    exact ReciprocalDetection.allowed_nonempty table enough
  have bound := OptionalRejectionLoop.event_le_uniform (step basis inner) candidate (completion p degree inner)
    (candidate_law valid basis inner) (allow table) nonempty outer event
  simpa only [accepted_eq, ReciprocalDetection.sample, program] using bound

omit [DecidableEq K] [Fintype K] [SampleableType K] [NeZero p] in
theorem head_cost (basis : Module.Basis (Fin degree) (ZMod p) K) (inner : ℕ) :
    OptionalRejectionWork.headCost (step basis inner) cost = CanonicalCoefficientWork.expectedBytes p inner (1 * degree) :=
  CanonicalExtensionSampler.expectedBytes basis inner 1

def consumedBytes (result : OptionalRejectionLoop.Result K (Trial p degree K)) : ℕ :=
  OptionalRejectionWork.consumed cost result

def expectedBytes (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → K) (inner outer : ℕ) : ENNReal :=
  ∫⁻ value, value ∂𝒟[(fun result => (consumedBytes result : ENNReal)) <$> program basis table inner outer]

/-- Exact byte work includes rejected complete trials and the partially
completed last field trial. No cost/value independence premise is needed. -/
theorem expectedBytes_formula (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → K)
    (inner outer : ℕ) :
    expectedBytes basis table inner outer = CanonicalCoefficientWork.expectedBytes p inner (1 * degree) *
      (∑ attempt ∈ Finset.range outer,
        (completion p degree inner * RejectionSampling.reject (ReciprocalDetection.allowed table)) ^ attempt) := by
  have work := OptionalRejectionWork.expectedCost_formula (step basis inner) candidate (completion p degree inner)
    (candidate_law valid basis inner) (allow table) cost outer
  rw [head_cost] at work
  simpa only [accepted_eq, OptionalRejectionWork.expectedCost, expectedBytes, consumedBytes, program] using work

section SharedRuntime

variable {Cfg Input Digest Payload Later : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

omit [Fintype K] [SampleableType K] [NeZero p] in
/-- Ideal private byte trials preserve the incoming hash/cache/checkpoints;
the full nested observation, including a partial last trial, is retained. -/
theorem private_state (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → K) (inner outer : ℕ)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (PrivateSampling.embed Cfg Input Digest (program basis table inner outer))).run state =
      (fun result => (result, state)) <$> program basis table inner outer :=
  PrivateSampling.run_probComp enc dummy shape _ state

/-- Arbitrary later shared work may inspect every nested raw trace. It cannot
increase a fixed accepted-offset event of the actual earlier result. -/
theorem retained_bound (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → K)
    (enough : size + 1 < Fintype.card K) (inner outer : ℕ)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (next : OptionalRejectionLoop.Result K (Trial p degree K) →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Later)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) (event : K → Prop) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (SharedContinuation.program (PrivateSampling.embed Cfg Input Digest (program basis table inner outer)) next)).run state}[
        outcome.1.1.value.elim False event] ≤ Pr{let value ← ReciprocalDetection.sample table}[event value] := by
  have retained := SharedContinuation.earlier_event_le enc dummy shape
    (PrivateSampling.embed Cfg Input Digest (program basis table inner outer)) next state (fun earlier => earlier.value.elim False event)
  have sampled := event_le_ideal valid basis table enough inner outer event
  exact retained.trans (by simpa only [PrivateSampling.run_probComp, prEvent_map] using sampled)

end SharedRuntime

end

end FormalProof4FHE.HasteBoots.ByteReciprocalSampler
