module

public import FormalProof4FHE.HasteBoots.JointMatrixOpening
public import FormalProof4FHE.HasteBoots.ShortCircuitSequence
public import FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening

@[expose] public section

/-!
# Arithmetic for factor openings with actual early rejection

The native column phase returns its result, retained private memory and
verification flag. The factor loop uses that flag to stop before any later
factor's coins or hash calls. The arithmetic bound applies to attempted
openings, including a rejected attempt, on this same actual execution.
Authentication and native worker-flag linkage remain separate interfaces.
-/

open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening

namespace FormalProof4FHE.HasteBoots.StoppingJointMatrixOpening

noncomputable section

variable {F Factor Cfg Input Digest Response Memory : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  {leftCount b m size queries height : ℕ}

abbrev Data (F Digest Response : Type) (leftCount b height queries : ℕ) :=
  SampleData F Response leftCount b height queries × Columns F Digest leftCount b height

/-- Private memory returned by the column phase is carried into the next
factor. Projecting it out does not delete any actual oracle calls. -/
def step [SampleableType (TestMatrix F leftCount b)]
    [SampleableType (Fin queries → Fin (2 ^ height))]
    (respond : Factor → Memory → TestMatrix F leftCount b →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Response)
    (next : Factor → Memory → SampleData F Response leftCount b height queries →
      OracleComp (SharedSequence.Shared Cfg Input Digest) ((Columns F Digest leftCount b height × Memory) × Bool))
    (factor : Factor) (memory : Memory) :
    OracleComp (SharedSequence.Shared Cfg Input Digest)
      (ShortCircuitSequence.StepResult (JointMatrixOpening.Data F Digest Response leftCount b height queries) Memory) :=
  (fun outcome => (⟨(outcome.1, outcome.2.1.1), outcome.2.1.2, outcome.2.2⟩ :
    ShortCircuitSequence.StepResult (JointMatrixOpening.Data F Digest Response leftCount b height queries) Memory)) <$>
    InteractiveSampling.complete ($ᵗ (TestMatrix F leftCount b)) (respond factor memory)
      ($ᵗ (Fin queries → Fin (2 ^ height))) (next factor memory)

/-- Enforce the deterministic native response/value checks after the worker
phase, without issuing any additional oracle queries. -/
def checkedNext
    (check : Factor → JointMatrixOpening.Data F Digest Response leftCount b height queries → Bool)
    (next : Factor → Memory → SampleData F Response leftCount b height queries →
      OracleComp (SharedSequence.Shared Cfg Input Digest) ((Columns F Digest leftCount b height × Memory) × Bool))
    (factor : Factor) (memory : Memory) (sample : SampleData F Response leftCount b height queries) :=
  (fun result => (result.1, result.2 && check factor (sample, result.1.1))) <$> next factor memory sample

omit [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest] in
/-- Checking native response data is exactly enforcement at the step boundary;
the equality preserves the oracle program, including all worker calls. -/
theorem checked_step_eq [SampleableType (TestMatrix F leftCount b)]
    [SampleableType (Fin queries → Fin (2 ^ height))]
    (check : Factor → JointMatrixOpening.Data F Digest Response leftCount b height queries → Bool)
    (respond : Factor → Memory → TestMatrix F leftCount b →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Response)
    (next : Factor → Memory → SampleData F Response leftCount b height queries →
      OracleComp (SharedSequence.Shared Cfg Input Digest) ((Columns F Digest leftCount b height × Memory) × Bool))
    (factor : Factor) (memory : Memory) :
    step respond (checkedNext check next) factor memory =
      ShortCircuitSequence.enforce check (step respond next) factor memory := by
  simp only [step, checkedNext, ShortCircuitSequence.enforce, InteractiveSampling.complete,
    map_bind, map_pure, bind_map_left]

omit [Field F] [DecidableEq F] in
/-- Expose the real sampled prefix and native column-phase execution of a
supported step. The returned flag is the actual column-phase flag. -/
theorem step_supported [SampleableType (TestMatrix F leftCount b)]
    [SampleableType (Fin queries → Fin (2 ^ height))]
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (shape : Cfg → Skeleton)
    (respond : Factor → Memory → TestMatrix F leftCount b →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Response)
    (next : Factor → Memory → SampleData F Response leftCount b height queries →
      OracleComp (SharedSequence.Shared Cfg Input Digest) ((Columns F Digest leftCount b height × Memory) × Bool))
    (factor : Factor) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : ShortCircuitSequence.StepResult (JointMatrixOpening.Data F Digest Response leftCount b height queries) Memory ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (step respond next factor memory)).run before)) :
    ∃ earlier ∈ support ((simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (InteractiveSampling.program ($ᵗ (TestMatrix F leftCount b)) (respond factor memory)
          ($ᵗ (Fin queries → Fin (2 ^ height))))).run before),
      ∃ later ∈ support ((simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (next factor memory earlier.1)).run earlier.2),
        outcome = (⟨(earlier.1, later.1.1.1), later.1.1.2, later.1.2⟩, later.2) := by
  rw [step, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨packet, packetSupported, equal⟩ := supported
  have parts := (SharedContinuation.support_program enc dummy shape
    (InteractiveSampling.program ($ᵗ (TestMatrix F leftCount b)) (respond factor memory)
      ($ᵗ (Fin queries → Fin (2 ^ height)))) (next factor memory) before packet).mp packetSupported
  obtain ⟨earlier, earlierSupported, later, laterSupported, packetEqual⟩ := parts
  subst packet
  exact ⟨earlier, earlierSupported, later, laterSupported, equal.symm⟩

variable {K : Type} [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq K]

variable [SampleableType (TestMatrix F leftCount b)]
  [SampleableType (Fin queries → Fin (2 ^ height))]
  [SampleableType ((Fin leftCount × Fin b) → K)]

/-- Each arithmetic loss is uniform over the actual incoming private memory
and shared cache. Row-span samplers are internal proof devices. -/
theorem step_arithmetic_bound [NeZero m] [NeZero b]
    (basis : Module.Basis (Fin b) F K)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (domain : Fin (2 ^ height) ↪ F) (enough : m ≤ Fintype.card (Fin (2 ^ height)))
    (capacity : size ≤ m * b) (radius : ℕ)
    (source : Fin (2 ^ height) → (Fin leftCount × Fin b) → Fin b → F)
    (left : Factor → Fin leftCount → Matrix (Fin b) (Fin b) F)
    (right : Factor → Fin size → Matrix (Fin b) (Fin b) F)
    (respond : Factor → Memory → TestMatrix F leftCount b →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Response)
    (next : Factor → Memory → SampleData F Response leftCount b height queries →
      OracleComp (SharedSequence.Shared Cfg Input Digest) ((Columns F Digest leftCount b height × Memory) × Bool))
    (testResponse structuredResponse : Factor → TestMatrix F leftCount b → Response → Fin b → Fin size → F)
    (factor : Factor) (memory : Memory)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      enc dummy (fun _ : Cfg => Skeleton.perfect height)) (step respond next factor memory)).run state}[
        SharedMatrixSampling.ArithmeticBad domain capacity radius source (left factor) (right factor)
          (testResponse factor) (structuredResponse factor) outcome.1.result.1] ≤
      JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) domain radius := by
  classical
  let : Fintype (Matrix.rowSpan (BaseMatrixProximity.stack basis source)) := Fintype.ofFinite _
  let : SampleableType (Matrix.rowSpan (BaseMatrixProximity.stack basis source)) := SampleableType.ofFintype _
  let : Fintype (RowSpanSampling.toSpan (BaseMatrixProximity.stack basis source)).toAddMonoidHom.ker :=
    Fintype.ofFinite _
  let : SampleableType (RowSpanSampling.toSpan (BaseMatrixProximity.stack basis source)).toAddMonoidHom.ker :=
    SampleableType.ofFintype _
  rw [step, simulateQ_map, StateT.run_map, prEvent_map]
  exact SharedMatrixSampling.arithmetic_after_bound basis domain enough capacity radius source
    (left factor) (right factor) enc dummy (fun _ : Cfg => Skeleton.perfect height)
    (respond factor memory) (testResponse factor) (structuredResponse factor) (next factor memory) state small

/-- Joint arithmetic error is independent of source availability and incoming
hash safety. This is the interface averaged over a multi-root commitment prefix. -/
theorem arithmetic_union_bound [NeZero m] [NeZero b]
    (basis : Module.Basis (Fin b) F K)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (domain : Fin (2 ^ height) ↪ F) (enough : m ≤ Fintype.card (Fin (2 ^ height)))
    (capacity : size ≤ m * b) (radius : ℕ)
    (source : Factor → Fin (2 ^ height) → (Fin leftCount × Fin b) → Fin b → F)
    (left : Factor → Fin leftCount → Matrix (Fin b) (Fin b) F)
    (right : Factor → Fin size → Matrix (Fin b) (Fin b) F)
    (respond : Factor → Memory → TestMatrix F leftCount b →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Response)
    (next : Factor → Memory → SampleData F Response leftCount b height queries →
      OracleComp (SharedSequence.Shared Cfg Input Digest) ((Columns F Digest leftCount b height × Memory) × Bool))
    (testResponse structuredResponse : Factor → TestMatrix F leftCount b → Response → Fin b → Fin size → F)
    (indices : List Factor) (memory : Memory)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      enc dummy (fun _ : Cfg => Skeleton.perfect height))
      (ShortCircuitSequence.program (step respond next) indices memory)).run state}[
        SharedSequence.AnyBad (fun factor data => SharedMatrixSampling.ArithmeticBad domain capacity radius
          (source factor) (left factor) (right factor) (testResponse factor) (structuredResponse factor) data.1)
          outcome.1.results] ≤
      (indices.map (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) domain radius)).sum :=
  ShortCircuitSequence.arithmetic_union_bound enc dummy (fun _ : Cfg => Skeleton.perfect height)
    (step respond next) _ _ indices (fun factor _ incoming initial =>
      step_arithmetic_bound basis enc dummy domain enough capacity radius (source factor) left right
        respond next testResponse structuredResponse factor incoming initial small) memory state

end

end FormalProof4FHE.HasteBoots.StoppingJointMatrixOpening
