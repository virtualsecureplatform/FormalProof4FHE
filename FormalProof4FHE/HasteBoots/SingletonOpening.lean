module

public import FormalProof4FHE.HasteBoots.NativeBatchVerifier
public import FormalProof4FHE.HasteBoots.NativeColumnWorkerPool

@[expose] public section

/-!
# Exact single-opening execution through the one-claim batch interface

One structured response, a per-root binding prelude, one test and column draw,
exact column attachment before workers, and the actual single-column pool.
Theorems below identify this program with the one-claim batch program. This
is an equality of oracle computations, including all rejected-path hashes;
no independent resampling or batch-security assumption is introduced.
Raw proof-shape preflight, native scheduling and Rust refinement remain open.
-/

open OracleSpec OracleComp BinaryTree Matrix
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim

namespace FormalProof4FHE.HasteBoots.SingletonOpening

noncomputable section

structure Protocol (F Input Digest Cfg Response Memory : Type)
    (b front suffix m queries height : ℕ) where
  encoding : MerkleOracle.Encoding Input Digest (List F)
  domain : Fin (2 ^ height) ↪ F
  root : Digest
  query : Query F b (front + suffix)
  value : Fin b → F
  testResponse : TestMatrix F (2 ^ front) b → Response → Fin b → Fin (2 ^ suffix) → F
  structuredResponse : TestMatrix F (2 ^ front) b → Response → Fin b → Fin (2 ^ suffix) → F
  prepare : Memory → OracleComp (SharedSequence.Shared Cfg Input Digest) Memory
  respond : Memory → TestMatrix F (2 ^ front) b → OracleComp (SharedSequence.Shared Cfg Input Digest) Response
  receiveColumns : Memory → SampleData F Response (2 ^ front) b height queries →
    OracleComp (SharedSequence.Shared Cfg Input Digest) (Columns F Digest (2 ^ front) b height × Memory)
  choose : Memory → (sample : SampleData F Response (2 ^ front) b height queries) →
    (columns : Columns F Digest (2 ^ front) b height) → HashWorkerPool.Workers Input Digest columns.length → Memory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (Option (Fin columns.length) × Memory)
  fuel : Memory → SampleData F Response (2 ^ front) b height queries → Columns F Digest (2 ^ front) b height → ℕ

variable {F Input Digest Cfg Response Memory : Type} [Field F] [DecidableEq F]
  [DecidableEq Input] [DecidableEq Digest] {b front suffix m queries height : ℕ}

def toBatch (p : Protocol F Input Digest Cfg Response Memory b front suffix m queries height) :
    NativeBatchVerifier.Protocol F Input Digest Cfg Response Memory b front suffix 1 m queries height where
  encoding := p.encoding
  domain := p.domain
  root := p.root
  query := fun _ => p.query
  values := fun _ => p.value
  testResponse := p.testResponse
  groupResponse := fun _ => p.structuredResponse
  prepare := p.prepare
  respond := p.respond
  receiveColumns := p.receiveColumns
  choose := p.choose
  fuel := p.fuel

omit [Field F] [DecidableEq Input] [DecidableEq Digest] in
theorem groupCount (query : Query F b (front + suffix)) :
    BatchQueryLayout.groupCount (front := front) (suffix := suffix) (fun _ : Fin 1 => query) = 1 := by
  simp [BatchQueryLayout.groupCount, BatchQueryLayout.keys, List.ofFn_succ,
    BatchGrouping.compute, BatchGrouping.run, BatchGrouping.step]

omit [DecidableEq Input] [DecidableEq Digest] in
theorem coordinates {width rows block groups : ℕ} [NeZero groups]
    (columns : List (NativeColumnLayout.Column F Digest height rows block))
    (testWeights structuredWeights : Fin (width * rows) → F)
    (testResponse structuredResponse : Fin (width * ((2 ^ height) * block)) → F) :
    BatchColumnChecks.allCoordinates columns testWeights (fun _ : Fin groups => structuredWeights)
      testResponse (fun _ => structuredResponse) =
      NativeColumnLayout.allCoordinates columns testWeights structuredWeights testResponse structuredResponse := by
  apply Bool.eq_iff_iff.mpr
  rw [BatchColumnChecks.allCoordinates_iff, NativeColumnLayout.allCoordinates_eq_true_iff]
  simp only [forall_const]

omit [DecidableEq Input] in
theorem worker {width leftCount block groups : ℕ} [NeZero groups]
    (enc : MerkleOracle.Encoding Input Digest (List F)) (root : Digest)
    (testWeights structuredWeights : Fin (width * (leftCount * width)) → F)
    (testResponse structuredResponse : Fin (width * ((2 ^ height) * block)) → F)
    (column : NativeColumnLayout.Column F Digest height (leftCount * width) block) :
    NativeBatchColumnWorkerPool.worker enc root testWeights (fun _ : Fin groups => structuredWeights)
      testResponse (fun _ => structuredResponse) column =
      NativeColumnWorkerPool.worker enc root testWeights structuredWeights testResponse structuredResponse column := by
  simp only [NativeBatchColumnWorkerPool.worker, NativeColumnWorkerPool.worker, coordinates]

omit [DecidableEq Input] in
theorem pool {width leftCount block groups : ℕ} [NeZero groups]
    (enc : MerkleOracle.Encoding Input Digest (List F)) (root : Digest)
    (testWeights structuredWeights : Fin (width * (leftCount * width)) → F)
    (testResponse structuredResponse : Fin (width * ((2 ^ height) * block)) → F)
    (columns : List (NativeColumnLayout.Column F Digest height (leftCount * width) block))
    (choose : HashWorkerPool.Workers Input Digest columns.length → Memory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (Option (Fin columns.length) × Memory))
    (fuel : ℕ) (memory : Memory) :
    NativeBatchColumnWorkerPool.program enc root testWeights (fun _ : Fin groups => structuredWeights)
      testResponse (fun _ => structuredResponse) columns choose fuel memory =
      NativeColumnWorkerPool.program enc root testWeights structuredWeights testResponse structuredResponse columns choose fuel memory := by
  have same : NativeBatchColumnWorkerPool.workers enc root testWeights (fun _ : Fin groups => structuredWeights)
      testResponse (fun _ => structuredResponse) columns =
      NativeColumnWorkerPool.workers enc root testWeights structuredWeights testResponse structuredResponse columns := by
    funext index
    exact worker enc root testWeights structuredWeights testResponse structuredResponse _
  simp only [NativeBatchColumnWorkerPool.program, NativeColumnWorkerPool.program, same]

def next (p : Protocol F Input Digest Cfg Response Memory b front suffix m queries height)
    (incoming : Memory) (sample : SampleData F Response (2 ^ front) b height queries) := do
  let received ← p.receiveColumns incoming sample
  if NativeBatchChecks.columnsCheck received.1 sample.2 then
    NativeColumnWorkerPool.program p.encoding p.root
      (NativeColumnLayout.flattenWeights sample.1.1)
      (NativeColumnLayout.flattenWeights (MatrixResponse.weights
        (SubclaimSourceLayout.leftWeights (front := front) (suffix := suffix) p.query)))
      (NativeColumnLayout.flattenResponse (MatrixOpeningSecurity.encodeMessages (m := m) p.domain
        (p.testResponse sample.1.1 sample.1.2)))
      (NativeColumnLayout.flattenResponse (MatrixOpeningSecurity.encodeMessages (m := m) p.domain
        (p.structuredResponse sample.1.1 sample.1.2)))
      received.1 (p.choose incoming sample received.1) (p.fuel incoming sample received.1) received.2
  else pure ((received.1, received.2), false)

def checks (p : Protocol F Input Digest Cfg Response Memory b front suffix m queries height) :
    JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries → Bool :=
  NativeFactorChecks.check (m := m) p.domain
    (SubclaimSourceLayout.leftWeights (front := front) (suffix := suffix) p.query)
    (SubclaimSourceLayout.rightWeights (front := front) (suffix := suffix) p.query)
    p.value p.testResponse p.structuredResponse

omit [DecidableEq Input] in
theorem next_eq (p : Protocol F Input Digest Cfg Response Memory b front suffix m queries height)
    (incoming : Memory) (sample : SampleData F Response (2 ^ front) b height queries) :
    NativeBatchVerifier.next (toBatch p) incoming sample = next p incoming sample := by
  have : NeZero (BatchQueryLayout.groupCount (front := front) (suffix := suffix) (fun _ : Fin 1 => p.query)) :=
    ⟨by rw [groupCount]; decide⟩
  simp only [NativeBatchVerifier.next, toBatch, NativeBatchChecks.groupLeft, NativeBatchChecks.left, next, pool]

omit [DecidableEq Input] [DecidableEq Digest] in
theorem checks_eq (p : Protocol F Input Digest Cfg Response Memory b front suffix m queries height)
    (data : JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries) :
    NativeBatchVerifier.checks (toBatch p) data = checks p data := by
  have : NeZero (BatchQueryLayout.groupCount (front := front) (suffix := suffix) (fun _ : Fin 1 => p.query)) :=
    ⟨by rw [groupCount]; decide⟩
  simp only [NativeBatchVerifier.checks, toBatch, NativeBatchChecks.check, NativeBatchChecks.coordinates,
    NativeBatchChecks.groupLeft, NativeBatchChecks.left, NativeBatchChecks.right, NativeBatchChecks.structured,
    coordinates, List.ofFn_succ, List.ofFn_zero, List.all_cons, List.all_nil, Bool.and_true, checks,
    NativeFactorChecks.check, id_eq]
  rfl

variable [SampleableType (TestMatrix F (2 ^ front) b)] [SampleableType (Fin queries → Fin (2 ^ height))]

def sampledStep (p : Protocol F Input Digest Cfg Response Memory b front suffix m queries height) (memory : Memory) :=
  StoppingJointMatrixOpening.step (fun _ : Unit => p.respond)
    (StoppingJointMatrixOpening.checkedNext (fun _ : Unit => checks p) (fun _ : Unit => next p)) () memory

def step (p : Protocol F Input Digest Cfg Response Memory b front suffix m queries height) (memory : Memory) := do
  let prepared ← p.prepare memory
  sampledStep p prepared

omit [DecidableEq Input] in
/-- Exact transition equality, including binding, rejection and worker work. -/
theorem step_eq (p : Protocol F Input Digest Cfg Response Memory b front suffix m queries height) (memory : Memory) :
    NativeBatchVerifier.step (toBatch p) memory = step p memory := by
  have checked : NativeBatchVerifier.checks (toBatch p) = checks p := funext (checks_eq p)
  have continuation : NativeBatchVerifier.next (toBatch p) = next p := funext (fun memory => funext (next_eq p memory))
  unfold NativeBatchVerifier.step step
  congr 1
  funext prepared
  unfold NativeBatchVerifier.sampledStep sampledStep
  rw [checked, continuation]
  rfl

end

end FormalProof4FHE.HasteBoots.SingletonOpening
