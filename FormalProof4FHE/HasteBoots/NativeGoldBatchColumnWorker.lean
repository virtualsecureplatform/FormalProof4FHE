module

public import FormalProof4FHE.HasteBoots.NativeGoldColumnWorker
@[expose] public section

/-! Raw native batch column workers authenticate each original payload/path
once, then check the shared random test and every grouped structured response
in native lane/coordinate order. Replay uses the common raw hash cache.
Native Rayon/compiler refinement, physical cost and availability remain open. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchColumnWorker
open InputIndexedOracle (Input)
open NativeRootMessage (Digest)
open NativeFieldRepresentation (GoldWord)
open NativeGoldColumnAuthentication (Column encoding decodePath)
open NativeBrakedownParameters (Geometry)
open NativeGoldColumnChecks (dot equal)
open OracleSpec OracleComp
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

abbrev Response := List GoldWord × List GoldWord

/-- Native test-first loop: one shared test, then every grouped response at the same coordinate. -/
def coordinate (geometry : Geometry) (random test values : List GoldWord) (groups : List Response)
    (index lane component : ℕ) : Bool :=
  let address := lane*geometry.stride+index*geometry.blockWidth+component
  equal (dot geometry.rows geometry.blockWidth random values lane component) (test[address]?.getD 0) &&
    groups.all (fun response => equal (dot geometry.rows geometry.blockWidth response.1 values lane component) (response.2[address]?.getD 0))

def check (geometry : Geometry) (width : ℕ) (random test values : List GoldWord) (groups : List Response) (index : ℕ) : Bool :=
  (List.range width).all (fun lane => (List.range geometry.blockWidth).all
    (fun component => coordinate geometry random test values groups index lane component))

theorem check_each (geometry : Geometry) (width : ℕ) (random test values : List GoldWord) (groups : List Response) (index : ℕ)
    (accepted : check geometry width random test values groups index = true) (response : Response) (member : response ∈ groups) :
    NativeGoldColumnChecks.check geometry width random response.1 test response.2 values index = true := by
  simp only [check,List.all_eq_true] at accepted
  simp only [NativeGoldColumnChecks.check,List.all_eq_true]
  intro lane laneMem component componentMem
  have one := Bool.and_eq_true_iff.mp (accepted lane laneMem component componentMem)
  exact Bool.and_eq_true_iff.mpr ⟨one.1,(List.all_eq_true.mp one.2) response member⟩

def worker (geometry : Geometry) (width : ℕ) (random test : List GoldWord) (groups : List Response)
    (root : Digest) (index : ℕ) (column : Column) : OracleComp (Input →ₒ Digest) Bool :=
  NativeGoldColumnWorker.authentication geometry.height index root column >>= fun accepted =>
    if accepted then pure (check geometry width random test column.values.val groups index) else pure false

/-- Exactly one raw authentication computation precedes the pure grouped coordinate loop. -/
theorem worker_compile (geometry : Geometry) (width : ℕ) (random test : List GoldWord) (groups : List Response)
    (root : Digest) (index : ℕ) (column : Column) :
    NativeHashOracleBridge.compile (worker geometry width random test groups root index column) =
      OracleProgram.bind (NativeGoldColumnAuthentication.verify geometry.height index root column)
        (fun accepted => .pure (if accepted then check geometry width random test column.values.val groups index else false)) := by
  rw [worker,NativeHashOracleBridge.compile_bind,NativeGoldColumnWorker.authentication_compile]
  congr 1
  funext accepted
  cases accepted <;> rfl

theorem worker_accepts (geometry : Geometry) (width : ℕ) (random test : List GoldWord) (groups : List Response)
    (root : Digest) (index : ℕ) (column : Column) (cache : (Input →ₒ Digest).QueryCache)
    (accepted : simulateQ cache.toPartialImpl (worker geometry width random test groups root index column) = some true) :
    simulateQ cache.toPartialImpl (NativeGoldColumnWorker.authentication geometry.height index root column) = some true ∧
      check geometry width random test column.values.val groups index = true := by
  rw [worker,simulateQ_bind] at accepted
  obtain ⟨flag,read,rest⟩ := Option.bind_eq_some_iff.mp accepted
  cases flag with
  | false => simp only [Bool.false_eq_true,reduceIte,simulateQ_pure] at rest; contradiction
  | true => exact ⟨read,Option.some.inj rest⟩

/-- Accepted replay authenticates the original raw row once and checks every actual group. -/
theorem worker_raw_replay (geometry : Geometry) (width : ℕ) (random test : List GoldWord) (groups : List Response)
    (root : Digest) (index : ℕ) (column : Column) (cache : (Input →ₒ Digest).QueryCache)
    (accepted : simulateQ cache.toPartialImpl (worker geometry width random test groups root index column) = some true) :
    ∃ leaf siblings, decodePath geometry.height column.path.val = some (leaf,siblings) ∧
      column.path.val = leaf :: siblings.toList ∧
      simulateQ cache.toPartialImpl (NativeMerkleVerifier.verifyPayload encoding geometry.height index column.values leaf root siblings) = some true ∧
      check geometry width random test column.values.val groups index = true ∧
      ∀ response ∈ groups, NativeGoldColumnChecks.check geometry width random response.1 test response.2 column.values.val index = true := by
  have facts := worker_accepts geometry width random test groups root index column cache accepted
  cases parsed : decodePath geometry.height column.path.val with
  | none =>
    have impossible : (some false : Option Bool) = some true := by
      simpa only [NativeGoldColumnWorker.authentication,parsed,simulateQ_pure,Option.pure_def] using facts.1
    cases impossible
  | some pair =>
    obtain ⟨leaf,siblings⟩ := pair
    refine ⟨leaf,siblings,rfl,NativeGoldColumnAuthentication.decodePath_spec _ _ _ _ parsed,?_,facts.2,?_⟩
    · simpa only [NativeGoldColumnWorker.authentication,parsed] using facts.1
    · exact check_each geometry width random test column.values.val groups index facts.2

noncomputable section

def workers (geometry : Geometry) (width : ℕ) (random test : List GoldWord) (groups : List Response)
    (root : Digest) (jobs : List NativeGoldColumnWorker.Job) : HashWorkerPool.Workers Input Digest jobs.length :=
  fun index => worker geometry width random test groups root (jobs.get index).index (jobs.get index).column
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchColumnWorker
