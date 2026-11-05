module

public import FormalProof4FHE.HasteBoots.NativeParentLedger
public import FormalProof4FHE.HasteBoots.NativeDirectRootFreeze
@[expose] public section

/-! Online helper/source root snapshots with persistent partial-parent metadata.
The ledger reads only the old owned byte cache before a selected raw input.
Erasure preserves the exact original oracle computation and both real caches.
Initial ledgers must come from a coherent instrumented prelude, or be empty;
a supplied parent table does not authenticate lineage or prior snapshots.
Orphan/receipt coverage and trusted context/shape interpretation remain open. -/
namespace FormalProof4FHE.HasteBoots.NativeParentRootFreeze
open InputIndexedOracle (Input)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open OracleSpec OracleComp
open scoped Classical
noncomputable section
abbrev Spec := NativeDirectRootFreeze.Spec
abbrev Ledger := NativeParentLedger.State

def prepend {A : Type} (observation : Observation) (result : (A × List Observation) × Ledger) :=
  (NativeCheckpointProgram.prepend observation result.1,result.2)

def compile {A : Type} (ledger : Ledger) : OracleProgram.Program A →
    NativeLazyProgram.Execution Digest ((A × List Observation) × Ledger)
  | .pure value => pure ((value,[]),ledger)
  | .start input next => do
    let cache ← get
    prepend (.start input) <$> compile (NativeParentLedger.discover ledger cache input) next
  | .read input offset count next => do
    let cache ← get
    let plan := NativeParentLedger.prepare ledger cache input
    let after := if 0 < count then plan.next else NativeParentLedger.discover ledger cache input
    if 0 < count then
      let _ ← liftM (RecordRoots.program plan.requests : OracleComp Spec Unit)
      pure ()
    else pure ()
    let output ← NativeShakeCache.read input offset count
    prepend (.output input offset output) <$> compile after (next output)
  | .hash input next => do
    let cache ← get
    let after := NativeParentLedger.discover ledger cache input
    let answer ← liftM (liftM (Spec.query (.inr (.inl input))) : OracleComp Spec Digest)
    prepend (.hash input (List.ofFn answer)) <$> compile after (next answer)

def project {A : Type} (result : ((A × List Observation) × Ledger) × NativeShakeCache.Cache) :=
  (result.1.1,result.2)

theorem project_prepend {A : Type} (observation : Observation)
    (program : OracleComp Spec (((A × List Observation) × Ledger) × NativeShakeCache.Cache)) :
    project <$> ((fun result => (prepend observation result.1,result.2)) <$> program) =
    (fun result => (NativeCheckpointProgram.prepend observation result.1,result.2)) <$> (project <$> program) := by
  rw [Functor.map_map,Functor.map_map]
  rfl

theorem erase_compile {A : Type} (ledger : Ledger) (program : OracleProgram.Program A)
    (cache : NativeShakeCache.Cache) :
    project <$> simulateQ NativeDirectRootFreeze.erase ((compile ledger program).run cache) =
      (NativeLazyProgram.compile (Cfg := Digest) program).run cache := by
  induction program generalizing ledger cache with
  | pure value => simp [compile,NativeLazyProgram.compile,StateT.run_pure,project]
  | start input next ih =>
    simp only [compile,StateT.run_bind,StateT.run_get,pure_bind,StateT.run_map,simulateQ_map,
      NativeLazyProgram.compile]
    rw [project_prepend,ih]
  | read input offset count next ih =>
    simp only [compile,NativeLazyProgram.compile,StateT.run_bind,StateT.run_get,pure_bind]
    split <;>
      simp only [StateT.run_bind,StateT.run_liftM,StateT.run_map,simulateQ_bind,
        simulateQ_map,NativeDirectRootFreeze.erase_roots,simulateQ_pure,pure_bind,
        NativeDirectRootFreeze.erase_read,map_bind]
    all_goals
      apply bind_congr
      intro result
      rw [project_prepend,ih]
  | hash input next ih =>
    simp only [compile,NativeLazyProgram.compile,StateT.run_bind,StateT.run_get,pure_bind,
      StateT.run_liftM,simulateQ_bind,simulateQ_map,simulateQ_spec_query,NativeDirectRootFreeze.erase,
      StateT.run_map,map_bind]
    apply bind_congr
    intro answer
    rw [project_prepend,ih]

theorem canonical_compile {A : Type} (ledger : Ledger) (program : OracleProgram.Program A)
    (cache : NativeShakeCache.Cache) :
    project <$> simulateQ (CheckpointExecution.canonical (Cfg := Digest) (QueryImpl.ofLift unifSpec ProbComp))
      ((compile ledger program).run cache) =
    simulateQ (CheckpointExecution.canonical (Cfg := Digest) (QueryImpl.ofLift unifSpec ProbComp))
      ((NativeLazyProgram.compile (Cfg := Digest) program).run cache) := by
  have equal := congrArg (fun code => simulateQ
    (CheckpointExecution.canonical (Cfg := Digest) (QueryImpl.ofLift unifSpec ProbComp)) code)
      (erase_compile ledger program cache)
  rw [simulateQ_map,NativeDirectRootFreeze.canonical_erase] at equal
  exact equal

def execute {Payload A : Type} (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (ledger : Ledger) (program : OracleProgram.Program A)
    (cache : NativeShakeCache.Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :=
  (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
    ((compile ledger program).run cache)).run state

theorem execute_erasure {Payload A : Type} (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (ledger : Ledger) (program : OracleProgram.Program A)
    (cache : NativeShakeCache.Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    (fun result => (project result.1,result.2.hash.cache)) <$> execute enc dummy shape ledger program cache state =
      Prod.map id (fun state => state.hash.cache) <$>
        NativeLazyStateExecution.execute enc dummy shape program cache state := by
  have factor : (fun result => (project result.1,result.2.hash.cache)) <$> execute enc dummy shape ledger program cache state =
      Prod.map project id <$> (Prod.map id (fun state => state.hash.cache) <$>
        execute enc dummy shape ledger program cache state) := by
    rw [Functor.map_map]
    rfl
  rw [factor]
  unfold execute NativeLazyStateExecution.execute
  rw [CheckpointExecution.project_run,CheckpointExecution.project_run]
  have equal := congrArg (fun code => code.run state.hash.cache) (canonical_compile ledger program cache)
  simpa only [StateT.run_map,Prod.map_def,id_eq] using equal

theorem execute_pure {Payload A : Type} (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (ledger : Ledger) (value : A) (cache : NativeShakeCache.Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    execute enc dummy shape ledger (.pure value) cache state = pure ((((value,[]),ledger),cache),state) := by
  simp only [execute,compile,StateT.run_pure,simulateQ_pure]

def prependExecution {A : Type} {S : Type} (observation : Observation)
    (result : (((A × List Observation) × Ledger) × NativeShakeCache.Cache) × S) :=
  ((prepend observation result.1.1,result.1.2),result.2)

theorem execute_read {Payload A : Type} (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (ledger : Ledger) (input : Input) (offset count : ℕ)
    (next : Input → OracleProgram.Program A) (cache : NativeShakeCache.Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) (positive : 0 < count) :
    execute enc dummy shape ledger (.read input offset count next) cache state = (do
      let first ← NativeShakeReadLaw.sample input offset count cache
      let rest ← execute enc dummy shape (NativeParentLedger.prepare ledger cache input).next (next first.1) first.2
        (RecordRoots.state shape (NativeParentLedger.prepare ledger cache input).requests state)
      pure (prependExecution (.output input offset first.1) rest)) := by
  simp only [execute,compile,positive,ite_true,StateT.run_bind,StateT.run_get,pure_bind,
    StateT.run_liftM,simulateQ_bind,simulateQ_map,RecordRoots.run_program,StateT.run_pure,
    simulateQ_pure,NativeShakeReadLaw.shared_read,StateT.run_map,bind_map_left]
  simp only [bind_pure_comp,prependExecution]

theorem execute_zero {Payload A : Type} (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (ledger : Ledger) (input : Input) (offset : ℕ)
    (next : Input → OracleProgram.Program A) (cache : NativeShakeCache.Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    execute enc dummy shape ledger (.read input offset 0 next) cache state =
      prependExecution (.output input offset []) <$>
        execute enc dummy shape (NativeParentLedger.discover ledger cache input) (next []) cache state := by
  simp only [execute,compile,Nat.lt_irrefl,ite_false,StateT.run_bind,StateT.run_get,pure_bind,
    NativeShakeCache.read_zero,StateT.run_map,simulateQ_map]
  rfl

theorem compile_bind {A B : Type} (ledger : Ledger) (program : OracleProgram.Program A)
    (next : A → OracleProgram.Program B) :
    compile ledger (OracleProgram.bind program next) = (do
      let first ← compile ledger program
      let second ← compile first.2 (next first.1.1)
      pure ((second.1.1,first.1.2++second.1.2),second.2)) := by
  induction program generalizing ledger with
  | pure value => simp [compile,OracleProgram.bind]
  | start input tail ih => simp [compile,OracleProgram.bind,ih,prepend,NativeCheckpointProgram.prepend]
  | read input offset count tail ih =>
    by_cases positive : 0 < count <;>
      simp [compile,OracleProgram.bind,positive,ih,bind_assoc,prepend,NativeCheckpointProgram.prepend]
  | hash input tail ih => simp [compile,OracleProgram.bind,ih,bind_assoc,prepend,NativeCheckpointProgram.prepend]

theorem compile_resume {A : Type} (ledger : Ledger) (fuel : ℕ) (program : OracleProgram.Program A) :
    compile ledger program = (do
      let first ← compile ledger (NativeProgramPrefix.take fuel program)
      let second ← compile first.2 (NativeProgramPrefix.resume first.1.1)
      pure ((second.1.1,first.1.2++second.1.2),second.2)) := by
  simpa only [NativeProgramPrefix.take_resume] using
    (compile_bind ledger (NativeProgramPrefix.take fuel program) NativeProgramPrefix.resume)

theorem read_snapshot {Payload A : Type} (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (ledger : Ledger) (input : Input) (offset count : ℕ)
    (next : Input → OracleProgram.Program A) (cache : NativeShakeCache.Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) (positive : 0 < count)
    (key : NativeCanonicalLookupWire.Source) (member : key ∈ (NativeParentLedger.prepare ledger cache input).requests)
    (result : (((A × List Observation) × Ledger) × NativeShakeCache.Cache) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (possible : result ∈ support (execute enc dummy shape ledger (.read input offset count next) cache state)) :
    ⟨key.1,⟨key.2,state.hash.log⟩⟩ ∈ result.2.checkpoints.checkpoints := by
  rw [execute_read enc dummy shape ledger input offset count next cache state positive,mem_support_bind_iff] at possible
  obtain ⟨first,_,possible⟩ := possible
  rw [bind_pure_comp,support_map,Set.mem_image] at possible
  obtain ⟨rest,reached,rfl⟩ := possible
  unfold execute at reached
  exact CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape key.1
    ⟨key.2,state.hash.log⟩ ((compile (NativeParentLedger.prepare ledger cache input).next (next first.1)).run first.2)
      (RecordRoots.state shape (NativeParentLedger.prepare ledger cache input).requests state)
        (RecordRoots.recorded shape (NativeParentLedger.prepare ledger cache input).requests state key member) rest reached

/-- Actual-parent helper keys are frozen before this read, even when the seed is only partly observed. -/
theorem actual_helper_snapshot {Payload A : Type} (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (ledger : Ledger) (log : List Observation)
    (world : InputIndexedOracle.World) (input : Input) (parent : NativeParentLedger.Parent)
    (present : parent ∈ ledger.parents)
    (quoted : NativeChildSeedView.quote input = some (InputIndexedOracle.block world parent.input 0 64))
    (context root : Digest) (helper : context ∈ parent.helpers) (committed : root ∈ NativeParentLedger.roots input)
    (unseen : (context,root) ∉ ledger.frozen) (offset count : ℕ) (positive : 0 < count)
    (next : Input → OracleProgram.Program A)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (result : (((A × List Observation) × Ledger) × NativeShakeCache.Cache) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (possible : result ∈ support (execute enc dummy shape ledger (.read input offset count next)
      (NativeShakeKernel.observed log world) state)) :
    ⟨context,⟨root,state.hash.log⟩⟩ ∈ result.2.checkpoints.checkpoints :=
  read_snapshot enc dummy shape ledger input offset count next _ state positive (context,root)
    ((NativeParentLedger.prepare_mem _ _ _ _).mpr
      ⟨NativeParentLedger.resolve_actual_helper ledger log world input parent present quoted context root helper committed,unseen⟩)
    result possible

end
end FormalProof4FHE.HasteBoots.NativeParentRootFreeze
