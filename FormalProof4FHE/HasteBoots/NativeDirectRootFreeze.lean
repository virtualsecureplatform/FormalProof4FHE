module

public import FormalProof4FHE.HasteBoots.NativeRootInputView
public import FormalProof4FHE.HasteBoots.NativeLazyStateExecution
public import FormalProof4FHE.HasteBoots.RecordRoots
@[expose] public section

/-! Online checkpoint instrumentation for roots directly mentioned by native
framed inputs. Newly mentioned context/root keys are recorded before the
first nonempty raw read, without changing native queries, log or owned byte
cache after erasure. Context digests are tags; trusted shape/context identity
must be established at protocol instantiation. Parent/helper association,
receipt-linked descendants and arbitrary inherited-prelude snapshots remain
separate obligations. Earliest-exposure security requires history, owned
cache and checkpoints from the same instrumented prelude (or empty initial
state); a supplied past alone does not certify earlier registrations. -/
namespace FormalProof4FHE.HasteBoots.NativeDirectRootFreeze
open InputIndexedOracle (Input)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open OracleSpec OracleComp
open scoped Classical
noncomputable section
abbrev Spec := CheckpointExecution.Spec unifSpec Digest Input Digest

def inputRoots (input : Input) : List NativeCanonicalLookupWire.Source := (NativeRootInputView.raw input).getD []
def exposed : Observation → List NativeCanonicalLookupWire.Source
  | .output input _ values => if values = [] then [] else inputRoots input
  | _ => []
def seen (past : List Observation) : Finset NativeCanonicalLookupWire.Source := (past.flatMap exposed).toFinset

def fresh (past : List Observation) (input : Input) : List NativeCanonicalLookupWire.Source :=
  (inputRoots input).eraseDups.filter (fun key => key ∉ seen past)

/-- Instrument the actual lazy compiler, threading the complete real native history. -/
def compile {A : Type} (past : List Observation) : OracleProgram.Program A → NativeLazyProgram.Execution Digest (A × List Observation)
  | .pure value => pure (value,[])
  | .start input next => NativeCheckpointProgram.prepend (.start input) <$> compile (past++[.start input]) next
  | .read input offset count next => do
    if 0 < count then
      let _ ← liftM (RecordRoots.program (fresh past input) : OracleComp Spec Unit)
      pure ()
    else pure ()
    let output ← NativeShakeCache.read input offset count
    NativeCheckpointProgram.prepend (.output input offset output) <$>
      compile (past++[.output input offset output]) (next output)
  | .hash input next => do
    let answer ← liftM (liftM (Spec.query (.inr (.inl input))) : OracleComp Spec Digest)
    NativeCheckpointProgram.prepend (.hash input (List.ofFn answer)) <$>
      compile (past++[.hash input (List.ofFn answer)]) (next answer)

/-- Erase only checkpoint annotations; private and hash queries remain literal queries. -/
def erase : QueryImpl Spec (OracleComp Spec) := fun query => match query with
  | .inl privateQuery => liftM (Spec.query (.inl privateQuery))
  | .inr (.inl hashQuery) => liftM (Spec.query (.inr (.inl hashQuery)))
  | .inr (.inr _) => pure ()

theorem erase_byte (key : NativeShakeCache.Key) (cache : NativeShakeCache.Cache) :
    simulateQ erase ((NativeShakeCache.byte (Cfg := Digest) key).run cache) =
      (NativeShakeCache.byte (Cfg := Digest) key).run cache := by
  cases known : cache key with
  | none =>
    rw [NativeShakeCache.byte_fresh cache key known,simulateQ_map,simulateQ_spec_query]
    rfl
  | some value => rw [NativeShakeCache.byte_cached cache key value known,simulateQ_pure]

theorem erase_read (input : Input) (offset count : ℕ) (cache : NativeShakeCache.Cache) :
    simulateQ erase ((NativeShakeCache.read (Cfg := Digest) input offset count).run cache) =
      (NativeShakeCache.read (Cfg := Digest) input offset count).run cache := by
  induction count generalizing offset cache with
  | zero => simp [NativeShakeCache.read,StateT.run_pure]
  | succ count ih =>
    simp only [NativeShakeCache.read,StateT.run_bind,simulateQ_bind,erase_byte,StateT.run_pure,simulateQ_pure,ih]

theorem erase_roots (roots : List NativeCanonicalLookupWire.Source) :
    simulateQ erase (RecordRoots.program roots) = pure () := by
  induction roots with
  | nil => rfl
  | cons root roots ih =>
    simp only [RecordRoots.program,simulateQ_bind,simulateQ_spec_query,erase,pure_bind,ih]

/-- Erasing annotations recovers the original compiled computation and owned cache exactly. -/
theorem erase_compile {A : Type} (past : List Observation) (program : OracleProgram.Program A)
    (cache : NativeShakeCache.Cache) :
    simulateQ erase ((compile past program).run cache) = (NativeLazyProgram.compile (Cfg := Digest) program).run cache := by
  induction program generalizing past cache with
  | pure value => simp [compile,NativeLazyProgram.compile,StateT.run_pure]
  | start input next ih => simp only [compile,NativeLazyProgram.compile,StateT.run_map,simulateQ_map,ih]
  | read input offset count next ih =>
    simp only [compile,NativeLazyProgram.compile,StateT.run_bind,StateT.run_map]
    split
    · simp only [StateT.run_bind,StateT.run_liftM,simulateQ_bind,simulateQ_map,StateT.run_map,
        erase_roots,simulateQ_pure,pure_bind,erase_read,ih]
    · simp only [StateT.run_bind,simulateQ_bind,StateT.run_map,simulateQ_map,erase_read,ih]
  | hash input next ih =>
    simp only [compile,NativeLazyProgram.compile,StateT.run_bind,StateT.run_liftM,simulateQ_bind,simulateQ_map,
      simulateQ_spec_query,erase,StateT.run_map,ih,simulateQ_pure]


theorem canonical_erase {A : Type} (program : OracleComp Spec A) :
    simulateQ (CheckpointExecution.canonical (Cfg := Digest) (QueryImpl.ofLift unifSpec ProbComp))
      (simulateQ erase program) =
    simulateQ (CheckpointExecution.canonical (Cfg := Digest) (QueryImpl.ofLift unifSpec ProbComp)) program := by
  apply QueryImpl.simulateQ_simulateQ_eq_of_apply _ program
  intro query
  rcases query with privateQuery | (hashQuery | request)
  · simp only [erase,simulateQ_spec_query]
  · simp only [erase,simulateQ_spec_query]
  · simp only [erase,simulateQ_pure]
    rfl

theorem canonical_compile {A : Type} (past : List Observation) (program : OracleProgram.Program A)
    (cache : NativeShakeCache.Cache) :
    simulateQ (CheckpointExecution.canonical (Cfg := Digest) (QueryImpl.ofLift unifSpec ProbComp))
      ((compile past program).run cache) =
    simulateQ (CheckpointExecution.canonical (Cfg := Digest) (QueryImpl.ofLift unifSpec ProbComp))
      ((NativeLazyProgram.compile (Cfg := Digest) program).run cache) := by
  have equal := congrArg (fun code => simulateQ
    (CheckpointExecution.canonical (Cfg := Digest) (QueryImpl.ofLift unifSpec ProbComp)) code)
      (erase_compile past program cache)
  rw [canonical_erase] at equal
  exact equal

def execute {Payload A : Type} (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (past : List Observation) (program : OracleProgram.Program A)
    (cache : NativeShakeCache.Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :=
  (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
    ((compile past program).run cache)).run state

/-- Actual handler projection preserves result/log, owned SHAKE cache and the shared hash cache. -/
theorem execute_erasure {Payload A : Type} (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (past : List Observation) (program : OracleProgram.Program A)
    (cache : NativeShakeCache.Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    Prod.map id (fun state => state.hash.cache) <$> execute enc dummy shape past program cache state =
      Prod.map id (fun state => state.hash.cache) <$>
        NativeLazyStateExecution.execute enc dummy shape program cache state := by
  unfold execute NativeLazyStateExecution.execute
  rw [CheckpointExecution.project_run,CheckpointExecution.project_run,canonical_compile]


/-- Returning a native result issues no annotation or oracle query. -/
theorem execute_pure {Payload A : Type} (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (past : List Observation) (value : A) (cache : NativeShakeCache.Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    execute enc dummy shape past (.pure value) cache state = pure (((value,[]),cache),state) := by
  simp only [execute,compile,StateT.run_pure,simulateQ_pure]

/-- A zero-length raw read retains its observation but records no root. -/
theorem execute_zero {Payload A : Type} (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (past : List Observation) (input : Input) (offset : ℕ)
    (next : Input → OracleProgram.Program A) (cache : NativeShakeCache.Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    execute enc dummy shape past (.read input offset 0 next) cache state =
      NativeLazyStateExecution.prepend (.output input offset []) <$>
        execute enc dummy shape (past++[.output input offset []]) (next []) cache state := by
  simp only [execute,compile,Nat.lt_irrefl,ite_false,StateT.run_bind,NativeShakeCache.read_zero,
    pure_bind,StateT.run_map,simulateQ_map]
  rfl

/-- Every new direct-root snapshot precedes the first byte sampled by this nonempty raw read. -/
theorem execute_read {Payload A : Type} (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (past : List Observation) (input : Input) (offset count : ℕ)
    (next : Input → OracleProgram.Program A) (cache : NativeShakeCache.Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) (positive : 0 < count) :
    execute enc dummy shape past (.read input offset count next) cache state = (do
      let first ← NativeShakeReadLaw.sample input offset count cache
      let rest ← execute enc dummy shape (past++[.output input offset first.1]) (next first.1) first.2
        (RecordRoots.state shape (fresh past input) state)
      pure (NativeLazyStateExecution.prepend (.output input offset first.1) rest)) := by
  simp only [execute,compile,positive,ite_true,StateT.run_bind,StateT.run_liftM,simulateQ_bind,simulateQ_map,
    RecordRoots.run_program,StateT.run_pure,simulateQ_pure,pure_bind,NativeShakeReadLaw.shared_read,
    StateT.run_map,bind_map_left]
  simp only [bind_pure_comp,NativeLazyStateExecution.prepend]


theorem fresh_mem (past : List Observation) (input : Input) (key : NativeCanonicalLookupWire.Source) :
    key ∈ fresh past input ↔ key ∈ inputRoots input ∧ key ∉ seen past := by
  simp [fresh]

theorem seen_append (past later : List Observation) : seen (past++later) = seen past ∪ seen later := by
  simp [seen,List.flatMap_append,List.toFinset_append]

theorem seen_output (past : List Observation) (input : Input) (offset : ℕ) (values : Input)
    (nonempty : values ≠ []) :
    seen (past++[.output input offset values]) = seen past ∪ (inputRoots input).toFinset := by
  simp [seen,exposed,nonempty]

/-- A completed nonempty read prevents the same keys being frozen again on a cloned input. -/
theorem fresh_after_output (past : List Observation) (input : Input) (offset : ℕ) (values : Input)
    (nonempty : values ≠ []) : fresh (past++[.output input offset values]) input = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro key member
  obtain ⟨present,unseen⟩ := (fresh_mem _ _ _).mp member
  exact unseen (by rw [seen_output past input offset values nonempty]; exact Finset.mem_union_right _ (List.mem_toFinset.mpr present))

/-- Composition threads the actual native history and the same owned byte cache. -/
theorem compile_bind {A B : Type} (past : List Observation) (program : OracleProgram.Program A)
    (next : A → OracleProgram.Program B) :
    compile past (OracleProgram.bind program next) = (do
      let first ← compile past program
      let second ← compile (past++first.2) (next first.1)
      pure (second.1,first.2++second.2)) := by
  induction program generalizing past with
  | pure value => simp [compile,OracleProgram.bind]
  | start input tail ih => simp [compile,OracleProgram.bind,ih,NativeCheckpointProgram.prepend,List.append_assoc]
  | read input offset count tail ih =>
    simp only [compile,OracleProgram.bind]
    split <;> simp [ih,bind_assoc,NativeCheckpointProgram.prepend,List.append_assoc]
  | hash input tail ih => simp [compile,OracleProgram.bind,ih,bind_assoc,NativeCheckpointProgram.prepend,List.append_assoc]

/-- Suspending an analysis prefix retains history, roots and the actual residual native program. -/
theorem compile_resume {A : Type} (past : List Observation) (fuel : ℕ) (program : OracleProgram.Program A) :
    compile past program = (do
      let first ← compile past (NativeProgramPrefix.take fuel program)
      let second ← compile (past++first.2) (NativeProgramPrefix.resume first.1)
      pure (second.1,first.2++second.2)) := by
  simpa only [NativeProgramPrefix.take_resume] using
    (compile_bind past (NativeProgramPrefix.take fuel program) NativeProgramPrefix.resume)

/-- Every supported continuation retains the snapshot of the actual pre-read cumulative hash log, even after monitor failure. -/
theorem read_snapshot {Payload A : Type} (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (past : List Observation) (input : Input) (offset count : ℕ)
    (next : Input → OracleProgram.Program A) (cache : NativeShakeCache.Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) (positive : 0 < count)
    (key : NativeCanonicalLookupWire.Source) (member : key ∈ fresh past input)
    (result : ((A × List Observation) × NativeShakeCache.Cache) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (possible : result ∈ support (execute enc dummy shape past (.read input offset count next) cache state)) :
    ⟨key.1,⟨key.2,state.hash.log⟩⟩ ∈ result.2.checkpoints.checkpoints := by
  rw [execute_read enc dummy shape past input offset count next cache state positive,mem_support_bind_iff] at possible
  obtain ⟨first,_,possible⟩ := possible
  rw [bind_pure_comp,support_map,Set.mem_image] at possible
  obtain ⟨rest,reached,rfl⟩ := possible
  unfold execute at reached
  exact CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape key.1
    ⟨key.2,state.hash.log⟩ ((compile (past++[Observation.output input offset first.1]) (next first.1)).run first.2)
      (RecordRoots.state shape (fresh past input) state)
        (RecordRoots.recorded shape (fresh past input) state key member) rest reached

end
end FormalProof4FHE.HasteBoots.NativeDirectRootFreeze
