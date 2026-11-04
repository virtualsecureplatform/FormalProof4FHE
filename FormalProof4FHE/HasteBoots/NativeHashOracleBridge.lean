module

public import FormalProof4FHE.HasteBoots.OracleProgram
public import FormalProof4FHE.HasteBoots.NativeRootMessage
public import FormalProof4FHE.HasteBoots.JointHashCache
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial

@[expose] public section

/-! Compile hash-only VCVio checks into the same mixed-oracle program used
by the native transcript. Every call, including cached repeats, is retained.
This is a computation bridge, not an authentication/security premise. -/
namespace FormalProof4FHE.HasteBoots.NativeHashOracleBridge

open InputIndexedOracle (Input World sha512)
open NativeRootMessage (Digest)
open NativeTranscript (Execution Observation)
open OracleSpec OracleComp

def compile {A : Type} : OracleComp (Input →ₒ Digest) A → OracleProgram.Program A
  | .pure value => .pure value
  | .queryBind input next => .hash input (fun digest => compile (next digest))

def implementation (world : World) : QueryImpl (Input →ₒ Digest) Execution := fun input => ObservationReplay.hash world input

theorem compile_pure {A : Type} (value : A) : compile (pure value) = .pure value := rfl

theorem compile_hash (input : Input) :
    compile (liftM ((Input →ₒ Digest).query input) : OracleComp (Input →ₒ Digest) Digest) =
      .hash input (fun answer => .pure answer) := rfl

theorem compile_query {A : Type} (input : Input) (next : Digest → OracleComp (Input →ₒ Digest) A) :
    compile ((liftM ((Input →ₒ Digest).query input) : OracleComp (Input →ₒ Digest) Digest) >>= next) =
      .hash input (fun answer => compile (next answer)) := rfl

theorem compile_bind {A B : Type} (program : OracleComp (Input →ₒ Digest) A) (next : A → OracleComp (Input →ₒ Digest) B) :
    compile (program >>= next) = OracleProgram.bind (compile program) (fun value => compile (next value)) := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input tail ih =>
    change OracleProgram.Program.hash input (fun answer => compile (tail answer >>= next)) =
      OracleProgram.Program.hash input (fun answer => OracleProgram.bind (compile (tail answer)) (fun value => compile (next value)))
    simp only [ih]

theorem run_compile {A : Type} (program : OracleComp (Input →ₒ Digest) A) (world : World) :
    OracleProgram.run (compile program) world = simulateQ (implementation world) program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
    simp only [compile_query,OracleProgram.run,simulateQ_bind,simulateQ_spec_query,implementation,ih]

/-- Knowing every actual hash query suffices to replay the original VCVio
checker, with no substituted acceptance flag. -/
theorem replay_of_known {A : Type} (program : OracleComp (Input →ₒ Digest) A) (world : World)
    (cache : (Input →ₒ Digest).QueryCache)
    (known : ∀ input digest, Observation.hash input (List.ofFn digest) ∈
      (simulateQ (implementation world) program).run.2 → cache input = some digest) :
    simulateQ cache.toPartialImpl program = some (simulateQ (implementation world) program).run.1 := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
    have first : cache input = some (sha512 world input) := known input _ (by
      simp only [simulateQ_bind,simulateQ_spec_query,implementation,ObservationReplay.hash,ObservationReplay.run_bind,
        WriterT.run_mk,List.singleton_append,List.mem_cons_self])
    rw [simulateQ_bind,simulateQ_spec_query,QueryCache.toPartialImpl_apply,first]
    change simulateQ cache.toPartialImpl (next (sha512 world input)) = _
    have remaining := ih (sha512 world input) (by
      intro query answer member
      apply known query answer
      simp only [simulateQ_bind,simulateQ_spec_query,implementation,ObservationReplay.hash,ObservationReplay.run_bind,
        WriterT.run_mk,List.singleton_append]
      exact List.mem_cons_of_mem _ member)
    simpa only [simulateQ_bind,simulateQ_spec_query,implementation,ObservationReplay.hash,ObservationReplay.run_bind,WriterT.run_mk,Option.bind_some] using remaining

theorem truthful {A : Type} (program : OracleComp (Input →ₒ Digest) A) (world : World) :
    ObservationReplay.Agrees world (simulateQ (implementation world) program).run.2 := by
  induction program using OracleComp.inductionOn with
  | pure value => intro entry member; cases member
  | query_bind input next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,implementation,ObservationReplay.hash,ObservationReplay.run_bind,WriterT.run_mk]
    intro entry member
    rcases List.mem_cons.mp member with same | member
    · subst entry; rfl
    · exact ih (sha512 world input) entry member

/-- Every actual hash observation is present with its actual response in
its projected common cache, including observations with repeated keys. -/
theorem cache_known (world : World) (log : List Observation) (truthful : ObservationReplay.Agrees world log)
    (input : Input) (digest : Digest) (member : Observation.hash input (List.ofFn digest) ∈ log) :
    (JointHashCache.project log).cache input = some digest := by
  have valid := JointHashCache.project_valid world log truthful
  have key : input ∈ (JointHashCache.project log).keys := by
    rw [JointHashCache.project_keys]
    exact List.mem_toFinset.mpr ((JointHashCache.mem_hashInputs log input).mpr ⟨List.ofFn digest,member⟩)
  obtain ⟨answer,found⟩ := valid.1.mem_keys_iff input |>.mp key
  have same := List.ofFn_injective (truthful _ member)
  exact found.trans (congrArg some ((valid.2 input answer found).trans same))

theorem replay_actual {A : Type} (program : OracleComp (Input →ₒ Digest) A) (world : World)
    (earlier : List Observation) (past : ObservationReplay.Agrees world earlier) :
    simulateQ (JointHashCache.project (earlier ++ (simulateQ (implementation world) program).run.2)).cache.toPartialImpl program =
      some (simulateQ (implementation world) program).run.1 := by
  apply replay_of_known
  intro input digest member
  exact cache_known world _ ((ObservationReplay.agrees_append world _ _).mpr ⟨past,truthful program world⟩)
    input digest (List.mem_append_right earlier member)

end FormalProof4FHE.HasteBoots.NativeHashOracleBridge
