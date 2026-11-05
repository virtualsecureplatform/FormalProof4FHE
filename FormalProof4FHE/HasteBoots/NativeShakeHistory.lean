module

public import FormalProof4FHE.HasteBoots.NativeLazyProgram
public import FormalProof4FHE.HasteBoots.NativeShakeKernel

@[expose] public section

/-! Exact byte-cache reconstruction from retained native observations.
No response, prior exposure or cache write is discarded. These support laws
are operational invariants, not yet a whole-program distribution theorem. -/
namespace FormalProof4FHE.HasteBoots.NativeShakeHistory

open InputIndexedOracle (Byte Input)
open NativeShakeCache (Cache Key)
open NativeTranscript (Observation)
open OracleSpec OracleComp

noncomputable section

def writeBytes (cache : Cache) (input : Input) (offset : ℕ) : Input → Cache
  | [] => cache
  | value::rest => writeBytes (Function.update cache (input,offset) (some value)) input (offset+1) rest

def record (cache : Cache) : Observation → Cache
  | .output input offset values => writeBytes cache input offset values
  | _ => cache

/-- The installed byte is exactly the returned answer, including cache hits. -/
theorem byte_records {Cfg : Type} (cache : Cache) (key : Key) (result : Byte × Cache)
    (possible : result ∈ support ((NativeShakeCache.byte (Cfg := Cfg) key).run cache)) :
    result.2 = Function.update cache key (some result.1) := by
  cases known : cache key with
  | some value =>
    rw [NativeShakeCache.byte_cached cache key value known] at possible
    have same := eq_of_mem_support_pure _ possible
    subst result
    funext other
    by_cases same : other = key
    · subst other
      simp [known]
    · simp [Function.update_of_ne same]
  | none =>
    rw [NativeShakeCache.byte_fresh cache key known,support_map,Set.mem_image] at possible
    obtain ⟨value,_,rfl⟩ := possible
    rfl

/-- A whole read writes precisely its returned interval and no other byte. -/
theorem read_records {Cfg : Type} (input : Input) (offset count : ℕ) (cache : Cache)
    (result : Input × Cache)
    (possible : result ∈ support ((NativeShakeCache.read (Cfg := Cfg) input offset count).run cache)) :
    result.2 = writeBytes cache input offset result.1 := by
  induction count generalizing offset cache result with
  | zero =>
    have same := eq_of_mem_support_pure _ possible
    subst result
    rfl
  | succ count ih =>
    rw [NativeShakeCache.read,StateT.run_bind,mem_support_bind_iff] at possible
    obtain ⟨first,queried,tail⟩ := possible
    rw [StateT.run_bind,mem_support_bind_iff] at tail
    obtain ⟨rest,readRest,returned⟩ := tail
    have same := eq_of_mem_support_pure _ returned
    subst result
    have final := ih (offset+1) first.2 rest readRest
    change rest.2 = writeBytes _ _ _ _
    rw [writeBytes,← byte_records cache (input,offset) first queried]
    exact final

/-- The complete byte-cache effect is a fold of the full ordered native log. -/
theorem compile_records {Cfg A : Type} (program : OracleProgram.Program A) (cache : Cache)
    (result : (A × List Observation) × Cache)
    (possible : result ∈ support ((NativeLazyProgram.compile (Cfg := Cfg) program).run cache)) :
    result.2 = result.1.2.foldl record cache := by
  induction program generalizing cache result with
  | pure value =>
    have same := eq_of_mem_support_pure _ possible
    subst result
    rfl
  | start input tail ih =>
    rw [NativeLazyProgram.compile,StateT.run_map,support_map,Set.mem_image] at possible
    obtain ⟨rest,read,rfl⟩ := possible
    simpa only [NativeCheckpointProgram.prepend,List.foldl_cons,record] using ih cache rest read
  | read input offset count tail ih =>
    rw [NativeLazyProgram.compile,StateT.run_bind,mem_support_bind_iff] at possible
    obtain ⟨block,queried,rest⟩ := possible
    rw [StateT.run_map,support_map,Set.mem_image] at rest
    obtain ⟨output,read,rfl⟩ := rest
    have written := read_records input offset count cache block queried
    simpa only [NativeCheckpointProgram.prepend,List.foldl_cons,record,← written] using
      ih block.1 block.2 output read
  | hash input tail ih =>
    rw [NativeLazyProgram.compile,StateT.run_bind,StateT.run_liftM,support_bind] at possible
    simp only [Set.mem_iUnion] at possible
    obtain ⟨answer,queried,rest⟩ := possible
    rw [bind_pure_comp,support_map,Set.mem_image] at queried
    obtain ⟨digest,_,rfl⟩ := queried
    rw [StateT.run_map,support_map,Set.mem_image] at rest
    obtain ⟨output,read,rfl⟩ := rest
    simpa only [NativeCheckpointProgram.prepend,List.foldl_cons,record] using
      ih digest cache output read


/-- Any typed oracle implementation can only remove possible outcomes, so
cache reconstruction also holds after the actual shared handler runs. -/
theorem simulated_records {Cfg A S : Type}
    (impl : QueryImpl (CheckpointExecution.Spec unifSpec Cfg Input NativeRootMessage.Digest) (StateT S ProbComp))
    (program : OracleProgram.Program A) (cache : Cache) (state : S)
    (result : ((A × List Observation) × Cache) × S)
    (possible : result ∈ support ((simulateQ impl ((NativeLazyProgram.compile program).run cache)).run state)) :
    result.1.2 = result.1.1.2.foldl record cache := by
  have projected : result.1 ∈ support
      ((simulateQ impl ((NativeLazyProgram.compile program).run cache)).run' state) := by
    rw [StateT.run'_eq,support_map,Set.mem_image]
    exact ⟨result,possible,rfl⟩
  exact compile_records program cache result.1
    (support_simulateQ_run'_subset impl _ state projected)

end
end FormalProof4FHE.HasteBoots.NativeShakeHistory
