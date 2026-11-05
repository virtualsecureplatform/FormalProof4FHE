module

public import FormalProof4FHE.HasteBoots.NativeShakeCache
public import FormalProof4FHE.HasteBoots.NativeProgramPrefix

@[expose] public section

/-! Native mixed-oracle programs with interpreter-owned SHAKE state.
Every SHA-512 request still goes through the canonical shared handler.
This compiler supplies no world or cache argument to native continuations.
Its distributional equivalence to the product-world model is a separate theorem. -/
namespace FormalProof4FHE.HasteBoots.NativeLazyProgram

open InputIndexedOracle (Input)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open OracleSpec OracleComp

abbrev Execution (Cfg A : Type) := StateT NativeShakeCache.Cache
  (OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest)) A

noncomputable section

/-- Retain every original observation, including repeated reads and hash hits. -/
def compile {Cfg A : Type} : OracleProgram.Program A → Execution Cfg (A × List Observation)
  | .pure value => pure (value,[])
  | .start input next => NativeCheckpointProgram.prepend (.start input) <$> compile next
  | .read input offset count next => do
    let output ← NativeShakeCache.read input offset count
    NativeCheckpointProgram.prepend (.output input offset output) <$> compile (next output)
  | .hash input next => do
    let answer ← liftM (liftM
      ((CheckpointExecution.Spec unifSpec Cfg Input Digest).query (.inr (.inl input))) :
        OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Digest)
    NativeCheckpointProgram.prepend (.hash input (List.ofFn answer)) <$> compile (next answer)

/-- Composition preserves the entire ordered native transcript and threads one
cache across both programs. In particular, a prelude cannot be reset at bind. -/
theorem compile_bind {Cfg A B : Type} (program : OracleProgram.Program A)
    (next : A → OracleProgram.Program B) :
    compile (Cfg := Cfg) (OracleProgram.bind program next) = (do
      let first ← compile program
      let second ← compile (next first.1)
      pure (second.1, first.2 ++ second.2)) := by
  induction program with
  | pure value => simp [OracleProgram.bind, compile]
  | start input tail ih =>
    simp [OracleProgram.bind, compile, ih,
      NativeCheckpointProgram.prepend, List.cons_append]
  | read input offset count tail ih =>
    simp [OracleProgram.bind, compile, ih, bind_assoc,
      NativeCheckpointProgram.prepend, List.cons_append]
  | hash input tail ih =>
    simp [OracleProgram.bind, compile, ih, bind_assoc,
      NativeCheckpointProgram.prepend, List.cons_append]

/-- Every possible execution preserves all bytes exposed by its prelude,
including branches selected after a read and repeated hash requests. -/
theorem compile_preserves {Cfg A : Type} (program : OracleProgram.Program A)
    (cache : NativeShakeCache.Cache) (result : (A × List Observation) × NativeShakeCache.Cache)
    (possible : result ∈ support ((compile (Cfg := Cfg) program).run cache)) :
    ∀ key saved, cache key = some saved → result.2 key = some saved := by
  induction program generalizing cache result with
  | pure value =>
    have same := eq_of_mem_support_pure _ possible
    subst result
    exact fun _ _ h => h
  | start input tail ih =>
    rw [compile,StateT.run_map,support_map,Set.mem_image] at possible
    obtain ⟨rest,read,rfl⟩ := possible
    exact ih cache rest read
  | read input offset count tail ih =>
    rw [compile,StateT.run_bind,mem_support_bind_iff] at possible
    obtain ⟨block,queried,rest⟩ := possible
    rw [StateT.run_map,support_map,Set.mem_image] at rest
    obtain ⟨output,read,rfl⟩ := rest
    intro key saved known
    exact ih block.1 block.2 output read key saved
      (NativeShakeCache.read_preserves input offset count cache block queried key saved known)
  | hash input tail ih =>
    rw [compile,StateT.run_bind,StateT.run_liftM,support_bind] at possible
    simp only [Set.mem_iUnion] at possible
    obtain ⟨answer,queried,rest⟩ := possible
    rw [bind_pure_comp,support_map,Set.mem_image] at queried
    obtain ⟨digest,_,rfl⟩ := queried
    rw [StateT.run_map,support_map,Set.mem_image] at rest
    obtain ⟨output,read,rfl⟩ := rest
    exact ih digest cache output read

/-- Suspension retains the byte cache and the complete native residual program. -/
def compilePrefix {Cfg A : Type} (fuel : ℕ) (program : OracleProgram.Program A) :
    Execution Cfg ((OracleProgram.Program A ⊕ A) × List Observation) :=
  compile (NativeProgramPrefix.take fuel program)

/-- An analysis boundary never refreshes already exposed challenge bytes. -/
theorem compile_resume {Cfg A : Type} (fuel : ℕ) (program : OracleProgram.Program A) :
    compile (Cfg := Cfg) program = (do
      let first ← compilePrefix fuel program
      let second ← compile (NativeProgramPrefix.resume first.1)
      pure (second.1,first.2++second.2)) := by
  simpa only [NativeProgramPrefix.take_resume,compilePrefix] using
    (compile_bind (Cfg := Cfg) (NativeProgramPrefix.take fuel program) NativeProgramPrefix.resume)

end
end FormalProof4FHE.HasteBoots.NativeLazyProgram
