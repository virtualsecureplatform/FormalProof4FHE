module

public import FormalProof4FHE.HasteBoots.NativeParentRootFreeze
@[expose] public section

/-! The parent ledger and owned SHAKE cache are reconstructed from the complete
ordered native log. This invariant holds under every typed shared handler.
It does not certify arbitrary supplied initial metadata as a genuine prelude. -/
namespace FormalProof4FHE.HasteBoots.NativeParentHistory
open InputIndexedOracle (Input)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open OracleSpec OracleComp
open NativeParentRootFreeze (Ledger Spec compile)
noncomputable section

def record (state : Ledger × NativeShakeCache.Cache) : Observation → Ledger × NativeShakeCache.Cache
  | .start input => (NativeParentLedger.discover state.1 state.2 input,state.2)
  | .output input offset values =>
    (if values = [] then NativeParentLedger.discover state.1 state.2 input
     else (NativeParentLedger.prepare state.1 state.2 input).next,
     NativeShakeHistory.record state.2 (.output input offset values))
  | .hash input _ => (NativeParentLedger.discover state.1 state.2 input,state.2)

theorem read_record (ledger : Ledger) (input : Input) (offset count : ℕ) (cache : NativeShakeCache.Cache)
    (result : Input × NativeShakeCache.Cache)
    (possible : result ∈ support ((NativeShakeCache.read (Cfg := Digest) input offset count).run cache)) :
    record (ledger,cache) (.output input offset result.1) =
      (if 0 < count then (NativeParentLedger.prepare ledger cache input).next
       else NativeParentLedger.discover ledger cache input,result.2) := by
  have length := (NativeShakeCache.read_records input offset count cache result possible).1
  have written := NativeShakeHistory.read_records input offset count cache result possible
  have nonempty : result.1 = [] ↔ ¬ 0 < count := by
    rw [← List.length_eq_zero_iff,length]
    omega
  simp only [record,nonempty,NativeShakeHistory.record,← written]
  by_cases positive : 0 < count <;> simp [positive]
theorem compile_records {A : Type} (program : OracleProgram.Program A) (ledger : Ledger)
    (cache : NativeShakeCache.Cache)
    (result : ((A × List Observation) × Ledger) × NativeShakeCache.Cache)
    (possible : result ∈ support ((compile ledger program).run cache)) :
    (result.1.2,result.2) = result.1.1.2.foldl record (ledger,cache) := by
  induction program generalizing ledger cache result with
  | pure value =>
    have same := eq_of_mem_support_pure _ possible
    subst result
    rfl
  | start input tail ih =>
    simp only [compile,StateT.run_bind,StateT.run_get,pure_bind,StateT.run_map,support_map,Set.mem_image] at possible
    obtain ⟨rest,read,rfl⟩ := possible
    simpa only [NativeParentRootFreeze.prepend,NativeCheckpointProgram.prepend,List.foldl_cons,record] using
      ih (NativeParentLedger.discover ledger cache input) cache rest read
  | read input offset count tail ih =>
    simp only [compile,StateT.run_bind,StateT.run_get,pure_bind] at possible
    split at possible
    · rename_i positive
      simp only [StateT.run_bind,StateT.run_liftM] at possible
      rw [mem_support_bind_iff] at possible
      obtain ⟨annotation,annotated,possible⟩ := possible
      rw [bind_pure_comp,support_map,Set.mem_image] at annotated
      obtain ⟨_,_,rfl⟩ := annotated
      rw [mem_support_bind_iff] at possible
      obtain ⟨block,queried,rest⟩ := possible
      rw [StateT.run_map,support_map,Set.mem_image] at rest
      obtain ⟨output,read,rfl⟩ := rest
      have updated := read_record ledger input offset count cache block queried
      simpa only [NativeParentRootFreeze.prepend,NativeCheckpointProgram.prepend,List.foldl_cons,updated,ite_eq_left positive] using
        ih block.1 _ block.2 output read
    · rename_i positive
      simp only [StateT.run_bind] at possible
      rw [mem_support_bind_iff] at possible
      obtain ⟨block,queried,rest⟩ := possible
      rw [StateT.run_map,support_map,Set.mem_image] at rest
      obtain ⟨output,read,rfl⟩ := rest
      have updated := read_record ledger input offset count cache block queried
      simpa only [NativeParentRootFreeze.prepend,NativeCheckpointProgram.prepend,List.foldl_cons,updated,ite_eq_right positive] using
        ih block.1 _ block.2 output read
  | hash input tail ih =>
    simp only [compile,StateT.run_bind,StateT.run_get,pure_bind,StateT.run_liftM] at possible
    rw [mem_support_bind_iff] at possible
    obtain ⟨answer,queried,rest⟩ := possible
    rw [bind_pure_comp,support_map,Set.mem_image] at queried
    obtain ⟨answer,_,rfl⟩ := queried
    rw [StateT.run_map,support_map,Set.mem_image] at rest
    obtain ⟨output,read,rfl⟩ := rest
    simpa only [NativeParentRootFreeze.prepend,NativeCheckpointProgram.prepend,List.foldl_cons,record] using
      ih answer (NativeParentLedger.discover ledger cache input) cache output read

/-- Actual shared handlers preserve the reconstruction invariant. -/
theorem simulated_records {A S : Type}
    (impl : QueryImpl Spec (StateT S ProbComp))
    (program : OracleProgram.Program A) (ledger : Ledger) (cache : NativeShakeCache.Cache) (state : S)
    (result : (((A × List Observation) × Ledger) × NativeShakeCache.Cache) × S)
    (possible : result ∈ support ((simulateQ impl ((compile ledger program).run cache)).run state)) :
    (result.1.1.2,result.1.2) = result.1.1.1.2.foldl record (ledger,cache) := by
  have projected : result.1 ∈ support ((simulateQ impl ((compile ledger program).run cache)).run' state) := by
    rw [StateT.run'_eq,support_map,Set.mem_image]
    exact ⟨result,possible,rfl⟩
  exact compile_records program ledger cache result.1
    (support_simulateQ_run'_subset impl _ state projected)

theorem record_append (state : Ledger × NativeShakeCache.Cache) (first later : List Observation) :
    (first++later).foldl record state = later.foldl record (first.foldl record state) := List.foldl_append

theorem record_cache (state : Ledger × NativeShakeCache.Cache) (entry : Observation) :
    (record state entry).2 = NativeShakeHistory.record state.2 entry := by
  cases entry <;> rfl

theorem fold_cache (state : Ledger × NativeShakeCache.Cache) (log : List Observation) :
    (log.foldl record state).2 = log.foldl NativeShakeHistory.record state.2 := by
  induction log generalizing state with
  | nil => rfl
  | cons entry log ih => rw [List.foldl_cons,List.foldl_cons,ih,record_cache]

theorem record_keeps_frozen (state : Ledger × NativeShakeCache.Cache) (entry : Observation) :
    state.1.frozen ⊆ (record state entry).1.frozen := by
  cases entry with
  | start input => rw [record,NativeParentLedger.discover_frozen]
  | hash input digest => rw [record,NativeParentLedger.discover_frozen]
  | output input offset values =>
    simp only [record]
    split
    · rw [NativeParentLedger.discover_frozen]
    · exact NativeParentLedger.prepare_keeps _ _ _

theorem fold_keeps_frozen (state : Ledger × NativeShakeCache.Cache) (log : List Observation) :
    state.1.frozen ⊆ (log.foldl record state).1.frozen := by
  induction log generalizing state with
  | nil => exact Finset.Subset.refl _
  | cons entry log ih => exact (record_keeps_frozen state entry).trans (ih _)

theorem record_keeps_parents (state : Ledger × NativeShakeCache.Cache) (entry : Observation) :
    state.1.parents.Sublist (record state entry).1.parents := by
  cases entry with
  | start input => exact NativeParentLedger.discover_parents _ _ _
  | hash input digest => exact NativeParentLedger.discover_parents _ _ _
  | output input offset values =>
    simp only [record]
    split
    · exact NativeParentLedger.discover_parents _ _ _
    · exact NativeParentLedger.prepare_parents _ _ _

theorem fold_keeps_parents (state : Ledger × NativeShakeCache.Cache) (log : List Observation) :
    state.1.parents.Sublist (log.foldl record state).1.parents := by
  induction log generalizing state with
  | nil => exact List.Sublist.refl _
  | cons entry log ih => exact (record_keeps_parents state entry).trans (ih _)

end
end FormalProof4FHE.HasteBoots.NativeParentHistory
