module
public import FormalProof4FHE.HasteBoots.StoredParentSeedCheck
public import FormalProof4FHE.HasteBoots.CompactSourceHistory
@[expose] public section

/-! Measured replay of all observed SHAKE coordinates from a complete mixed
history. Starts and hashes are visited, every output byte is retained, and
repeated/overlapping intervals use the latest observed spelling. No oracle-world
or cache callback is executed. Parent parsing, source-ledger replay and physical
refinement remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.StoredShakeHistory
open InputIndexedOracle (Input)
open NativeTranscript (Observation)
open SolverOperationCost (Run)
open StoredShakeByteCache (Cache view write)

def outputBytes : Observation → ℕ
  | .output _ _ values => values.length
  | _ => 0

def bytes : List Observation → ℕ
  | [] => 0
  | head::tail => outputBytes head+bytes tail

def record (cache : Cache) : Observation → Run Cache
  | .output input offset values =>
    let result := write cache input offset values
    ⟨result.value,result.cost+2⟩
  | _ => ⟨cache,1⟩

theorem record_view (cache : Cache) (entry : Observation) :
    view (record cache entry).value = NativeShakeHistory.record (view cache) entry := by
  cases entry with
  | start input => rfl
  | hash input value => rfl
  | output input offset values =>
    simp only [record,StoredShakeByteCache.write_view,NativeShakeHistory.record,
      ExecutableSourceHistory.writeBytes_eq]

theorem record_cost (cache : Cache) (entry : Observation) :
    (record cache entry).cost ≤ 8*outputBytes entry+3 := by
  cases entry <;> simp only [record,outputBytes,StoredShakeByteCache.write_cost] <;> omega

theorem record_size (cache : Cache) (entry : Observation) :
    (record cache entry).value.length = cache.length+outputBytes entry := by
  cases entry <;> simp only [record,outputBytes,StoredShakeByteCache.write_size,Nat.add_zero]

def loop (cache : Cache) : List Observation → Run Cache
  | [] => ⟨cache,1⟩
  | head::tail =>
    let first := record cache head
    let rest := loop first.value tail
    ⟨rest.value,first.cost+rest.cost+2⟩

theorem loop_view (cache : Cache) (history : List Observation) :
    view (loop cache history).value = history.foldl NativeShakeHistory.record (view cache) := by
  induction history generalizing cache with
  | nil => rfl
  | cons head tail ih => simp only [loop,List.foldl_cons,ih,record_view]

theorem loop_cost (cache : Cache) (history : List Observation) :
    (loop cache history).cost ≤ 8*bytes history+5*history.length+1 := by
  induction history generalizing cache with
  | nil => simp [loop,bytes]
  | cons head tail ih =>
    have first := record_cost cache head
    have rest := ih (record cache head).value
    simp only [loop,bytes,List.length_cons]
    omega

theorem loop_size (cache : Cache) (history : List Observation) :
    (loop cache history).value.length = cache.length+bytes history := by
  induction history generalizing cache with
  | nil => simp [loop,bytes]
  | cons head tail ih => simp only [loop,bytes,ih,record_size,Nat.add_assoc]

def replay (history : List Observation) : Run Cache := loop [] history

theorem replay_cost (history : List Observation) :
    (replay history).cost ≤ 8*bytes history+5*history.length+1 := loop_cost [] history

theorem replay_size (history : List Observation) :
    (replay history).value.length = bytes history := by
  simpa only [replay,List.length_nil,Nat.zero_add] using loop_size [] history

theorem compact_record_bytes (state : ExecutableSourceHistory.State) (entry : Observation) :
    (CompactSourceHistory.record state entry).bytes = NativeShakeHistory.record state.bytes entry := by
  cases entry with
  | start input => rfl
  | hash input value => rfl
  | output input offset values =>
    by_cases empty : values = []
    · subst values; rfl
    · simp only [CompactSourceHistory.record,empty,ite_false,NativeShakeHistory.record,
        ExecutableSourceHistory.writeBytes_eq]

theorem replay_eq_compact (history : List Observation) :
    view (replay history).value = (CompactSourceHistory.reconstruct history).bytes := by
  have fold (state : ExecutableSourceHistory.State) :
      (history.foldl CompactSourceHistory.record state).bytes =
        history.foldl NativeShakeHistory.record state.bytes := by
    induction history generalizing state with
    | nil => rfl
    | cons head tail ih => simp only [List.foldl_cons,ih,compact_record_bytes]
  exact (loop_view [] history).trans (fold ExecutableSourceHistory.initial).symm

/-- Check one supplied stored child-seed quote against the complete old observed
byte history, retaining every partial exposure. Parsing/choosing parents remains
outside this entry point. -/
def parentCompatible (history : List Observation) (input : Input)
    (seed : Vector InputIndexedOracle.Byte 64) : Run Bool :=
  let cache := replay history
  let result := StoredParentSeedCheck.compatible cache.value input seed
  ⟨result.value,cache.cost+result.cost+1⟩

theorem parentCompatible_value (history : List Observation) (input : Input)
    (seed : Vector InputIndexedOracle.Byte 64) :
    (parentCompatible history input seed).value = ExecutableParentInputView.compatible
      (CompactSourceHistory.reconstruct history).bytes input seed.get := by
  simp only [parentCompatible,StoredParentSeedCheck.compatible_value,replay_eq_compact]

theorem parentCompatible_cost (history : List Observation) (input : Input)
    (seed : Vector InputIndexedOracle.Byte 64) :
    (parentCompatible history input seed).cost ≤
      8*bytes history+5*history.length+64*((6*input.length+14)*bytes history+5)+133 := by
  have cache := replay_cost history
  have result := StoredParentSeedCheck.compatible_cost (replay history).value input seed
  rw [replay_size] at result
  simp only [parentCompatible]
  omega
end FormalProof4FHE.HasteBoots.StoredShakeHistory
