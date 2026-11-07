module
public import FormalProof4FHE.HasteBoots.NativeRootMentionSize
public import FormalProof4FHE.HasteBoots.ClosedByteMachineLogWork
@[expose] public section

/-! The actual input-byte and registry budgets are bounded by executed
instruction work. This prices the one-hash hazard envelope, not yet its
unbounded lifetime probability or native physical-cost refinement. -/
namespace FormalProof4FHE.HasteBoots.ClosedByteMachineRootBudget
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open ClosedByteMachine (Instruction State take tick tickCost)
open NativeParentLedgerPools (Pools recordPools observedPools inputOf)
open OracleSpec OracleComp
noncomputable section

def inputWork (history : List Observation) : ℕ := (history.map (fun entry => (inputOf entry).length)).sum

theorem inputWork_append (first later : List Observation) : inputWork (first++later) = inputWork first+inputWork later := by
  simp only [inputWork,List.map_append,List.sum_append]

theorem tick_inputWork_le (code : List Instruction) (publicData : Input) (state : State) (world : World) :
    inputWork (OracleProgram.run (tick code publicData state) world).run.2 ≤ tickCost code publicData state := by
  cases stopped : state.stopped with
  | some stop => simp only [tick,tickCost,stopped]; exact le_rfl
  | none =>
    cases selected : code[state.pc]? with
    | none => simp only [tick,tickCost,stopped,selected]; exact Nat.zero_le _
    | some chosen =>
      simp only [tick,tickCost,stopped,selected]
      cases chosen with
      | start src => change (state.tapes src).length+0 ≤ 1+(state.tapes src).length; omega
      | read src dst offset count => change (state.tapes src).length+0 ≤ 1+(state.tapes src).length+offset.size+count; omega
      | readTape src dst offset count =>
        change (state.tapes src).length+0 ≤ 1+(state.tapes src).length+ClosedByteMachine.decodeWork (state.tapes offset)+
          ClosedByteMachine.decodeWork (state.tapes count)+TranscriptFrame.fromLittleEndian (state.tapes count)
        omega
      | hash src dst => change (state.tapes src).length+0 ≤ 1+(state.tapes src).length+64; omega
      | pop src dst =>
        cases h : state.tapes src <;> simp only [ClosedByteMachine.issue,h] <;> exact Nat.zero_le _
      | _ => exact Nat.zero_le _

theorem take_inputWork_le (code : List Instruction) (publicData : Input) (fuel : ℕ) (state : State) (world : World) :
    inputWork (OracleProgram.run (take code publicData fuel state) world).run.2 ≤
      (OracleProgram.run (take code publicData fuel state) world).run.1.work := by
  induction fuel with
  | zero => exact Nat.zero_le _
  | succ fuel ih =>
    rw [ClosedByteMachine.take_resume code publicData fuel 1,OracleProgram.run_bind,ObservationReplay.run_bind,inputWork_append,
      ClosedByteMachineLogWork.take_one_log,ClosedByteMachine.take_one_work]
    exact Nat.add_le_add ih (tick_inputWork_le _ _ _ _)

theorem fold_pools_card (history : List Observation) (pools : Pools) :
    (history.foldl recordPools pools).contexts.card ≤ pools.contexts.card+2*inputWork history ∧
    (history.foldl recordPools pools).roots.card ≤ pools.roots.card+2*inputWork history := by
  induction history generalizing pools with
  | nil => simp [inputWork]
  | cons entry rest ih =>
    obtain ⟨context,root⟩ := ih (recordPools pools entry)
    have contextStep := NativeParentLedgerPools.grow_contexts_card_le pools (inputOf entry)
    have rootStep := NativeParentLedgerPools.grow_roots_card_le pools (inputOf entry)
    have contextSize := NativeRootMentionSize.local_contexts_size (inputOf entry)
    have rootSize := NativeRootMentionSize.local_roots_size (inputOf entry)
    change (rest.foldl recordPools (recordPools pools entry)).contexts.card ≤ _ ∧
      (rest.foldl recordPools (recordPools pools entry)).roots.card ≤ _
    simp only [recordPools,inputWork,List.map_cons,List.sum_cons] at *
    constructor <;> omega

theorem observed_pools_card (history : List Observation) :
    (observedPools history).contexts.card ≤ 2*inputWork history ∧
    (observedPools history).roots.card ≤ 2*inputWork history := by
  simpa only [observedPools,Finset.card_empty,Nat.zero_add] using fold_pools_card history ⟨∅,∅⟩

theorem hash_keys_step (state : JointHashCache.State) (entry : Observation) :
    (JointHashCache.record state entry).keys.card ≤ state.keys.card+1 := by
  cases entry with
  | start input => exact Nat.le_add_right _ _
  | output input offset values => exact Nat.le_add_right _ _
  | hash input digest => exact Finset.card_insert_le _ _

theorem hash_keys_fold (history : List Observation) (state : JointHashCache.State) :
    (history.foldl JointHashCache.record state).keys.card ≤ state.keys.card+history.length := by
  induction history generalizing state with
  | nil => exact (Nat.le_refl _)
  | cons entry rest ih =>
    have first := hash_keys_step state entry
    have later := ih (JointHashCache.record state entry)
    simp only [List.foldl_cons,List.length_cons]
    omega

theorem hash_keys_le_log (history : List Observation) : (JointHashCache.project history).keys.card ≤ history.length := by
  simpa only [JointHashCache.project,CachedHashHandler.empty,Finset.card_empty,Nat.zero_add] using
    hash_keys_fold history CachedHashHandler.empty

/-- Actual fresh-hash loss on the actual closed-machine history is bounded
by a quadratic in its spent instruction work, with no checkpoint certificate. -/
theorem hash_loss_le_work (code : List Instruction) (publicData : Input) (fuel : ℕ) (state : State) (world : World)
    (dummy : Digest) (query : Input) :
    let history := (OracleProgram.run (take code publicData fuel state) world).run.2
    let work := (OracleProgram.run (take code publicData fuel state) world).run.1.work
    CheckpointCollision.loss unifSpec NativeMerkleShapeFamily.shape (.inr (.inl query))
      (NativeGoldBatchFamilyAvailability.reconstructed dummy history) ≤
        ((3*work+256*work*work : ℕ) : ENNReal)/(2 : ENNReal)^512 := by
  dsimp only
  apply (NativeParentLedgerPools.hash_loss_le_pools dummy _ query).trans
  apply ENNReal.div_le_div_right
  apply Nat.cast_le.mpr
  have bytes := take_inputWork_le code publicData fuel state world
  have keys := (hash_keys_le_log _).trans (ClosedByteMachineLogWork.log_le_work code publicData fuel state world)
  obtain ⟨contexts,roots⟩ := observed_pools_card (OracleProgram.run (take code publicData fuel state) world).run.2
  have bounded : (observedPools (OracleProgram.run (take code publicData fuel state) world).run.2).contexts.card ≤
      2*(OracleProgram.run (take code publicData fuel state) world).run.1.work := contexts.trans (Nat.mul_le_mul_left 2 bytes)
  have boundedRoots : (observedPools (OracleProgram.run (take code publicData fuel state) world).run.2).roots.card ≤
      2*(OracleProgram.run (take code publicData fuel state) world).run.1.work := roots.trans (Nat.mul_le_mul_left 2 bytes)
  have product := Nat.mul_le_mul bounded boundedRoots
  nlinarith
end
end FormalProof4FHE.HasteBoots.ClosedByteMachineRootBudget
