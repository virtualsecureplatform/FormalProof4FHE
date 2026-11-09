module
public import FormalProof4FHE.HasteBoots.PrivateCoinByteLogWork
public import FormalProof4FHE.HasteBoots.ClosedByteMachineRootBudget
@[expose] public section

/-! Input-byte, registry and hash-key budgets on actual runtime-coin prefixes.
Private coin steps add work but no oracle inputs or source-ledger mentions. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinByteRootBudget
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction State take tick tickCost)
open ClosedByteMachineRootBudget (inputWork inputWork_append observed_pools_card hash_keys_le_log)
open NativeParentLedgerPools (observedPools)
open OracleSpec OracleComp
noncomputable section

theorem tick_inputWork_le (code : List Instruction) (publicData : Input) (tape : Tape) (state : State) (world : World) :
    inputWork (OracleProgram.run (tick code publicData tape state) world).run.2 ≤ tickCost code publicData state := by
  cases stopped : state.machine.stopped with
  | some stop => simp only [tick, tickCost, stopped]; exact le_rfl
  | none =>
    cases selected : code[state.machine.pc]? with
    | none => simp only [tick, tickCost, stopped, selected]; exact Nat.zero_le _
    | some chosen =>
      cases chosen with
      | coin dst => simp only [tick, tickCost, stopped, selected]; exact Nat.zero_le _
      | base instruction =>
        have equal : (OracleProgram.run (tick code publicData tape state) world).run.2 =
            (OracleProgram.run (ClosedByteMachine.issue publicData state.machine instruction) world).run.2 := by
          simp only [tick, stopped, selected, OracleProgram.run_bind, ObservationReplay.run_bind,
            OracleProgram.run, CanonicalTranscriptSampler.run_pure, List.append_nil]
        rw [equal]
        simp only [tickCost, stopped, selected]
        cases instruction with
        | start src => change (state.machine.tapes src).length+0 ≤ 1+(state.machine.tapes src).length; omega
        | read src dst offset count =>
          change (state.machine.tapes src).length+0 ≤ 1+(state.machine.tapes src).length+offset.size+count
          omega
        | readTape src dst offset count =>
          change (state.machine.tapes src).length+0 ≤ 1+(state.machine.tapes src).length+
            ClosedByteMachine.decodeWork (state.machine.tapes offset)+ClosedByteMachine.decodeWork (state.machine.tapes count)+
              TranscriptFrame.fromLittleEndian (state.machine.tapes count)
          omega
        | hash src dst => change (state.machine.tapes src).length+0 ≤ 1+(state.machine.tapes src).length+64; omega
        | pop src dst => cases h : state.machine.tapes src <;> simp only [ClosedByteMachine.issue, h] <;> exact Nat.zero_le _
        | _ => exact Nat.zero_le _

theorem take_inputWork_le (code : List Instruction) (publicData : Input) (tape : Tape)
    (fuel : ℕ) (state : State) (world : World) :
    inputWork (OracleProgram.run (take code publicData tape fuel state) world).run.2 ≤
      (OracleProgram.run (take code publicData tape fuel state) world).run.1.work := by
  induction fuel with
  | zero => exact Nat.zero_le _
  | succ fuel ih =>
    rw [PrivateCoinByteMachine.take_resume code publicData tape fuel 1, OracleProgram.run_bind,
      ObservationReplay.run_bind, inputWork_append, PrivateCoinByteLogWork.take_one_log, PrivateCoinByteFixed.take_one_work]
    exact Nat.add_le_add ih (tick_inputWork_le _ _ _ _ _)

theorem hash_loss_le_work (code : List Instruction) (publicData : Input) (tape : Tape)
    (fuel : ℕ) (state : State) (world : World) (dummy : Digest) (query : Input) :
    let history := (OracleProgram.run (take code publicData tape fuel state) world).run.2
    let work := (OracleProgram.run (take code publicData tape fuel state) world).run.1.work
    CheckpointCollision.loss unifSpec NativeMerkleShapeFamily.shape (.inr (.inl query))
      (NativeGoldBatchFamilyAvailability.reconstructed dummy history) ≤
        ((3*work+256*work*work : ℕ) : ENNReal)/(2 : ENNReal)^512 := by
  dsimp only
  apply (NativeParentLedgerPools.hash_loss_le_pools dummy _ query).trans
  apply ENNReal.div_le_div_right
  apply Nat.cast_le.mpr
  have bytes := take_inputWork_le code publicData tape fuel state world
  have keys := (hash_keys_le_log _).trans (PrivateCoinByteLogWork.log_le_work code publicData tape fuel state world)
  obtain ⟨contexts, roots⟩ := observed_pools_card (OracleProgram.run (take code publicData tape fuel state) world).run.2
  have bounded : (observedPools (OracleProgram.run (take code publicData tape fuel state) world).run.2).contexts.card ≤
      2*(OracleProgram.run (take code publicData tape fuel state) world).run.1.work := contexts.trans (Nat.mul_le_mul_left 2 bytes)
  have boundedRoots : (observedPools (OracleProgram.run (take code publicData tape fuel state) world).run.2).roots.card ≤
      2*(OracleProgram.run (take code publicData tape fuel state) world).run.1.work := roots.trans (Nat.mul_le_mul_left 2 bytes)
  have product := Nat.mul_le_mul bounded boundedRoots
  nlinarith
end
end FormalProof4FHE.HasteBoots.PrivateCoinByteRootBudget
