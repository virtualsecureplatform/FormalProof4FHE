module
public import FormalProof4FHE.HasteBoots.PrivateCoinByteWork
@[expose] public section

/-! The runtime-coin instruction set preserves the original closed interpreter
on code containing only base instructions, from the same charged machine
state. The unused private cursor is retained exactly, without oracle effects. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinByteEmbedding
open InputIndexedOracle (Input World)
open PrivateCoinReplay (Tape)
open OracleProgram (Program bind run)
open PrivateCoinByteMachine (Instruction State tick take)

theorem tick_embed (code : List ClosedByteMachine.Instruction) (publicData : Input) (tape : Tape)
    (state : ClosedByteMachine.State) (cursor : ℕ) :
    tick (code.map Instruction.base) publicData tape ⟨state, cursor⟩ =
      bind (ClosedByteMachine.tick code publicData state) (fun next => .pure ⟨next, cursor⟩) := by
  cases stopped : state.stopped with
  | some stop => simp only [tick, ClosedByteMachine.tick, stopped, OracleProgram.bind]
  | none =>
    cases selected : code[state.pc]? with
    | none => simp only [tick, ClosedByteMachine.tick, stopped, List.getElem?_map, selected, Option.map_none,
        OracleProgram.bind]
    | some instruction => simp only [tick, ClosedByteMachine.tick, stopped, List.getElem?_map, selected, Option.map_some]

theorem take_embed (code : List ClosedByteMachine.Instruction) (publicData : Input) (tape : Tape)
    (fuel : ℕ) (state : ClosedByteMachine.State) (cursor : ℕ) :
    take (code.map Instruction.base) publicData tape fuel ⟨state, cursor⟩ =
      bind (ClosedByteMachine.take code publicData fuel state) (fun next => .pure ⟨next, cursor⟩) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    simp only [take, tick_embed, ClosedByteMachine.take, NativeProgramComposition.bind_assoc]
    congr 1
    funext next
    exact ih next

theorem run_embed (code : List ClosedByteMachine.Instruction) (publicData : Input) (tape : Tape)
    (fuel : ℕ) (state : ClosedByteMachine.State) (cursor : ℕ) (world : World) :
    (run (take (code.map Instruction.base) publicData tape fuel ⟨state, cursor⟩) world).run =
      (⟨(run (ClosedByteMachine.take code publicData fuel state) world).run.1, cursor⟩,
        (run (ClosedByteMachine.take code publicData fuel state) world).run.2) := by
  rw [take_embed, OracleProgram.run_bind, ObservationReplay.run_bind]
  simp only [OracleProgram.run, CanonicalTranscriptSampler.run_pure, List.append_nil]

theorem initial_work_embed (code : List ClosedByteMachine.Instruction)
    (privateData : ClosedByteMachine.Tape → Input) :
    (PrivateCoinByteMachine.initialise (code.map Instruction.base) privateData).work =
      (ClosedByteMachine.initialise code privateData).work + 1 := by
  simp only [PrivateCoinByteMachine.initialise, PrivateCoinByteMachine.State.work,
    ClosedByteMachine.initialise, List.map_map, List.map_nil, List.sum_nil, Nat.add_zero]
  change 4 + (List.ofFn (fun slot : ClosedByteMachine.Tape => (privateData slot).length)).sum + 1 +
      (code.map ClosedByteMachine.Instruction.size).sum = _
  omega
end FormalProof4FHE.HasteBoots.PrivateCoinByteEmbedding
