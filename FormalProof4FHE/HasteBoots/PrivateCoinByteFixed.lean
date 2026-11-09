module
public import FormalProof4FHE.HasteBoots.PrivateCoinByteFailure
@[expose] public section

/-! The fixed-private-tape view of the actual runtime-coin interpreter. These
are sections of its proved joint execution/work functions, not a new run or
a preloaded finite approximation of the private tape. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinByteFixed
open MeasureTheory
open InputIndexedOracle (Input World law)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction State take tickCost initialise)
noncomputable section
abbrev Packet := PrivateCoinByteLineage.Packet
def packet (state : State) (log : List NativeTranscript.Observation) : Packet := (.inl state, log)

def history (code : List Instruction) (publicData : Input) (tape : Tape)
    (privateData : ClosedByteMachine.Tape → Input) := PrivateCoinByteLineage.history code publicData privateData tape

theorem history_run (code : List Instruction) (publicData : Input) (tape : Tape)
    (privateData : ClosedByteMachine.Tape → Input) (fuel : ℕ) (world : World) :
    (history code publicData tape privateData fuel world).run =
      packet (OracleProgram.run (take code publicData tape fuel (initialise code privateData)) world).run.1
        (OracleProgram.run (take code publicData tape fuel (initialise code privateData)) world).run.2 :=
  PrivateCoinByteLineage.history_run code publicData privateData tape fuel world

theorem history_replay (code : List Instruction) (publicData : Input) (tape : Tape)
    (privateData : ClosedByteMachine.Tape → Input) (fuel : ℕ) : ObservationReplay.Replayable (history code publicData tape privateData fuel) :=
  PrivateCoinByteLineage.history_replay code publicData privateData tape fuel

def prefixWork (code : List Instruction) (publicData : Input) (tape : Tape)
    (privateData : ClosedByteMachine.Tape → Input) (fuel : ℕ) (world : World) : ENNReal :=
  PrivateCoinByteWork.prefixWork code publicData privateData fuel (tape, world)

def lifetimeWork (code : List Instruction) (publicData : Input) (tape : Tape)
    (privateData : ClosedByteMachine.Tape → Input) (world : World) : ENNReal :=
  PrivateCoinByteWork.lifetimeWork code publicData privateData (tape, world)

def expectedWork (code : List Instruction) (publicData : Input) (tape : Tape)
    (privateData : ClosedByteMachine.Tape → Input) : ENNReal := ∫⁻ world, lifetimeWork code publicData tape privateData world ∂law

theorem lifetimeWork_measurable (code : List Instruction) (publicData : Input) (tape : Tape)
    (privateData : ClosedByteMachine.Tape → Input) : Measurable (lifetimeWork code publicData tape privateData) :=
  (PrivateCoinByteWork.lifetimeWork_measurable code publicData privateData).comp (measurable_const.prodMk measurable_id)

theorem stepCost_tsum_le (code : List Instruction) (publicData : Input) (tape : Tape)
    (privateData : ClosedByteMachine.Tape → Input) (world : World) :
    (∑' fuel : ℕ, (tickCost code publicData (OracleProgram.run
      (take code publicData tape fuel (initialise code privateData)) world).run.1 : ENNReal)) ≤
        lifetimeWork code publicData tape privateData world :=
  PrivateCoinByteWork.stepCosts_le code publicData privateData (tape, world)

theorem tickCost_pos (code : List Instruction) (publicData : Input) (state : State)
    (active : state.machine.stopped = none) : 0 < tickCost code publicData state := by
  simp only [tickCost, active]
  cases selected : code[state.machine.pc]? with
  | none => exact Nat.zero_lt_one
  | some chosen => cases chosen with
    | coin dst => exact Nat.succ_pos 1
    | base instruction => exact ClosedByteMachine.price_pos publicData state.machine instruction

theorem take_one_work (code : List Instruction) (publicData : Input) (tape : Tape) (state : State) (world : World) :
    (OracleProgram.run (take code publicData tape 1 state) world).run.1.work = state.work + tickCost code publicData state :=
  PrivateCoinByteWork.take_succ_work code publicData tape 0 state world
end
end FormalProof4FHE.HasteBoots.PrivateCoinByteFixed
