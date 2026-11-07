module
import all FormalProof4FHE.HasteBoots.ClosedByteMachineRootLifetime
import all FormalProof4FHE.HasteBoots.ClosedByteMachineGoldRisk
import all FormalProof4FHETest.HasteBootsCalibrationSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World)
open ClosedByteMachine (Instruction State Tape initialise take)
namespace HasteBootsClosedMachineSmoke

def empty : Tape → Input := fun _ => []

-- Silent computation has work, even though its complete oracle log is empty.
example (world : World) :
    (OracleProgram.run (take [.jump 0] [] 8 (initialise [.jump 0] empty)) world).run.1.work =
      (initialise [.jump 0] empty).work+8 := by rfl
example (world : World) :
    (OracleProgram.run (take [.jump 0] [] 8 (initialise [.jump 0] empty)) world).run.2 = [] := by rfl

-- Byte arithmetic wraps in the byte alphabet.
example (world : World) :
    (OracleProgram.run (take [.constant 0 255,.constant 1 1,.add 2 0 1] [] 3
      (initialise [.constant 0 255,.constant 1 1,.add 2 0 1] empty)) world).run.1.registers 2 = 0 := by rfl

-- Termination/failure pays once and retains its work at arbitrary later fuel.
example (world : World) :
    (OracleProgram.run (take [.halt] [] 8 (initialise [.halt] empty)) world).run.1.work =
      (initialise [.halt] empty).work+1 := by rfl
example (world : World) :
    (OracleProgram.run (take [.reject] [] 8 (initialise [.reject] empty)) world).run.1.stopped = some .reject := by rfl
example (world : World) :
    (OracleProgram.run (take [] [] 8 (initialise [] empty)) world).run.1.work =
      (initialise [] empty).work+1 := by rfl
example (world : World) :
    (OracleProgram.run (take [.pop 0 0] [] 8 (initialise [.pop 0 0] empty)) world).run.1.stopped = some .abort := by rfl

-- Immutable public setup is charged when copied into working memory.
example (world : World) (publicData : Input) :
    (OracleProgram.run (take [.publicCopy 0] publicData 1 (initialise [.publicCopy 0] empty)) world).run.1.work =
      (initialise [.publicCopy 0] empty).work+(1+publicData.length) := by rfl

-- Returned bytes determine a later read's offset AND count; no static cap.
def adaptive : List Instruction := [.read 0 1 0 1,.readTape 0 2 1 1]
def initial : Tape → Input := fun tape => if tape = 0 then [9] else []
example (world : World) :
    (OracleProgram.run (take adaptive [] 2 (initialise adaptive initial)) world).run.2 =
      [.output [9] 0 [InputIndexedOracle.shake world [9] 0],
       .output [9] (InputIndexedOracle.shake world [9] 0).val
         (InputIndexedOracle.bytes world [9] (InputIndexedOracle.shake world [9] 0).val
           (InputIndexedOracle.shake world [9] 0).val)] := by rfl

-- Repeated reads share the same global byte coordinate.
def repeated : List Instruction := [.read 0 1 71 2,.read 0 2 71 2]
example (world : World) :
    let final := (OracleProgram.run (take repeated [] 2 (initialise repeated initial)) world).run.1
    final.tapes 1 = final.tapes 2 := by rfl

example (world : World) :
    let code : List Instruction := [.hash 0 1,.hash 0 2]
    let final := (OracleProgram.run (take code [] 2 (initialise code initial)) world).run.1
    final.tapes 1 = final.tapes 2 := by rfl

-- Empty reads are retained observations but are not stream exposures.
example (world : World) :
    CausalStreamExposure.seen
      (OracleProgram.run (take [.read 0 1 101 0] [] 1 (initialise [.read 0 1 101 0] empty)) world).run.2 [] = false := by rfl

-- Four instruction steps precede exposure, but only one observation does.
def delayed : List Instruction := [.constant 0 1,.push 0 0,.start 0,.jump 4,.read 0 1 37 1,.halt]
example (world : World) :
    (OracleProgram.run (take delayed [] 4 (initialise delayed empty)) world).run.2 = [.start [1]] := by rfl
example (world : World) :
    CausalFirstStreamPrefix.recover [1]
      (OracleProgram.run (take delayed [] 5 (initialise delayed empty)) world).run.2 = some [.start [1]] := by rfl

example (world : World) :
    CausalStreamExposure.firstRead (ClosedByteMachineRequest.command delayed [])
      (.inl (OracleProgram.run (take delayed [] 4 (initialise delayed empty)) world).run.1,
        (OracleProgram.run (take delayed [] 4 (initialise delayed empty)) world).run.2) = some [1] := by rfl

-- The numerical certificate bounds actual closed-machine exposure events.
-- This is not the full false-PBS event or a native physical-work refinement.
open HasteBootsCalibrationSmoke (ctx tables primitive constructed compatible)
open HasteBootsBatchMeaningSmoke (usize)
example (code : List Instruction) (publicData : Input) (privateData : Tape → Input) :
    InputIndexedOracle.law {world | ∃ fuel, ClosedByteMachineGoldRisk.event code publicData (fun _ => 0)
      ctx primitive .helper (fun _ => 0) (ClosedByteMachineGoldRisk.history code publicData privateData fuel world).run world} ≤
        ((17 : ENNReal)/2^141)*ClosedByteMachineWork.expectedWork code publicData privateData :=
  ClosedByteMachineGoldRisk.lifetime_le_work code publicData (fun _ => 0) ctx primitive .helper
    tables (usize 2048) (usize 4) (usize 2) constructed compatible (fun _ => 0) privateData

example (code : List Instruction) (publicData : Input) (privateData : Tape → Input) :
    ClosedByteMachineWork.expectedWork code publicData privateData =
      ⨆ fuel : ℕ, ∫⁻ world, ClosedByteMachineWork.prefixWork code publicData privateData fuel world ∂InputIndexedOracle.law :=
  ClosedByteMachineWork.expectedWork_eq_iSup code publicData privateData
end HasteBootsClosedMachineSmoke
