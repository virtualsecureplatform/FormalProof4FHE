module
public import FormalProof4FHE.HasteBoots.CompactParentHistory
public import FormalProof4FHE.HasteBoots.ClosedByteMachineLogWork
@[expose] public section

/-! Stored compact source/helper entries are polynomially bounded by the
closed interpreter's declared work. Work is not defined by log length. This
bounds metadata entries only, not total extraction time or physical memory. -/
namespace FormalProof4FHE.HasteBoots.CompactParentWorkStorage
open InputIndexedOracle (Input World)
open ClosedByteMachine (Instruction State take)

theorem metadataSize_le_work (code : List Instruction) (publicData : Input) (fuel : ℕ) (state : State) (world : World) :
    CompactParentLedger.metadataSize
      (CompactParentHistory.reconstruct (OracleProgram.run (take code publicData fuel state) world).run.2).1 ≤
      (OracleProgram.run (take code publicData fuel state) world).run.1.work *
        (4 * (OracleProgram.run (take code publicData fuel state) world).run.1.work ^ 2 +
          2 * (OracleProgram.run (take code publicData fuel state) world).run.1.work) := by
  have metadata := CompactParentHistory.metadataSize_le_inputWork
    (OracleProgram.run (take code publicData fuel state) world).run.2
  have inputs := ClosedByteMachineRootBudget.take_inputWork_le code publicData fuel state world
  have count := ClosedByteMachineLogWork.log_le_work code publicData fuel state world
  have square := Nat.mul_le_mul inputs inputs
  have bound : 4 * ClosedByteMachineRootBudget.inputWork (OracleProgram.run (take code publicData fuel state) world).run.2 ^ 2 +
      2 * ClosedByteMachineRootBudget.inputWork (OracleProgram.run (take code publicData fuel state) world).run.2 ≤
      4 * (OracleProgram.run (take code publicData fuel state) world).run.1.work ^ 2 +
        2 * (OracleProgram.run (take code publicData fuel state) world).run.1.work := by nlinarith
  exact metadata.trans (Nat.mul_le_mul count bound)
end FormalProof4FHE.HasteBoots.CompactParentWorkStorage
