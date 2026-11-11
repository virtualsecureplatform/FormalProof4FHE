module
import all FormalProof4FHE.HasteBoots.PrivateCoinJointPcsLedger
import all FormalProof4FHETest.HasteBootsPrivateCoinScalarSmoke

namespace FormalProof4FHE.HasteBoots.SharedHashLedgerSmoke
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
noncomputable section

/-- Merely installing private code/data emits no hash observations. -/
theorem initial_safe (code : List PrivateCoinByteMachine.Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (execution : PrivateCoinReplay.Tape × World) :
    ¬PrivateCoinSharedHash.Root code publicData privateData dummy 0 execution := by
  change ¬CheckpointCollision.Bad NativeMerkleShapeFamily.shape (CheckpointExecution.empty NativeMerkleShapeFamily.shape)
  rintro (flag | collision)
  · cases flag
  · exact CachedHashCollision.no_collision_empty collision

/-- Completing a pure program for PCS analysis cannot create a hash charge. -/
theorem completed_safe {A : Type} (value : A) (dummy : Digest) (world : World) :
    ¬SingleOpeningLifetimeSoundness.SourceBad dummy (SingleOpeningLifetimeSoundness.clean (.pure value)) id OracleProgramMachine.step world := by
  rw [PrivateCoinSharedHash.source_bad_iff]
  change ¬CheckpointCollision.Bad NativeMerkleShapeFamily.shape (CheckpointExecution.empty NativeMerkleShapeFamily.shape)
  rintro (flag | collision)
  · cases flag
  · exact CachedHashCollision.no_collision_empty collision

/-- A coin outside the actual finite strategy cannot change its hash event. -/
theorem unused_coin (dummy : Digest) (world : World) :
    NativeRootFamilyLifetime.Bad dummy (OracleProgram.run
      (PrivateCoinByteMachine.take PrivateCoinScalarSmoke.code [] PrivateCoinScalarSmoke.changed 1
        (PrivateCoinByteMachine.initialise PrivateCoinScalarSmoke.code (fun _ => []))) world).run.2 ↔
    NativeRootFamilyLifetime.Bad dummy (OracleProgram.run
      (PrivateCoinByteMachine.take PrivateCoinScalarSmoke.code [] PrivateCoinScalarSmoke.zero 1
        (PrivateCoinByteMachine.initialise PrivateCoinScalarSmoke.code (fun _ => []))) world).run.2 := by
  rw [PrivateCoinScalarSmoke.unused_coin]

end
end FormalProof4FHE.HasteBoots.SharedHashLedgerSmoke
