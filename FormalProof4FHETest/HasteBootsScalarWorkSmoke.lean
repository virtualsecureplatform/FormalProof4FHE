module
import all FormalProof4FHE.HasteBoots.PrivateCoinScalarWork
import all FormalProof4FHETest.HasteBootsScalarLifetimeSmoke

namespace FormalProof4FHE.HasteBoots.ScalarWorkSmoke
noncomputable section

/-- Native metadata changes width at the bincode varint boundary. -/
theorem varint_boundary :
    (NativeUsizeMessage.encode ⟨250,by decide⟩).length = 1 ∧
    (NativeUsizeMessage.encode ⟨251,by decide⟩).length = 3 := by decide +kernel

/-- Two zero-valued metadata fields occupy two bytes, not sixteen. -/
theorem minimal_info :
    (NativeScalarBatchWire.infoCodec.encode ⟨⟨0,by decide⟩,⟨0,by decide⟩⟩).length = 2 := by decide +kernel

/-- The same recovered statement used by the security kernel has one equation. -/
theorem actual_count : ScalarEquationWork.equations OracleProgramMachine.step
    (OracleProgram.runPrefix 0 ScalarLifetimeSmoke.repeated HasteBootsSamplerAncestrySmoke.worldZero).run = 1 := by
  change (match ScalarRecoveredReplay.recover ScalarReplaySmoke.target with
    | none => 0
    | some configuration => configuration.view.history.statement.infos.val.length) = 1
  rw [ScalarRecoverySmoke.found]
  rfl

/-- An empty read cannot incur a scalar equation charge even on a valid key. -/
theorem empty_read (state : ClosedByteMachine.State) (log : List NativeTranscript.Observation) :
    ScalarEquationWork.equations
      (fun current => ClosedByteMachineRequest.instruction [] current (.read 0 1 999 0)) (.inl state,log) = 0 := by
  simp [ScalarEquationWork.equations,CausalStreamExposure.firstRead,CausalSeedExposure.request,
    ClosedByteMachineRequest.instruction]

/-- Runtime coin consumption is a real instruction but creates no scalar read. -/
theorem coin_only (tape : PrivateCoinReplay.Tape) (log : List NativeTranscript.Observation) :
    ScalarEquationWork.equations (PrivateCoinByteRequest.command [.coin 0] [] tape)
      (.inl (PrivateCoinByteMachine.initialise [.coin 0] (fun _ => [])),log) = 0 := by
  simp [ScalarEquationWork.equations,CausalStreamExposure.firstRead,CausalSeedExposure.request,
    PrivateCoinByteRequest.command,PrivateCoinByteMachine.initialise,ClosedByteMachine.initialise]

end
end FormalProof4FHE.HasteBoots.ScalarWorkSmoke
