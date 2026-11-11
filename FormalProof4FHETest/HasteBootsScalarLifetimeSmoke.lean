module
import all FormalProof4FHE.HasteBoots.AllocatedJointIdentityBound
import all FormalProof4FHETest.HasteBootsFactorFiberSmoke
import all FormalProof4FHETest.HasteBootsScalarRecoverySmoke

namespace FormalProof4FHE.HasteBoots.ScalarLifetimeSmoke
open OracleProgram (Program runPrefix)
open HasteBootsSamplerAncestrySmoke (worldZero)
noncomputable section

/-- The empty read before a hash and far-offset read carries no scalar risk. -/
theorem empty_read : ScalarPositionKernel.charge FactorFiberSmoke.program 1 worldZero = 0 := by rfl

/-- A genuine first far-offset read is selected, but a malformed scalar key
cannot create an equation-count charge. -/
theorem malformed_first : ScalarPositionKernel.key FactorFiberSmoke.program 3 worldZero = some FactorFiberSmoke.input ∧
    ScalarPositionKernel.charge FactorFiberSmoke.program 3 worldZero = 0 := by
  constructor
  · exact FactorFiberSmoke.first.selected
  · unfold ScalarPositionKernel.charge ScalarPositionKernel.score
    rw [show CausalStreamExposure.firstRead OracleProgramMachine.step (runPrefix 3 FactorFiberSmoke.program worldZero).run =
      some FactorFiberSmoke.input from FactorFiberSmoke.first.selected]
    have decoded : TranscriptFrame.decodeAll FactorFiberSmoke.input = none := by
      cases parsed : TranscriptFrame.decodeAll FactorFiberSmoke.input with
      | none => rfl
      | some frames =>
        have bytes := (TranscriptFrame.decodeAll_sound _ frames parsed).2
        exfalso
        cases frames with
        | nil => have impossible := congrArg List.head? bytes; cases impossible
        | cons frame tail =>
          have first := congrArg List.head? bytes
          change some (17 : InputIndexedOracle.Byte) = some (⟨frame.kind.val,by omega⟩ : InputIndexedOracle.Byte) at first
          have equal := congrArg Fin.val (Option.some.inj first)
          change (17 : ℕ) = frame.kind.val at equal
          have inside := frame.kind.isLt
          omega
    simp only [ScalarRecoveredReplay.recover,ScalarTranscriptPrefix.parse,ScalarChallengeInputView.parse,decoded,Option.bind_none]

theorem stopped_suffix (later : ℕ) : ScalarPositionKernel.charge FactorFiberSmoke.program (5+later) worldZero = 0 :=
  ScalarPositionKernel.charge_after_finished FactorFiberSmoke.program 5 later worldZero () (by rfl)

def repeated : Program Unit := .read ScalarReplaySmoke.target 999 1 (fun _ => .read ScalarReplaySmoke.target 0 1 (fun _ => .pure ()))

/-- The native recovered statement, rather than a separately chosen bound,
selects the first-read equation count. -/
theorem actual_metadata : ScalarPositionKernel.charge repeated 0 worldZero = (4 : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) := by
  change (match ScalarRecoveredReplay.recover ScalarReplaySmoke.target with
    | none => (0 : ENNReal)
    | some configuration => (configuration.view.history.statement.infos.val.length : ENNReal) *
      ((4 : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ))) = _
  rw [ScalarRecoverySmoke.found]
  simp [ScalarRecoverySmoke.recovered,ScalarRecoverySmoke.expectedView,ScalarRecoverySmoke.history,ScalarReplaySmoke.statement]

/-- A later read of different bytes from the same valid scalar input is not
charged again; this includes native collector retries on that stream. -/
theorem same_key_later : ScalarPositionKernel.charge repeated 1 worldZero = 0 := by
  apply ScalarPositionKernel.charge_seen repeated 1 worldZero ScalarReplaySmoke.target 0 1 (fun _ => .pure ()) rfl
  change CausalStreamExposure.seen [NativeTranscript.Observation.output ScalarReplaySmoke.target 999
    (InputIndexedOracle.bytes worldZero ScalarReplaySmoke.target 999 1)] ScalarReplaySmoke.target = true
  simp [CausalStreamExposure.seen,CausalStreamExposure.touches,InputIndexedOracle.bytes_length]

end
end FormalProof4FHE.HasteBoots.ScalarLifetimeSmoke
