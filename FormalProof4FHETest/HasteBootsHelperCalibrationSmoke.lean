module
import all FormalProof4FHE.HasteBoots.CalibratedHelperSourceLedger

namespace FormalProof4FHE.HasteBoots.HelperCalibrationSmoke
noncomputable section

/-- The original-size Goldilocks helper certificate rejects width two. -/
theorem width_two_rejected (ctx : NativeGoldPcsExecution.Context) (width : ctx.parameters.width.val = 2) :
    ¬SingleOpeningCalibration.Matches ctx .helper := by
  intro admitted
  have required := admitted.width
  change ctx.parameters.width.val = 3 at required
  omega

/-- A smaller proof quota cannot be admitted by the trusted role certificate. -/
theorem short_quota_rejected (ctx : NativeGoldPcsExecution.Context) (quota : ctx.parameters.queries.val = 543) :
    ¬SingleOpeningCalibration.Matches ctx .helper := by
  intro admitted
  have required := admitted.queries
  omega

/-- Consuming a private byte emits no field/column request and creates no
helper exposure risk, even though its instruction has positive work. -/
theorem coin_no_exposure (dummy : NativeRootMessage.Digest) (ctx : NativeGoldPcsExecution.Context)
    (origin : CacheBackedSingleOpening.Origin ctx) (role : NativeBrakedownCalibration.Role)
    (tape : PrivateCoinReplay.Tape) (log : List NativeTranscript.Observation) :
    PrivateCoinHelperGoldRisk.risk [.coin 0] [] tape dummy ctx origin.primitive role
      (PrivateCoinByteFixed.packet (PrivateCoinByteMachine.initialise [.coin 0] (fun _ => [])) log) = 0 := by
  apply PrivateCoinHelperGoldRisk.risk_no_read
  rfl

end
end FormalProof4FHE.HasteBoots.HelperCalibrationSmoke
