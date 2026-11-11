module
public import FormalProof4FHE.HasteBoots.CalibratedJointWorkBound
@[expose] public section

/-! Decoding radius is a function of the retained full parameters. Sources
and helpers need not share a radius; role calibration proves the same value. -/
namespace FormalProof4FHE.HasteBoots.ParameterDecodingRadius
open NativeBrakedownContext (Parameters)
open NativeGoldBlockCode (Stored logSize)
noncomputable section

def ofParameters (parameters : Parameters Stored) : ℕ :=
  (PCSParameters.distance (logSize parameters.code) parameters.code.messageBlocks.val-1)/3

theorem source_eq (ctx : NativeGoldBatchPcsProgram.Context) (role : NativeBrakedownCalibration.Role)
    (admitted : NativeGoldBatchCalibration.Matches ctx role) :
    ofParameters ctx.parameters = NativeBrakedownCalibration.radius .goldilocks role := by
  rw [ofParameters,admitted.height,admitted.message]
  rfl

theorem helper_eq (ctx : NativeGoldPcsExecution.Context) (role : NativeBrakedownCalibration.Role)
    (admitted : SingleOpeningCalibration.Matches ctx role) :
    ofParameters ctx.parameters = NativeBrakedownCalibration.radius .goldilocks role := by
  rw [ofParameters,admitted.height,admitted.message]
  rfl

theorem source_small (ctx : NativeGoldBatchPcsProgram.Context) (origin : CacheBackedCodeOrigin.Origin ctx)
    (role : NativeBrakedownCalibration.Role) (admitted : NativeGoldBatchCalibration.Matches ctx role) :
    3*ofParameters ctx.parameters < ctx.parameters.code.blocks.val-ctx.parameters.code.messageBlocks.val+1 := by
  have valid := (NativeGoldBatchCalibration.radius_valid ctx origin.tables origin.request.message origin.request.block origin.request.blowup
    (origin.constructedAt ctx rfl) (origin.primitiveAt ctx rfl) role admitted).2
  rw [origin.distanceAt ctx rfl] at valid
  rwa [source_eq ctx role admitted]

theorem helper_small (ctx : NativeGoldPcsExecution.Context) (origin : CacheBackedSingleOpening.Origin ctx)
    (role : NativeBrakedownCalibration.Role) (admitted : SingleOpeningCalibration.Matches ctx role) :
    3*ofParameters ctx.parameters < ctx.parameters.code.blocks.val-ctx.parameters.code.messageBlocks.val+1 := by
  have valid := (SingleOpeningCalibration.radius_valid ctx origin role admitted).2
  rw [SingleOpeningConstructorBounds.distance origin] at valid
  rwa [helper_eq ctx role admitted]

end
end FormalProof4FHE.HasteBoots.ParameterDecodingRadius
