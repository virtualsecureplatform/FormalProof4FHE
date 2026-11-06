module
import all FormalProof4FHE.HasteBoots.NativeGoldBatchCalibration
import all FormalProof4FHE.HasteBoots.NativeNTTRoots
import all FormalProof4FHETest.HasteBootsProfileColumnSmoke
open FormalProof4FHE.HasteBoots
namespace HasteBootsCalibrationSmoke
noncomputable section
open NativeBrakedownCalibration (Field Role)
example : NativeBrakedownCalibration.polynomialSize = 1024 ∧ NativeBrakedownCalibration.lweDimension = 728 := by decide +kernel
example : NativeBrakedownCalibration.roleVariables .goldilocks .helper = 21 ∧
    NativeBrakedownCalibration.testWidth .goldilocks .helper = 3 ∧ NativeBrakedownCalibration.codeWidth .goldilocks = 4 := by decide +kernel
example : NativeBrakedownCalibration.roleVariables .babyBear .helper = 21 ∧
    NativeBrakedownCalibration.testWidth .babyBear .helper = 6 ∧ NativeBrakedownCalibration.codeWidth .babyBear = 8 := by decide +kernel
example (role : Role) : NativeBrakedownCalibration.proximity .babyBear role ≤ 1/2^137 :=
  NativeBrakedownCalibration.proximity_babyBear role
example (field : Field) : (2 : NNReal)^128 * (64*NativeBrakedownCalibration.totalError field 544) ≤ 17/32 :=
  NativeBrakedownCalibration.shape_allowance field 544 (by decide)
example (field : Field) : (2 : NNReal)^128 * (64*NativeBrakedownCalibration.roleError field
    (fun role => match role with | .source => 544 | .helper => 600 | .finalSource => 1024 | .finalHelper => 545)) ≤ 17/32 :=
  NativeBrakedownCalibration.role_shape_allowance field _ (by intro role; cases role <;> decide)

-- Scalar-extension arithmetic is deliberately not used for the base-field matrix.
example : RectangularPCSParameters.finiteProximity 101 3 5 1 = (32/101 : NNReal)^3 := rfl
example : RectangularPCSParameters.finiteProximity 101 3 5 1 ≠ (32 : NNReal)/101^3 := by
  intro equal
  have cast := congrArg (fun value : NNReal => (value : ℝ)) equal
  norm_num [RectangularPCSParameters.finiteProximity,PCSParameters.distance] at cast

open HasteBootsBatchMeaningSmoke (usize)
def root : NativeGoldSolinas.Word := ⟨455906449640507599,by decide +kernel⟩
def tables : NativeGoldBlockCode.Tables := ⟨fun _ => true,fun _ => true,fun _ => some root⟩
def code : NativeGoldBlockCode.Stored :=
  ⟨usize 2048,usize 4,usize 512,usize 1024,NativeBrakedownContext.modulus,NativeGoldSolinas.raw root⟩
def ctx : NativeGoldBatchPcsProgram.Context :=
  {HasteBootsBatchMeaningSmoke.ctx with tables := tables,parameters := ⟨usize 21,usize 3,usize 10,usize 544,code⟩}
theorem constructed : NativeGoldBlockCode.build tables (usize 2048) (usize 4) (usize 2) = .ok ctx.parameters.code := by decide +kernel
theorem primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot)
    (2^(NativeGoldBlockCode.logSize ctx.parameters.code+1)) := NativeNTTRoots.goldilocksMain_primitive

theorem compatible : NativeGoldBatchCalibration.Matches ctx .helper := by
  constructor <;> decide +kernel
-- Constructor/arithmetic fixture only: this does not assert a complete PBS run.
example : NativeGoldBatchFieldProximity.loss ctx primitive +
    NativeGoldBatchProfileColumnExposure.loss ctx primitive (NativeBrakedownCalibration.radius .goldilocks .helper) ≤ (17 : ENNReal)/2^141 :=
  NativeGoldBatchCalibration.loss_bound ctx tables (usize 2048) (usize 4) (usize 2) constructed primitive .helper compatible
example : NativeBrakedownCalibration.radius .goldilocks .helper < Fintype.card NativeFields.Goldilocks ∧
    3*NativeBrakedownCalibration.radius .goldilocks .helper < Code.minDist (BlockCode.code (NativeGoldBatchResponseMeaning.Domain ctx primitive)
      ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
        Set (NativeGoldBatchConcreteColumnFamily.Position ctx → NativeGoldBatchConcreteColumnFamily.Symbol ctx)) :=
  NativeGoldBatchCalibration.radius_valid ctx tables (usize 2048) (usize 4) (usize 2) constructed primitive .helper compatible
example {S A : Type} (step : S → OracleMachine.Command S A) (packet : NativeIndexExposureRisk.Packet S A) :
    NativeGoldBatchFieldProximity.risk HasteBootsBatchMeaningSmoke.root ctx primitive (NativeBrakedownCalibration.radius .goldilocks .helper) step packet +
      NativeGoldBatchProfileColumnExposure.risk HasteBootsBatchMeaningSmoke.root ctx primitive step packet
        (NativeBrakedownCalibration.radius .goldilocks .helper) ≤ (17 : ENNReal)/2^141 :=
  NativeGoldBatchCalibration.risk_bound HasteBootsBatchMeaningSmoke.root ctx tables (usize 2048) (usize 4) (usize 2)
    constructed primitive .helper compatible step packet

end
end HasteBootsCalibrationSmoke
