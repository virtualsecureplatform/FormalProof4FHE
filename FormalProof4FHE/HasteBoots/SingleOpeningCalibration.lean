module
public import FormalProof4FHE.HasteBoots.SingleOpeningConstructorBounds
public import FormalProof4FHE.HasteBoots.NativeGoldBatchCalibration
@[expose] public section

/-! Numerical field/column calibration for the original single-opening
helper, using its retained constructor and full parameter dimensions. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningCalibration
open NativeGoldPcsExecution (Context)
open NativeGoldBlockCode (logSize)
open CacheBackedSingleOpening (Origin)
open NativeBrakedownCalibration (Role height message testWidth radius)
noncomputable section

structure Matches (ctx : Context) (role : Role) : Prop where
  width : ctx.parameters.width.val = testWidth .goldilocks role
  height : logSize ctx.parameters.code = height .goldilocks role
  message : ctx.parameters.code.messageBlocks.val = message .goldilocks role
  queries : 544 ≤ ctx.parameters.queries.val

theorem proximity (ctx : Context) (origin : Origin ctx)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1))) :
    SingleOpeningFieldProximity.loss ctx primitive = RectangularPCSParameters.proximity NativeFields.goldilocksModulus
      ctx.parameters.width.val (logSize ctx.parameters.code) ctx.parameters.code.messageBlocks.val := by
  have spec := NativeGoldBlockCode.build_spec origin.tables origin.request.message origin.request.block origin.request.blowup ctx.parameters.code origin.constructed
  let : NeZero ctx.parameters.code.blockWidth.val := ⟨by rw [spec.blockEq]; exact spec.dimensions.2.1⟩
  have positive := (NativeGoldBlockCodeMeaning.constructor_dimensions origin.tables origin.request.message origin.request.block origin.request.blowup ctx.parameters.code origin.constructed).1
  unfold SingleOpeningFieldProximity.loss
  rw [RectangularPCSParameters.proximity_eq _ _ _ _ _ positive,NativeFields.goldilocks_card]

theorem columns (ctx : Context) (origin : Origin ctx)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1))) (radius : ℕ) :
    SingleOpeningProfileColumnExposure.loss ctx primitive radius = RectangularPCSParameters.columns
      (logSize ctx.parameters.code) ctx.parameters.code.messageBlocks.val ctx.parameters.queries.val radius := by
  have spec := NativeGoldBlockCode.build_spec origin.tables origin.request.message origin.request.block origin.request.blowup ctx.parameters.code origin.constructed
  let : NeZero ctx.parameters.code.blockWidth.val := ⟨by rw [spec.blockEq]; exact spec.dimensions.2.1⟩
  have positive := (NativeGoldBlockCodeMeaning.constructor_dimensions origin.tables origin.request.message origin.request.block origin.request.blowup ctx.parameters.code origin.constructed).1
  rw [SingleOpeningProfileColumnExposure.loss_eq_max,RectangularPCSParameters.columns_eq _ _ _ _ _ _ positive]

theorem combined (ctx : Context) (origin : Origin ctx)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1))) (radius : ℕ) :
    SingleOpeningFieldProximity.loss ctx primitive + SingleOpeningProfileColumnExposure.loss ctx primitive radius =
      RectangularPCSParameters.error NativeFields.goldilocksModulus ctx.parameters.width.val (logSize ctx.parameters.code)
        ctx.parameters.code.messageBlocks.val ctx.parameters.queries.val radius := by
  rw [proximity ctx origin primitive,columns ctx origin primitive radius]
  rfl

theorem loss_bound (ctx : Context) (origin : Origin ctx) (role : Role) (compatible : Matches ctx role) :
    SingleOpeningFieldProximity.loss ctx origin.primitive +
      SingleOpeningProfileColumnExposure.loss ctx origin.primitive (radius .goldilocks role) ≤ (17 : ENNReal)/2^141 := by
  rw [combined ctx origin origin.primitive,compatible.width,compatible.height,compatible.message]
  exact NativeBrakedownCalibration.error_ennreal_le .goldilocks role ctx.parameters.queries.val compatible.queries

theorem radius_valid (ctx : Context) (origin : Origin ctx) (role : Role) (compatible : Matches ctx role) :
    radius .goldilocks role < Fintype.card NativeFields.Goldilocks ∧
      3*radius .goldilocks role < Code.minDist (BlockCode.code (SingleOpeningConcreteColumnFamily.Domain ctx origin.primitive)
        ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
          Set (SingleOpeningConcreteColumnFamily.Position ctx → SingleOpeningConcreteColumnFamily.Symbol ctx)) := by
  have blocks := (NativeGoldBlockCodeMeaning.constructor_log origin.tables origin.request.message origin.request.block origin.request.blowup ctx.parameters.code origin.constructed).2
  rw [SingleOpeningConstructorBounds.distance origin,blocks,NativeFields.goldilocks_card,compatible.height,compatible.message]
  exact NativeBrakedownCalibration.radius_valid .goldilocks role

theorem field_risk_le_loss {S A : Type} (dummy : NativeRootMessage.Digest) (ctx : Context)
    (origin : Origin ctx) (r : ℕ) (step : S → OracleMachine.Command S A) (packet : NativeIndexExposureRisk.Packet S A) :
    SingleOpeningFieldProximity.risk dummy ctx origin.primitive r step packet ≤ SingleOpeningFieldProximity.loss ctx origin.primitive := by
  cases selected : SingleOpeningFieldExposure.select step packet with
  | none => simp only [SingleOpeningFieldProximity.risk,selected]; exact zero_le
  | some field =>
    simp only [SingleOpeningFieldProximity.risk,selected,SingleOpeningFieldProximity.score]
    split
    · exact le_rfl
    · exact zero_le

theorem risk_bound {S A : Type} (dummy : NativeRootMessage.Digest) (ctx : Context) (origin : Origin ctx)
    (role : Role) (compatible : Matches ctx role) (step : S → OracleMachine.Command S A) (packet : NativeIndexExposureRisk.Packet S A) :
    SingleOpeningFieldProximity.risk dummy ctx origin.primitive (radius .goldilocks role) step packet +
      SingleOpeningProfileColumnExposure.risk dummy ctx origin.primitive step packet (radius .goldilocks role) ≤ (17 : ENNReal)/2^141 :=
  (add_le_add (field_risk_le_loss dummy ctx origin _ step packet)
    (SingleOpeningProfileColumnExposure.risk_le_loss dummy ctx origin.primitive step packet _)).trans
      (loss_bound ctx origin role compatible)

end
end FormalProof4FHE.HasteBoots.SingleOpeningCalibration
