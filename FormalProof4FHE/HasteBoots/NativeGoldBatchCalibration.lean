module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchLifetimeMeasurable
public import FormalProof4FHE.HasteBoots.NativeGoldBatchArithmetic
public import FormalProof4FHE.HasteBoots.NativeBrakedownCalibration
@[expose] public section

/-! Constructor-backed native Goldilocks losses inherit the exact numerical
certificate when their public dimensions match an original-size role. These
are analysis conditions on trusted parameters, not verifier proof inputs.
Backend/profile construction refinement and physical work remain separate. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchCalibration
open NativeGoldBatchPcsProgram (Context)
open NativeGoldBlockCode (Tables logSize)
open NativeBrakedownCalibration (Role height message testWidth radius)
noncomputable section

structure Matches (ctx : Context) (role : Role) : Prop where
  width : ctx.parameters.width.val = testWidth .goldilocks role
  height : logSize ctx.parameters.code = height .goldilocks role
  message : ctx.parameters.code.messageBlocks.val = message .goldilocks role
  queries : 544 ≤ ctx.parameters.queries.val

theorem loss_bound (ctx : Context) (tables : Tables) (scalarMessage block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables scalarMessage block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (role : Role) (compatible : Matches ctx role) :
    NativeGoldBatchFieldProximity.loss ctx primitive +
      NativeGoldBatchProfileColumnExposure.loss ctx primitive (radius .goldilocks role) ≤ (17 : ENNReal)/2^141 := by
  rw [NativeGoldBatchArithmetic.combined ctx tables scalarMessage block blowup constructed primitive,
    compatible.width,compatible.height,compatible.message]
  exact NativeBrakedownCalibration.error_ennreal_le .goldilocks role ctx.parameters.queries.val compatible.queries

theorem radius_valid (ctx : Context) (tables : Tables) (scalarMessage block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables scalarMessage block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (role : Role) (compatible : Matches ctx role) :
    radius .goldilocks role < Fintype.card NativeFields.Goldilocks ∧
      3*radius .goldilocks role < Code.minDist (BlockCode.code (NativeGoldBatchResponseMeaning.Domain ctx primitive)
        ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
          Set (NativeGoldBatchConcreteColumnFamily.Position ctx → NativeGoldBatchConcreteColumnFamily.Symbol ctx)) := by
  have spec := NativeGoldBlockCode.build_spec tables scalarMessage block blowup ctx.parameters.code constructed
  let : NeZero ctx.parameters.code.blockWidth.val := ⟨by rw [spec.blockEq]; exact spec.dimensions.2.1⟩
  have positive := (NativeGoldBlockCodeMeaning.constructor_dimensions tables scalarMessage block blowup ctx.parameters.code constructed).1
  rw [NativeFields.goldilocks_card,BlockCode.minDist _ _ _ positive,Fintype.card_fin,compatible.height,compatible.message]
  exact NativeBrakedownCalibration.radius_valid .goldilocks role
theorem field_risk_le_loss {S A : Type} (dummy : NativeRootMessage.Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (r : ℕ) (step : S → OracleMachine.Command S A) (packet : NativeIndexExposureRisk.Packet S A) :
    NativeGoldBatchFieldProximity.risk dummy ctx primitive r step packet ≤ NativeGoldBatchFieldProximity.loss ctx primitive := by
  cases selected : NativeGoldBatchFieldExposure.select step packet with
  | none => simp only [NativeGoldBatchFieldProximity.risk,selected]; exact zero_le
  | some field =>
    simp only [NativeGoldBatchFieldProximity.risk,selected,NativeGoldBatchFieldProximity.score]
    split
    · exact le_rfl
    · exact zero_le

theorem risk_bound {S A : Type} (dummy : NativeRootMessage.Digest) (ctx : Context)
    (tables : Tables) (scalarMessage block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables scalarMessage block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (role : Role) (compatible : Matches ctx role) (step : S → OracleMachine.Command S A) (packet : NativeIndexExposureRisk.Packet S A) :
    NativeGoldBatchFieldProximity.risk dummy ctx primitive (radius .goldilocks role) step packet +
      NativeGoldBatchProfileColumnExposure.risk dummy ctx primitive step packet (radius .goldilocks role) ≤ (17 : ENNReal)/2^141 :=
  (add_le_add (field_risk_le_loss dummy ctx primitive _ step packet)
    (NativeGoldBatchProfileColumnExposure.risk_le_loss dummy ctx primitive step packet _)).trans
      (loss_bound ctx tables scalarMessage block blowup constructed primitive role compatible)

/-- The concrete public role dimensions discharge the lifetime theorem's
width and decoding-radius obligations. Hash/receipt hazards and expected
exposure charges are retained; this is not physical attacker-work coupling. -/
theorem prelude_bound {S A : Type} (Memory : Type) (dummy : NativeRootMessage.Digest) (ctx : Context)
    (tables : Tables) (scalarMessage block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables scalarMessage block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (role : Role) (compatible : Matches ctx role) (prelude : OracleProgram.Program S) (step : S → OracleMachine.Command S A) :
    InputIndexedOracle.law {world | NativeGoldBatchLifetimeSoundness.Failure Memory dummy ctx (radius .goldilocks role)
      (OracleProgram.run prelude) id step world} ≤
      (⨆ fuel : ℕ, NativeRootFamilyLifetime.prefixCharge dummy (.pure prelude) (OracleMachinePrelude.prepend step) fuel) +
        NativeGoldBatchLifetimeSoundness.exposureCharge (NativeGoldBatchLifetimeSoundness.clean prelude) id dummy ctx primitive
          (radius .goldilocks role) (OracleMachinePrelude.prepend step) := by
  have dimensions := radius_valid ctx tables scalarMessage block blowup constructed primitive role compatible
  have width : 3 ≤ ctx.parameters.width.val := by
    rw [compatible.width]
    cases role <;> decide +kernel
  exact NativeGoldBatchLifetimeSoundness.prelude_bound Memory dummy ctx primitive tables scalarMessage block blowup constructed
    (radius .goldilocks role) width prelude step dimensions.1 dimensions.2

end
end FormalProof4FHE.HasteBoots.NativeGoldBatchCalibration
