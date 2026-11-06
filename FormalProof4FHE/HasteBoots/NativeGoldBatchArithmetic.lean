module
public import FormalProof4FHE.HasteBoots.RectangularPCSParameters
public import FormalProof4FHE.HasteBoots.NativeGoldBatchFieldProximity
public import FormalProof4FHE.HasteBoots.NativeGoldBatchProfileColumnNative
@[expose] public section

/-! Exact arithmetic identities for the native Goldilocks field and trusted
ordered-column losses. Constructor success derives positive message/code
width; the code width and independent test width remain separate. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchArithmetic
open NativeGoldBatchPcsProgram (Context)
open NativeGoldBlockCode (Tables logSize)
noncomputable section

theorem proximity (ctx : Context) (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1))) :
    NativeGoldBatchFieldProximity.loss ctx primitive = RectangularPCSParameters.proximity NativeFields.goldilocksModulus
      ctx.parameters.width.val (logSize ctx.parameters.code) ctx.parameters.code.messageBlocks.val := by
  have spec := NativeGoldBlockCode.build_spec tables message block blowup ctx.parameters.code constructed
  let : NeZero ctx.parameters.code.blockWidth.val := ⟨by rw [spec.blockEq]; exact spec.dimensions.2.1⟩
  have positive := (NativeGoldBlockCodeMeaning.constructor_dimensions tables message block blowup ctx.parameters.code constructed).1
  unfold NativeGoldBatchFieldProximity.loss
  rw [RectangularPCSParameters.proximity_eq _ _ _ _ _ positive,NativeFields.goldilocks_card]

theorem columns (ctx : Context) (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1))) (radius : ℕ) :
    NativeGoldBatchProfileColumnExposure.loss ctx primitive radius = RectangularPCSParameters.columns
      (logSize ctx.parameters.code) ctx.parameters.code.messageBlocks.val ctx.parameters.queries.val radius := by
  have spec := NativeGoldBlockCode.build_spec tables message block blowup ctx.parameters.code constructed
  let : NeZero ctx.parameters.code.blockWidth.val := ⟨by rw [spec.blockEq]; exact spec.dimensions.2.1⟩
  have positive := (NativeGoldBlockCodeMeaning.constructor_dimensions tables message block blowup ctx.parameters.code constructed).1
  rw [NativeGoldBatchProfileColumnExposure.loss_eq_max,RectangularPCSParameters.columns_eq _ _ _ _ _ _ positive]

theorem combined (ctx : Context) (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1))) (radius : ℕ) :
    NativeGoldBatchFieldProximity.loss ctx primitive + NativeGoldBatchProfileColumnExposure.loss ctx primitive radius =
      RectangularPCSParameters.error NativeFields.goldilocksModulus ctx.parameters.width.val (logSize ctx.parameters.code)
        ctx.parameters.code.messageBlocks.val ctx.parameters.queries.val radius := by
  rw [proximity ctx tables message block blowup constructed primitive,columns ctx tables message block blowup constructed primitive radius]
  rfl
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchArithmetic
