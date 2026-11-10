module
public import FormalProof4FHE.HasteBoots.CacheBackedBatchSoundness
@[expose] public section

/-! Provenance records only a completed reachable constructor and the retained
code identity. Code correctness, capacity, primitive roots and distance are
derived rather than stored as caller-supplied security certificates. -/
namespace FormalProof4FHE.HasteBoots.CacheBackedCodeOrigin
open NativeGoldBatchPcsProgram (Context)
open NativeGoldBlockCodeProgram (Request Config Completed)
open NativeGoldBlockCode (logSize)
open NativeGoldBatchResponseMeaning (Domain)
open NativeFieldRepresentation (goldValue)
open NativeFields (Goldilocks)
noncomputable section

structure Origin (ctx : Context) where
  request : Request
  config : Config
  reachable : NativeGoldBlockCodeProgram.Reachable request config
  result : Completed
  finished : config.phase = .done result
  retained : result.code = ctx.parameters.code

namespace Origin
variable {ctx : Context} (origin : Origin ctx)
include origin

theorem retainedAt (candidate : Context) (same : candidate.parameters = ctx.parameters) :
    origin.result.code = candidate.parameters.code :=
  origin.retained.trans (congrArg (fun parameters => parameters.code) same).symm

def tables := CacheBackedBatchSoundness.constructorTables origin.request origin.config origin.reachable

theorem constructedAt (candidate : Context) (same : candidate.parameters = ctx.parameters) :
    NativeGoldBlockCode.build origin.tables origin.request.message origin.request.block origin.request.blowup = .ok candidate.parameters.code :=
  CacheBackedBatchSoundness.constructed candidate origin.request origin.config origin.reachable origin.result origin.finished
    (origin.retainedAt candidate same)

theorem primitiveAt (candidate : Context) (same : candidate.parameters = ctx.parameters) :
    IsPrimitiveRoot (goldValue candidate.parameters.code.domainRoot) (2 ^ (logSize candidate.parameters.code + 1)) :=
  CacheBackedBatchSoundness.primitive candidate origin.request origin.config origin.reachable origin.result origin.finished
    (origin.retainedAt candidate same)

theorem capacityAt (candidate : Context) (same : candidate.parameters = ctx.parameters) :
    candidate.parameters.code.messageLength.val ≤ candidate.parameters.code.messageBlocks.val * candidate.parameters.code.blockWidth.val :=
  (NativeGoldBlockCodeMeaning.constructor_dimensions origin.tables origin.request.message origin.request.block origin.request.blowup
    candidate.parameters.code (origin.constructedAt candidate same)).2.2.1

theorem distanceAt (candidate : Context) (same : candidate.parameters = ctx.parameters) :
    Code.minDist (BlockCode.code (Domain candidate (origin.primitiveAt candidate same))
      candidate.parameters.code.messageBlocks.val candidate.parameters.code.blockWidth.val :
      Set (Fin (2 ^ logSize candidate.parameters.code) → Fin candidate.parameters.code.blockWidth.val → Goldilocks)) =
      candidate.parameters.code.blocks.val - candidate.parameters.code.messageBlocks.val + 1 :=
  CacheBackedBatchSoundness.distance candidate origin.request origin.config origin.reachable origin.result origin.finished
    (origin.retainedAt candidate same)

theorem radius_fits (radius : ℕ)
    (small : 3 * radius < ctx.parameters.code.blocks.val - ctx.parameters.code.messageBlocks.val + 1) :
    radius < Fintype.card Goldilocks := by
  have constructed := origin.constructedAt ctx rfl
  have sizes := NativeGoldBlockCodeMeaning.constructor_dimensions origin.tables origin.request.message origin.request.block origin.request.blowup ctx.parameters.code constructed
  have blocks := (NativeGoldBlockCodeMeaning.constructor_log origin.tables origin.request.message origin.request.block origin.request.blowup ctx.parameters.code constructed).2
  have cardinal : ctx.parameters.code.blocks.val ≤ Fintype.card Goldilocks := by
    have embedded := Fintype.card_le_of_injective (Domain ctx (origin.primitiveAt ctx rfl)) (Domain ctx (origin.primitiveAt ctx rfl)).injective
    simpa only [Fintype.card_fin,← blocks] using embedded
  have positive := sizes.1
  omega

end Origin
end
end FormalProof4FHE.HasteBoots.CacheBackedCodeOrigin
