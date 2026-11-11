module
public import FormalProof4FHE.HasteBoots.SingleOpeningLifetimeMeasurable
@[expose] public section

/-! Numerical code/radius facts follow from the retained single-opening
constructor. Transport across equal full parameters keeps its actual request
and configuration, rather than choosing a different matching constructor. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningConstructorBounds
open NativeGoldPcsExecution (Context)
open CacheBackedSingleOpening (Origin)
open NativeGoldBlockCode (logSize)
open SingleOpeningConcreteColumnFamily (Domain Position Symbol)
open NativeFields (Goldilocks)
noncomputable section
variable {ctx : Context} (origin : Origin ctx)
include origin

def transport (candidate : Context) (same : candidate.parameters = ctx.parameters) : Origin candidate where
  request := origin.request
  config := origin.config
  reachable := origin.reachable
  result := origin.result
  finished := origin.finished
  retained := origin.retained.trans (congrArg (fun parameters => parameters.code) same).symm

theorem transport_data (candidate : Context) (same : candidate.parameters = ctx.parameters) :
    (transport origin candidate same).request = origin.request ∧ (transport origin candidate same).config = origin.config := ⟨rfl,rfl⟩

theorem distance : Code.minDist (BlockCode.code (Domain ctx origin.primitive)
      ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val : Set (Position ctx → Symbol ctx)) =
    ctx.parameters.code.blocks.val - ctx.parameters.code.messageBlocks.val + 1 := by
  have spec := NativeGoldBlockCode.build_spec origin.tables origin.request.message origin.request.block origin.request.blowup ctx.parameters.code origin.constructed
  have sizes := NativeGoldBlockCodeMeaning.constructor_dimensions origin.tables origin.request.message origin.request.block origin.request.blowup ctx.parameters.code origin.constructed
  have logs := (NativeGoldBlockCodeMeaning.constructor_log origin.tables origin.request.message origin.request.block origin.request.blowup ctx.parameters.code origin.constructed).2
  let : NeZero ctx.parameters.code.blockWidth.val := ⟨by rw [spec.blockEq]; exact spec.dimensions.2.1⟩
  have exactDistance := BlockCode.minDist (Domain ctx origin.primitive) ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val sizes.1
  simpa only [Fintype.card_fin,← logs] using exactDistance

theorem radius_fits (radius : ℕ)
    (small : 3*radius < ctx.parameters.code.blocks.val-ctx.parameters.code.messageBlocks.val+1) : radius < Fintype.card Goldilocks := by
  have sizes := NativeGoldBlockCodeMeaning.constructor_dimensions origin.tables origin.request.message origin.request.block origin.request.blowup ctx.parameters.code origin.constructed
  have blocks := (NativeGoldBlockCodeMeaning.constructor_log origin.tables origin.request.message origin.request.block origin.request.blowup ctx.parameters.code origin.constructed).2
  have cardinal : ctx.parameters.code.blocks.val ≤ Fintype.card Goldilocks := by
    have embedded := Fintype.card_le_of_injective (Domain ctx origin.primitive) (Domain ctx origin.primitive).injective
    simpa only [Fintype.card_fin,← blocks] using embedded
  have positive := sizes.1
  omega

theorem prelude_bound {S A : Type} (Memory : Type) (dummy : NativeRootMessage.Digest) (radius : ℕ)
    (width : 3 ≤ ctx.parameters.width.val) (prelude : OracleProgram.Program S) (step : S → OracleMachine.Command S A)
    (small : 3*radius < ctx.parameters.code.blocks.val-ctx.parameters.code.messageBlocks.val+1) :
    InputIndexedOracle.law {world | SingleOpeningLifetimeSoundness.Failure Memory dummy ctx radius (OracleProgram.run prelude) id step world} ≤
      (⨆ fuel : ℕ, NativeRootFamilyLifetime.prefixCharge dummy (.pure prelude) (OracleMachinePrelude.prepend step) fuel) +
        SingleOpeningLifetimeSoundness.exposureCharge (SingleOpeningLifetimeSoundness.clean prelude) id dummy ctx origin radius
          (OracleMachinePrelude.prepend step) := by
  apply SingleOpeningLifetimeSoundness.prelude_bound Memory dummy ctx origin radius width prelude step (radius_fits origin radius small)
  rw [distance origin]
  exact small

end
end FormalProof4FHE.HasteBoots.SingleOpeningConstructorBounds
