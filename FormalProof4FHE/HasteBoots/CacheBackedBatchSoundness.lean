module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchInteractiveSoundness
public import FormalProof4FHE.HasteBoots.LookupPCSBackendCode
@[expose] public section

/-! Native batch finishing soundness with constructor and primitive-root facts
derived from actual completed cache-backed construction. Packing/test width
and code-block width remain independent. This is the shared ideal interactive
experiment; production Fiat--Shamir and physical refinement remain open. -/
namespace FormalProof4FHE.HasteBoots.CacheBackedBatchSoundness
open NativeGoldBatchPcsProgram (Context Prepared)
open NativeGoldBlockCodeProgram (Request Config Completed)
open NativeGoldBlockCode (logSize)
open NativeGoldBatchResponseMeaning (Domain)
open NativeGoldBatchRectangularData (Query Group groupOf left right claimed)
open NativeGoldBatchRectangularWeights (Row)
open NativeGoldBatchInteractiveSoundness (messages testMessages)
open NativeFieldRepresentation (goldValue)
open NativeFields (Goldilocks)
open OracleProgram (run)
open OracleComp
noncomputable section

def constructorTables (request : Request) (config : Config)
    (reachable : NativeGoldBlockCodeProgram.Reachable request config) : NativeGoldBlockCode.Tables :=
  NativeGoldBlockCodeBackend.observations config.cache (NativeGoldBlockCodeProgram.reachable_good request config reachable).1

theorem constructed (ctx : Context) (request : Request) (config : Config)
    (reachable : NativeGoldBlockCodeProgram.Reachable request config)
    (result : Completed) (finished : config.phase = .done result) (retained : result.code = ctx.parameters.code) :
    NativeGoldBlockCode.build (constructorTables request config reachable) request.message request.block request.blowup = .ok ctx.parameters.code := by
  have built := NativeGoldBlockCodeBackend.completed_build request config reachable result finished
  rw [retained] at built
  exact built

theorem primitive (ctx : Context) (request : Request) (config : Config)
    (reachable : NativeGoldBlockCodeProgram.Reachable request config)
    (result : Completed) (finished : config.phase = .done result) (retained : result.code = ctx.parameters.code) :
    IsPrimitiveRoot (goldValue ctx.parameters.code.domainRoot) (2 ^ (logSize ctx.parameters.code + 1)) := by
  rw [← retained]
  exact NativeGoldBlockCodeBackend.completed_primitive request config reachable result finished

theorem distance (ctx : Context) (request : Request) (config : Config)
    (reachable : NativeGoldBlockCodeProgram.Reachable request config)
    (result : Completed) (finished : config.phase = .done result) (retained : result.code = ctx.parameters.code) :
    Code.minDist (BlockCode.code (Domain ctx (primitive ctx request config reachable result finished retained))
      ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
      Set (Fin (2 ^ logSize ctx.parameters.code) → Fin ctx.parameters.code.blockWidth.val → Goldilocks)) =
      ctx.parameters.code.blocks.val - ctx.parameters.code.messageBlocks.val + 1 := by
  have built := constructed ctx request config reachable result finished retained
  have spec := NativeGoldBlockCode.build_spec _ request.message request.block request.blowup ctx.parameters.code built
  have sizes := NativeGoldBlockCodeMeaning.constructor_dimensions _ request.message request.block request.blowup ctx.parameters.code built
  have logs := (NativeGoldBlockCodeMeaning.constructor_log _ request.message request.block request.blowup ctx.parameters.code built).2
  let : NeZero ctx.parameters.code.blockWidth.val := ⟨by rw [spec.blockEq]; exact spec.dimensions.2.1⟩
  have exactDistance := BlockCode.minDist (Domain ctx (primitive ctx request config reachable result finished retained))
    ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val sizes.1
  simpa only [Fintype.card_fin,← logs] using exactDistance

theorem soundness_bound {Response : Type} (ctx : Context) (world : InputIndexedOracle.World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (request : Request) (config : Config) (reachable : NativeGoldBlockCodeProgram.Reachable request config)
    (result : Completed) (finished : config.phase = .done result) (retained : result.code = ctx.parameters.code)
    (radius : ℕ)
    (word : Fin (2^(logSize ctx.parameters.code)) → Row ctx → Fin ctx.parameters.code.blockWidth.val → Goldilocks)
    (respond : (Fin ctx.parameters.width.val → Row ctx → Goldilocks) → ProbComp Response)
    (opening : Response → NativeGoldBatchOpening.Opening)
    [SampleableType (Row ctx → Goldilocks)]
    [SampleableType (Fin ctx.parameters.width.val → Row ctx → Goldilocks)]
    [SampleableType (Fin ctx.parameters.queries.val → Fin (2^(logSize ctx.parameters.code)))]
    [SampleableType (Submodule.span Goldilocks (Set.range (RectangularBaseProximity.stack word)))]
    [SampleableType (ModuleCodeProximity.toSpan (F := Goldilocks) (RectangularBaseProximity.stack word)).toAddMonoidHom.ker]
    (small : 3*radius < (ctx.parameters.code.blocks.val - ctx.parameters.code.messageBlocks.val + 1)) :
    Pr{let pair ← RectangularOpeningKernel.experiment (F := Goldilocks) (Row := Row ctx) (Position := Fin (2^(logSize ctx.parameters.code))) ctx.parameters.width.val ctx.parameters.queries.val respond}[
      (∃ query : Query work, claimed ctx work query ≠ matrixEvaluation
        (NativeGoldBatchRectangularWeights.left ctx world work prepared query) (right ctx world work prepared query)
        (RectangularMatrixOpeningKernel.extract (Domain ctx (primitive ctx request config reachable result finished retained))
          (NativeGoldBlockCodeMeaning.constructor_dimensions (constructorTables request config reachable) request.message request.block request.blowup ctx.parameters.code (constructed ctx request config reachable result finished retained)).2.2.1 radius word)) ∧
      NativeGoldBatchPcsProgram.finish ctx.parameters work.binding (opening pair.1.2) = .ok () ∧
      RectangularMatrixOpeningKernel.Checks (m := ctx.parameters.code.messageBlocks.val) (Domain ctx (primitive ctx request config reachable result finished retained)) word pair.1.1
        (testMessages ctx work (opening pair.1.2)) pair.2 ∧
      ∀ test : Group ctx work × Fin ctx.parameters.width.val, ColumnOpening.Agrees
        (StructuredOpening.combine (RectangularBatchOpeningKernel.weights (left ctx world work prepared) test) word)
        (BlockEncoder.encode (Domain ctx (primitive ctx request config reachable result finished retained)) (RowLayout.padded (m := ctx.parameters.code.messageBlocks.val) (b := ctx.parameters.code.blockWidth.val)
          (messages ctx work (opening pair.1.2) test.1 test.2))) pair.2] ≤
      (((ctx.parameters.code.blocks.val - ctx.parameters.code.messageBlocks.val + 1 : ℕ) : ENNReal) / Fintype.card Goldilocks)^ctx.parameters.width.val +
      max (ColumnOpening.missBound (Fin (2^(logSize ctx.parameters.code))) ctx.parameters.queries.val
        ((ctx.parameters.code.blocks.val - ctx.parameters.code.messageBlocks.val + 1) - radius))
        (ColumnOpening.missBound (Fin (2^(logSize ctx.parameters.code))) ctx.parameters.queries.val (radius+1)) := by
  have distanceEq := distance ctx request config reachable result finished retained
  have code := constructed ctx request config reachable result finished retained
  have sizes := NativeGoldBlockCodeMeaning.constructor_dimensions _ request.message request.block request.blowup ctx.parameters.code code
  have blocks := (NativeGoldBlockCodeMeaning.constructor_log _ request.message request.block request.blowup ctx.parameters.code code).2
  have cardinal : ctx.parameters.code.blocks.val ≤ Fintype.card Goldilocks := by
    have embedded := Fintype.card_le_of_injective
      (Domain ctx (primitive ctx request config reachable result finished retained))
      (Domain ctx (primitive ctx request config reachable result finished retained)).injective
    simpa only [Fintype.card_fin,← blocks] using embedded
  have large : radius < Fintype.card Goldilocks := by
    have positive := sizes.1
    omega
  have nativeSmall : 3 * radius < Code.minDist (BlockCode.code
      (Domain ctx (primitive ctx request config reachable result finished retained))
      ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
      Set (Fin (2 ^ logSize ctx.parameters.code) → Fin ctx.parameters.code.blockWidth.val → Goldilocks)) := by
    rw [distanceEq]
    exact small
  have bound := NativeGoldBatchInteractiveSoundness.soundness_bound ctx world work prepared
    (constructorTables request config reachable) request.message request.block request.blowup
    (constructed ctx request config reachable result finished retained) (primitive ctx request config reachable result finished retained)
    radius word respond opening large nativeSmall
  simpa only [distanceEq] using bound

end
end FormalProof4FHE.HasteBoots.CacheBackedBatchSoundness
