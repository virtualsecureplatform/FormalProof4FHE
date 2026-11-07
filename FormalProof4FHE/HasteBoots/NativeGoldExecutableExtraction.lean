module
public import FormalProof4FHE.HasteBoots.ExecutableRectangularMatrixExtraction
public import FormalProof4FHE.HasteBoots.NativeGoldBatchCausalCoverage
public import FormalProof4FHE.HasteBoots.NTTDomainCost
@[expose] public section

/-! Executable extraction for the original native Goldilocks row geometry.
Evaluation points use the same bit-reversed odd-root order as the existing
native code semantics. The constructor supplies positive code dimensions and
capacity; this module does not establish byte availability or Rust refinement. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldExecutableExtraction
open NativeGoldBatchPcsProgram (Context)
open NativeGoldBatchRectangularWeights (Row)
open NativeGoldBlockCode (Tables logSize)
open NativeFields (Goldilocks)
open NativeFieldRepresentation (goldValue)

def points (ctx : Context) : Fin (2^(logSize ctx.parameters.code)) → Goldilocks :=
  NTTButterfly.nodes (logSize ctx.parameters.code) (goldValue ctx.parameters.code.domainRoot)

def pointTableWithCost (ctx : Context) :=
  NTTDomainCost.nodes (logSize ctx.parameters.code) (goldValue ctx.parameters.code.domainRoot)

theorem pointTable_value (ctx : Context) :
    (pointTableWithCost ctx).value = Vector.ofFn (points ctx) := by
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_ofFn]
  change (NTTDomainCost.nodes (logSize ctx.parameters.code)
    (goldValue ctx.parameters.code.domainRoot)).value.get ⟨i,hi⟩ = _
  exact NTTDomainCost.nodes_get _ _ ⟨i,hi⟩

theorem pointTable_cost (ctx : Context) :
    (pointTableWithCost ctx).cost+5 =
      2^(logSize ctx.parameters.code)*(2*logSize ctx.parameters.code+9) :=
  NTTDomainCost.nodes_cost _ _

/-- Abstract field/access charge including domain generation. Raw byte/input
materialization and native backend refinement remain separate. -/
def extractWithCost (ctx : Context) (radius : ℕ)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val)
    (raw : Fin (2^(logSize ctx.parameters.code)) → Row ctx → Fin ctx.parameters.code.blockWidth.val → Goldilocks) :
    SolverOperationCost.Run (Vector (Vector (Vector Goldilocks ctx.parameters.width.val) ctx.parameters.code.messageLength.val)
      (2^ctx.parameters.leftVariables.val)) :=
  let domain := pointTableWithCost ctx
  let result := DenseSourceExtraction.extractRectangular radius domain.value capacity
    (ExecutableCommonSource.prepareRaw (CommonSourceReindex.reindex finProdFinEquiv.symm raw))
  ⟨result.value,domain.cost+result.cost+1⟩

theorem extractWithCost_value (ctx : Context) (radius : ℕ)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val)
    (raw : Fin (2^(logSize ctx.parameters.code)) → Row ctx → Fin ctx.parameters.code.blockWidth.val → Goldilocks) :
    (extractWithCost ctx radius capacity raw).value =
      (ExecutableRectangularMatrixExtraction.extractWithCost radius (points ctx) capacity raw).value := by
  simp only [extractWithCost,pointTable_value,ExecutableRectangularMatrixExtraction.extractWithCost]

def extract (ctx : Context) (radius : ℕ)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val)
    (raw : Fin (2^(logSize ctx.parameters.code)) → Row ctx → Fin ctx.parameters.code.blockWidth.val → Goldilocks) :
    Vector (Vector (Vector Goldilocks ctx.parameters.width.val) ctx.parameters.code.messageLength.val)
      (2^ctx.parameters.leftVariables.val) := (extractWithCost ctx radius capacity raw).value

theorem extractWithCost_cost (ctx : Context) (radius : ℕ)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val)
    (raw : Fin (2^(logSize ctx.parameters.code)) → Row ctx → Fin ctx.parameters.code.blockWidth.val → Goldilocks) :
    let n := 2^(logSize ctx.parameters.code)
    let left := 2^ctx.parameters.leftVariables.val
    let packing := ctx.parameters.width.val
    let m := ctx.parameters.code.messageBlocks.val
    let b := ctx.parameters.code.blockWidth.val
    let size := ctx.parameters.code.messageLength.val
    (extractWithCost ctx radius capacity raw).cost ≤ DenseCommonSource.operationBound n (left*packing) m b radius+
      (left*packing)*(7*size+2)+left*(size*(5*packing+2)+2)+
      n*(2*logSize ctx.parameters.code+9)+5 := by
  have domain := pointTable_cost ctx
  have bound := DenseSourceExtraction.extractRectangular_cost radius
    (pointTableWithCost ctx).value capacity
    (ExecutableCommonSource.prepareRaw (CommonSourceReindex.reindex finProdFinEquiv.symm raw))
  dsimp only [extractWithCost]
  omega

def table (ctx : Context) (radius : ℕ)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val)
    (raw : Fin (2^(logSize ctx.parameters.code)) → Row ctx → Fin ctx.parameters.code.blockWidth.val → Goldilocks) :
    Fin (2^ctx.parameters.leftVariables.val) → Fin ctx.parameters.code.messageLength.val → Fin ctx.parameters.width.val → Goldilocks :=
  let values := extract ctx radius capacity raw
  fun left right channel => ((values.get left).get right).get channel

theorem extract_eq_analysis (ctx : Context) (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (radius : ℕ) (uniqueRadius : 2*radius < 2^(logSize ctx.parameters.code)-ctx.parameters.code.messageBlocks.val+1)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val)
    (raw : Fin (2^(logSize ctx.parameters.code)) → Row ctx → Fin ctx.parameters.code.blockWidth.val → Goldilocks)
    (left : Fin (2^ctx.parameters.leftVariables.val)) (right : Fin ctx.parameters.code.messageLength.val)
    (channel : Fin ctx.parameters.width.val) :
    (((extract ctx radius capacity raw).get left).get right).get channel =
      RectangularMatrixOpeningKernel.extract (NativeGoldBatchResponseMeaning.Domain ctx primitive) capacity radius raw left right channel := by
  have dimensions := NativeGoldBlockCodeMeaning.constructor_dimensions tables message block blowup ctx.parameters.code constructed
  have spec := NativeGoldBlockCode.build_spec tables message block blowup ctx.parameters.code constructed
  let : NeZero ctx.parameters.code.messageBlocks.val := ⟨Nat.ne_of_gt dimensions.1⟩
  let : NeZero ctx.parameters.code.blockWidth.val := ⟨by rw [spec.blockEq]; exact spec.dimensions.2.1⟩
  simp only [extract,extractWithCost_value]
  exact ExecutableRectangularMatrixExtraction.extract_eq_analysis radius
    (NativeGoldBatchResponseMeaning.Domain ctx primitive) capacity raw uniqueRadius dimensions.2.1.le left right channel

theorem table_eq_analysis (ctx : Context) (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (radius : ℕ) (uniqueRadius : 2*radius < 2^(logSize ctx.parameters.code)-ctx.parameters.code.messageBlocks.val+1)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val)
    (raw : Fin (2^(logSize ctx.parameters.code)) → Row ctx → Fin ctx.parameters.code.blockWidth.val → Goldilocks) :
    table ctx radius capacity raw =
      RectangularMatrixOpeningKernel.extract (NativeGoldBatchResponseMeaning.Domain ctx primitive) capacity radius raw := by
  funext left right channel
  exact extract_eq_analysis ctx tables message block blowup constructed primitive radius uniqueRadius capacity raw left right channel

/-- The same original-query falsity test, now against executable extraction. -/
def FalseClaim (dummy : NativeRootMessage.Digest) (ctx : Context)
    (work : NativeGoldBatchPcsProgram.Prepared) (decoded : NativeGoldBatchChallengeLink.View)
    (log : List NativeTranscript.Observation)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val)
    (radius : ℕ) : Prop :=
  ∀ sourceLog, NativeGoldBatchFirstFieldSource.recover dummy log decoded.field = some sourceLog →
    ∃ query : NativeGoldBatchRectangularData.Query work,
      (fun lane : Fin ctx.parameters.width.val => NativeGoldBatchFixedResponseData.claimed decoded.field.data.values query.val lane.val) ≠
        matrixEvaluation (NativeGoldBatchFixedResponseData.leftAt ctx.parameters decoded.field.data.queries query.val)
          (NativeGoldBatchFixedResponseData.rightAt ctx.parameters decoded.field.data.queries query.val)
          (table ctx radius capacity (NativeGoldBatchConcreteColumnFamily.source dummy ctx decoded sourceLog))

theorem falseClaim_iff_analysis (dummy : NativeRootMessage.Digest) (ctx : Context)
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (work : NativeGoldBatchPcsProgram.Prepared) (decoded : NativeGoldBatchChallengeLink.View)
    (log : List NativeTranscript.Observation)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val)
    (radius : ℕ) (uniqueRadius : 2*radius < 2^(logSize ctx.parameters.code)-ctx.parameters.code.messageBlocks.val+1) :
    FalseClaim dummy ctx work decoded log capacity radius ↔
      NativeGoldBatchCausalCoverage.FalseClaim dummy ctx primitive work decoded log capacity radius := by
  simp only [FalseClaim,NativeGoldBatchCausalCoverage.FalseClaim,
    table_eq_analysis ctx tables message block blowup constructed primitive radius uniqueRadius capacity]
end FormalProof4FHE.HasteBoots.NativeGoldExecutableExtraction
