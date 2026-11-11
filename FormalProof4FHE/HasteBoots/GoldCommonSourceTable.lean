module
public import FormalProof4FHE.HasteBoots.BatchOpeningNativeObligation
public import FormalProof4FHE.HasteBoots.SingleOpeningNativeObligation
@[expose] public section

/-! One parameter-indexed analysis table for native single and batch openings.
The exact selected log is an explicit argument: equal roots alone do not
identify snapshots selected at different first field reads. -/
namespace FormalProof4FHE.HasteBoots.GoldCommonSourceTable
open NativeBrakedownContext (Parameters)
open NativeGoldBlockCode (Stored logSize)
open NativeRootMessage (Digest)
open NativeRootFamilySourceSelection (Log)
open NativeFields (Goldilocks)
noncomputable section

abbrev Primitive (parameters : Parameters Stored) :=
  IsPrimitiveRoot (NativeFieldRepresentation.goldValue parameters.code.domainRoot) (2^(logSize parameters.code+1))
abbrev Capacity (parameters : Parameters Stored) :=
  parameters.code.messageLength.val ≤ parameters.code.messageBlocks.val*parameters.code.blockWidth.val

def domain (parameters : Parameters Stored) (primitive : Primitive parameters) :=
  NTTButterfly.domain (logSize parameters.code) (NativeFieldRepresentation.goldValue parameters.code.domainRoot) primitive

def word (parameters : Parameters Stored) (dummy context root : Digest) (sourceLog : Log) :
    Fin (2^logSize parameters.code) → (Fin (2^parameters.leftVariables.val) × Fin parameters.width.val) →
      Fin parameters.code.blockWidth.val → Goldilocks :=
  fun symbol row component => NativeGoldBatchSelectedWord.values dummy context root parameters.code sourceLog symbol.val
    ((row.1.val*parameters.width.val+row.2.val)*parameters.code.blockWidth.val+component.val)

def rectangular (parameters : Parameters Stored) (primitive : Primitive parameters) (capacity : Capacity parameters)
    (dummy context root : Digest) (sourceLog : Log) (radius : ℕ) :=
  RectangularMatrixOpeningKernel.extract (domain parameters primitive) capacity radius (word parameters dummy context root sourceLog)

def cube (parameters : Parameters Stored) (primitive : Primitive parameters) (capacity : Capacity parameters)
    (dummy context root : Digest) (sourceLog : Log) (radius back : ℕ)
    (length : parameters.code.messageLength.val = 2^back)
    (arity : parameters.numVariables.val = parameters.leftVariables.val+back) :=
  QueryReindex.source arity (QueryRectangularNativeMeaning.source parameters back length
    (rectangular parameters primitive capacity dummy context root sourceLog radius))

/-- The canonical native split, with its geometry supplied by successful
preparation rather than by an independent table-padding assertion. -/
def table (parameters : Parameters Stored) (primitive : Primitive parameters) (capacity : Capacity parameters)
    (dummy context root : Digest) (sourceLog : Log) (radius : ℕ)
    (geometry : parameters.numVariables.val = parameters.leftVariables.val +
      (parameters.numVariables.val-parameters.leftVariables.val) ∧
      parameters.code.messageLength.val = 2^(parameters.numVariables.val-parameters.leftVariables.val)) :=
  cube parameters primitive capacity dummy context root sourceLog radius
    (parameters.numVariables.val-parameters.leftVariables.val) geometry.2 geometry.1

theorem table_congr {first second : Parameters Stored} (same : first = second)
    (firstPrimitive : Primitive first) (secondPrimitive : Primitive second)
    (firstCapacity : Capacity first) (secondCapacity : Capacity second)
    (dummy context root : Digest) (sourceLog : Log) (radius : ℕ)
    (firstGeometry : first.numVariables.val = first.leftVariables.val+(first.numVariables.val-first.leftVariables.val) ∧
      first.code.messageLength.val = 2^(first.numVariables.val-first.leftVariables.val))
    (secondGeometry : second.numVariables.val = second.leftVariables.val+(second.numVariables.val-second.leftVariables.val) ∧
      second.code.messageLength.val = 2^(second.numVariables.val-second.leftVariables.val)) :
    HEq (table first firstPrimitive firstCapacity dummy context root sourceLog radius firstGeometry)
      (table second secondPrimitive secondCapacity dummy context root sourceLog radius secondGeometry) := by
  cases same
  rfl

/-- Raw words, dimensions, decoder radius and the exact old log are retained.
No response, opening query, scheduler, or future oracle work is an argument. -/
theorem rectangular_congr {first second : Parameters Stored} (same : first = second)
    (firstPrimitive : Primitive first) (secondPrimitive : Primitive second)
    (firstCapacity : Capacity first) (secondCapacity : Capacity second)
    (dummy context root : Digest) (sourceLog : Log) (radius : ℕ) :
    HEq (rectangular first firstPrimitive firstCapacity dummy context root sourceLog radius)
      (rectangular second secondPrimitive secondCapacity dummy context root sourceLog radius) := by
  cases same
  rfl

/-- Parameter transport preserves the complete cube, not only a particular
query's evaluation. Exact log identity remains a necessary hypothesis. -/
theorem cube_congr {first second : Parameters Stored} (same : first = second)
    (firstPrimitive : Primitive first) (secondPrimitive : Primitive second)
    (firstCapacity : Capacity first) (secondCapacity : Capacity second)
    (dummy context root : Digest) (sourceLog : Log) (radius back : ℕ)
    (firstLength : first.code.messageLength.val = 2^back) (secondLength : second.code.messageLength.val = 2^back)
    (firstArity : first.numVariables.val = first.leftVariables.val+back)
    (secondArity : second.numVariables.val = second.leftVariables.val+back) :
    HEq (cube first firstPrimitive firstCapacity dummy context root sourceLog radius back firstLength firstArity)
      (cube second secondPrimitive secondCapacity dummy context root sourceLog radius back secondLength secondArity) := by
  cases same
  rfl

theorem batch_rectangular (dummy : Digest) (ctx : NativeGoldBatchPcsProgram.Context)
    (primitive : Primitive ctx.parameters) (capacity : Capacity ctx.parameters)
    (decoded : NativeGoldBatchChallengeLink.View) (sourceLog : Log) (radius : ℕ) :
    BatchOpeningNativeObligation.rectangular dummy ctx primitive capacity decoded radius sourceLog =
      rectangular ctx.parameters primitive capacity dummy decoded.field.data.context decoded.field.data.root sourceLog radius := rfl

theorem batch_cube (dummy : Digest) (ctx : NativeGoldBatchPcsProgram.Context)
    (primitive : Primitive ctx.parameters) (capacity : Capacity ctx.parameters)
    (world : InputIndexedOracle.World) (work : NativeGoldBatchPcsProgram.Prepared)
    (prepared : (OracleProgram.run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (decoded : NativeGoldBatchChallengeLink.View) (sourceLog : Log) (radius : ℕ) :
    BatchOpeningNativeObligation.source dummy ctx primitive capacity world work prepared decoded radius sourceLog =
      cube ctx.parameters primitive capacity dummy decoded.field.data.context decoded.field.data.root sourceLog radius
        (ctx.parameters.numVariables.val-ctx.parameters.leftVariables.val)
        (BatchOpeningNativeObligation.dimensions ctx world work prepared).2
        (BatchOpeningNativeObligation.dimensions ctx world work prepared).1 := rfl

theorem single_rectangular (dummy : Digest) (ctx : NativeGoldPcsExecution.Context)
    (origin : CacheBackedSingleOpening.Origin ctx) (decoded : SingleOpeningChallengeLink.View) (sourceLog : Log) (radius : ℕ) :
    SingleOpeningExtractedTableMeaning.rectangular dummy ctx origin decoded sourceLog radius =
      rectangular ctx.parameters origin.primitive origin.capacity dummy decoded.field.data.context decoded.field.data.root sourceLog radius := rfl

theorem single_cube (dummy : Digest) (ctx : NativeGoldPcsExecution.Context)
    (origin : CacheBackedSingleOpening.Origin ctx) (world : InputIndexedOracle.World) (work : NativeGoldPcsWorkers.Prepared)
    (prepared : (OracleProgram.run ctx.prefix world).run.1 = .prepared work)
    (decoded : SingleOpeningChallengeLink.View) (sourceLog : Log) (radius : ℕ) :
    SingleOpeningNativeObligation.source dummy ctx origin world work prepared decoded sourceLog radius =
      cube ctx.parameters origin.primitive origin.capacity dummy decoded.field.data.context decoded.field.data.root sourceLog radius
        (ctx.parameters.numVariables.val-ctx.parameters.leftVariables.val)
        (SingleOpeningExtractedTableMeaning.prepared_dimensions ctx world work prepared).2
        (SingleOpeningExtractedTableMeaning.prepared_dimensions ctx world work prepared).1 := rfl

/-- The single and batch analysis extractors agree on the entire cube when
full parameters, context/root and the exact selected log agree. This does not
assert equality of logs selected at different field-read times. -/
theorem single_batch_same (dummy : Digest)
    (single : NativeGoldPcsExecution.Context) (origin : CacheBackedSingleOpening.Origin single)
    (batch : NativeGoldBatchPcsProgram.Context) (primitive : Primitive batch.parameters) (capacity : Capacity batch.parameters)
    (world : InputIndexedOracle.World) (singleWork : NativeGoldPcsWorkers.Prepared) (batchWork : NativeGoldBatchPcsProgram.Prepared)
    (singlePrepared : (OracleProgram.run single.prefix world).run.1 = .prepared singleWork)
    (batchPrepared : (OracleProgram.run (NativeGoldBatchPcsProgram.prepareProgram batch) world).run.1 = .prepared batchWork)
    (singleView : SingleOpeningChallengeLink.View) (batchView : NativeGoldBatchChallengeLink.View)
    (parameters : single.parameters = batch.parameters)
    (context : singleView.field.data.context = batchView.field.data.context)
    (root : singleView.field.data.root = batchView.field.data.root)
    (sourceLog : Log) (radius : ℕ) :
    HEq (SingleOpeningNativeObligation.source dummy single origin world singleWork singlePrepared singleView sourceLog radius)
      (BatchOpeningNativeObligation.source dummy batch primitive capacity world batchWork batchPrepared batchView radius sourceLog) := by
  change HEq (table single.parameters origin.primitive origin.capacity dummy singleView.field.data.context singleView.field.data.root
    sourceLog radius (SingleOpeningExtractedTableMeaning.prepared_dimensions single world singleWork singlePrepared))
    (table batch.parameters primitive capacity dummy batchView.field.data.context batchView.field.data.root
      sourceLog radius (BatchOpeningNativeObligation.dimensions batch world batchWork batchPrepared))
  rw [context,root]
  exact table_congr parameters origin.primitive primitive origin.capacity capacity dummy _ _ sourceLog radius _ _

/-- Different batch call data or different original query indices do not
change the extracted cube under the same complete source identity. -/
theorem batches_same (dummy : Digest) (first second : NativeGoldBatchPcsProgram.Context)
    (firstPrimitive : Primitive first.parameters) (secondPrimitive : Primitive second.parameters)
    (firstCapacity : Capacity first.parameters) (secondCapacity : Capacity second.parameters)
    (world : InputIndexedOracle.World) (firstWork secondWork : NativeGoldBatchPcsProgram.Prepared)
    (firstPrepared : (OracleProgram.run (NativeGoldBatchPcsProgram.prepareProgram first) world).run.1 = .prepared firstWork)
    (secondPrepared : (OracleProgram.run (NativeGoldBatchPcsProgram.prepareProgram second) world).run.1 = .prepared secondWork)
    (firstView secondView : NativeGoldBatchChallengeLink.View)
    (parameters : first.parameters = second.parameters)
    (context : firstView.field.data.context = secondView.field.data.context)
    (root : firstView.field.data.root = secondView.field.data.root)
    (sourceLog : Log) (radius : ℕ) :
    HEq (BatchOpeningNativeObligation.source dummy first firstPrimitive firstCapacity world firstWork firstPrepared firstView radius sourceLog)
      (BatchOpeningNativeObligation.source dummy second secondPrimitive secondCapacity world secondWork secondPrepared secondView radius sourceLog) := by
  change HEq (table first.parameters firstPrimitive firstCapacity dummy firstView.field.data.context firstView.field.data.root
    sourceLog radius (BatchOpeningNativeObligation.dimensions first world firstWork firstPrepared))
    (table second.parameters secondPrimitive secondCapacity dummy secondView.field.data.context secondView.field.data.root
      sourceLog radius (BatchOpeningNativeObligation.dimensions second world secondWork secondPrepared))
  rw [context,root]
  exact table_congr parameters firstPrimitive secondPrimitive firstCapacity secondCapacity dummy _ _ sourceLog radius _ _

end
end FormalProof4FHE.HasteBoots.GoldCommonSourceTable
