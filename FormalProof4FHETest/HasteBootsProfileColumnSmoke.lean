module
import all FormalProof4FHE.HasteBoots.NativeGoldBatchProfileColumnNative
import all FormalProof4FHE.HasteBoots.NativeGoldBatchLifetimeMeasurable
import all FormalProof4FHETest.HasteBootsLifetimeSoundnessSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (World law)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
namespace HasteBootsProfileColumnSmoke
noncomputable section
open HasteBootsBatchOrderedSmoke (ctx world work prepared)
open HasteBootsBatchMeaningSmoke (root usize)
open HasteBootsEarlyReceiptSmoke (view step)
open HasteBootsFieldColumnSmoke (past replay first parsed)
open HasteBootsRecoveredChallengeSmoke (parent parentValid batchFits responseFits)
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq

theorem primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot)
    (2^(NativeGoldBlockCode.logSize ctx.parameters.code+1)) := HasteBootsBatchMeaningSmoke.primitive

theorem selected : NativeGoldBatchProfileColumnExposure.select ctx step (past world).run = some view :=
  NativeGoldBatchProfileColumnNative.selected_native ctx world work prepared HasteBootsFieldInputSmoke.parentFrames parent parentValid
    batchFits responseFits view parsed ctx.tables (usize 2) (usize 4) (usize 2) HasteBootsBatchOrderedSmoke.constructed step (past world).run first

theorem loss : NativeGoldBatchProfileColumnExposure.loss ctx primitive 0 = ((31 : ENNReal)/32)^3 := by
  unfold NativeGoldBatchProfileColumnExposure.loss
  rw [HasteBootsConcreteColumnSmoke.distanceZero]
  rfl
example : NativeGoldBatchProfileColumnExposure.risk root ctx primitive step (past world).run 0 = ((31 : ENNReal)/32)^3 := by
  rw [NativeGoldBatchProfileColumnExposure.risk_selected root ctx primitive step (past world).run 0 view selected [] HasteBootsConcreteColumnSmoke.recovered]
  exact loss
-- Sampling quota three is preserved although transport has only two jobs.
example : ctx.parameters.queries.val = 3 ∧ work.sample.indices.length = 2 := by decide +kernel

-- A complete valid nonce with a smaller foreign quota passed the broad selector.
def foreign : NativeGoldBatchPcsProgram.Context := {ctx with parameters := {ctx.parameters with queries := usize 1}}
def foreignInput := NativeGoldBatchColumnRequestLaw.input foreign work world
def foreignStep (_ : Unit) : OracleMachine.Command Unit Unit := .read foreignInput 999 1 (fun _ => ())
example : (NativeGoldBatchConcreteColumnExposure.select ctx foreignStep (past world).run).isSome = true := by decide +kernel
theorem foreignPresent : (NativeGoldBatchConcreteColumnExposure.select ctx foreignStep (past world).run).isSome = true := by decide +kernel
def foreignView := (NativeGoldBatchConcreteColumnExposure.select ctx foreignStep (past world).run).get foreignPresent
theorem foreignSelected : NativeGoldBatchConcreteColumnExposure.select ctx foreignStep (past world).run = some foreignView :=
  (Option.some_get foreignPresent).symm
example : NativeGoldBatchConcreteColumnExposure.risk root ctx primitive foreignStep (past world).run 0 = (31 : ENNReal)/32 := by
  have found : NativeGoldBatchFirstFieldSource.recover root (past world).run.2 foreignView.field = some [] := by decide +kernel
  have quota : foreignView.column.index.count.val = 1 := by decide +kernel
  simp only [NativeGoldBatchConcreteColumnExposure.risk,foreignSelected,found,quota]
  rw [HasteBootsConcreteColumnSmoke.distanceZero]
  change ((31 : ENNReal)/32)^1 = (31 : ENNReal)/32
  exact pow_one _

example : NativeGoldBatchProfileColumnExposure.select ctx foreignStep (past world).run = none := by decide +kernel
example : NativeGoldBatchProfileColumnExposure.risk root ctx primitive foreignStep (past world).run 0 = 0 := by
  have absent : NativeGoldBatchProfileColumnExposure.select ctx foreignStep (past world).run = none := by decide +kernel
  simp only [NativeGoldBatchProfileColumnExposure.risk,absent]

-- Filtering the column charge retains the foreign query in global source history.
def foreignHistory : List NativeTranscript.Observation := [.output foreignInput 999 [0],.hash [77] (List.ofFn root)]
example : NativeGoldBatchSelectedSource.log root foreignHistory view.field = [] := by decide +kernel

-- A correctly shaped index request may still quote the wrong field matrix count.
def wrongField : NativeGoldBatchFieldInputView.View := {view.field with count := usize 1}
def wrongInput := NativeGoldBatchChallengeOrigin.input wrongField ctx.parent.profile ctx.opening NativeGoldBatchColumns.label
  ctx.parameters.code.blocks ctx.parameters.queries view.receipt
def wrongStep (_ : Unit) : OracleMachine.Command Unit Unit := .read wrongInput 999 1 (fun _ => ())
example : (NativeGoldBatchConcreteColumnExposure.select ctx wrongStep (past world).run).isSome = true := by decide +kernel
example : NativeGoldBatchProfileColumnExposure.select ctx wrongStep (past world).run = none := by decide +kernel
example (packet : NativeIndexExposureRisk.Packet Unit Unit) :
    NativeGoldBatchProfileColumnExposure.risk root ctx primitive step packet 0 ≤ NativeGoldBatchProfileColumnExposure.loss ctx primitive 0 :=
  NativeGoldBatchProfileColumnExposure.risk_le_loss root ctx primitive step packet 0

example : (law[|{other | (past other).run = (past world).run}])
    {other | NativeGoldBatchProfileColumnExposure.event root ctx primitive root step (past other).run 0 other} ≤
      NativeGoldBatchProfileColumnExposure.risk root ctx primitive step (past world).run 0 :=
  NativeGoldBatchProfileColumnExposure.conditional_bound replay root ctx primitive root step world 0
end
end HasteBootsProfileColumnSmoke
