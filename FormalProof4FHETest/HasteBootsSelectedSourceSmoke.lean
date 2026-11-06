module
import all FormalProof4FHE.HasteBoots.NativeGoldBatchSelectedChecks
import all FormalProof4FHETest.HasteBootsRecoveredChallengeSmoke
import all FormalProof4FHETest.HasteBootsNativeRectangularSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open NativeGoldColumnAuthentication (encoding)
open NativeMerkleShapeFamily (shape)
open NativeRootFamilySourceSelection (contains select Full)
open OracleProgram (run)
namespace HasteBootsSelectedSourceSmoke
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq
open HasteBootsBatchMeaningSmoke (root usize)
open HasteBootsFieldInputSmoke (fieldInput view decoded)

def key : NativeCanonicalLookupWire.Source := (view.data.context,view.data.root)
def readEntry : Observation := .output fieldInput 999 [0]
def oldHistory : List Observation := [readEntry,.hash [77] (List.ofFn root)]
def oldState := NativeRootFamilyHistory.reconstruct encoding root oldHistory

example : NativeGoldBatchSelectedSource.log root [] view = [] := rfl
example : oldState.2.hash.log.length = 1 := by decide +kernel
example : key ∈ oldState.1.1.frozen := by decide +kernel
example : NativeGoldBatchSelectedSource.log root oldHistory view = [] := by decide +kernel
example : contains oldState key [] = true := by decide +kernel
example : contains oldState key oldState.2.hash.log = false := by decide +kernel
example (after : List Observation) : ∀ index : NativeMerkleShapeFamily.Height,
    ⟨(view.data.context,index),⟨view.data.root,NativeGoldBatchSelectedSource.log root oldHistory view⟩⟩ ∈
      (NativeGoldBatchFamilyAvailability.reconstructed root (oldHistory++ .output fieldInput 0 [0] :: after)).checkpoints.checkpoints :=
  NativeGoldBatchSelectedSource.selected_snapshot root oldHistory after fieldInput view decoded 0 [0] (by decide)

-- A one-height decoy cannot replace a common log across all 64 heights.
def decoyLog : NativeRootFamilySourceSelection.Log := [⟨[77],root⟩]
def decoyCheckpoint := CheckpointExecution.record shape
  {CheckpointExecution.empty shape with hash := {CachedHashHandler.empty with log := decoyLog}}
  (key.1,⟨0,by decide⟩) key.2
def completeCheckpoints := RecordRoots.state shape (NativeMerkleShapeFamily.family key)
  {decoyCheckpoint with hash := CachedHashHandler.empty}
def completeState : NativeRootFamilyState.State :=
  (({NativeParentLedger.empty with frozen := {key}},NativeShakeCache.empty),completeCheckpoints)
example : contains completeState key decoyLog = false := by decide +kernel
example : contains completeState key [] = true := by decide +kernel
example : select completeState key = [] := by decide +kernel

example (sourceLog : NativeRootFamilySourceSelection.Log) :
    NativeGoldBatchRectangularWeights.source HasteBootsBatchOrderedSmoke.ctx HasteBootsBatchOrderedSmoke.world
      HasteBootsBatchOrderedSmoke.work HasteBootsBatchOrderedSmoke.prepared
      (NativeGoldBatchLinearEquations.Frozen root view.data.context HasteBootsBatchOrderedSmoke.work sourceLog) =
      NativeGoldBatchSelectedWord.word root view.data.context HasteBootsBatchOrderedSmoke.ctx.root HasteBootsBatchOrderedSmoke.ctx sourceLog :=
  NativeGoldBatchSelectedWord.prepared_word root view.data.context HasteBootsBatchOrderedSmoke.ctx HasteBootsBatchOrderedSmoke.world
    HasteBootsBatchOrderedSmoke.work HasteBootsBatchOrderedSmoke.prepared HasteBootsBatchOrderedSmoke.ctx.tables
    (usize 2) (usize 4) (usize 2) HasteBootsBatchOrderedSmoke.constructed sourceLog

section Accepted
open HasteBootsBatchMeaningSmoke (ctx world)
open HasteBootsNativeFinishingSmoke (work choose completion parent executed accepted)
def nativeInput := (NativeGoldBatchRandomLaw.phase work).pending.input
theorem parsed : NativeGoldBatchFieldInputView.parse nativeInput = some view := by
  have equal : nativeInput = fieldInput := by decide +kernel
  rw [equal]
  exact decoded

def history : List Observation := .output nativeInput 999 [0] :: (run (NativeGoldBatchPcsProgram.program ctx choose 6 ()) world).run.2
theorem nativeAccepted : NativeGoldBatchAnySourceRisk.Accepted world history ctx choose 6 () work := by
  refine ⟨?_,completion,parent,executed,accepted,?_⟩
  · exact ⟨HasteBootsFieldInputSmoke.parentFrames,by decide +kernel,HasteBootsRecoveredChallengeSmoke.parentValid,by decide +kernel⟩
  · exact List.sublist_append_right [_] _
theorem truthful : ObservationReplay.Agrees world history := by
  change ObservationReplay.Agrees world ([.output nativeInput 999 [0]] ++ (run (NativeGoldBatchPcsProgram.program ctx choose 6 ()) world).run.2)
  apply (ObservationReplay.agrees_append _ _ _).mpr
  refine ⟨?_,(OracleProgram.run_replay (NativeGoldBatchPcsProgram.program ctx choose 6 ())).truthful world⟩
  change ObservationReplay.Agrees world (ObservationReplay.read world nativeInput 999 1).run.2
  exact (ObservationReplay.read_replay nativeInput 999 1).truthful world

-- Actual accepted execution is instantiated with the old selected log;
-- source consistency is charged to the existing shared disagreement event.
example (safe : ¬CheckpointAvailability.Disagreement encoding root shape (NativeGoldBatchFamilyAvailability.reconstructed root history)) :
    ∃ requests : List (NativeGoldColumnWorker.Job × NativeGoldRawRequests.Request NativeMerkleShapeFamily.height),
      (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ctx.parameters) world).run.1 = some view.data.context ∧
      NativeGoldBatchFamilyRequests.prepare view.data.context work = some requests ∧
      (∀ index : NativeMerkleShapeFamily.Height, ⟨(view.data.context,index),⟨work.root,NativeGoldBatchSelectedSource.log root [] view⟩⟩ ∈
        (NativeGoldBatchFamilyAvailability.reconstructed root history).checkpoints.checkpoints) ∧
      ∀ entry ∈ requests,
        entry.2.payload = NativeGoldRawAvailability.frozenRaw root NativeMerkleShapeFamily.height entry.2.tag
          ⟨entry.2.root,NativeGoldBatchSelectedSource.log root [] view⟩ entry.2.position ∧
        NativeGoldBatchRawAvailability.Equations (NativeGoldBatchRawAvailability.view work requests)
          (NativeGoldRawAvailability.frozenValue root NativeMerkleShapeFamily.height entry.2.tag
            ⟨entry.2.root,NativeGoldBatchSelectedSource.log root [] view⟩ entry.2.position) entry.2.position.val :=
  NativeGoldBatchSelectedSource.accepted_selected root ctx world work choose 6 () [] _ view parsed 999 [0] (by decide) nativeAccepted truthful safe
example (safe : ¬CheckpointAvailability.Disagreement encoding root shape (NativeGoldBatchFamilyAvailability.reconstructed root history)) :
    ∃ draw : Fin ctx.parameters.queries.val → Fin (2^(NativeGoldBlockCode.logSize ctx.parameters.code)),
      (List.ofFn draw).map Fin.val = work.sample.draws ∧
      RectangularMatrixOpeningKernel.Checks (m := ctx.parameters.code.messageBlocks.val)
        (NativeGoldBatchResponseMeaning.Domain ctx HasteBootsBatchMeaningSmoke.primitive)
        (NativeGoldBatchSelectedWord.word root view.data.context ctx.root ctx (NativeGoldBatchSelectedSource.log root [] view))
        (NativeGoldBatchRecoveredMatrix.random ctx work.state) (NativeGoldBatchRectangularData.testMessages ctx work) draw := by
  obtain ⟨prepared,draw,_,ordered,checks,_,_⟩ := NativeGoldBatchSelectedChecks.accepted_checks root ctx world work ctx.tables
    (usize 2) (usize 4) (usize 2) HasteBootsBatchMeaningSmoke.constructed HasteBootsBatchMeaningSmoke.primitive
    choose 6 () [] _ view parsed 999 [0] (by decide) nativeAccepted truthful safe
  exact ⟨draw,ordered,checks⟩

end Accepted
end
end HasteBootsSelectedSourceSmoke
