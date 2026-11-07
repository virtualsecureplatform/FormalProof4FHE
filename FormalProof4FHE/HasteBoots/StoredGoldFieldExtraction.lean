module
public import FormalProof4FHE.HasteBoots.StoredGoldFieldSourceRecovery
public import FormalProof4FHE.HasteBoots.CausalStoredGoldExtraction
@[expose] public section

/-! Original raw field input through stored causal-source extraction. The key
is produced by full field/batch parsing; no caller source/key or snapshot is
accepted. Trusted application context/capacity production and actual backend
refinement remain separate from this measured structural composition. -/
namespace FormalProof4FHE.HasteBoots.StoredGoldFieldExtraction
open InputIndexedOracle (Input Byte)
open NativeTranscript (Observation)
open NativeGoldBatchPcsProgram (Context)
open SolverOperationCost (Run)
open StoredGoldBatchFieldInputCost (view)

def run (history : List Observation) (input : Input) (dummy : Vector Byte 64) (ctx : Context) (radius : ℕ)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val) :=
  let recovered := StoredGoldFieldSourceRecovery.run history input
  match recovered.value with
  | none => Run.mk none (recovered.cost+2)
  | some result =>
    let root := StoredDigestView.fromVector result.field.data.source.2
    let extracted := StoredGoldPublicSource.extract dummy root.value ctx result.log radius capacity
    Run.mk (some (result.field,extracted.value)) (recovered.cost+root.cost+extracted.cost+3)

theorem run_value (history : List Observation) (input : Input) (dummy : Vector Byte 64) (ctx : Context) (radius : ℕ)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val) :
    (run history input dummy ctx radius capacity).value.map (fun pair => (view pair.1,pair.2)) =
      (NativeGoldBatchFieldInputView.parse input).bind (fun field =>
        (ExecutableSourceSelection.recover history field).map (fun log =>
          (field,(NativeGoldPublicSource.extractWithCost dummy.get field.data.root ctx log radius capacity).value))) := by
  have recovered := StoredGoldFieldSourceRecovery.run_value history input
  have mapped : (run history input dummy ctx radius capacity).value.map (fun pair => (view pair.1,pair.2)) =
      ((StoredGoldFieldSourceRecovery.run history input).value.map StoredGoldFieldSourceRecovery.resultView).map
        (fun pair => (pair.1,(NativeGoldPublicSource.extractWithCost dummy.get pair.1.data.root ctx pair.2 radius capacity).value)) := by
    cases found : (StoredGoldFieldSourceRecovery.run history input).value with
    | none => simp only [run,found,Option.map_none]
    | some result =>
      simp only [run,found,Option.map_some,StoredGoldPublicSource.extract_eq,StoredDigestView.view_fromVector,
        StoredGoldFieldSourceRecovery.resultView,view,StoredBatchMessageCost.view]
  rw [mapped,recovered]
  cases parsed : NativeGoldBatchFieldInputView.parse input with
  | none => rfl
  | some field => simp only [Option.bind_some,Option.map_map,Function.comp_def]

theorem run_cost (history : List Observation) (input : Input) (dummy : Vector Byte 64) (ctx : Context) (radius : ℕ)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val) :
    (run history input dummy ctx radius capacity).cost ≤ 587*input.length+
      6*StoredGoldBatchFieldInputCost.labelBytes+3554+(6*input.length+16)*history.length+
      StoredSourceSnapshotBudget.stepBound (ClosedByteMachineRootBudget.inputWork history)
        history.length (StoredShakeHistory.bytes history)*history.length+
      5308*ClosedByteMachineRootBudget.inputWork history^2+
      ((StoredGoldFieldSourceRecovery.run history input).value.map
        (fun result => CausalStoredGoldExtraction.sourceBound ctx result.log radius)).getD 0 := by
  have recovered := StoredGoldFieldSourceRecovery.run_cost history input
  simp only [run]
  split
  · rename_i absent
    simp only [absent,Option.map_none,Option.getD_none]
    omega
  · rename_i result found
    have extracted := StoredGoldPublicSource.extract_cost dummy
      (StoredDigestView.fromVector result.field.data.source.2).value ctx result.log radius capacity
    simp only [found,Option.map_some,Option.getD_some]
    dsimp only [StoredDigestView.fromVector,CausalStoredGoldExtraction.sourceBound] at extracted ⊢
    omega

theorem run_reject (history : List Observation) (input : Input) (dummy : Vector Byte 64) (ctx : Context) (radius : ℕ)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val)
    (rejected : (StoredGoldFieldSourceRecovery.run history input).value = none) :
    (run history input dummy ctx radius capacity).value = none ∧
      (run history input dummy ctx radius capacity).cost = (StoredGoldFieldSourceRecovery.run history input).cost+2 := by
  simp [run,rejected]
end FormalProof4FHE.HasteBoots.StoredGoldFieldExtraction
