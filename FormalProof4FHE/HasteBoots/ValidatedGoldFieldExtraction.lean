module
public import FormalProof4FHE.HasteBoots.StoredGoldGeometryCost
public import FormalProof4FHE.HasteBoots.StoredGoldFieldExtraction
@[expose] public section

/-! Runtime geometry and capacity production before original-field extraction.
The geometry gate equals the existing native parameter constructor. The extra
capacity gate is the preceding extractor's explicit precondition; successful
native code construction proves it, so no honest constructor result is excluded.
Application registry/context identity and constructor/backend physical refinement
remain separate. No table/row-code callback is evaluated by this entry point. -/
namespace FormalProof4FHE.HasteBoots.ValidatedGoldFieldExtraction
open InputIndexedOracle (Input Byte)
open NativeTranscript (Observation)
open SolverOperationCost (Run)
open NativeGoldBatchPcsProgram (Context)
open StoredGoldGeometryCost (Parameters)

structure Checked (parameters : Parameters) where
  geometry : NativeBrakedownParameters.Geometry
  capacity : parameters.code.messageLength.val ≤ parameters.code.messageBlocks.val*parameters.code.blockWidth.val

def validate (parameters : Parameters) : Run (Option (Checked parameters)) :=
  let built := StoredGoldGeometryCost.build parameters
  match built.value with
  | none => ⟨none,built.cost+2⟩
  | some geometry =>
    if capacity : parameters.code.messageLength.val ≤ parameters.code.messageBlocks.val*parameters.code.blockWidth.val then
      ⟨some ⟨geometry,capacity⟩,built.cost+16⟩
    else ⟨none,built.cost+12⟩

theorem validate_value (parameters : Parameters) :
    (validate parameters).value.map Checked.geometry =
      (NativeBrakedownParameters.build NativeGoldBlockCode.description parameters).bind (fun geometry =>
        if parameters.code.messageLength.val ≤ parameters.code.messageBlocks.val*parameters.code.blockWidth.val then some geometry else none) := by
  simp only [validate,← StoredGoldGeometryCost.build_value]
  cases built : (StoredGoldGeometryCost.build parameters).value with
  | none => rfl
  | some geometry =>
    by_cases capacity : parameters.code.messageLength.val ≤ parameters.code.messageBlocks.val*parameters.code.blockWidth.val <;>
      simp only [capacity,dite_true,dite_false,ite_true,ite_false,Option.map_some,Option.map_none,Option.bind_some]

theorem validate_cost (parameters : Parameters) : (validate parameters).cost ≤ 1516 := by
  have built := StoredGoldGeometryCost.build_cost parameters
  simp only [validate]
  split
  · dsimp only; omega
  · split <;> dsimp only <;> omega

theorem validate_spec (parameters : Parameters) (checked : Checked parameters)
    (accepted : (validate parameters).value = some checked) :
    NativeBrakedownParameters.Spec NativeGoldBlockCode.description parameters checked.geometry ∧
      parameters.code.messageLength.val ≤ parameters.code.messageBlocks.val*parameters.code.blockWidth.val := by
  have native := validate_value parameters
  rw [accepted,Option.map_some] at native
  obtain ⟨geometry,built,selected⟩ := Option.bind_eq_some_iff.mp native.symm
  split at selected
  · have same := Option.some.inj selected
    subst geometry
    exact ⟨NativeBrakedownParameters.build_spec _ _ _ built,checked.capacity⟩
  · cases selected

theorem constructor_capacity (tables : NativeGoldBlockCode.Tables) (message block blowup : NativeUsizeMessage.Usize)
    (parameters : Parameters)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok parameters.code) :
    parameters.code.messageLength.val ≤ parameters.code.messageBlocks.val*parameters.code.blockWidth.val :=
  (NativeGoldBlockCodeMeaning.constructor_dimensions tables message block blowup parameters.code constructed).2.2.1

theorem constructor_complete (tables : NativeGoldBlockCode.Tables) (message block blowup : NativeUsizeMessage.Usize)
    (parameters : Parameters) (geometry : NativeBrakedownParameters.Geometry)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok parameters.code)
    (built : NativeBrakedownParameters.build NativeGoldBlockCode.description parameters = some geometry) :
    (validate parameters).value.map Checked.geometry = some geometry := by
  rw [validate_value,built,Option.bind_some,ite_eq_left (constructor_capacity tables message block blowup parameters constructed)]

def run (history : List Observation) (input : Input) (dummy : Vector Byte 64) (ctx : Context) (radius : ℕ) :=
  let validated := validate ctx.parameters
  match validated.value with
  | none => Run.mk none (validated.cost+2)
  | some checked =>
    let extracted := StoredGoldFieldExtraction.run history input dummy ctx radius checked.capacity
    Run.mk extracted.value (validated.cost+extracted.cost+3)

theorem run_validated (history : List Observation) (input : Input) (dummy : Vector Byte 64) (ctx : Context) (radius : ℕ)
    (checked : Checked ctx.parameters) (accepted : (validate ctx.parameters).value = some checked) :
    (run history input dummy ctx radius).value =
      (StoredGoldFieldExtraction.run history input dummy ctx radius checked.capacity).value ∧
    (run history input dummy ctx radius).cost = (validate ctx.parameters).cost+
      (StoredGoldFieldExtraction.run history input dummy ctx radius checked.capacity).cost+3 := by
  simp [run,accepted]

theorem run_reject (history : List Observation) (input : Input) (dummy : Vector Byte 64) (ctx : Context) (radius : ℕ)
    (rejected : (validate ctx.parameters).value = none) :
    (run history input dummy ctx radius).value = none ∧ (run history input dummy ctx radius).cost ≤ 1518 := by
  have bounded := validate_cost ctx.parameters
  simp only [run,rejected]
  exact ⟨True.intro,by omega⟩
def extractionBound (history : List Observation) (input : Input) (ctx : Context) (radius : ℕ) : ℕ :=
  587*input.length+6*StoredGoldBatchFieldInputCost.labelBytes+3554+(6*input.length+16)*history.length+
  StoredSourceSnapshotBudget.stepBound (ClosedByteMachineRootBudget.inputWork history)
    history.length (StoredShakeHistory.bytes history)*history.length+
  5308*ClosedByteMachineRootBudget.inputWork history^2+
  ((StoredGoldFieldSourceRecovery.run history input).value.map
    (fun result => CausalStoredGoldExtraction.sourceBound ctx result.log radius)).getD 0

theorem run_cost (history : List Observation) (input : Input) (dummy : Vector Byte 64) (ctx : Context) (radius : ℕ) :
    (run history input dummy ctx radius).cost ≤ 1519+extractionBound history input ctx radius := by
  have validated := validate_cost ctx.parameters
  simp only [run]
  split
  · dsimp only; omega
  · rename_i checked accepted
    have extracted := StoredGoldFieldExtraction.run_cost history input dummy ctx radius checked.capacity
    dsimp only [extractionBound]
    omega
end FormalProof4FHE.HasteBoots.ValidatedGoldFieldExtraction
