module
public import FormalProof4FHE.HasteBoots.StoredGoldBatchFieldInputCost
public import FormalProof4FHE.HasteBoots.CausalStoredSourceRecovery
@[expose] public section

/-! Recover the original Gold field's source from its complete raw input and
mixed history. The full stored context/root comes from the strict structural
field parser, rather than caller callbacks or supplied source certificates.
Application parameter/ownership validation and physical refinement remain open. -/
namespace FormalProof4FHE.HasteBoots.StoredGoldFieldSourceRecovery
open InputIndexedOracle (Input)
open NativeTranscript (Observation)
open SolverOperationCost (Run)
open StoredGoldBatchFieldInputCost (Stored view)
open StoredGoldPublicSource (Log viewLog)

structure Recovered where
  field : Stored
  log : Log

def resultView (result : Recovered) := (view result.field,viewLog result.log)

def run (history : List Observation) (input : Input) : Run (Option Recovered) :=
  let parsed := StoredGoldBatchFieldInputCost.parse input
  match parsed.value with
  | none => ⟨none,parsed.cost+2⟩
  | some field =>
    let recovered := CausalStoredSourceRecovery.run history input field.data.source
    ⟨recovered.value.map (fun log => ⟨field,log⟩),parsed.cost+recovered.cost+3⟩

theorem field_recovery (history : List Observation) (input : Input) (field : Stored)
    (parsed : (StoredGoldBatchFieldInputCost.parse input).value = some field) :
    (CausalStoredSourceRecovery.run history input field.data.source).value.map viewLog =
      ExecutableSourceSelection.recover history (view field) := by
  apply CausalStoredSourceRecovery.run_field_value history input field.data.source (view field)
  · exact (StoredGoldBatchFieldInputCost.parse_sound input field parsed).1.symm
  · rfl

theorem run_value (history : List Observation) (input : Input) :
    (run history input).value.map resultView = (NativeGoldBatchFieldInputView.parse input).bind (fun field =>
      (ExecutableSourceSelection.recover history field).map (fun log => (field,log))) := by
  simp only [run,← StoredGoldBatchFieldInputCost.parse_value]
  cases parsed : (StoredGoldBatchFieldInputCost.parse input).value with
  | none => rfl
  | some field =>
    have recovered := field_recovery history input field parsed
    cases found : (CausalStoredSourceRecovery.run history input field.data.source).value with
    | none =>
      rw [found,Option.map_none] at recovered
      simp only [found,Option.map_some,Option.bind_some,← recovered,Option.map_none]
    | some log =>
      rw [found,Option.map_some] at recovered
      simp only [found,Option.map_some,Option.bind_some,← recovered,resultView]

theorem run_cost (history : List Observation) (input : Input) :
    (run history input).cost ≤ 587*input.length+6*StoredGoldBatchFieldInputCost.labelBytes+3422+
      (6*input.length+16)*history.length+
      StoredSourceSnapshotBudget.stepBound (ClosedByteMachineRootBudget.inputWork history)
        history.length (StoredShakeHistory.bytes history)*history.length+
      5308*ClosedByteMachineRootBudget.inputWork history^2 := by
  have parsed := StoredGoldBatchFieldInputCost.parse_cost input
  simp only [run]
  split
  · dsimp only; omega
  · rename_i field found
    have recovered := CausalStoredSourceRecovery.run_cost history input field.data.source
    dsimp only
    omega

theorem run_parsed (history : List Observation) (input : Input) (result : Recovered)
    (found : (run history input).value = some result) :
    (StoredGoldBatchFieldInputCost.parse input).value = some result.field := by
  simp only [run] at found
  split at found
  · cases found
  · rename_i field parsed
    obtain ⟨log,_,same⟩ := Option.map_eq_some_iff.mp found
    cases same
    exact parsed
end FormalProof4FHE.HasteBoots.StoredGoldFieldSourceRecovery
