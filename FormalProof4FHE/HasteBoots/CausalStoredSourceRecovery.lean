module
public import FormalProof4FHE.HasteBoots.CausalPrefixReadCost
@[expose] public section

/-! Recover the original stream boundary and select its stored source from the
complete preceding mixed history. Future hashes/reads are never substituted for
the first-read prefix. The stream and full context/root key are stored input data;
parsing the original field input and whole-extractor refinement are separate. -/
namespace FormalProof4FHE.HasteBoots.CausalStoredSourceRecovery
open InputIndexedOracle (Input)
open NativeTranscript (Observation)
open StoredSourceVectorReadCost (Source sourceView)
open StoredGoldPublicSource (Log viewLog)
open SolverOperationCost (Run)
open ClosedByteMachineRootBudget (inputWork)
open StoredShakeHistory (bytes)

def run (history : List Observation) (input : Input) (key : Source) : Run (Option Log) :=
  let recovered := CausalPrefixReadCost.recover input history
  match recovered.value with
  | none => ⟨none,recovered.cost+2⟩
  | some before =>
    let selected := StoredSourceSnapshotSelection.run before key
    ⟨some selected.value,recovered.cost+selected.cost+3⟩

theorem run_value (history : List Observation) (input : Input) (key : Source) :
    (run history input key).value.map viewLog = (CausalFirstStreamPrefix.recover input history).map
      (fun before => ExecutableSourceSelection.select (ExecutableSourceHistory.reconstruct before) (sourceView key)) := by
  simp only [run,CausalPrefixReadCost.recover_value]
  cases found : CausalFirstStreamPrefix.recover input history with
  | none => rfl
  | some before => simp only [Option.map_some,StoredSourceSnapshotSelection.run_value]

theorem recovered_sizes (history before : List Observation) (input : Input)
    (found : (CausalPrefixReadCost.recover input history).value = some before) :
    inputWork before ≤ inputWork history ∧ before.length ≤ history.length ∧ bytes before ≤ bytes history := by
  obtain ⟨_,offset,values,after,_,same⟩ := CausalPrefixReadCost.recover_sound input history before found
  rw [same]
  constructor
  · rw [ClosedByteMachineRootBudget.inputWork_append]
    exact Nat.le_add_right _ _
  · constructor
    · simp only [List.length_append,List.length_cons]; omega
    · rw [StoredParentMetadataBudget.bytes_append]
      exact Nat.le_add_right _ _

theorem stepBound_mono (N P Q nextN nextP nextQ : ℕ)
    (inputs : N ≤ nextN) (count : P ≤ nextP) (outputs : Q ≤ nextQ) :
    StoredSourceSnapshotBudget.stepBound N P Q ≤ StoredSourceSnapshotBudget.stepBound nextN nextP nextQ := by
  unfold StoredSourceSnapshotBudget.stepBound StoredFrozenLedgerBudget.stepBound
    StoredFrozenLedgerBudget.requestBound StoredFrozenLedgerBudget.sourceBound
    StoredParentMetadataBudget.stepBound StoredHistorySourceResolutionCost.resolutionBound
    StoredParentMetadataBudget.metadataBound
  gcongr

theorem selected_cost (history before : List Observation) (input : Input) (key : Source)
    (found : (CausalPrefixReadCost.recover input history).value = some before) :
    (StoredSourceSnapshotSelection.run before key).cost ≤
      StoredSourceSnapshotBudget.stepBound (inputWork history) history.length (bytes history)*history.length+
      5308*inputWork history^2+5 := by
  obtain ⟨inputs,count,outputs⟩ := recovered_sizes history before input found
  have bounded := StoredSourceSnapshotSelection.run_cost before key
  have step := stepBound_mono (inputWork before) before.length (bytes before)
    (inputWork history) history.length (bytes history) inputs count outputs
  have replay := Nat.mul_le_mul step count
  have square := Nat.mul_le_mul inputs inputs
  nlinarith

theorem run_cost (history : List Observation) (input : Input) (key : Source) :
    (run history input key).cost ≤ (6*input.length+16)*history.length+
      StoredSourceSnapshotBudget.stepBound (inputWork history) history.length (bytes history)*history.length+
      5308*inputWork history^2+9 := by
  have recovered := CausalPrefixReadCost.recover_cost input history
  simp only [run]
  split
  · dsimp only; omega
  · rename_i before found
    have selected := selected_cost history before input key found
    dsimp only
    omega

theorem run_at (before after : List Observation) (input : Input) (key : Source) (offset : ℕ) (values : Input)
    (unseen : CausalStreamExposure.seen before input = false) (positive : values ≠ []) :
    (run (before++ .output input offset values :: after) input key).value =
      some (StoredSourceSnapshotSelection.run before key).value := by
  have touched : CausalStreamExposure.touches input (.output input offset values) = true := by
    simp only [CausalStreamExposure.touches,decide_eq_true_eq]
    exact ⟨True.intro,List.length_pos_iff.mpr positive⟩
  simp only [run,CausalPrefixReadCost.recover_at input before after _ unseen touched]

theorem run_field_value (history : List Observation) (input : Input) (key : Source)
    (field : NativeGoldBatchFieldInputView.View) (stream : input = NativeGoldBatchFirstFieldSource.input field)
    (source : sourceView key = (field.data.context,field.data.root)) :
    (run history input key).value.map viewLog = ExecutableSourceSelection.recover history field := by
  rw [run_value,stream]
  simp only [ExecutableSourceSelection.recover,ExecutableSourceSelection.selected,
    NativeGoldBatchFirstFieldSource.input,source]

theorem run_append (history later : List Observation) (input : Input) (key : Source) (log : Log)
    (found : (run history input key).value = some log) :
    (run (history++later) input key).value = some log := by
  simp only [run] at found
  split at found
  · cases found
  · rename_i before recovered
    have stable := CausalPrefixReadCost.recover_append input history later before recovered
    simp only [run,stable]
    exact found
end FormalProof4FHE.HasteBoots.CausalStoredSourceRecovery
