module
public import FormalProof4FHE.HasteBoots.StoredParentMetadataBudget
@[expose] public section

/-! Complete-history source resolution using causally replayed stored metadata.
This closes the source/helper inheritance path, not frozen-request extraction,
snapshot ownership, application soundness, or physical/compiler refinement. -/
namespace FormalProof4FHE.HasteBoots.StoredHistorySourceResolutionCost
open InputIndexedOracle (Input)
open NativeTranscript (Observation)
open SolverOperationCost (Run)
open StoredSourceVectorReadCost (Source sourceView)
open StoredParentMetadataHistory (reconstruct)
open StoredParentMetadataBudget (metadataBound)
open ClosedByteMachineRootBudget (inputWork)
open StoredShakeHistory (bytes)

def run (history : List Observation) (input : Input) : Run (List Source) :=
  let state := reconstruct history
  let resolved := StoredParentResolutionCost.resolve state.value.cache state.value.parents input
  ⟨resolved.value,state.cost+resolved.cost+1⟩

theorem run_value (history : List Observation) (input : Input) :
    (run history input).value.map sourceView =
      ExecutableParentLedger.resolve (CompactSourceHistory.reconstruct history).ledger
        (CompactSourceHistory.reconstruct history).bytes input := by
  simp only [run,StoredParentResolutionCost.resolve_value,ExecutableParentLedger.resolve,
    ExecutableParentLedger.active,StoredParentResolutionCost.ledgerView,
    StoredParentMetadataHistory.reconstruct_parents,StoredParentMetadataHistory.reconstruct_cache]

def resolutionBound (N P Q inputSize : ℕ) : ℕ :=
  StoredParentResolutionCost.inputFactor*inputSize+6*StoredChildSeedQuote.seedLabel.length+600+
  64*(6*N+14*P)*Q+464*P+6*metadataBound N P+(9*inputSize+6)*metadataBound N P

theorem resolution_cost (history : List Observation) (input : Input) :
    (StoredParentResolutionCost.resolve (reconstruct history).value.cache
      (reconstruct history).value.parents input).cost ≤
      resolutionBound (inputWork history) history.length (bytes history) input.length := by
  have bounded := StoredParentResolutionCost.resolve_cost (reconstruct history).value.cache
    (reconstruct history).value.parents input
  obtain ⟨inputs,count,sources,helpers,outputs⟩ := StoredParentMetadataBudget.reconstruct_majorized
    history (inputWork history) history.length (bytes history) le_rfl le_rfl le_rfl
  apply bounded.trans
  unfold resolutionBound
  gcongr

theorem run_cost (history : List Observation) (input : Input) :
    (run history input).cost ≤
      (StoredParentMetadataBudget.stepBound (inputWork history) history.length (bytes history)+
        8*bytes history+8)*history.length+
      resolutionBound (inputWork history) history.length (bytes history) input.length+2 := by
  have replayed := StoredParentMetadataBudget.reconstruct_cost history
  have resolved := resolution_cost history input
  simp only [run]
  omega

theorem run_size (history : List Observation) (input : Input) :
    (run history input).value.length ≤ input.length+
      metadataBound (inputWork history) history.length*(input.length+1) := by
  have bounded := StoredParentResolutionCost.resolve_size (reconstruct history).value.cache
    (reconstruct history).value.parents input
  obtain ⟨inputs,count,sources,helpers,outputs⟩ := StoredParentMetadataBudget.reconstruct_majorized
    history (inputWork history) history.length (bytes history) le_rfl le_rfl le_rfl
  have scaled := Nat.mul_le_mul_right input.length helpers
  simp only [run]
  nlinarith
end FormalProof4FHE.HasteBoots.StoredHistorySourceResolutionCost
