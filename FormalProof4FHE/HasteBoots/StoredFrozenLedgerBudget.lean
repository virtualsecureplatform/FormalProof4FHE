module
public import FormalProof4FHE.HasteBoots.StoredFrozenLedgerHistory
@[expose] public section

/-! Polynomial cost of the complete stored ledger/cache/frozen-key replay.
These are extractor operation bounds derived from actual replay sizes, not
attacker fee proxies. Snapshot-log storage and selection remain separate. -/
namespace FormalProof4FHE.HasteBoots.StoredFrozenLedgerBudget
open InputIndexedOracle (Input)
open NativeTranscript (Observation)
open StoredFrozenLedgerHistory (Ledger record loop reconstruct)
open StoredParentMetadataBudget (metadataBound Majorized)
open ClosedByteMachineRootBudget (inputWork)
open StoredShakeHistory (bytes outputBytes)

def sourceBound (N P : ℕ) := N+metadataBound N P*(N+1)

def requestBound (N P Q : ℕ) :=
  StoredHistorySourceResolutionCost.resolutionBound N P Q N+
  1331*(sourceBound N P+1)^2+(1327*(4*N^2)+5)*sourceBound N P+3*(4*N^2)+7

theorem prepare_cost (state : Ledger) (input : Input) (N P Q : ℕ)
    (metadata : Majorized state.metadata N P Q) (frozen : state.frozen.length ≤ 4*N^2)
    (inputSize : input.length ≤ N) :
    (StoredFrozenRequestsCost.prepare state.metadata.cache state.metadata.parents state.frozen input).cost ≤ requestBound N P Q := by
  obtain ⟨inputs,count,sources,helpers,outputs⟩ := metadata
  have resolved := StoredParentResolutionCost.resolve_cost state.metadata.cache state.metadata.parents input
  have resolvedBound : (StoredParentResolutionCost.resolve state.metadata.cache state.metadata.parents input).cost ≤
      StoredHistorySourceResolutionCost.resolutionBound N P Q N := by
    apply resolved.trans
    unfold StoredHistorySourceResolutionCost.resolutionBound
    gcongr
  have size := StoredParentResolutionCost.resolve_size state.metadata.cache state.metadata.parents input
  have cross := Nat.mul_le_mul helpers inputSize
  have sizeBound : (StoredParentResolutionCost.resolve state.metadata.cache state.metadata.parents input).value.length ≤ sourceBound N P := by
    unfold sourceBound
    nlinarith
  have prepared := StoredFrozenRequestsCost.prepare_cost state.metadata.cache state.metadata.parents state.frozen input
  apply prepared.trans
  unfold requestBound
  gcongr

def stepBound (N P Q : ℕ) := StoredParentMetadataBudget.stepBound N P Q+8*Q+requestBound N P Q+12

theorem record_cost (state : Ledger) (entry : Observation) (N P Q : ℕ)
    (metadata : Majorized state.metadata N P Q) (frozen : state.frozen.length ≤ 4*N^2)
    (inputSize : (NativeParentLedgerPools.inputOf entry).length ≤ N) (outputSize : outputBytes entry ≤ Q) :
    (record state entry).cost+2 ≤ stepBound N P Q := by
  have metadataRun := StoredParentMetadataHistory.record_cost state.metadata entry
  have metadataBound := StoredParentMetadataBudget.discoverBound_le state.metadata (NativeParentLedgerPools.inputOf entry) N P Q metadata inputSize
  have bounded := StoredFrozenLedgerHistory.record_cost state entry
  cases entry with
  | start input =>
    simp only [stepBound,outputBytes] at *
    omega
  | hash input digest =>
    simp only [stepBound,outputBytes] at *
    omega
  | output input offset values =>
    cases values with
    | nil =>
      simp only [stepBound,outputBytes] at *
      omega
    | cons byte tail =>
      have prepared := prepare_cost state input N P Q metadata frozen inputSize
      simp only [stepBound] at *
      omega

theorem loop_cost (prior later : List Observation) (N P Q : ℕ)
    (inputs : inputWork (prior++later) ≤ N) (count : (prior++later).length ≤ P)
    (outputs : bytes (prior++later) ≤ Q) :
    (loop (reconstruct prior).value later).cost ≤ stepBound N P Q*later.length+1 := by
  induction later generalizing prior with
  | nil => simp [loop]
  | cons entry tail ih =>
    have inputsSplit : inputWork prior+(NativeParentLedgerPools.inputOf entry).length+inputWork tail ≤ N := by
      have splitInputs := inputs
      rw [ClosedByteMachineRootBudget.inputWork_append] at splitInputs
      change inputWork prior+((NativeParentLedgerPools.inputOf entry).length+inputWork tail) ≤ N at splitInputs
      omega
    have outputsSplit : bytes prior+outputBytes entry+bytes tail ≤ Q := by
      simpa only [StoredParentMetadataBudget.bytes_append,bytes,Nat.add_assoc] using outputs
    have countSplit : prior.length+1+tail.length ≤ P := by
      simpa only [List.length_append,List.length_cons,Nat.add_assoc,Nat.add_comm 1] using count
    have metadata : Majorized (reconstruct prior).value.metadata N P Q := by
      rw [StoredFrozenLedgerHistory.reconstruct_metadata]
      exact StoredParentMetadataBudget.reconstruct_majorized prior N P Q (by omega) (by omega) (by omega)
    have size := StoredFrozenLedgerHistory.reconstruct_frozen_size prior
    have square := Nat.mul_le_mul (show inputWork prior ≤ N by omega) (show inputWork prior ≤ N by omega)
    have frozen : (reconstruct prior).value.frozen.length ≤ 4*N^2 := by nlinarith
    have first := record_cost (reconstruct prior).value entry N P Q metadata frozen (by omega) (by omega)
    have nextInputs : inputWork ((prior++[entry])++tail) ≤ N := by simpa only [List.append_assoc,List.singleton_append] using inputs
    have nextCount : ((prior++[entry])++tail).length ≤ P := by simpa only [List.append_assoc,List.singleton_append] using count
    have nextOutputs : bytes ((prior++[entry])++tail) ≤ Q := by simpa only [List.append_assoc,List.singleton_append] using outputs
    have rest := ih (prior++[entry]) nextInputs nextCount nextOutputs
    rw [StoredFrozenLedgerHistory.reconstruct_record_value] at rest
    simp only [loop,List.length_cons]
    nlinarith

theorem reconstruct_cost (history : List Observation) :
    (reconstruct history).cost ≤ stepBound (inputWork history) history.length (bytes history)*history.length+1 :=
  loop_cost [] history (inputWork history) history.length (bytes history) le_rfl le_rfl le_rfl
end FormalProof4FHE.HasteBoots.StoredFrozenLedgerBudget
