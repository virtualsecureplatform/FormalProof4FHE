module
public import FormalProof4FHE.HasteBoots.StoredSourceSnapshotHistory
@[expose] public section

/-! Polynomial causal stored snapshot replay. Logs are immutable shared data;
mark creation charges pointer/record construction, while log append traversals
and fixed digest decoding are priced separately. Physical/backend refinement
and source selection remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.StoredSourceSnapshotBudget
open InputIndexedOracle (Input)
open NativeTranscript (Observation)
open StoredSourceSnapshotHistory (State record loop reconstruct)
open StoredParentMetadataBudget (Majorized metadataBound)
open ClosedByteMachineRootBudget (inputWork)
open StoredShakeHistory (bytes outputBytes)

theorem request_size (state : State) (entry : Observation) (N P Q : ℕ)
    (metadata : Majorized state.ledger.metadata N P Q)
    (inputSize : (NativeParentLedgerPools.inputOf entry).length ≤ N) :
    (StoredFrozenLedgerHistory.record state.ledger entry).value.requests.length ≤ StoredFrozenLedgerBudget.sourceBound N P := by
  cases entry with
  | start input => exact Nat.zero_le _
  | hash input digest => exact Nat.zero_le _
  | output input offset values =>
    cases values with
    | nil => exact Nat.zero_le _
    | cons byte tail =>
      change input.length ≤ N at inputSize
      have prepared := StoredFrozenRequestsCost.prepare_size state.ledger.metadata.cache state.ledger.metadata.parents state.ledger.frozen input
      have resolved := StoredParentResolutionCost.resolve_size state.ledger.metadata.cache state.ledger.metadata.parents input
      obtain ⟨inputs,count,sources,helpers,outputs⟩ := metadata
      have cross := Nat.mul_le_mul helpers inputSize
      change (StoredFrozenRequestsCost.prepare _ _ _ _).value.requests.length ≤ _
      unfold StoredFrozenLedgerBudget.sourceBound
      nlinarith

def stepBound (N P Q : ℕ) := StoredFrozenLedgerBudget.stepBound N P Q+
  4*StoredFrozenLedgerBudget.sourceBound N P+12*N^2+3*P+271

theorem record_cost (state : State) (entry : Observation) (N P Q : ℕ)
    (metadata : Majorized state.ledger.metadata N P Q) (frozen : state.ledger.frozen.length ≤ 4*N^2)
    (snapshots : state.snapshots.length ≤ 4*N^2) (hashes : state.hashes.length ≤ P)
    (inputSize : (NativeParentLedgerPools.inputOf entry).length ≤ N) (outputSize : outputBytes entry ≤ Q) :
    (record state entry).cost+2 ≤ stepBound N P Q := by
  have ledger := StoredFrozenLedgerBudget.record_cost state.ledger entry N P Q metadata frozen inputSize outputSize
  have bounded := StoredSourceSnapshotHistory.record_cost state entry
  have requests := request_size state entry N P Q metadata inputSize
  unfold stepBound
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
    have metadata : Majorized (reconstruct prior).value.ledger.metadata N P Q := by
      rw [StoredSourceSnapshotHistory.reconstruct_ledger,StoredFrozenLedgerHistory.reconstruct_metadata]
      exact StoredParentMetadataBudget.reconstruct_majorized prior N P Q (by omega) (by omega) (by omega)
    have square := Nat.mul_le_mul (show inputWork prior ≤ N by omega) (show inputWork prior ≤ N by omega)
    have frozenSize : (reconstruct prior).value.ledger.frozen.length ≤ 4*N^2 := by
      rw [StoredSourceSnapshotHistory.reconstruct_ledger]
      have bound := StoredFrozenLedgerHistory.reconstruct_frozen_size prior
      nlinarith
    have snapshotSize : (reconstruct prior).value.snapshots.length ≤ 4*N^2 := by
      have bound := StoredSourceSnapshotHistory.reconstruct_snapshots_size prior
      nlinarith
    have hashSize : (reconstruct prior).value.hashes.length ≤ P :=
      (StoredSourceSnapshotHistory.reconstruct_hashes_size prior).trans (by omega)
    have first := record_cost (reconstruct prior).value entry N P Q metadata frozenSize snapshotSize hashSize (by omega) (by omega)
    have nextInputs : inputWork ((prior++[entry])++tail) ≤ N := by simpa only [List.append_assoc,List.singleton_append] using inputs
    have nextCount : ((prior++[entry])++tail).length ≤ P := by simpa only [List.append_assoc,List.singleton_append] using count
    have nextOutputs : bytes ((prior++[entry])++tail) ≤ Q := by simpa only [List.append_assoc,List.singleton_append] using outputs
    have rest := ih (prior++[entry]) nextInputs nextCount nextOutputs
    rw [StoredSourceSnapshotHistory.reconstruct_record_value] at rest
    simp only [loop,List.length_cons]
    nlinarith

theorem reconstruct_cost (history : List Observation) :
    (reconstruct history).cost ≤ stepBound (inputWork history) history.length (bytes history)*history.length+1 :=
  loop_cost [] history (inputWork history) history.length (bytes history) le_rfl le_rfl le_rfl
end FormalProof4FHE.HasteBoots.StoredSourceSnapshotBudget
