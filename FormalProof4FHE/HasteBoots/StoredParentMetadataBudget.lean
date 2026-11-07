module
public import FormalProof4FHE.HasteBoots.StoredParentMetadataHistory
@[expose] public section

/-! Polynomial running-time bounds for causal stored parent-metadata replay.
Input bytes, retained observations and actual observed output bytes parameterize
an extractor operation bound. This is not an attacker fee or physical-work credit.
All metadata bounds are derived from the compact reference invariant. -/
namespace FormalProof4FHE.HasteBoots.StoredParentMetadataBudget
open InputIndexedOracle (Input)
open NativeTranscript (Observation)
open StoredParentMetadataHistory (State initial record loop reconstruct Related discoverBound)
open StoredParentContributionsCost (Parent inputBytes sourceCount helperCount)
open ClosedByteMachineRootBudget (inputWork)
open StoredShakeHistory (bytes outputBytes)

private theorem inputWork_cons (entry : Observation) (tail : List Observation) :
    inputWork (entry::tail) = (NativeParentLedgerPools.inputOf entry).length+inputWork tail := rfl

theorem bytes_append (first later : List Observation) : bytes (first++later) = bytes first+bytes later := by
  induction first with
  | nil => simp [bytes]
  | cons head tail ih => simp only [List.cons_append,bytes,ih]; omega

theorem loop_cache_size (state : State) (history : List Observation) :
    (loop state history).value.cache.length = state.cache.length+bytes history := by
  induction history generalizing state with
  | nil => simp [loop,bytes]
  | cons entry tail ih =>
    simp only [loop,ih,record,StoredShakeHistory.record_size,bytes]
    omega

theorem loop_inputBytes (state : State) (history : List Observation) :
    inputBytes (loop state history).value.parents ≤ inputBytes state.parents+inputWork history := by
  induction history generalizing state with
  | nil => simp [loop,inputWork]
  | cons entry tail ih =>
    have first := StoredParentMetadataHistory.discover_inputBytes state.cache state.parents (NativeParentLedgerPools.inputOf entry)
    have rest := ih (record state entry).value
    simp only [loop,record,inputWork_cons] at *
    omega

theorem reconstruct_count (history : List Observation) : (reconstruct history).value.parents.length ≤ history.length := by
  have same := congrArg List.length (StoredParentMetadataHistory.reconstruct_related history).1
  rw [List.length_map] at same
  rw [same]
  exact CompactParentHistory.reconstruct_parent_count history

theorem metadataSize (parents : List Parent) (frozen : Finset NativeCanonicalLookupWire.Source) :
    sourceCount parents+helperCount parents =
      CompactParentLedger.metadataSize ⟨parents.map StoredParentContributionsCost.view,frozen⟩ := by
  induction parents with
  | nil => rfl
  | cons head tail ih =>
    simp only [CompactParentLedger.metadataSize,List.map_cons,List.sum_cons,
      StoredParentContributionsCost.view,List.length_map,sourceCount,helperCount] at *
    omega

def metadataBound (N P : ℕ) := P*(4*N^2+2*N)

theorem reconstruct_metadataSize (history : List Observation) :
    sourceCount (reconstruct history).value.parents+helperCount (reconstruct history).value.parents ≤
      metadataBound (inputWork history) history.length := by
  have same := (StoredParentMetadataHistory.reconstruct_related history).1
  have bound := CompactParentHistory.metadataSize_le_inputWork history
  rw [metadataSize _ (CompactParentHistory.reconstruct history).1.frozen] 
  have ledger : (⟨(reconstruct history).value.parents.map StoredParentContributionsCost.view,
      (CompactParentHistory.reconstruct history).1.frozen⟩ : NativeParentLedger.State) =
      (CompactParentHistory.reconstruct history).1 := by
    rw [same]
  rw [ledger]
  exact bound

def Majorized (state : State) (N P Q : ℕ) : Prop :=
  inputBytes state.parents ≤ N ∧ state.parents.length ≤ P ∧
    sourceCount state.parents ≤ metadataBound N P ∧ helperCount state.parents ≤ metadataBound N P ∧
    state.cache.length ≤ Q

theorem reconstruct_majorized (history : List Observation) (N P Q : ℕ)
    (inputs : inputWork history ≤ N) (count : history.length ≤ P) (outputs : bytes history ≤ Q) :
    Majorized (reconstruct history).value N P Q := by
  have inputSize := loop_inputBytes initial history
  simp only [initial,inputBytes,Nat.zero_add] at inputSize
  have cacheSize := loop_cache_size initial history
  have parentSize := reconstruct_count history
  have metadata := reconstruct_metadataSize history
  have square := Nat.mul_le_mul inputs inputs
  have total : 4*inputWork history^2+2*inputWork history ≤ 4*N^2+2*N := by nlinarith
  have scaled := Nat.mul_le_mul count total
  dsimp only [Majorized,metadataBound] at metadata ⊢
  refine ⟨?_,parentSize.trans count,?_,?_,?_⟩
  · exact (show inputBytes (reconstruct history).value.parents ≤ inputWork history from inputSize).trans inputs
  · omega
  · omega
  · change (loop initial history).value.cache.length ≤ Q
    rw [cacheSize]
    simpa only [initial,List.length_nil,Nat.zero_add] using outputs

/-- A uniform per-input operation bound under the proved metadata envelope. -/
def stepBound (N P Q : ℕ) : ℕ :=
  (27+StoredParentResolutionCost.inputFactor+StoredParentContextsCost.inputFactor)*N+
  12*StoredChildSeedQuote.seedLabel.length+6*ParentSeedRequestCost.label.length+
  6*ParentSeedRequestCost.message.length+1200+
  128*(6*N+14*P)*Q+922*P+6*metadataBound N P+(9*N+9)*metadataBound N P+
  1331*(N+metadataBound N P+metadataBound N P*N+1)^2+
  668*(N+metadataBound N P+1)^2

theorem discoverBound_le (state : State) (input : Input) (N P Q : ℕ)
    (majorized : Majorized state N P Q) (inputSize : input.length ≤ N) :
    discoverBound state.cache state.parents input ≤ stepBound N P Q := by
  obtain ⟨inputs,count,sources,helpers,outputs⟩ := majorized
  unfold discoverBound stepBound
  gcongr

theorem reconstruct_record_value (prior : List Observation) (entry : Observation) :
    (reconstruct (prior++[entry])).value = (record (reconstruct prior).value entry).value := by
  have append (state : State) :
      (loop state (prior++[entry])).value = (record (loop state prior).value entry).value := by
    induction prior generalizing state with
    | nil => rfl
    | cons head tail ih => exact ih (record state head).value
  exact append initial

theorem loop_cost (prior later : List Observation) (N P Q : ℕ)
    (inputs : inputWork (prior++later) ≤ N) (count : (prior++later).length ≤ P)
    (outputs : bytes (prior++later) ≤ Q) :
    (loop (reconstruct prior).value later).cost ≤ (stepBound N P Q+8*Q+8)*later.length+1 := by
  induction later generalizing prior with
  | nil => simp [loop]
  | cons entry tail ih =>
    have prefixInputs : inputWork prior ≤ N := by
      rw [ClosedByteMachineRootBudget.inputWork_append,inputWork_cons] at inputs
      omega
    have prefixCount : prior.length ≤ P := by simp only [List.length_append,List.length_cons] at count; omega
    have prefixOutputs : bytes prior ≤ Q := by rw [bytes_append,bytes] at outputs; omega
    have majorized := reconstruct_majorized prior N P Q prefixInputs prefixCount prefixOutputs
    have inputSize : (NativeParentLedgerPools.inputOf entry).length ≤ N := by
      rw [ClosedByteMachineRootBudget.inputWork_append,inputWork_cons] at inputs
      omega
    have outputSize : outputBytes entry ≤ Q := by rw [bytes_append,bytes] at outputs; omega
    have first := StoredParentMetadataHistory.record_cost (reconstruct prior).value entry
    have bounded := discoverBound_le (reconstruct prior).value (NativeParentLedgerPools.inputOf entry) N P Q majorized inputSize
    have nextInputs : inputWork ((prior++[entry])++tail) ≤ N := by simpa only [List.append_assoc,List.singleton_append] using inputs
    have nextCount : ((prior++[entry])++tail).length ≤ P := by simpa only [List.append_assoc,List.singleton_append] using count
    have nextOutputs : bytes ((prior++[entry])++tail) ≤ Q := by simpa only [List.append_assoc,List.singleton_append] using outputs
    have rest := ih (prior++[entry]) nextInputs nextCount nextOutputs
    rw [reconstruct_record_value] at rest
    simp only [loop,List.length_cons]
    nlinarith

theorem reconstruct_cost (history : List Observation) :
    (reconstruct history).cost ≤
      (stepBound (inputWork history) history.length (bytes history)+8*bytes history+8)*history.length+1 := by
  exact loop_cost [] history (inputWork history) history.length (bytes history) (by rfl) (by rfl) (by rfl)
end FormalProof4FHE.HasteBoots.StoredParentMetadataBudget
