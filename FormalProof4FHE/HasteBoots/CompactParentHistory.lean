module
public import FormalProof4FHE.HasteBoots.CompactParentLedger
public import FormalProof4FHE.HasteBoots.ExecutableSourceHistory
public import FormalProof4FHE.HasteBoots.ClosedByteMachineRootBudget
@[expose] public section

/-! Compact parent metadata for complete mixed histories. This module proves
membership equivalence and storage bounds. Snapshot selection is transported
separately by `CompactSourceHistory`; running-time refinement remains open. -/
namespace FormalProof4FHE.HasteBoots.CompactParentHistory
open InputIndexedOracle (Input)
open NativeTranscript (Observation)
abbrev State := NativeParentLedger.State × NativeShakeCache.Cache

def initial : State := (ExecutableParentLedger.empty,NativeShakeCache.empty)

def record (state : State) : Observation → State
  | .start input => (CompactParentLedger.discover state.1 state.2 input,state.2)
  | .hash input _ => (CompactParentLedger.discover state.1 state.2 input,state.2)
  | .output input offset values =>
    (if values = [] then CompactParentLedger.discover state.1 state.2 input
     else (CompactParentLedger.prepare state.1 state.2 input).next,
     ExecutableSourceHistory.writeBytes state.2 input offset values)

def reconstruct (history : List Observation) : State := history.foldl record initial

def Related (compact : State) (reference : ExecutableSourceHistory.State) : Prop :=
  CompactParentLedger.Related compact.1 reference.ledger ∧ compact.2 = reference.bytes

theorem record_related (compact : State) (reference : ExecutableSourceHistory.State) (related : Related compact reference)
    (entry : Observation) : Related (record compact entry) (ExecutableSourceHistory.record reference entry) := by
  obtain ⟨ledger,cache⟩ := related
  cases entry with
  | start input =>
    change CompactParentLedger.Related (CompactParentLedger.discover compact.1 compact.2 input)
      (ExecutableParentLedger.discover reference.ledger reference.bytes input) ∧ compact.2 = reference.bytes
    rw [cache]
    exact ⟨CompactParentLedger.discover_related ledger _ _,rfl⟩
  | hash input digest =>
    change CompactParentLedger.Related (CompactParentLedger.discover compact.1 compact.2 input)
      (ExecutableParentLedger.discover reference.ledger reference.bytes input) ∧ compact.2 = reference.bytes
    rw [cache]
    exact ⟨CompactParentLedger.discover_related ledger _ _,rfl⟩
  | output input offset values =>
    by_cases empty : values = []
    · subst values
      change CompactParentLedger.Related (CompactParentLedger.discover compact.1 compact.2 input)
        (ExecutableParentLedger.discover reference.ledger reference.bytes input) ∧ compact.2 = reference.bytes
      rw [cache]
      exact ⟨CompactParentLedger.discover_related ledger _ _,rfl⟩
    · simp only [Related,record,ExecutableSourceHistory.record,empty,ite_false]
      rw [cache]
      exact ⟨CompactParentLedger.prepare_related ledger _ _,rfl⟩

theorem reconstruct_related (history : List Observation) :
    Related (reconstruct history) (ExecutableSourceHistory.reconstruct history) := by
  have fold (compact : State) (reference : ExecutableSourceHistory.State) (related : Related compact reference) :
      Related (history.foldl record compact) (history.foldl ExecutableSourceHistory.record reference) := by
    induction history generalizing compact reference with
    | nil => exact related
    | cons entry rest ih => exact ih _ _ (record_related compact reference related entry)
  exact fold initial ExecutableSourceHistory.initial ⟨CompactParentLedger.related_refl _,rfl⟩

theorem record_distinct (state : State) (distinct : CompactParentLedger.Distinct state.1) (entry : Observation) :
    CompactParentLedger.Distinct (record state entry).1 := by
  cases entry with
  | start input => exact CompactParentLedger.discover_distinct _ distinct _ _
  | hash input digest => exact CompactParentLedger.discover_distinct _ distinct _ _
  | output input offset values =>
    simp only [record]
    split
    · exact CompactParentLedger.discover_distinct _ distinct _ _
    · exact CompactParentLedger.prepare_distinct _ distinct _ _

theorem reconstruct_distinct (history : List Observation) : CompactParentLedger.Distinct (reconstruct history).1 := by
  have fold (state : State) (distinct : CompactParentLedger.Distinct state.1) :
      CompactParentLedger.Distinct (history.foldl record state).1 := by
    induction history generalizing state with
    | nil => exact distinct
    | cons entry rest ih => exact ih _ (record_distinct state distinct entry)
  exact fold initial (by intro parent present; cases present)

theorem record_parent_count (state : State) (entry : Observation) :
    (record state entry).1.parents.length ≤ state.1.parents.length + 1 := by
  cases entry with
  | start input => exact CompactParentLedger.discover_parent_count _ _ _
  | hash input digest => exact CompactParentLedger.discover_parent_count _ _ _
  | output input offset values =>
    simp only [record]
    split
    · exact CompactParentLedger.discover_parent_count _ _ _
    · exact CompactParentLedger.prepare_parent_count _ _ _

theorem reconstruct_parent_count (history : List Observation) : (reconstruct history).1.parents.length ≤ history.length := by
  have fold (state : State) : (history.foldl record state).1.parents.length ≤ state.1.parents.length + history.length := by
    induction history generalizing state with
    | nil => simp
    | cons entry rest ih =>
      have tail := ih (record state entry)
      have head := record_parent_count state entry
      simp only [List.foldl_cons,List.length_cons]
      omega
  have bounded := fold initial
  change (reconstruct history).1.parents.length ≤ 0 + history.length at bounded
  simpa only [Nat.zero_add] using bounded

theorem metadataSize_le (history : List Observation) (pools : NativeParentLedgerPools.Pools)
    (coherent : NativeParentLedgerPools.Coherent (ExecutableSourceHistory.reconstruct history).ledger pools) :
    CompactParentLedger.metadataSize (reconstruct history).1 ≤
      history.length * (pools.contexts.card * pools.roots.card + pools.contexts.card) := by
  have compactCoherent := CompactParentLedger.coherent_related (reconstruct_related history).1 pools coherent
  exact (CompactParentLedger.metadataSize_le _ (reconstruct_distinct history) pools compactCoherent).trans
    (Nat.mul_le_mul_right _ (reconstruct_parent_count history))

theorem reconstruct_coherent (history : List Observation) :
    NativeParentLedgerPools.Coherent (reconstruct history).1 (NativeParentLedgerPools.observedPools history) := by
  have reference : NativeParentLedgerPools.Coherent (ExecutableSourceHistory.reconstruct history).ledger
      (NativeParentLedgerPools.observedPools history) := by
    rw [ExecutableSourceHistory.reconstruct_eq NativeGoldColumnAuthentication.encoding (fun _ => 0)]
    exact NativeParentLedgerPools.reconstructed_coherent (fun _ => 0) history
  exact CompactParentLedger.coherent_related (reconstruct_related history).1 _ reference

theorem metadataSize_le_inputWork (history : List Observation) :
    CompactParentLedger.metadataSize (reconstruct history).1 ≤
      history.length * (4 * ClosedByteMachineRootBudget.inputWork history ^ 2 + 2 * ClosedByteMachineRootBudget.inputWork history) := by
  have coherent := reconstruct_coherent history
  have raw := CompactParentLedger.metadataSize_le _ (reconstruct_distinct history) _ coherent
  have count := reconstruct_parent_count history
  obtain ⟨contexts,roots⟩ := ClosedByteMachineRootBudget.observed_pools_card history
  have product := Nat.mul_le_mul contexts roots
  have total : (NativeParentLedgerPools.observedPools history).contexts.card *
      (NativeParentLedgerPools.observedPools history).roots.card + (NativeParentLedgerPools.observedPools history).contexts.card ≤
      4 * ClosedByteMachineRootBudget.inputWork history ^ 2 + 2 * ClosedByteMachineRootBudget.inputWork history := by
    nlinarith
  exact raw.trans (Nat.mul_le_mul count total)
end FormalProof4FHE.HasteBoots.CompactParentHistory
