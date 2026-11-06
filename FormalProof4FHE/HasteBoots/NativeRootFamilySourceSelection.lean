module
public import FormalProof4FHE.HasteBoots.NativeRootFamilyHistory
public import FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication
@[expose] public section

/-! Select one common source log from the actual earlier history. Existing
snapshots are found by finite search; a new key uses the current pre-read hash
log. Selection neither reads a world nor inspects future verifier work. -/
namespace FormalProof4FHE.HasteBoots.NativeRootFamilySourceSelection
open InputIndexedOracle (Input)
open NativeRootMessage (Digest)
open NativeCanonicalLookupWire (Source)
open NativeMerkleShapeFamily (Height shape)
open NativeRootFamilyState (State record)
open NativeTranscript (Observation)
open MerkleTreeMultiExtractability
noncomputable section
variable {Payload : Type}
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq
abbrev Log := MerkleTreeExtractor.QueryLog Input Digest

/-- The same full log, context and root must occur at every supported height. -/
def Full (state : State) (key : Source) (log : Log) : Prop := ∀ index : Height,
  ⟨(key.1,index),⟨key.2,log⟩⟩ ∈ state.2.checkpoints.checkpoints

def contains (state : State) (key : Source) (log : Log) : Bool :=
  (List.finRange 64).all (fun index => state.2.checkpoints.checkpoints.any (fun entry =>
    decide (entry.1 = (key.1,index) ∧ entry.2.root = key.2 ∧ entry.2.cumulativeLog = log)))

theorem contains_iff (state : State) (key : Source) (log : Log) : contains state key log = true ↔ Full state key log := by
  simp only [contains,List.all_eq_true,List.any_eq_true,decide_eq_true_eq]
  constructor
  · intro found index
    obtain ⟨entry,member,tag,root,logged⟩ := found index (List.mem_finRange index)
    rcases entry with ⟨tagValue,⟨rootValue,logValue⟩⟩
    dsimp only at tag root logged
    subst tagValue
    subst rootValue
    subst logValue
    exact member
  · intro full index _
    exact ⟨⟨(key.1,index),⟨key.2,log⟩⟩,full index,rfl,rfl,rfl⟩

/-- Finite checkpoint search, with the actual current log as fallback. -/
def select (state : State) (key : Source) : Log :=
  if key ∈ state.1.1.frozen then
    ((state.2.checkpoints.checkpoints.map (fun entry => entry.2.cumulativeLog)).find? (contains state key)).getD state.2.hash.log
  else state.2.hash.log

theorem select_new (state : State) (key : Source) (fresh : key ∉ state.1.1.frozen) :
    select state key = state.2.hash.log := by simp only [select,fresh,ite_false]

theorem select_old (state : State) (covered : NativeRootFamilyHistory.Covered state) (key : Source)
    (old : key ∈ state.1.1.frozen) : Full state key (select state key) := by
  obtain ⟨log,full⟩ := covered key old
  have present : log ∈ state.2.checkpoints.checkpoints.map (fun entry => entry.2.cumulativeLog) :=
    List.mem_map.mpr ⟨⟨(key.1,⟨0,by decide⟩),⟨key.2,log⟩⟩,full ⟨0,by decide⟩,rfl⟩
  have yes := (contains_iff state key log).mpr full
  cases found : (state.2.checkpoints.checkpoints.map (fun entry => entry.2.cumulativeLog)).find? (contains state key) with
  | none =>
    have absent := List.find?_eq_none.mp found log present
    rw [yes] at absent
    contradiction
  | some chosen =>
    have yesChosen := List.find?_some found
    have selected : select state key = chosen := by simp only [select,old,ite_true,found,Option.getD_some]
    rw [selected]
    exact (contains_iff state key chosen).mp yesChosen

/-- A positive read records the preselected common log at all heights,
whether the source key was old or first resolved by this pending input. -/
theorem selected_record (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (state : State) (covered : NativeRootFamilyHistory.Covered state) (key : Source)
    (input : Input) (offset : ℕ) (values : Input) (positive : values ≠ [])
    (resolved : key ∈ NativeParentLedger.resolve state.1.1 state.1.2 input) :
    Full (record enc dummy state (.output input offset values)) key (select state key) := by
  by_cases old : key ∈ state.1.1.frozen
  · intro index
    exact NativeRootFamilyHistory.record_retains enc dummy state _ _ _ (select_old state covered key old index)
  · rw [select_new state key old]
    intro index
    simp only [record,positive,ite_false]
    exact RecordRoots.recorded shape _ state.2 ((key.1,index),key.2)
      (NativeMerkleShapeFamily.requests_member _ key ((NativeParentLedger.prepare_mem _ _ _ _).mpr ⟨resolved,old⟩) index)

/-- Every continuation retains the log selected from the original prefix. -/
theorem selected_history (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (before after : List Observation) (key : Source) (input : Input) (offset : ℕ) (values : Input) (positive : values ≠ [])
    (resolved : key ∈ NativeParentLedger.resolve (NativeRootFamilyHistory.reconstruct enc dummy before).1.1
      (NativeRootFamilyHistory.reconstruct enc dummy before).1.2 input) :
    Full (NativeRootFamilyHistory.reconstruct enc dummy (before++ .output input offset values :: after)) key
      (select (NativeRootFamilyHistory.reconstruct enc dummy before) key) := by
  intro index
  have recorded := selected_record enc dummy _ (NativeRootFamilyHistory.reconstruct_covered enc dummy before) key input offset values positive resolved index
  simpa only [NativeRootFamilyHistory.reconstruct,List.foldl_append,List.foldl_cons] using
    NativeRootFamilyHistory.fold_retains enc dummy _ after _ _ recorded
end
end FormalProof4FHE.HasteBoots.NativeRootFamilySourceSelection
