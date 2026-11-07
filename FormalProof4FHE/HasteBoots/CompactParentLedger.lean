module
public import FormalProof4FHE.HasteBoots.ExecutableParentLedger
public import FormalProof4FHE.HasteBoots.NativeParentLedgerPools
public import Mathlib.Data.List.Dedup
@[expose] public section

/-! Compact inherited metadata without choosing a single compatible parent.
Ordering and duplicate multiplicity are irrelevant to membership, while every
parent input and every source/helper possibility is retained. Snapshot ordering
is transported separately by `CompactSourceHistory`. -/
namespace FormalProof4FHE.HasteBoots.CompactParentLedger
open InputIndexedOracle (Input)
open NativeRootMessage (Digest)
open NativeCanonicalLookupWire (Source)
open NativeParentLedger (State Parent Plan)
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

structure ParentRelated (compact reference : Parent) : Prop where
  input : compact.input = reference.input
  sources : ∀ key, key ∈ compact.sources ↔ key ∈ reference.sources
  helpers : ∀ context, context ∈ compact.helpers ↔ context ∈ reference.helpers

structure Related (compact reference : State) : Prop where
  frozen : compact.frozen = reference.frozen
  forward : ∀ parent ∈ compact.parents, ∃ other ∈ reference.parents, ParentRelated parent other
  backward : ∀ other ∈ reference.parents, ∃ parent ∈ compact.parents, ParentRelated parent other

def discover (state : State) (cache : NativeShakeCache.Cache) (input : Input) : State :=
  match ExecutableParentInputView.parseParent input with
  | none => state
  | some _ => { state with parents :=
      ⟨input,(ExecutableParentLedger.resolve state cache input).dedup,
        (ExecutableParentLedger.contexts state cache input).dedup⟩ :: state.parents }

def prepare (state : State) (cache : NativeShakeCache.Cache) (input : Input) : Plan :=
  let requests := (ExecutableParentLedger.resolve state cache input).dedup.filter (fun key => key ∉ state.frozen)
  ⟨requests,{ discover state cache input with frozen := state.frozen ∪ requests.toFinset }⟩

theorem related_refl (state : State) : Related state state := by
  refine ⟨rfl,?_,?_⟩ <;> intro parent present <;> exact ⟨parent,present,⟨rfl,fun _ => Iff.rfl,fun _ => Iff.rfl⟩⟩

theorem active_forward {compact reference : State} (related : Related compact reference)
    (cache : NativeShakeCache.Cache) (input : Input) (parent : Parent)
    (present : parent ∈ ExecutableParentLedger.active compact cache input) :
    ∃ other ∈ ExecutableParentLedger.active reference cache input, ParentRelated parent other := by
  unfold ExecutableParentLedger.active at present ⊢
  cases quoted : NativeChildSeedView.quote input with
  | none => simp only [quoted,List.not_mem_nil] at present
  | some seed =>
    simp only [quoted,List.mem_filter] at present ⊢
    obtain ⟨other,member,relation⟩ := related.forward parent present.1
    exact ⟨other,⟨member,by rw [← relation.input]; exact present.2⟩,relation⟩

theorem active_backward {compact reference : State} (related : Related compact reference)
    (cache : NativeShakeCache.Cache) (input : Input) (other : Parent)
    (present : other ∈ ExecutableParentLedger.active reference cache input) :
    ∃ parent ∈ ExecutableParentLedger.active compact cache input, ParentRelated parent other := by
  unfold ExecutableParentLedger.active at present ⊢
  cases quoted : NativeChildSeedView.quote input with
  | none => simp only [quoted,List.not_mem_nil] at present
  | some seed =>
    simp only [quoted,List.mem_filter] at present ⊢
    obtain ⟨parent,member,relation⟩ := related.backward other present.1
    exact ⟨parent,⟨member,by rw [relation.input]; exact present.2⟩,relation⟩

theorem contribution_iff {parent other : Parent} (related : ParentRelated parent other)
    (roots : List Digest) (key : Source) :
    (key ∈ parent.sources ∨ ∃ context ∈ parent.helpers, key ∈ roots.map (fun root => (context,root))) ↔
      (key ∈ other.sources ∨ ∃ context ∈ other.helpers, key ∈ roots.map (fun root => (context,root))) := by
  simp_rw [related.sources,related.helpers]

theorem resolve_iff {compact reference : State} (related : Related compact reference)
    (cache : NativeShakeCache.Cache) (input : Input) (key : Source) :
    key ∈ ExecutableParentLedger.resolve compact cache input ↔ key ∈ ExecutableParentLedger.resolve reference cache input := by
  simp only [ExecutableParentLedger.resolve,List.mem_append,List.mem_flatMap]
  constructor
  · rintro (localKey | ⟨parent,present,member⟩)
    · exact Or.inl localKey
    · obtain ⟨other,active,relation⟩ := active_forward related cache input parent present
      exact Or.inr ⟨other,active,(contribution_iff relation _ key).mp member⟩
  · rintro (localKey | ⟨other,present,member⟩)
    · exact Or.inl localKey
    · obtain ⟨parent,active,relation⟩ := active_backward related cache input other present
      exact Or.inr ⟨parent,active,(contribution_iff relation _ key).mpr member⟩

theorem contexts_iff {compact reference : State} (related : Related compact reference)
    (cache : NativeShakeCache.Cache) (input : Input) (context : Digest) :
    context ∈ ExecutableParentLedger.contexts compact cache input ↔ context ∈ ExecutableParentLedger.contexts reference cache input := by
  simp only [ExecutableParentLedger.contexts,List.mem_append,List.mem_flatMap]
  constructor
  · rintro (localContext | ⟨parent,present,member⟩)
    · exact Or.inl localContext
    · obtain ⟨other,active,relation⟩ := active_forward related cache input parent present
      exact Or.inr ⟨other,active,(relation.helpers context).mp member⟩
  · rintro (localContext | ⟨other,present,member⟩)
    · exact Or.inl localContext
    · obtain ⟨parent,active,relation⟩ := active_backward related cache input other present
      exact Or.inr ⟨parent,active,(relation.helpers context).mpr member⟩

theorem discover_related {compact reference : State} (related : Related compact reference)
    (cache : NativeShakeCache.Cache) (input : Input) :
    Related (discover compact cache input) (ExecutableParentLedger.discover reference cache input) := by
  unfold discover ExecutableParentLedger.discover
  cases parsed : ExecutableParentInputView.parseParent input with
  | none => exact related
  | some frames =>
    have newest : ParentRelated
        ⟨input,(ExecutableParentLedger.resolve compact cache input).dedup,(ExecutableParentLedger.contexts compact cache input).dedup⟩
        ⟨input,ExecutableParentLedger.resolve reference cache input,ExecutableParentLedger.contexts reference cache input⟩ := by
      refine ⟨rfl,?_,?_⟩
      · intro key; simpa only [List.mem_dedup] using resolve_iff related cache input key
      · intro context; simpa only [List.mem_dedup] using contexts_iff related cache input context
    refine ⟨related.frozen,?_,?_⟩
    · intro parent present
      rcases List.mem_cons.mp present with rfl | old
      · exact ⟨_,List.mem_cons_self,newest⟩
      · obtain ⟨other,member,relation⟩ := related.forward parent old
        exact ⟨other,List.mem_cons_of_mem _ member,relation⟩
    · intro other present
      rcases List.mem_cons.mp present with rfl | old
      · exact ⟨_,List.mem_cons_self,newest⟩
      · obtain ⟨parent,member,relation⟩ := related.backward other old
        exact ⟨parent,List.mem_cons_of_mem _ member,relation⟩

theorem requests_iff {compact reference : State} (related : Related compact reference)
    (cache : NativeShakeCache.Cache) (input : Input) (key : Source) :
    key ∈ (prepare compact cache input).requests ↔ key ∈ (ExecutableParentLedger.prepare reference cache input).requests := by
  simp only [prepare,ExecutableParentLedger.prepare,List.mem_filter,List.mem_dedup,List.mem_eraseDups,
    decide_eq_true_eq,resolve_iff related,related.frozen]

theorem prepare_related {compact reference : State} (related : Related compact reference)
    (cache : NativeShakeCache.Cache) (input : Input) :
    Related (prepare compact cache input).next (ExecutableParentLedger.prepare reference cache input).next := by
  have parents := discover_related related cache input
  refine ⟨?_,parents.forward,parents.backward⟩
  apply Finset.ext
  intro key
  simp only [prepare,ExecutableParentLedger.prepare,Finset.mem_union,List.mem_toFinset,
    List.mem_filter,List.mem_dedup,List.mem_eraseDups,decide_eq_true_eq,related.frozen,resolve_iff related]

theorem requests_perm {compact reference : State} (related : Related compact reference)
    (cache : NativeShakeCache.Cache) (input : Input) :
    (prepare compact cache input).requests.Perm (ExecutableParentLedger.prepare reference cache input).requests := by
  apply (List.perm_ext_iff_of_nodup ?_ ?_).mpr
  · exact requests_iff related cache input
  · exact (List.nodup_dedup _).filter _
  · rw [ExecutableParentLedger.prepare_eq]
    exact NativeRootFamilyBudget.requests_nodup _ _ _

def Distinct (state : State) : Prop :=
  ∀ parent ∈ state.parents, parent.sources.Nodup ∧ parent.helpers.Nodup

theorem discover_distinct (state : State) (distinct : Distinct state) (cache : NativeShakeCache.Cache) (input : Input) :
    Distinct (discover state cache input) := by
  unfold discover
  split
  · exact distinct
  · intro parent present
    rcases List.mem_cons.mp present with rfl | old
    · exact ⟨List.nodup_dedup _,List.nodup_dedup _⟩
    · exact distinct parent old

theorem prepare_distinct (state : State) (distinct : Distinct state) (cache : NativeShakeCache.Cache) (input : Input) :
    Distinct (prepare state cache input).next := discover_distinct state distinct cache input

theorem coherent_related {compact reference : State} (related : Related compact reference)
    (pools : NativeParentLedgerPools.Pools) (coherent : NativeParentLedgerPools.Coherent reference pools) :
    NativeParentLedgerPools.Coherent compact pools := by
  refine ⟨?_,?_⟩
  · intro parent present
    obtain ⟨other,member,relation⟩ := related.forward parent present
    refine ⟨?_,?_⟩
    · intro key source
      exact (coherent.1 other member).1 key ((relation.sources key).mp source)
    · intro context helper
      exact (coherent.1 other member).2 context ((relation.helpers context).mp helper)
  · rw [related.frozen]
    exact coherent.2

theorem discover_parent_count (state : State) (cache : NativeShakeCache.Cache) (input : Input) :
    (discover state cache input).parents.length ≤ state.parents.length + 1 := by
  unfold discover
  split <;> simp

theorem prepare_parent_count (state : State) (cache : NativeShakeCache.Cache) (input : Input) :
    (prepare state cache input).next.parents.length ≤ state.parents.length + 1 := discover_parent_count state cache input

theorem parent_lengths (state : State) (distinct : Distinct state) (pools : NativeParentLedgerPools.Pools)
    (coherent : NativeParentLedgerPools.Coherent state pools) (parent : Parent) (present : parent ∈ state.parents) :
    parent.sources.length ≤ pools.contexts.card * pools.roots.card ∧ parent.helpers.length ≤ pools.contexts.card := by
  have sourceSubset : parent.sources.toFinset ⊆ NativeParentLedgerPools.sources pools := by
    intro key member
    exact (coherent.1 parent present).1 key (List.mem_toFinset.mp member)
  have helperSubset : parent.helpers.toFinset ⊆ pools.contexts := by
    intro context member
    exact (coherent.1 parent present).2 context (List.mem_toFinset.mp member)
  constructor
  · have bound := Finset.card_le_card sourceSubset
    simpa only [List.toFinset_card_of_nodup (distinct parent present).1,NativeParentLedgerPools.sources,Finset.card_product] using bound
  · have bound := Finset.card_le_card helperSubset
    simpa only [List.toFinset_card_of_nodup (distinct parent present).2] using bound

def metadataSize (state : State) : ℕ := (state.parents.map (fun parent => parent.sources.length + parent.helpers.length)).sum

theorem metadataSize_le (state : State) (distinct : Distinct state) (pools : NativeParentLedgerPools.Pools)
    (coherent : NativeParentLedgerPools.Coherent state pools) :
    metadataSize state ≤ state.parents.length * (pools.contexts.card * pools.roots.card + pools.contexts.card) := by
  let bound := pools.contexts.card * pools.roots.card + pools.contexts.card
  have sumBound (parents : List Parent) :
      (∀ parent ∈ parents, parent.sources.length + parent.helpers.length ≤ bound) →
      (parents.map (fun parent => parent.sources.length + parent.helpers.length)).sum ≤ parents.length * bound := by
    induction parents with
    | nil => simp
    | cons parent rest ih =>
      intro bounded
      have head := bounded parent List.mem_cons_self
      have tail := ih (fun next present => bounded next (List.mem_cons_of_mem parent present))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      calc
        _ ≤ bound + rest.length * bound := Nat.add_le_add head tail
        _ = _ := by ring
  apply sumBound state.parents
  intro parent present
  obtain ⟨sources,helpers⟩ := parent_lengths state distinct pools coherent parent present
  exact Nat.add_le_add sources helpers
end FormalProof4FHE.HasteBoots.CompactParentLedger
