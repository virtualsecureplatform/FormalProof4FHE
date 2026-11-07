module
public import FormalProof4FHE.HasteBoots.StoredHistorySourceResolutionCost
@[expose] public section

/-! Closed measured preparation of frozen source requests. Full context/root
pairs are compared as stored bytes; sharing a root does not merge contexts.
Original compact-request order is retained. The frozen list is an executable
representation of the reference set, with no functional digest equality call. -/
namespace FormalProof4FHE.HasteBoots.StoredFrozenRequestsCost
open InputIndexedOracle (Input)
open SolverOperationCost (Run)
open StoredSourceVectorReadCost (Source sourceView)
open StoredParentContributionsCost (Parent view)
open StoredShakeByteCache (Cache)
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq

def frozenView (frozen : List Source) : Finset NativeCanonicalLookupWire.Source :=
  (frozen.map sourceView).toFinset

theorem containsSource_view (key : Source) (frozen : List Source) :
    (StoredMetadataCost.containsSource key frozen).value = decide (sourceView key ∈ frozenView frozen) := by
  apply Bool.eq_iff_iff.mpr
  rw [StoredMetadataCost.containsSource_value]
  simp only [decide_eq_true_eq,frozenView,List.mem_toFinset,List.mem_map]
  constructor
  · intro member; exact ⟨key,member,rfl⟩
  · rintro ⟨other,member,same⟩
    exact StoredMetadataCost.sourceView_injective same ▸ member

def fresh (frozen : List Source) : List Source → Run (List Source)
  | [] => ⟨[],1⟩
  | head::tail =>
    let present := StoredMetadataCost.containsSource head frozen
    let rest := fresh frozen tail
    ⟨if present.value then rest.value else head::rest.value,present.cost+rest.cost+4⟩

theorem fresh_value (frozen values : List Source) :
    (fresh frozen values).value.map sourceView =
      (values.map sourceView).filter (fun key => key ∉ frozenView frozen) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    simp only [fresh,containsSource_view,List.map_cons,List.filter_cons]
    by_cases member : sourceView head ∈ frozenView frozen <;>
      simp only [member,decide_true,decide_false,ite_true,Bool.false_eq_true,ite_false,not_true_eq_false,
        not_false_eq_true,List.map_cons,ih]

theorem fresh_size (frozen values : List Source) : (fresh frozen values).value.length ≤ values.length := by
  induction values with
  | nil => exact le_rfl
  | cons head tail ih =>
    simp only [fresh]
    split
    · exact ih.trans (Nat.le_succ _)
    · change (fresh frozen tail).value.length+1 ≤ tail.length+1
      omega

theorem fresh_cost (frozen values : List Source) :
    (fresh frozen values).cost ≤ (1327*frozen.length+5)*values.length+1 := by
  induction values with
  | nil => simp [fresh]
  | cons head tail ih =>
    have searched := StoredMetadataCost.containsSource_cost head frozen
    simp only [fresh,List.length_cons]
    nlinarith

structure Plan where
  requests : List Source
  frozen : List Source

def prepare (cache : Cache) (parents : List Parent) (frozen : List Source) (input : Input) : Run Plan :=
  let resolved := StoredParentResolutionCost.resolve cache parents input
  let compact := StoredMetadataCost.dedupSources resolved.value
  let requests := fresh frozen compact.value
  let saved := StoredRegistrySourcesCost.appendSources frozen requests.value
  ⟨⟨requests.value,saved.value⟩,resolved.cost+compact.cost+requests.cost+saved.cost+5⟩

theorem prepare_requests (cache : Cache) (parents : List Parent) (frozen : List Source) (input : Input) :
    (prepare cache parents frozen input).value.requests.map sourceView =
      (CompactParentLedger.prepare ⟨parents.map view,frozenView frozen⟩
        (StoredShakeByteCache.view cache) input).requests := by
  simp only [prepare,fresh_value,StoredMetadataCost.dedupSources_view,
    StoredParentResolutionCost.resolve_value,CompactParentLedger.prepare]
  rfl

theorem prepare_frozen (cache : Cache) (parents : List Parent) (frozen : List Source) (input : Input) :
    frozenView (prepare cache parents frozen input).value.frozen =
      (CompactParentLedger.prepare ⟨parents.map view,frozenView frozen⟩
        (StoredShakeByteCache.view cache) input).next.frozen := by
  change frozenView (prepare cache parents frozen input).value.frozen =
    frozenView frozen ∪ ((CompactParentLedger.prepare ⟨parents.map view,frozenView frozen⟩
      (StoredShakeByteCache.view cache) input).requests).toFinset
  rw [← prepare_requests]
  simp only [prepare,StoredRegistrySourcesCost.appendSources_value,frozenView,List.map_append,List.toFinset_append]

theorem prepare_distinct (cache : Cache) (parents : List Parent) (frozen : List Source) (input : Input)
    (distinct : (frozen.map sourceView).Nodup) :
    ((prepare cache parents frozen input).value.frozen.map sourceView).Nodup := by
  have requests := prepare_requests cache parents frozen input
  have appended : (prepare cache parents frozen input).value.frozen =
      frozen ++ (prepare cache parents frozen input).value.requests := by
    simp only [prepare,StoredRegistrySourcesCost.appendSources_value]
  rw [appended,List.map_append,List.nodup_append']
  refine ⟨distinct,?_,?_⟩
  · rw [requests]
    exact (List.nodup_dedup _).filter _
  · apply List.disjoint_left.mpr
    intro key prior freshKey
    rw [requests] at freshKey
    have notFrozen := (List.mem_filter.mp freshKey).2
    have present : key ∈ frozenView frozen := List.mem_toFinset.mpr prior
    exact (of_decide_eq_true notFrozen) present

theorem prepare_size (cache : Cache) (parents : List Parent) (frozen : List Source) (input : Input) :
    (prepare cache parents frozen input).value.requests.length ≤
      (StoredParentResolutionCost.resolve cache parents input).value.length := by
  exact (fresh_size frozen _).trans (StoredMetadataCost.dedup_size _ _)

theorem prepare_frozen_size (cache : Cache) (parents : List Parent) (frozen : List Source) (input : Input) :
    (prepare cache parents frozen input).value.frozen.length ≤
      frozen.length+(StoredParentResolutionCost.resolve cache parents input).value.length := by
  have requests := prepare_size cache parents frozen input
  simp only [prepare,StoredRegistrySourcesCost.appendSources_value,List.length_append] at *
  omega

theorem prepare_cost (cache : Cache) (parents : List Parent) (frozen : List Source) (input : Input) :
    (prepare cache parents frozen input).cost ≤
      (StoredParentResolutionCost.resolve cache parents input).cost+
      1331*((StoredParentResolutionCost.resolve cache parents input).value.length+1)^2+
      (1327*frozen.length+5)*(StoredParentResolutionCost.resolve cache parents input).value.length+
      3*frozen.length+7 := by
  have compact := StoredMetadataCost.dedupSources_cost (StoredParentResolutionCost.resolve cache parents input).value
  have requests := fresh_cost frozen (StoredMetadataCost.dedupSources (StoredParentResolutionCost.resolve cache parents input).value).value
  have size := StoredMetadataCost.dedup_size StoredMetadataCost.sourceEqual (StoredParentResolutionCost.resolve cache parents input).value
  have scaled := Nat.mul_le_mul_left (1327*frozen.length+5) size
  simp only [prepare,StoredRegistrySourcesCost.appendSources_cost]
  dsimp only [StoredMetadataCost.dedupSources] at compact requests ⊢
  omega
end FormalProof4FHE.HasteBoots.StoredFrozenRequestsCost
