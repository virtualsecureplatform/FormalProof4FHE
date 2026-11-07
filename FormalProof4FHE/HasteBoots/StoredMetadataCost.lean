module
public import FormalProof4FHE.HasteBoots.StoredSourceVectorCost
public import FormalProof4FHE.HasteBoots.CompactParentLedger
@[expose] public section

/-! Closed byte comparisons and bounded stored metadata compaction. The generic
list loops include every supplied comparison charge; public root/source programs
fix their concrete byte comparator. Compaction matches the existing compact
ledger's last-occurrence deduplication, not registry ownership or snapshot order.
Bounds concern reference operations, not physical runtime or attacker work. -/
namespace FormalProof4FHE.HasteBoots.StoredMetadataCost
open InputIndexedOracle (Input Byte)
open SolverOperationCost (Run)
open StoredSourceVectorReadCost (Source sourceView)
abbrev Root := Vector Byte 64

def rootEqual (first last : Root) : Run Bool :=
  let left := StoredDigestView.fromVector first
  let right := StoredDigestView.fromVector last
  let compared := BytePrefixMatchCost.equal left.value.val right.value.val
  ⟨compared.value,left.cost+right.cost+compared.cost+3⟩

theorem rootEqual_value (first last : Root) : (rootEqual first last).value = decide (first = last) := by
  simp only [rootEqual,StoredDigestView.fromVector,BytePrefixMatchCost.equal_value]
  congr 1
  exact propext Vector.toList_inj

theorem rootEqual_cost (first last : Root) : (rootEqual first last).cost ≤ 660 := by
  have compared := BytePrefixMatchCost.equal_cost first.toList last.toList
  simp only [Vector.length_toList] at compared
  simp only [rootEqual,StoredDigestView.fromVector]
  omega

def sourceEqual (first last : Source) : Run Bool :=
  let context := rootEqual first.1 last.1
  let root := rootEqual first.2 last.2
  ⟨context.value && root.value,context.cost+root.cost+3⟩

theorem sourceEqual_value (first last : Source) : (sourceEqual first last).value = decide (first = last) := by
  by_cases context : first.1 = last.1 <;> by_cases root : first.2 = last.2 <;>
    simp [sourceEqual,rootEqual_value,Prod.ext_iff,context,root]

theorem sourceEqual_cost (first last : Source) : (sourceEqual first last).cost ≤ 1323 := by
  have context := rootEqual_cost first.1 last.1
  have root := rootEqual_cost first.2 last.2
  simp only [sourceEqual]
  omega

/-- Generic operation-model loop. Each comparison is charged by its own Run. -/
def contains {A : Type} (equal : A → A → Run Bool) (key : A) : List A → Run Bool
  | [] => ⟨false,1⟩
  | head::tail =>
    let same := equal key head
    if same.value then ⟨true,same.cost+3⟩
    else
      let rest := contains equal key tail
      ⟨rest.value,same.cost+rest.cost+4⟩

theorem contains_value {A : Type} [DecidableEq A] (equal : A → A → Run Bool)
    (correct : ∀ first last, (equal first last).value = decide (first = last)) (key : A) (values : List A) :
    (contains equal key values).value = decide (key ∈ values) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    by_cases same : key = head <;>
      simp only [contains,correct,same,decide_true,decide_false,ite_true,Bool.false_eq_true,
        ite_false,ih,List.mem_cons,decide_true,false_or,true_or]

theorem contains_cost {A : Type} (equal : A → A → Run Bool) (C : ℕ)
    (bounded : ∀ first last, (equal first last).cost ≤ C) (key : A) (values : List A) :
    (contains equal key values).cost ≤ (C+4)*values.length+1 := by
  induction values with
  | nil => simp [contains]
  | cons head tail ih =>
    have first := bounded key head
    simp only [contains,List.length_cons]
    split <;> dsimp only <;> nlinarith

/-- The compact ledger retains last occurrences, using the already compacted tail. -/
def dedup {A : Type} (equal : A → A → Run Bool) : List A → Run (List A)
  | [] => ⟨[],1⟩
  | head::tail =>
    let rest := dedup equal tail
    let present := contains equal head rest.value
    ⟨if present.value then rest.value else head::rest.value,rest.cost+present.cost+4⟩

theorem dedup_value {A : Type} [DecidableEq A] (equal : A → A → Run Bool)
    (correct : ∀ first last, (equal first last).value = decide (first = last)) (values : List A) :
    (dedup equal values).value = values.dedup := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    simp only [dedup,contains_value equal correct,ih,List.dedup_cons',decide_eq_true_eq]

theorem dedup_size {A : Type} (equal : A → A → Run Bool) (values : List A) :
    (dedup equal values).value.length ≤ values.length := by
  induction values with
  | nil => exact le_rfl
  | cons head tail ih =>
    simp only [dedup,List.length_cons]
    split
    · omega
    · change (dedup equal tail).value.length+1 ≤ tail.length+1
      omega

theorem dedup_cost {A : Type} (equal : A → A → Run Bool) (C : ℕ)
    (bounded : ∀ first last, (equal first last).cost ≤ C) (values : List A) :
    (dedup equal values).cost ≤ (C+8)*(values.length+1)^2 := by
  induction values with
  | nil => simp only [dedup,List.length_nil]; nlinarith
  | cons head tail ih =>
    have search := contains_cost equal C bounded head (dedup equal tail).value
    have size := dedup_size equal tail
    have scaled := Nat.mul_le_mul_left (C+4) size
    simp only [dedup,List.length_cons]
    nlinarith

def containsRoot (key : Root) (values : List Root) : Run Bool := contains rootEqual key values
def containsSource (key : Source) (values : List Source) : Run Bool := contains sourceEqual key values
def dedupRoots (values : List Root) : Run (List Root) := dedup rootEqual values
def dedupSources (values : List Source) : Run (List Source) := dedup sourceEqual values

theorem containsRoot_value (key : Root) (values : List Root) :
    (containsRoot key values).value = decide (key ∈ values) := by
  apply Bool.eq_iff_iff.mpr
  simp only [containsRoot,contains_value rootEqual rootEqual_value,decide_eq_true_eq]

theorem containsSource_value (key : Source) (values : List Source) :
    (containsSource key values).value = decide (key ∈ values) := by
  apply Bool.eq_iff_iff.mpr
  simp only [containsSource,contains_value sourceEqual sourceEqual_value,decide_eq_true_eq]

theorem containsRoot_cost (key : Root) (values : List Root) :
    (containsRoot key values).cost ≤ 664*values.length+1 := contains_cost rootEqual 660 rootEqual_cost key values

theorem containsSource_cost (key : Source) (values : List Source) :
    (containsSource key values).cost ≤ 1327*values.length+1 := contains_cost sourceEqual 1323 sourceEqual_cost key values

theorem dedupRoots_value (values : List Root) : (dedupRoots values).value = values.dedup :=
  dedup_value rootEqual rootEqual_value values

theorem dedupSources_value (values : List Source) : (dedupSources values).value = values.dedup :=
  dedup_value sourceEqual sourceEqual_value values

theorem dedupRoots_cost (values : List Root) : (dedupRoots values).cost ≤ 668*(values.length+1)^2 :=
  dedup_cost rootEqual 660 rootEqual_cost values

theorem dedupSources_cost (values : List Source) : (dedupSources values).cost ≤ 1331*(values.length+1)^2 :=
  dedup_cost sourceEqual 1323 sourceEqual_cost values

theorem rootView_injective : Function.Injective (fun root : Root => root.get) := by
  intro first last same
  apply Vector.ext
  intro i hi
  exact congrFun same ⟨i,hi⟩

theorem sourceView_injective : Function.Injective sourceView := by
  intro first last same
  exact Prod.ext (rootView_injective (congrArg Prod.fst same)) (rootView_injective (congrArg Prod.snd same))

local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq

theorem dedupRoots_view (values : List Root) :
    (dedupRoots values).value.map (fun root => root.get) = (values.map (fun root => root.get)).dedup := by
  rw [dedupRoots_value, List.dedup_map_of_injective rootView_injective]

theorem dedupSources_view (values : List Source) :
    (dedupSources values).value.map sourceView = (values.map sourceView).dedup := by
  rw [dedupSources_value,List.dedup_map_of_injective sourceView_injective]
end FormalProof4FHE.HasteBoots.StoredMetadataCost
