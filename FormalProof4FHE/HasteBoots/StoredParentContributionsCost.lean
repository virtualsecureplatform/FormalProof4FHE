module
public import FormalProof4FHE.HasteBoots.StoredMetadataCost
public import FormalProof4FHE.HasteBoots.StoredParentSeedCheck
public import FormalProof4FHE.HasteBoots.StoredChildSeedQuote
public import FormalProof4FHE.HasteBoots.StoredSourceMentionsCost
public import FormalProof4FHE.HasteBoots.StoredHelperRootsCost
@[expose] public section

/-! Stored parent candidates and complete inherited source contributions. Every
compatible record is retained, including repeated inputs and unexposed/partial
seeds. Source/helper byte vectors are stored data, not executable callbacks.
These operations take an explicit current cache; replay must pass its causal
prefix cache, before writing the current observation's new output bytes. -/
namespace FormalProof4FHE.HasteBoots.StoredParentContributionsCost
open InputIndexedOracle (Input)
open SolverOperationCost (Run)
open StoredMetadataCost (Root)
open StoredSourceVectorReadCost (Source sourceView)
open StoredShakeByteCache (Cache)

structure Parent where
  input : Input
  sources : List Source
  helpers : List Root

def view (parent : Parent) : NativeParentLedger.Parent :=
  ⟨parent.input,parent.sources.map sourceView,parent.helpers.map (fun root => root.get)⟩

def inputBytes : List Parent → ℕ
  | [] => 0
  | head::tail => head.input.length+inputBytes tail

def sourceCount : List Parent → ℕ
  | [] => 0
  | head::tail => head.sources.length+sourceCount tail

def helperCount : List Parent → ℕ
  | [] => 0
  | head::tail => head.helpers.length+helperCount tail

def select (cache : Cache) (seed : Root) : List Parent → Run (List Parent)
  | [] => ⟨[],1⟩
  | head::tail =>
    let compatible := StoredParentSeedCheck.compatible cache head.input seed
    let rest := select cache seed tail
    ⟨if compatible.value then head::rest.value else rest.value,compatible.cost+rest.cost+3⟩

theorem select_value (cache : Cache) (seed : Root) (parents : List Parent) :
    (select cache seed parents).value.map view =
      (parents.map view).filter (fun parent => ExecutableParentInputView.compatible (StoredShakeByteCache.view cache) parent.input seed.get) := by
  induction parents with
  | nil => rfl
  | cons head tail ih =>
    simp only [select,List.map_cons,List.filter_cons,StoredParentSeedCheck.compatible_value,view]
    split <;> simp only [List.map_cons,ih,view]

theorem select_cost (cache : Cache) (seed : Root) (parents : List Parent) :
    (select cache seed parents).cost ≤
      64*(6*inputBytes parents+14*parents.length)*cache.length+454*parents.length+1 := by
  induction parents with
  | nil => simp [select,inputBytes]
  | cons head tail ih =>
    have first := StoredParentSeedCheck.compatible_cost cache head.input seed
    simp only [select,inputBytes,List.length_cons]
    nlinarith

theorem select_sourceCount (cache : Cache) (seed : Root) (parents : List Parent) :
    sourceCount (select cache seed parents).value ≤ sourceCount parents := by
  induction parents with
  | nil => exact le_rfl
  | cons head tail ih =>
    simp only [select,sourceCount]
    split
    · change head.sources.length+sourceCount (select cache seed tail).value ≤ head.sources.length+sourceCount tail
      omega
    · exact ih.trans (Nat.le_add_left _ _)

theorem select_helperCount (cache : Cache) (seed : Root) (parents : List Parent) :
    helperCount (select cache seed parents).value ≤ helperCount parents := by
  induction parents with
  | nil => exact le_rfl
  | cons head tail ih =>
    simp only [select,helperCount]
    split
    · change head.helpers.length+helperCount (select cache seed tail).value ≤ head.helpers.length+helperCount tail
      omega
    · exact ih.trans (Nat.le_add_left _ _)

theorem select_size (cache : Cache) (seed : Root) (parents : List Parent) :
    (select cache seed parents).value.length ≤ parents.length := by
  induction parents with
  | nil => exact le_rfl
  | cons head tail ih =>
    simp only [select,List.length_cons]
    split
    · change (select cache seed tail).value.length+1 ≤ tail.length+1
      omega
    · omega

def pairRoots (context : Root) : List Root → Run (List Source)
  | [] => ⟨[],1⟩
  | root::tail =>
    let rest := pairRoots context tail
    ⟨(context,root)::rest.value,rest.cost+3⟩

theorem pairRoots_value (context : Root) (roots : List Root) :
    (pairRoots context roots).value = roots.map (fun root => (context,root)) := by
  induction roots with
  | nil => rfl
  | cons root tail ih => simp only [pairRoots,List.map_cons,ih]

theorem pairRoots_cost (context : Root) (roots : List Root) :
    (pairRoots context roots).cost = 3*roots.length+1 := by
  induction roots with
  | nil => rfl
  | cons root tail ih => simp only [pairRoots,List.length_cons,ih]; omega

def cross (helpers roots : List Root) : Run (List Source) :=
  match helpers with
  | [] => ⟨[],1⟩
  | context::tail =>
    let first := pairRoots context roots
    let rest := cross tail roots
    let joined := StoredRegistrySourcesCost.appendSources first.value rest.value
    ⟨joined.value,first.cost+rest.cost+joined.cost+4⟩

theorem cross_value (helpers roots : List Root) :
    (cross helpers roots).value = helpers.flatMap (fun context => roots.map (fun root => (context,root))) := by
  induction helpers with
  | nil => rfl
  | cons context tail ih => simp only [cross,StoredRegistrySourcesCost.appendSources_value,pairRoots_value,ih,List.flatMap_cons]

theorem cross_size (helpers roots : List Root) : (cross helpers roots).value.length = helpers.length*roots.length := by
  induction helpers with
  | nil => simp [cross]
  | cons context tail ih =>
    simp only [cross,StoredRegistrySourcesCost.appendSources_value,pairRoots_value,List.length_append,
      List.length_map,ih,List.length_cons]
    nlinarith

theorem cross_cost (helpers roots : List Root) :
    (cross helpers roots).cost ≤ (6*roots.length+6)*helpers.length+1 := by
  induction helpers with
  | nil => simp [cross]
  | cons context tail ih =>
    simp only [cross,StoredRegistrySourcesCost.appendSources_cost,pairRoots_cost,pairRoots_value,
      List.length_map,List.length_cons]
    nlinarith

def contribution (roots : List Root) (parent : Parent) : Run (List Source) :=
  let inherited := cross parent.helpers roots
  let joined := StoredRegistrySourcesCost.appendSources parent.sources inherited.value
  ⟨joined.value,inherited.cost+joined.cost+4⟩

theorem contribution_value (roots : List Root) (parent : Parent) :
    (contribution roots parent).value.map sourceView =
      (view parent).sources ++ (view parent).helpers.flatMap (fun context =>
        (roots.map (fun root => root.get)).map (fun root => (context,root))) := by
  simp only [contribution,StoredRegistrySourcesCost.appendSources_value,cross_value,List.map_append,
    List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def,view,sourceView]

theorem contribution_size (roots : List Root) (parent : Parent) :
    (contribution roots parent).value.length = parent.sources.length+parent.helpers.length*roots.length := by
  simp only [contribution,StoredRegistrySourcesCost.appendSources_value,List.length_append,cross_size]

theorem contribution_cost (roots : List Root) (parent : Parent) :
    (contribution roots parent).cost ≤ 3*parent.sources.length+(6*roots.length+6)*parent.helpers.length+6 := by
  have inherited := cross_cost parent.helpers roots
  simp only [contribution,StoredRegistrySourcesCost.appendSources_cost]
  omega

def inheritSources (roots : List Root) : List Parent → Run (List Source)
  | [] => ⟨[],1⟩
  | head::tail =>
    let first := contribution roots head
    let rest := inheritSources roots tail
    let joined := StoredRegistrySourcesCost.appendSources first.value rest.value
    ⟨joined.value,first.cost+rest.cost+joined.cost+3⟩

theorem inheritSources_value (roots : List Root) (parents : List Parent) :
    (inheritSources roots parents).value.map sourceView = (parents.map view).flatMap (fun parent =>
      parent.sources ++ parent.helpers.flatMap (fun context =>
        (roots.map (fun root => root.get)).map (fun root => (context,root)))) := by
  induction parents with
  | nil => rfl
  | cons head tail ih =>
    simp only [inheritSources,StoredRegistrySourcesCost.appendSources_value,List.map_append,
      contribution_value,ih,List.map_cons,List.flatMap_cons]

theorem inheritSources_size (roots : List Root) (parents : List Parent) :
    (inheritSources roots parents).value.length = sourceCount parents+helperCount parents*roots.length := by
  induction parents with
  | nil => simp [inheritSources,sourceCount,helperCount]
  | cons head tail ih =>
    simp only [inheritSources,StoredRegistrySourcesCost.appendSources_value,List.length_append,
      contribution_size,ih,sourceCount,helperCount]
    nlinarith

theorem inheritSources_cost (roots : List Root) (parents : List Parent) :
    (inheritSources roots parents).cost ≤
      6*sourceCount parents+(9*roots.length+6)*helperCount parents+10*parents.length+1 := by
  induction parents with
  | nil => simp [inheritSources,sourceCount,helperCount]
  | cons head tail ih =>
    have first := contribution_cost roots head
    simp only [inheritSources,StoredRegistrySourcesCost.appendSources_cost,contribution_size,
      sourceCount,helperCount,List.length_cons]
    nlinarith
end FormalProof4FHE.HasteBoots.StoredParentContributionsCost
