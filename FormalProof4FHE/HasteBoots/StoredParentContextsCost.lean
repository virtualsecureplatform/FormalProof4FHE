module
public import FormalProof4FHE.HasteBoots.StoredParentResolutionCost
public import FormalProof4FHE.HasteBoots.StoredBindingHelpersCost
@[expose] public section

/-! Complete stored helper-context inheritance over every compatible parent.
Local helpers are recognized only through complete canonical binding decoding. -/
namespace FormalProof4FHE.HasteBoots.StoredParentContextsCost
open InputIndexedOracle (Input)
open SolverOperationCost (Run)
open StoredParentContributionsCost (Parent view inputBytes helperCount)
open StoredParentResolutionCost (active ledgerView)
open StoredMetadataCost (Root)
open StoredShakeByteCache (Cache)

def inheritHelpers : List Parent → Run (List Root)
  | [] => ⟨[],1⟩
  | head::tail =>
    let rest := inheritHelpers tail
    let joined := StoredHelperRootsCost.appendRoots head.helpers rest.value
    ⟨joined.value,rest.cost+joined.cost+3⟩

theorem inheritHelpers_value (parents : List Parent) :
    (inheritHelpers parents).value.map Vector.get = (parents.map view).flatMap (fun parent => parent.helpers) := by
  induction parents with
  | nil => rfl
  | cons head tail ih =>
    simp only [inheritHelpers,StoredHelperRootsCost.appendRoots_value,List.map_append,ih,
      List.map_cons,List.flatMap_cons,view]

theorem inheritHelpers_size (parents : List Parent) :
    (inheritHelpers parents).value.length = helperCount parents := by
  induction parents with
  | nil => rfl
  | cons head tail ih =>
    simp only [inheritHelpers,StoredHelperRootsCost.appendRoots_value,List.length_append,helperCount,ih]

theorem inheritHelpers_cost (parents : List Parent) :
    (inheritHelpers parents).cost ≤ 3*helperCount parents+4*parents.length+1 := by
  induction parents with
  | nil => simp [inheritHelpers,helperCount]
  | cons head tail ih =>
    simp only [inheritHelpers,StoredHelperRootsCost.appendRoots_cost,helperCount,List.length_cons]
    omega

def contexts (cache : Cache) (parents : List Parent) (input : Input) : Run (List Root) :=
  let direct := StoredBindingHelpersCost.fromInput input
  let candidates := active cache parents input
  let inherited := inheritHelpers candidates.value
  let joined := StoredHelperRootsCost.appendRoots direct.value inherited.value
  ⟨joined.value,direct.cost+candidates.cost+inherited.cost+joined.cost+5⟩

theorem contexts_value (cache : Cache) (parents : List Parent) (input : Input) :
    (contexts cache parents input).value.map Vector.get =
      ExecutableParentLedger.contexts (ledgerView parents) (StoredShakeByteCache.view cache) input := by
  simp only [contexts,StoredHelperRootsCost.appendRoots_value,List.map_append,
    StoredBindingHelpersCost.fromInput_value,inheritHelpers_value,StoredParentResolutionCost.active_value,
    ExecutableParentLedger.contexts]

theorem contexts_size (cache : Cache) (parents : List Parent) (input : Input) :
    (contexts cache parents input).value.length ≤ input.length+helperCount parents := by
  have direct := StoredBindingHelpersCost.fromInput_size input
  have candidates := StoredParentResolutionCost.active_helperCount cache parents input
  simp only [contexts,StoredHelperRootsCost.appendRoots_value,List.length_append,inheritHelpers_size]
  omega

def inputFactor : ℕ := 4998+6*StoredBindingFramesCost.label.length

theorem contexts_cost (cache : Cache) (parents : List Parent) (input : Input) :
    (contexts cache parents input).cost ≤ inputFactor*input.length+6*StoredChildSeedQuote.seedLabel.length+510+
      64*(6*inputBytes parents+14*parents.length)*cache.length+458*parents.length+3*helperCount parents := by
  have direct := StoredBindingHelpersCost.fromInput_cost input
  have directSize := StoredBindingHelpersCost.fromInput_size input
  have candidates := StoredParentResolutionCost.active_cost cache parents input
  have inherited := inheritHelpers_cost (active cache parents input).value
  have helpers := StoredParentResolutionCost.active_helperCount cache parents input
  have count := StoredParentResolutionCost.active_size cache parents input
  simp only [contexts,StoredHelperRootsCost.appendRoots_cost,inputFactor]
  nlinarith
end FormalProof4FHE.HasteBoots.StoredParentContextsCost
