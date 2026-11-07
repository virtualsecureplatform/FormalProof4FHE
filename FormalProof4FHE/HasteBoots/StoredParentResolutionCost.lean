module
public import FormalProof4FHE.HasteBoots.StoredParentContributionsCost
@[expose] public section

/-! Closed source resolution over stored parent metadata and an explicit cache.
The value is the complete original resolver, preserving every compatible parent
and contribution in order. No metadata compaction or registry-owner choice is
performed here. The cache must be supplied by causal replay; this module does
not reconstruct past metadata from a final cache. -/
namespace FormalProof4FHE.HasteBoots.StoredParentResolutionCost
open InputIndexedOracle (Input)
open SolverOperationCost (Run)
open StoredParentContributionsCost (Parent view inputBytes sourceCount helperCount select inheritSources)
open StoredMetadataCost (Root)
open StoredSourceVectorReadCost (Source sourceView)
open StoredShakeByteCache (Cache)

def ledgerView (parents : List Parent) : NativeParentLedger.State := ⟨parents.map view,∅⟩

def active (cache : Cache) (parents : List Parent) (input : Input) : Run (List Parent) :=
  let quote := StoredChildSeedQuote.quote input
  match quote.value with
  | none => ⟨[],quote.cost+2⟩
  | some seed =>
    let selected := select cache seed parents
    ⟨selected.value,quote.cost+selected.cost+3⟩

theorem active_value (cache : Cache) (parents : List Parent) (input : Input) :
    (active cache parents input).value.map view =
      ExecutableParentLedger.active (ledgerView parents) (StoredShakeByteCache.view cache) input := by
  have quote := StoredChildSeedQuote.quote_value input
  cases parsed : (StoredChildSeedQuote.quote input).value with
  | none =>
    rw [parsed,Option.map_none] at quote
    simp only [active,parsed,ExecutableParentLedger.active,← quote,List.map_nil]
  | some seed =>
    rw [parsed,Option.map_some] at quote
    simp only [active,parsed,ExecutableParentLedger.active,← quote,ledgerView,
      StoredParentContributionsCost.select_value]

theorem active_cost (cache : Cache) (parents : List Parent) (input : Input) :
    (active cache parents input).cost ≤ 24*input.length+6*StoredChildSeedQuote.seedLabel.length+491+
      64*(6*inputBytes parents+14*parents.length)*cache.length+454*parents.length := by
  have quote := StoredChildSeedQuote.quote_cost input
  simp only [active]
  split
  · dsimp only; nlinarith
  · rename_i seed parsed
    have selected := StoredParentContributionsCost.select_cost cache seed parents
    dsimp only
    nlinarith

theorem active_sourceCount (cache : Cache) (parents : List Parent) (input : Input) :
    sourceCount (active cache parents input).value ≤ sourceCount parents := by
  simp only [active]
  split
  · exact Nat.zero_le _
  · exact StoredParentContributionsCost.select_sourceCount _ _ _

theorem active_helperCount (cache : Cache) (parents : List Parent) (input : Input) :
    helperCount (active cache parents input).value ≤ helperCount parents := by
  simp only [active]
  split
  · exact Nat.zero_le _
  · exact StoredParentContributionsCost.select_helperCount _ _ _

theorem active_size (cache : Cache) (parents : List Parent) (input : Input) :
    (active cache parents input).value.length ≤ parents.length := by
  simp only [active]
  split
  · exact Nat.zero_le _
  · exact StoredParentContributionsCost.select_size _ _ _

theorem roots_size (input : Input) : (StoredHelperRootsCost.fromInput input).value.length ≤ input.length := by
  have same := congrArg List.length (StoredHelperRootsCost.fromInput_value input)
  rw [List.length_map,ExecutableParentLedger.roots_eq] at same
  rw [same]
  exact NativeRootMentionSize.input_roots_size input

def resolve (cache : Cache) (parents : List Parent) (input : Input) : Run (List Source) :=
  let direct := StoredSourceMentionsCost.fromInput input
  let roots := StoredHelperRootsCost.fromInput input
  let candidates := active cache parents input
  let inherited := inheritSources roots.value candidates.value
  let joined := StoredRegistrySourcesCost.appendSources direct.value inherited.value
  ⟨joined.value,direct.cost+roots.cost+candidates.cost+inherited.cost+joined.cost+6⟩

theorem resolve_value (cache : Cache) (parents : List Parent) (input : Input) :
    (resolve cache parents input).value.map sourceView =
      ExecutableParentLedger.resolve (ledgerView parents) (StoredShakeByteCache.view cache) input := by
  simp only [resolve,StoredRegistrySourcesCost.appendSources_value,List.map_append,
    StoredSourceMentionsCost.direct_value,StoredParentContributionsCost.inheritSources_value,
    StoredHelperRootsCost.fromInput_value,active_value,ExecutableParentLedger.resolve]

def inputFactor : ℕ := 11127+12*StoredSourceMentionsCost.frameLabelBytes+
  6*StoredSourceMentionsCost.singleLabelBytes+6*StoredHelperRootsCost.label.length

theorem resolve_size (cache : Cache) (parents : List Parent) (input : Input) :
    (resolve cache parents input).value.length ≤ input.length+sourceCount parents+helperCount parents*input.length := by
  have direct := StoredSourceMentionsCost.fromInput_size input
  have roots := roots_size input
  have sources := active_sourceCount cache parents input
  have helpers := active_helperCount cache parents input
  have cross := Nat.mul_le_mul helpers roots
  simp only [resolve,StoredRegistrySourcesCost.appendSources_value,List.length_append,
    StoredParentContributionsCost.inheritSources_size]
  omega

theorem resolve_cost (cache : Cache) (parents : List Parent) (input : Input) :
    (resolve cache parents input).cost ≤ inputFactor*input.length+6*StoredChildSeedQuote.seedLabel.length+600+
      64*(6*inputBytes parents+14*parents.length)*cache.length+464*parents.length+
      6*sourceCount parents+(9*input.length+6)*helperCount parents := by
  have direct := StoredSourceMentionsCost.fromInput_cost input
  have directSize := StoredSourceMentionsCost.fromInput_size input
  have roots := StoredHelperRootsCost.fromInput_cost input
  have rootSize := roots_size input
  have candidates := active_cost cache parents input
  have inherited := StoredParentContributionsCost.inheritSources_cost
    (StoredHelperRootsCost.fromInput input).value (active cache parents input).value
  have sources := active_sourceCount cache parents input
  have helpers := active_helperCount cache parents input
  have count := active_size cache parents input
  have cross := Nat.mul_le_mul helpers rootSize
  simp only [resolve,StoredRegistrySourcesCost.appendSources_cost,inputFactor]
  nlinarith
end FormalProof4FHE.HasteBoots.StoredParentResolutionCost
