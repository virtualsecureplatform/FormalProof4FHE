module
public import FormalProof4FHE.HasteBoots.StoredParentContextsCost
public import FormalProof4FHE.HasteBoots.StoredShakeHistory
@[expose] public section

/-! Causal replay of complete stored source/helper parent metadata. Every observed
input is visited, including starts, hashes and empty outputs. Parent resolution
uses the preceding cache; only afterwards are new output bytes written. This is
the metadata/cache projection of the compact reference history. Frozen source
requests, snapshot selection and whole-extractor physical refinement are separate. -/
namespace FormalProof4FHE.HasteBoots.StoredParentMetadataHistory
open InputIndexedOracle (Input)
open NativeTranscript (Observation)
open SolverOperationCost (Run)
open StoredParentContributionsCost (Parent inputBytes sourceCount helperCount)
open StoredMetadataCost (dedupSources dedupRoots)
open StoredShakeByteCache (Cache)

structure State where
  parents : List Parent
  cache : Cache

def initial : State := ⟨[],[]⟩

def discover (cache : Cache) (parents : List Parent) (input : Input) : Run (List Parent) :=
  let parsed := ParentSeedRequestCost.parse input
  match parsed.value with
  | none => ⟨parents,parsed.cost+2⟩
  | some _ =>
    let sources := StoredParentResolutionCost.resolve cache parents input
    let helpers := StoredParentContextsCost.contexts cache parents input
    let compactSources := dedupSources sources.value
    let compactHelpers := dedupRoots helpers.value
    ⟨⟨input,compactSources.value,compactHelpers.value⟩::parents,
      parsed.cost+sources.cost+helpers.cost+compactSources.cost+compactHelpers.cost+8⟩

theorem discover_value (cache : Cache) (parents : List Parent) (input : Input)
    (frozen : Finset NativeCanonicalLookupWire.Source) :
    (discover cache parents input).value.map StoredParentContributionsCost.view =
      (CompactParentLedger.discover ⟨parents.map StoredParentContributionsCost.view,frozen⟩
        (StoredShakeByteCache.view cache) input).parents := by
  simp only [discover,ParentSeedRequestCost.parse_value,CompactParentLedger.discover]
  cases parsed : ExecutableParentInputView.parseParent input with
  | none => rfl
  | some frames =>
    simp only [List.map_cons,StoredParentContributionsCost.view,StoredMetadataCost.dedupSources_view,
      StoredMetadataCost.dedupRoots_view,StoredParentResolutionCost.resolve_value,
      StoredParentContextsCost.contexts_value]
    rfl

def discoverBound (cache : Cache) (parents : List Parent) (input : Input) : ℕ :=
  (27+StoredParentResolutionCost.inputFactor+StoredParentContextsCost.inputFactor)*input.length+
  12*StoredChildSeedQuote.seedLabel.length+6*ParentSeedRequestCost.label.length+
  6*ParentSeedRequestCost.message.length+1200+
  128*(6*inputBytes parents+14*parents.length)*cache.length+922*parents.length+
  6*sourceCount parents+(9*input.length+9)*helperCount parents+
  1331*(input.length+sourceCount parents+helperCount parents*input.length+1)^2+
  668*(input.length+helperCount parents+1)^2

theorem discover_cost (cache : Cache) (parents : List Parent) (input : Input) :
    (discover cache parents input).cost ≤ discoverBound cache parents input := by
  have parsed := ParentSeedRequestCost.parse_cost input
  simp only [discover]
  split
  · dsimp only [discoverBound]; nlinarith
  · have sources := StoredParentResolutionCost.resolve_cost cache parents input
    have helpers := StoredParentContextsCost.contexts_cost cache parents input
    have sourceSize := StoredParentResolutionCost.resolve_size cache parents input
    have helperSize := StoredParentContextsCost.contexts_size cache parents input
    have compactSources := StoredMetadataCost.dedupSources_cost (StoredParentResolutionCost.resolve cache parents input).value
    have compactHelpers := StoredMetadataCost.dedupRoots_cost (StoredParentContextsCost.contexts cache parents input).value
    have sourceSquare := Nat.mul_le_mul (Nat.succ_le_succ sourceSize) (Nat.succ_le_succ sourceSize)
    have helperSquare := Nat.mul_le_mul (Nat.succ_le_succ helperSize) (Nat.succ_le_succ helperSize)
    dsimp only [discoverBound]
    nlinarith

theorem discover_count (cache : Cache) (parents : List Parent) (input : Input) :
    (discover cache parents input).value.length ≤ parents.length+1 := by
  simp only [discover]
  split
  · dsimp only; omega
  · exact le_rfl

theorem discover_inputBytes (cache : Cache) (parents : List Parent) (input : Input) :
    inputBytes (discover cache parents input).value ≤ inputBytes parents+input.length := by
  simp only [discover]
  split
  · dsimp only; omega
  · dsimp only [inputBytes]; omega

def record (state : State) (entry : Observation) : Run State :=
  let metadata := discover state.cache state.parents (NativeParentLedgerPools.inputOf entry)
  let bytes := StoredShakeHistory.record state.cache entry
  ⟨⟨metadata.value,bytes.value⟩,metadata.cost+bytes.cost+3⟩

def Related (stored : State) (reference : CompactParentHistory.State) : Prop :=
  stored.parents.map StoredParentContributionsCost.view = reference.1.parents ∧
    StoredShakeByteCache.view stored.cache = reference.2

theorem reference_record_parents (state : CompactParentHistory.State) (entry : Observation) :
    (CompactParentHistory.record state entry).1.parents =
      (CompactParentLedger.discover state.1 state.2 (NativeParentLedgerPools.inputOf entry)).parents := by
  cases entry with
  | start input => rfl
  | hash input digest => rfl
  | output input offset values =>
    simp only [CompactParentHistory.record,NativeParentLedgerPools.inputOf]
    split <;> rfl

theorem reference_record_cache (state : CompactParentHistory.State) (entry : Observation) :
    (CompactParentHistory.record state entry).2 = NativeShakeHistory.record state.2 entry := by
  cases entry with
  | start input => rfl
  | hash input digest => rfl
  | output input offset values => exact ExecutableSourceHistory.writeBytes_eq _ _ _ _

theorem record_related (stored : State) (reference : CompactParentHistory.State)
    (related : Related stored reference) (entry : Observation) :
    Related (record stored entry).value (CompactParentHistory.record reference entry) := by
  have state : (⟨stored.parents.map StoredParentContributionsCost.view,reference.1.frozen⟩ : NativeParentLedger.State) = reference.1 := by
    cases reference with
    | mk ledger cache =>
      cases ledger
      simp only [Related] at related
      simp only [related.1]
  constructor
  · change (discover stored.cache stored.parents (NativeParentLedgerPools.inputOf entry)).value.map _ = _
    rw [discover_value _ _ _ reference.1.frozen,state,related.2,reference_record_parents]
  · change StoredShakeByteCache.view (StoredShakeHistory.record stored.cache entry).value = _
    rw [StoredShakeHistory.record_view,related.2,reference_record_cache]

theorem record_cost (state : State) (entry : Observation) :
    (record state entry).cost ≤ discoverBound state.cache state.parents (NativeParentLedgerPools.inputOf entry)+
      8*StoredShakeHistory.outputBytes entry+6 := by
  have metadata := discover_cost state.cache state.parents (NativeParentLedgerPools.inputOf entry)
  have bytes := StoredShakeHistory.record_cost state.cache entry
  simp only [record]
  omega

def loop (state : State) : List Observation → Run State
  | [] => ⟨state,1⟩
  | entry::tail =>
    let first := record state entry
    let rest := loop first.value tail
    ⟨rest.value,first.cost+rest.cost+2⟩

theorem loop_related (stored : State) (reference : CompactParentHistory.State)
    (related : Related stored reference) (history : List Observation) :
    Related (loop stored history).value (history.foldl CompactParentHistory.record reference) := by
  induction history generalizing stored reference with
  | nil => exact related
  | cons entry tail ih => exact ih _ _ (record_related stored reference related entry)

def reconstruct (history : List Observation) : Run State := loop initial history

theorem reconstruct_related (history : List Observation) :
    Related (reconstruct history).value (CompactParentHistory.reconstruct history) :=
  loop_related initial CompactParentHistory.initial ⟨rfl,rfl⟩ history

theorem reconstruct_parents (history : List Observation) :
    (reconstruct history).value.parents.map StoredParentContributionsCost.view =
      (CompactSourceHistory.reconstruct history).ledger.parents := by
  have related := (reconstruct_related history).1
  rw [← CompactSourceHistory.parentProjection_reconstruct] at related
  exact related
theorem reconstruct_cache (history : List Observation) :
    StoredShakeByteCache.view (reconstruct history).value.cache = (CompactSourceHistory.reconstruct history).bytes := by
  have related := (reconstruct_related history).2
  rw [← CompactSourceHistory.parentProjection_reconstruct] at related
  exact related
end FormalProof4FHE.HasteBoots.StoredParentMetadataHistory
