module
public import FormalProof4FHE.HasteBoots.NativeRootFamilyBudget
@[expose] public section

/-! Parent resolution can repeat inherited metadata, but cannot invent new
context or root values. Every frozen source lies in the Cartesian product of
atomic values discovered in actual observed inputs. All compatible parents,
including orphans and partial seeds, remain in the ledger. -/
namespace FormalProof4FHE.HasteBoots.NativeParentLedgerPools
open InputIndexedOracle (Input)
open NativeRootMessage (Digest)
open NativeCanonicalLookupWire (Source)
open NativeParentLedger (Parent State direct helpers roots active resolve contexts discover prepare)
open NativeTranscript (Observation)
open OracleSpec OracleComp
noncomputable section
open scoped Classical

structure Pools where
  contexts : Finset Digest
  roots : Finset Digest

def sources (pools : Pools) : Finset Source := pools.contexts ×ˢ pools.roots

def localPools (input : Input) : Pools :=
  ⟨((direct input).map Prod.fst ++ helpers input).toFinset,
    ((direct input).map Prod.snd ++ roots input).toFinset⟩

def grow (pools : Pools) (input : Input) : Pools :=
  ⟨pools.contexts ∪ (localPools input).contexts,pools.roots ∪ (localPools input).roots⟩

theorem grow_contexts_card_le (pools : Pools) (input : Input) :
    (grow pools input).contexts.card ≤ pools.contexts.card+(localPools input).contexts.card :=
  Finset.card_union_le _ _

theorem grow_roots_card_le (pools : Pools) (input : Input) :
    (grow pools input).roots.card ≤ pools.roots.card+(localPools input).roots.card :=
  Finset.card_union_le _ _

def Coherent (state : State) (pools : Pools) : Prop :=
  (∀ parent ∈ state.parents, (∀ key ∈ parent.sources, key ∈ sources pools) ∧
    ∀ context ∈ parent.helpers, context ∈ pools.contexts) ∧ state.frozen ⊆ sources pools

theorem sources_grow (pools : Pools) (input : Input) : sources pools ⊆ sources (grow pools input) := by
  intro key present
  obtain ⟨context,root⟩ := Finset.mem_product.mp present
  exact Finset.mem_product.mpr ⟨Finset.mem_union_left _ context,Finset.mem_union_left _ root⟩

theorem coherent_grow (state : State) (pools : Pools) (input : Input) (coherent : Coherent state pools) :
    Coherent state (grow pools input) := by
  refine ⟨?_,coherent.2.trans (sources_grow pools input)⟩
  intro parent present
  obtain ⟨source,helper⟩ := coherent.1 parent present
  exact ⟨fun key member => sources_grow pools input (source key member),
    fun context member => Finset.mem_union_left _ (helper context member)⟩

theorem direct_mem (pools : Pools) (input : Input) (key : Source) (present : key ∈ direct input) :
    key ∈ sources (grow pools input) := by
  apply Finset.mem_product.mpr
  constructor
  · apply Finset.mem_union_right
    apply List.mem_toFinset.mpr
    exact List.mem_append_left _ (List.mem_map.mpr ⟨key,present,rfl⟩)
  · apply Finset.mem_union_right
    apply List.mem_toFinset.mpr
    exact List.mem_append_left _ (List.mem_map.mpr ⟨key,present,rfl⟩)

theorem active_parent (state : State) (cache : NativeShakeCache.Cache) (input : Input) (parent : Parent)
    (present : parent ∈ active state cache input) : parent ∈ state.parents := by
  unfold active at present
  split at present
  · simp only [List.not_mem_nil] at present
  · exact (List.mem_filter.mp present).1

theorem resolve_mem (state : State) (cache : NativeShakeCache.Cache) (pools : Pools) (input : Input)
    (coherent : Coherent state pools) (key : Source) (present : key ∈ resolve state cache input) :
    key ∈ sources (grow pools input) := by
  rcases List.mem_append.mp present with localKey | inherited
  · exact direct_mem pools input key localKey
  · obtain ⟨parent,parentIn,member⟩ := List.mem_flatMap.mp inherited
    obtain ⟨source,helper⟩ := coherent.1 parent (active_parent state cache input parent parentIn)
    rcases List.mem_append.mp member with old | cross
    · exact sources_grow pools input (source key old)
    · obtain ⟨context,contextIn,rootMember⟩ := List.mem_flatMap.mp cross
      obtain ⟨root,rootIn,rfl⟩ := List.mem_map.mp rootMember
      apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_union_left _ (helper context contextIn)
      · apply Finset.mem_union_right
        apply List.mem_toFinset.mpr
        exact List.mem_append_right _ rootIn

theorem contexts_mem (state : State) (cache : NativeShakeCache.Cache) (pools : Pools) (input : Input)
    (coherent : Coherent state pools) (context : Digest) (present : context ∈ contexts state cache input) :
    context ∈ (grow pools input).contexts := by
  rcases List.mem_append.mp present with localContext | inherited
  · apply Finset.mem_union_right
    apply List.mem_toFinset.mpr
    exact List.mem_append_right _ localContext
  · obtain ⟨parent,parentIn,contextIn⟩ := List.mem_flatMap.mp inherited
    exact Finset.mem_union_left _ ((coherent.1 parent (active_parent state cache input parent parentIn)).2 context contextIn)

theorem discover_coherent (state : State) (cache : NativeShakeCache.Cache) (pools : Pools) (input : Input)
    (coherent : Coherent state pools) : Coherent (discover state cache input) (grow pools input) := by
  have old := coherent_grow state pools input coherent
  unfold discover
  split
  · exact old
  · refine ⟨?_,old.2⟩
    intro parent member
    rcases List.mem_cons.mp member with rfl | prior
    · exact ⟨fun key present => resolve_mem state cache pools input coherent key present,
        fun context present => contexts_mem state cache pools input coherent context present⟩
    · exact old.1 parent prior

theorem prepare_coherent (state : State) (cache : NativeShakeCache.Cache) (pools : Pools) (input : Input)
    (coherent : Coherent state pools) : Coherent (prepare state cache input).next (grow pools input) := by
  have discovered := discover_coherent state cache pools input coherent
  refine ⟨discovered.1,?_⟩
  rw [NativeParentLedger.prepare_frozen]
  intro key present
  rcases Finset.mem_union.mp present with old | newKey
  · exact sources_grow pools input (coherent.2 old)
  · exact resolve_mem state cache pools input coherent key (List.mem_toFinset.mp newKey)

def inputOf : Observation → Input
  | .start input | .output input _ _ | .hash input _ => input

def recordPools (pools : Pools) (entry : Observation) : Pools := grow pools (inputOf entry)

theorem record_coherent {Payload : Type} (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (state : NativeRootFamilyState.State) (pools : Pools) (entry : Observation) (coherent : Coherent state.1.1 pools) :
    Coherent (NativeRootFamilyState.record enc dummy state entry).1.1 (recordPools pools entry) := by
  cases entry with
  | start input => exact discover_coherent _ _ _ _ coherent
  | hash input digest => exact discover_coherent _ _ _ _ coherent
  | output input offset values =>
    by_cases empty : values = []
    · simpa only [NativeRootFamilyState.record,NativeParentHistory.record,empty,ite_true,recordPools,inputOf] using
        discover_coherent state.1.1 state.1.2 pools input coherent
    · simpa only [NativeRootFamilyState.record,NativeParentHistory.record,empty,ite_false,recordPools,inputOf] using
        prepare_coherent state.1.1 state.1.2 pools input coherent

theorem fold_coherent {Payload : Type} (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (history : List Observation) (state : NativeRootFamilyState.State) (pools : Pools) (coherent : Coherent state.1.1 pools) :
    Coherent (history.foldl (NativeRootFamilyState.record enc dummy) state).1.1 (history.foldl recordPools pools) := by
  induction history generalizing state pools with
  | nil => exact coherent
  | cons entry rest ih => exact ih _ _ (record_coherent enc dummy state pools entry coherent)

def observedPools (history : List Observation) : Pools := history.foldl recordPools ⟨∅,∅⟩

theorem reconstructed_coherent (dummy : Digest) (history : List Observation) :
    Coherent (NativeRootFamilyBudget.ledger dummy history) (observedPools history) := by
  exact fold_coherent NativeGoldColumnAuthentication.encoding dummy history _ ⟨∅,∅⟩
    (by simp [Coherent,NativeParentLedger.empty])

theorem frozen_card_le (dummy : Digest) (history : List Observation) :
    (NativeRootFamilyBudget.ledger dummy history).frozen.card ≤
      (observedPools history).contexts.card*(observedPools history).roots.card := by
  have bound := Finset.card_le_card (reconstructed_coherent dummy history).2
  simpa only [sources,Finset.card_product] using bound

theorem hash_loss_le_pools (dummy : Digest) (history : List Observation) (query : Input) :
    CheckpointCollision.loss unifSpec NativeMerkleShapeFamily.shape (.inr (.inl query))
      (NativeGoldBatchFamilyAvailability.reconstructed dummy history) ≤
      ((3*(JointHashCache.project history).keys.card+
        64*((observedPools history).contexts.card*(observedPools history).roots.card) : ℕ) : ENNReal)/(2 : ENNReal)^512 := by
  apply (NativeRootFamilyBudget.hash_loss_bound dummy history query).trans
  apply ENNReal.div_le_div_right
  apply Nat.cast_le.mpr
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 64 (frozen_card_le dummy history)) _
end
end FormalProof4FHE.HasteBoots.NativeParentLedgerPools
