module
public import FormalProof4FHE.HasteBoots.NativeRootFamilyAudit
@[expose] public section

/-! Exact counting in the actual cumulative root-family registry. The 64
annotations are shapes per frozen key, not attacker attempts or physical
work. Fresh-hash loss is bounded without expanding any complete Merkle tree. -/
namespace FormalProof4FHE.HasteBoots.NativeRootFamilyBudget
open NativeParentLedger (prepare)
open InputIndexedOracle (Input)
open NativeRootMessage (Digest)
open NativeMerkleShapeFamily (shape)
open NativeTranscript (Observation)
open OracleSpec OracleComp MerkleTreeMultiExtractability
noncomputable section
open scoped Classical

private theorem eraseDups_nodup {A : Type} [BEq A] [LawfulBEq A] (values : List A) : values.eraseDups.Nodup := by
  cases values with
  | nil => simp
  | cons head tail =>
    rw [List.eraseDups_cons,List.nodup_cons]
    exact ⟨by simp,eraseDups_nodup _⟩
termination_by values.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem requests_nodup (state : NativeParentLedger.State) (cache : NativeShakeCache.Cache) (input : Input) :
    (prepare state cache input).requests.Nodup := by
  exact (eraseDups_nodup _).filter _

theorem requests_disjoint (state : NativeParentLedger.State) (cache : NativeShakeCache.Cache) (input : Input) :
    Disjoint state.frozen (prepare state cache input).requests.toFinset := by
  apply Finset.disjoint_left.mpr
  intro key earlier later
  exact (NativeParentLedger.prepare_mem state cache input key).mp (List.mem_toFinset.mp later) |>.2 earlier

theorem prepare_card (state : NativeParentLedger.State) (cache : NativeShakeCache.Cache) (input : Input) :
    (prepare state cache input).next.frozen.card = state.frozen.card+(prepare state cache input).requests.length := by
  change (state.frozen ∪ (prepare state cache input).requests.toFinset).card = _
  rw [Finset.card_union_of_disjoint (requests_disjoint state cache input),
    List.toFinset_card_of_nodup (requests_nodup state cache input)]

theorem roots_count (roots : List (NativeMerkleShapeFamily.Tag × Digest))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    (RecordRoots.state shape roots state).checkpoints.checkpoints.length = state.checkpoints.checkpoints.length+roots.length := by
  induction roots generalizing state with
  | nil => exact (Nat.add_zero _).symm
  | cons root rest ih =>
    rw [RecordRoots.state,ih]
    simp only [CheckpointExecution.record,ExtractorState.recordCumulative_checkpoints,List.length_append,List.length_cons,List.length_nil]
    omega

def Counted (state : NativeRootFamilyState.State) : Prop :=
  state.2.checkpoints.checkpoints.length = 64*state.1.1.frozen.card

theorem record_counted {Payload : Type} (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (state : NativeRootFamilyState.State) (counted : Counted state) (entry : Observation) :
    Counted (NativeRootFamilyState.record enc dummy state entry) := by
  cases entry with
  | start input =>
    simpa only [Counted,NativeRootFamilyState.record,NativeParentHistory.record,NativeLazyStateExecution.record,
      NativeParentLedger.discover_frozen] using counted
  | hash input digest =>
    simpa only [Counted,NativeRootFamilyState.record,NativeParentHistory.record,NativeLazyStateExecution.record,
      CheckpointExecution.afterHash,NativeParentLedger.discover_frozen] using counted
  | output input offset values =>
    by_cases empty : values = []
    · simpa only [Counted,NativeRootFamilyState.record,NativeParentHistory.record,empty,ite_true,
        NativeParentLedger.discover_frozen] using counted
    · simp only [Counted,NativeRootFamilyState.record,NativeParentHistory.record,empty,ite_false,
        roots_count,NativeMerkleShapeFamily.requests_length,prepare_card]
      rw [show state.2.checkpoints.checkpoints.length = 64*state.1.1.frozen.card from counted]
      omega

theorem fold_counted {Payload : Type} (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (history : List Observation) (state : NativeRootFamilyState.State) (counted : Counted state) :
    Counted (history.foldl (NativeRootFamilyState.record enc dummy) state) := by
  induction history generalizing state with
  | nil => exact counted
  | cons entry rest ih => exact ih _ (record_counted enc dummy state counted entry)

def ledger (dummy : Digest) (history : List Observation) : NativeParentLedger.State :=
  (history.foldl (NativeRootFamilyState.record NativeGoldColumnAuthentication.encoding dummy)
    ((NativeParentLedger.empty,NativeShakeCache.empty),CheckpointExecution.empty shape)).1.1

theorem reconstructed_count (dummy : Digest) (history : List Observation) :
    (NativeGoldBatchFamilyAvailability.reconstructed dummy history).checkpoints.checkpoints.length =
      64*(ledger dummy history).frozen.card :=
  fold_counted NativeGoldColumnAuthentication.encoding dummy history _ (by rfl)

/-- The node-budget clamp removes any dependence on full-tree expansion. -/
theorem hash_loss_bound (dummy : Digest) (history : List Observation) (query : Input) :
    CheckpointCollision.loss unifSpec shape (.inr (.inl query))
      (NativeGoldBatchFamilyAvailability.reconstructed dummy history) ≤
        ((3*(JointHashCache.project history).keys.card+64*(ledger dummy history).frozen.card : ℕ) : ENNReal)/(2 : ENNReal)^512 := by
  rw [CheckpointCollision.hash_loss]
  split
  · rw [JointHashKernel.digest_card,Nat.cast_pow,Nat.cast_ofNat]
    apply ENNReal.div_le_div_right
    apply Nat.cast_le.mpr
    rw [reconstructed_count,NativeGoldBatchFamilyAvailability.reconstructed_hash]
    have bounded := Nat.min_le_right
      (NativeGoldBatchFamilyAvailability.reconstructed dummy history).checkpoints.totalNodeBudget
      (2*(JointHashCache.project history).keys.card+64*(ledger dummy history).frozen.card)
    omega
  · exact zero_le
end
end FormalProof4FHE.HasteBoots.NativeRootFamilyBudget
