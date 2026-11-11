module
public import FormalProof4FHE.HasteBoots.OriginalSharedParent
public import FormalProof4FHE.HasteBoots.GoldContextCollision
@[expose] public section

/-! Matching observed context digests identify full original parameter
records across a replay fiber, outside the same shared root/hash bad event.
Observation of both preimages in the old prefix is explicit; a later context
computation is not silently treated as a prior observation. -/
namespace FormalProof4FHE.HasteBoots.GoldContextFiber
open InputIndexedOracle (World)
open NativeTranscript (Execution)
open NativeRootMessage (Digest)
open NativeBrakedownContext (Parameters)
open NativeGoldBlockCode (Stored description)
open OracleProgram (run)
noncomputable section

theorem parameters_or_bad {A : Type} {past : World → Execution A} (replay : ObservationReplay.Replayable past)
    (world other : World) (left right : Parameters Stored) (digest dummy : Digest)
    (leftComputed : (run (NativeBrakedownContext.context description.row left) world).run.1 = some digest)
    (rightComputed : (run (NativeBrakedownContext.context description.row right) other).run.1 = some digest)
    (leftObserved : (run (NativeBrakedownContext.context description.row left) world).run.2.Sublist (past world).run.2)
    (rightObserved : (run (NativeBrakedownContext.context description.row right) other).run.2.Sublist (past other).run.2)
    (same : (past other).run = (past world).run) :
    left = right ∨ NativeRootFamilyLifetime.Bad dummy (past world).run.2 := by
  by_cases equal : left = right
  · exact Or.inl equal
  · apply Or.inr
    apply Or.inr
    rw [NativeGoldBatchFamilyAvailability.reconstructed_hash]
    have leftMember := GoldContextCollision.observed left world digest leftComputed _ leftObserved
    have rightMember := GoldContextCollision.observed right other digest rightComputed _ rightObserved
    rw [same] at rightMember
    exact ⟨GoldContextInput.bytes left,GoldContextInput.bytes right,digest,digest,
      (fun bytes => equal (GoldContextInput.bytes_injective bytes)),
      NativeHashOracleBridge.cache_known world _ (replay.truthful world) _ digest leftMember,
      NativeHashOracleBridge.cache_known world _ (replay.truthful world) _ digest rightMember,HEq.rfl⟩

theorem on_parent_fiber {A : Type} {past : World → Execution A} (replay : ObservationReplay.Replayable past)
    (world other : World) (left right : Parameters Stored) (digest dummy : Digest)
    (leftComputed : (run (NativeBrakedownContext.context description.row left) world).run.1 = some digest)
    (rightComputed : (run (NativeBrakedownContext.context description.row right) other).run.1 = some digest)
    (leftObserved : (run (NativeBrakedownContext.context description.row left) world).run.2.Sublist (past world).run.2)
    (rightObserved : (run (NativeBrakedownContext.context description.row right) other).run.2.Sublist (past other).run.2)
    (same : (ParentFactorFiber.extend past other).run = (ParentFactorFiber.extend past world).run) :
    left = right ∨ NativeRootFamilyLifetime.Bad dummy (past world).run.2 :=
  parameters_or_bad replay world other left right digest dummy leftComputed rightComputed leftObserved rightObserved
    (ParentFactorFiber.old_packet past world other same)

/-- One matched ordered registry and observed original slot computations
identify the full parameter record and root at corresponding ordinals. -/
theorem registry_slot {A : Type} {past : World → Execution A} (replay : ObservationReplay.Replayable past)
    (world other : World) (left right : NativePrefixCodec.Vector (NativeSharedLookupParent.Oracle Stored))
    (view : SharedParentInputView.View)
    (leftComputed : (run (NativeSharedLookupParent.contexts description.row left.val) world).run.1 = some view.sources.val)
    (rightComputed : (run (NativeSharedLookupParent.contexts description.row right.val) other).run.1 = some view.sources.val)
    (leftIndex : Fin left.val.length) (rightIndex : Fin right.val.length) (ordinal : leftIndex.val = rightIndex.val)
    (leftObserved : (run (NativeBrakedownContext.context description.row left.val[leftIndex.val].parameters) world).run.2.Sublist (past world).run.2)
    (rightObserved : (run (NativeBrakedownContext.context description.row right.val[rightIndex.val].parameters) other).run.2.Sublist (past other).run.2)
    (dummy : Digest) (same : (ParentFactorFiber.extend past other).run = (ParentFactorFiber.extend past world).run) :
    (left.val[leftIndex.val].parameters = right.val[rightIndex.val].parameters ∧ left.val[leftIndex.val].root = right.val[rightIndex.val].root) ∨
      NativeRootFamilyLifetime.Bad dummy (past world).run.2 := by
  obtain ⟨source,_,context,_⟩ := OriginalSharedParent.slot description.row left world view leftComputed leftIndex
  have compared := OriginalSharedParent.slot_compare description.row left world description.row right other view leftComputed rightComputed leftIndex rightIndex ordinal
  have rightContext := compared.1.symm.trans context
  rcases on_parent_fiber replay world other _ _ source.1 dummy context rightContext leftObserved rightObserved same with equal | bad
  · exact Or.inl ⟨equal,compared.2⟩
  · exact Or.inr bad

/-- The same observed parameter preimages, context digest, root and original
raw prefix identify the entire public packed table, including every padding
lane. Other verifier-call fields do not select a replacement source. -/
theorem packed_on_fiber {A : Type} {past : World → Execution A} (replay : ObservationReplay.Replayable past)
    (world other : World) (left right : NativeGoldBatchPcsProgram.Context) (context dummy : Digest)
    (leftComputed : (run (NativeBrakedownContext.context description.row left.parameters) world).run.1 = some context)
    (rightComputed : (run (NativeBrakedownContext.context description.row right.parameters) other).run.1 = some context)
    (leftObserved : (run (NativeBrakedownContext.context description.row left.parameters) world).run.2.Sublist (past world).run.2)
    (rightObserved : (run (NativeBrakedownContext.context description.row right.parameters) other).run.2.Sublist (past other).run.2)
    (root : left.root = right.root) (radius : ℕ)
    (leftCapacity : GoldCommonSourceTable.Capacity left.parameters) (rightCapacity : GoldCommonSourceTable.Capacity right.parameters)
    (leftGeometry : GoldHistorySourceTable.Geometry left.parameters) (rightGeometry : GoldHistorySourceTable.Geometry right.parameters)
    {padding : ℕ} (leftWidth : left.parameters.width.val = 3+padding) (rightWidth : right.parameters.width.val = 3+padding)
    (same : (ParentFactorFiber.extend past other).run = (ParentFactorFiber.extend past world).run) :
    HEq (ScalarPublicSourceModel.publicPacked left dummy context left.root (past world).run.2 radius leftCapacity leftGeometry leftWidth)
      (ScalarPublicSourceModel.publicPacked right dummy context right.root (past other).run.2 radius rightCapacity rightGeometry rightWidth) ∨
        NativeRootFamilyLifetime.Bad dummy (past world).run.2 := by
  rcases on_parent_fiber replay world other left.parameters right.parameters context dummy leftComputed rightComputed leftObserved rightObserved same with parameters | bad
  · apply Or.inl
    rw [congrArg Prod.snd (ParentFactorFiber.old_packet past world other same),← root]
    cases left
    cases right
    cases parameters
    rfl
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.GoldContextFiber
