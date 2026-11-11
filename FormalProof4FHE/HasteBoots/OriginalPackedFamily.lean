module
public import FormalProof4FHE.HasteBoots.AllocatedParentFamily
@[expose] public section

/-! Corresponding original slots give equal whole packed source tables.
The fixed helper parameters give the same whole table for each common root.
Original helper-root ordinal alignment and job selection remain separate. -/
namespace FormalProof4FHE.HasteBoots.OriginalPackedFamily
open InputIndexedOracle (World)
open NativeGoldBlockCode (description)
open NativeRootMessage (Digest)
open NativeGoldBatchPcsProgram (Context)
open OracleProgram (Program run runPrefix)
open OriginalParentFamily (Family)
noncomputable section

theorem entry_eq {T : Type} (left right : NativePrefixCodec.Vector T) (same : left = right)
    (leftIndex : Fin left.val.length) (rightIndex : Fin right.val.length) (ordinal : leftIndex.val = rightIndex.val) :
    left.val.get leftIndex = right.val.get rightIndex := by
  subst right
  have index : leftIndex = rightIndex := Fin.ext ordinal
  subst rightIndex
  rfl

theorem source {A : Type} (program : Program A) (position : ℕ) (world other : World)
    (left : Family program position world) (right : Family program position other)
    (registry : left.registry = right.registry) (parents : left.parent = right.parent)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run)
    (leftIndex : Fin left.registry.val.length) (rightIndex : Fin right.registry.val.length) (ordinal : leftIndex.val = rightIndex.val)
    (leftContext rightContext : Context)
    (leftParameters : leftContext.parameters = (left.registry.val.get leftIndex).parameters)
    (rightParameters : rightContext.parameters = (right.registry.val.get rightIndex).parameters)
    (dummy : Digest) (radius : ℕ)
    (leftCapacity : GoldCommonSourceTable.Capacity leftContext.parameters) (rightCapacity : GoldCommonSourceTable.Capacity rightContext.parameters)
    (leftGeometry : GoldHistorySourceTable.Geometry leftContext.parameters) (rightGeometry : GoldHistorySourceTable.Geometry rightContext.parameters)
    {leftPadding rightPadding : ℕ} (leftWidth : leftContext.parameters.width.val = 3+leftPadding) (rightWidth : rightContext.parameters.width.val = 3+rightPadding) :
    HEq (ScalarPublicSourceModel.publicPacked leftContext dummy
      (InputIndexedOracle.sha512 world (GoldContextInput.bytes (left.registry.val.get leftIndex).parameters))
      (left.registry.val.get leftIndex).root (runPrefix position program world).run.2 radius leftCapacity leftGeometry leftWidth)
      (ScalarPublicSourceModel.publicPacked rightContext dummy
      (InputIndexedOracle.sha512 other (GoldContextInput.bytes (right.registry.val.get rightIndex).parameters))
      (right.registry.val.get rightIndex).root (runPrefix position program other).run.2 radius rightCapacity rightGeometry rightWidth) := by
  have entries := entry_eq left.registry right.registry registry leftIndex rightIndex ordinal
  have computed : (run (NativeSharedLookupParent.contexts description.row right.registry.val) other).run.1 = some left.parent.sources.val := by
    rw [parents]
    exact right.computed
  have compared := OriginalSharedParent.slot_compare description.row left.registry world description.row right.registry other left.parent
    left.computed computed leftIndex rightIndex ordinal
  rw [GoldContextCollision.context_run,GoldContextCollision.context_run] at compared
  apply PackedContextCongruence.packed leftContext rightContext
    (leftParameters.trans ((congrArg NativeSharedLookupParent.Oracle.parameters entries).trans rightParameters.symm)) dummy _ _ _ _
    (Option.some.inj compared.1) compared.2 _ _
    (congrArg Prod.snd (ParentFactorFiber.old_packet (runPrefix position program) world other same)).symm radius
    leftCapacity rightCapacity leftGeometry rightGeometry leftWidth rightWidth

/-- The helper keeps its own full row dimension and packing lanes. This
compares all tables indexed by a common root, without selecting a new root. -/
theorem helper {A : Type} (program : Program A) (position : ℕ) (world other : World)
    (left : Family program position world) (right : Family program position other)
    (parameters : left.helper = right.helper) (bindings : left.bindings = right.bindings)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run)
    (leftContext rightContext : Context)
    (leftParameters : leftContext.parameters = left.helper) (rightParameters : rightContext.parameters = right.helper)
    (dummy root : Digest) (radius : ℕ)
    (leftCapacity : GoldCommonSourceTable.Capacity leftContext.parameters) (rightCapacity : GoldCommonSourceTable.Capacity rightContext.parameters)
    (leftGeometry : GoldHistorySourceTable.Geometry leftContext.parameters) (rightGeometry : GoldHistorySourceTable.Geometry rightContext.parameters)
    {leftPadding rightPadding : ℕ} (leftWidth : leftContext.parameters.width.val = 3+leftPadding) (rightWidth : rightContext.parameters.width.val = 3+rightPadding) :
    HEq (ScalarPublicSourceModel.publicPacked leftContext dummy (InputIndexedOracle.sha512 world (GoldContextInput.bytes left.helper))
      root (runPrefix position program world).run.2 radius leftCapacity leftGeometry leftWidth)
      (ScalarPublicSourceModel.publicPacked rightContext dummy (InputIndexedOracle.sha512 other (GoldContextInput.bytes right.helper))
      root (runPrefix position program other).run.2 radius rightCapacity rightGeometry rightWidth) := by
  have related : List.Forall₂ (ParentBindingTrace.ForRequest description.row right.registry.val right.helper other) right.requests.val left.bindings.bindings := by
    rw [bindings]
    exact right.related
  have contexts := CanonicalHelperFiber.helper_contexts left.registry.val right.registry.val left.helper right.helper world other left.requests.val
    right.requests.val left.bindings.bindings left.nonempty left.related related
  rw [GoldContextCollision.context_run,GoldContextCollision.context_run] at contexts
  exact PackedContextCongruence.packed leftContext rightContext (leftParameters.trans (parameters.trans rightParameters.symm))
    dummy _ _ root root (Option.some.inj contexts) rfl _ _
    (congrArg Prod.snd (ParentFactorFiber.old_packet (runPrefix position program) world other same)).symm radius
    leftCapacity rightCapacity leftGeometry rightGeometry leftWidth rightWidth

/-- Original slot-address vectors determine their typed selector uniquely;
proofs of bounds cannot permute equal-looking aliases. -/
theorem slots {leftCount rightCount : ℕ} {leftRequest rightRequest : NativeSharedLookupStatement.Request}
    (count : leftCount = rightCount) (request : leftRequest = rightRequest)
    (left : LookupOriginalSlots.Slots leftCount leftRequest) (right : LookupOriginalSlots.Slots rightCount rightRequest) :
    HEq left.slot right.slot := by
  subst rightCount
  subst rightRequest
  have values := List.ofFn_inj.mp (left.ordered.trans right.ordered.symm)
  apply heq_of_eq
  funext column
  exact Fin.ext (congrFun values column)

end
end FormalProof4FHE.HasteBoots.OriginalPackedFamily
