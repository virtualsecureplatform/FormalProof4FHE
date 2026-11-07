module
public import FormalProof4FHE.HasteBoots.PreparedMerkleNodes
@[expose] public section

/-! Views between stored digest bytes and the existing functional digest model.
Only conversion from a stored vector is priced here: 64 byte loads, 64 list
stores and initialization. Arbitrary incoming function materialization and
physical/compiler refinement remain separate. -/
namespace FormalProof4FHE.HasteBoots.StoredDigestView
open InputIndexedOracle (Byte)
open NativeRootMessage (Digest)
open PreparedMerklePayloads (StoredDigest store)
open SolverOperationCost (Run)

def view (label : StoredDigest) : Digest :=
  fun i => label.val[i.val]'(by rw [label.property]; exact i.isLt)

theorem view_store (label : Digest) : view (store label) = label := by
  funext i
  simp only [view,store,List.getElem_ofFn]

theorem store_view (label : StoredDigest) : store (view label) = label := by
  apply Subtype.ext
  apply List.ext_getElem
  · simp only [store,List.length_ofFn,label.property]
  · intro i left right
    simp only [store,List.getElem_ofFn,view]

def fromVector (value : Vector Byte 64) : Run StoredDigest :=
  ⟨⟨value.toList,by simp⟩,129⟩

theorem fromVector_value (value : Vector Byte 64) : (fromVector value).value = store value.get := by
  apply Subtype.ext
  exact (FixedByteReadCost.ofFn_get value).symm

theorem view_fromVector (value : Vector Byte 64) : view (fromVector value).value = value.get := by
  rw [fromVector_value,view_store]

theorem fromVector_cost (value : Vector Byte 64) : (fromVector value).cost = 129 := rfl
end FormalProof4FHE.HasteBoots.StoredDigestView
