module
public import FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers
public import FormalProof4FHE.HasteBoots.NativeSharedLookupGuard
@[expose] public section

/-! Semantic handoff for the original single-opening helper call. Guard equality
is field equality; it does not license rewriting raw words or transcript bytes. -/
namespace FormalProof4FHE.HasteBoots.SingleHelperNativeValue
open NativeFieldRepresentation NativeExtensionFields NativeFieldWire
noncomputable section

theorem matched_value (left right : GoldExtension)
    (matched : NativeGoldInterpolation.equal left right = true) :
    goldExtensionValue left = goldExtensionValue right := by
  apply (NativeGoldExtensionArithmetic.equal_iff left right).mp
  change (∀ i, goldCanonical (left i) = goldCanonical (right i))
  exact of_decide_eq_true matched

theorem matched_vector (width : ℕ) (left right : GoldExtension)
    (matched : NativeGoldInterpolation.equal left right = true) :
    (NativeGoldHelper.vector width left).map goldValue =
      (NativeGoldHelper.vector width right).map goldValue := by
  rw [NativeGoldHelper.vector_value, NativeGoldHelper.vector_value,
    matched_value left right matched]

/-- The actual successful terminal guard supplies the equality; no independent
algebraic equality certificate is required. -/
theorem guard_vector (data : NativeSharedLookupGuard.Inputs)
    (claims : List NativeScalarBatchVerifier.SubClaim) (sourceVars width : ℕ)
    (result : NativeSharedLookupGuard.Result)
    (accepted : NativeSharedLookupGuard.guard data claims sourceVars width = some result)
    (checked : NativeSharedLookupGuard.Checked) (member : checked ∈ result.checked) :
    (NativeGoldHelper.vector width checked.sumClaim.expected).map goldValue =
      (NativeGoldHelper.vector width checked.helper).map goldValue := by
  exact matched_vector width _ _
    ((NativeSharedLookupGuard.guard_spec data claims sourceVars width result accepted).checked checked member).matched

/-- Retain the actual root/query/opening and received helper words. Only the
field interpretation is shared with the checked sum obligation. -/
theorem packet_at {S B : Type} (width : NativeUsizeMessage.Usize)
    (point : List GoldExtension) (proof : NativeSharedLookupProofData.Proof S B)
    (plan : NativeSharedLookupHelpers.Plan S)
    (built : NativeSharedLookupHelpers.build width point proof = some plan)
    (index : ℕ) (root : NativeRootMessage.Digest) (helper sum : GoldExtension) (opening : S)
    (atRoot : proof.roots.val[index]? = some root)
    (atValue : proof.helpers.val[index]? = some helper)
    (atOpening : proof.helperOpenings.val[index]? = some opening)
    (matched : NativeGoldInterpolation.equal sum helper = true) :
    ∃ call, plan.calls[index]? = some call ∧ call.root = root ∧ call.query = plan.query ∧
      call.opening = opening ∧ call.values = NativeSharedLookupHelpers.vector width helper ∧
      call.values.val.map goldValue = (NativeGoldHelper.vector width.val sum).map goldValue := by
  refine ⟨⟨root,plan.query,NativeSharedLookupHelpers.vector width helper,opening⟩,
    NativeSharedLookupHelpers.packet_at width point proof plan built index root helper opening
      atRoot atValue atOpening, rfl, rfl, rfl, rfl, ?_⟩
  exact (matched_vector width.val sum helper matched).symm

end
end FormalProof4FHE.HasteBoots.SingleHelperNativeValue
