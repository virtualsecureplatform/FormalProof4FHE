module

public import FormalProof4FHE.HasteBoots.NativeGoldPcsWire
public import FormalProof4FHE.HasteBoots.NativeGoldScalarQuery
@[expose] public section

/-! Scalar guards construct validated raw matrices. Their existing checks
imply the exact usize/matrix-vector domains needed by the PCS wire adapter;
conversion preserves the actual pairs and omits only the local post-map. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldScalarPcsQuery
noncomputable section

theorem built_valid (width : ℕ) (low high : List NativeGoldExtensionArithmetic.Word)
    (shape : NativeGoldProjection.dimensions width = true)
    (pair : NativeGoldCoefficientsQuery.Pair) (member : pair ∈ (NativeGoldScalarQuery.built width low high shape).pairs) :
    NativeGoldMatrix.validate pair.zero width = true ∧ NativeGoldMatrix.validate pair.one width = true := by
  cases high with
  | nil => cases member
  | cons value tail =>
    simp only [NativeGoldScalarQuery.built,List.mem_cons] at member
    rcases member with rfl | later
    · exact ⟨NativeGoldMatrixProduct.result_valid _ _ _ _ _,NativeGoldMatrixProduct.result_valid _ _ _ _ _⟩
    · obtain ⟨point,_,rfl⟩ := List.mem_map.mp later
      exact ⟨NativeGoldMultiplicationMatrix.matrix_valid _ _ shape,NativeGoldMultiplicationMatrix.matrix_valid _ _ shape⟩

theorem scalar_valid (sourceVars width : ℕ) (point : List NativeGoldExtensionArithmetic.Word)
    (query : NativeGoldCoefficientsQuery.Query) (success : NativeGoldScalarQuery.scalarQuery sourceVars width point = some query)
    (pair : NativeGoldCoefficientsQuery.Pair) (member : pair ∈ query.pairs) :
    NativeGoldMatrix.validate pair.zero width = true ∧ NativeGoldMatrix.validate pair.one width = true := by
  have checked := NativeGoldScalarQuery.scalarQuery_checked sourceVars width point query success
  have same := Option.some.inj ((NativeGoldScalarQuery.scalarQuery_success sourceVars width point checked).symm.trans success)
  subst query
  exact built_valid _ _ _ _ pair member

/-- Native validation already establishes both matrix allocation bounds and
scalar-pair count; conversion adds no extra successful-domain assumption. -/
theorem scalar_complete (sourceVars width : ℕ) (point : List NativeGoldExtensionArithmetic.Word)
    (query : NativeGoldCoefficientsQuery.Query) (success : NativeGoldScalarQuery.scalarQuery sourceVars width point = some query) :
    ∃ wire, NativeGoldPcsWire.fromPairs query.pairs = some wire ∧ wire.models = query.pairs := by
  have checked := NativeGoldScalarQuery.scalarQuery_checked sourceVars width point query success
  have dimensions := (NativeScalarQueryShape.check_iff _ _ _).mp checked
  have count : query.pairs.length < 2^64 := by
    rw [NativeGoldScalarQuery.scalarQuery_length _ _ _ _ success]
    omega
  have fits : ∀ pair ∈ query.pairs, NativeGoldPcsWire.pairFits pair := by
    intro pair member
    have valid := scalar_valid sourceVars width point query success pair member
    exact ⟨NativeGoldPcsWire.valid_fits _ width valid.1,NativeGoldPcsWire.valid_fits _ width valid.2⟩
  obtain ⟨wire,packed⟩ := NativeGoldPcsWire.fromPairs_complete query.pairs count fits
  exact ⟨wire,packed,NativeGoldPcsWire.fromPairs_spec _ _ packed⟩
end
end FormalProof4FHE.HasteBoots.NativeGoldScalarPcsQuery
