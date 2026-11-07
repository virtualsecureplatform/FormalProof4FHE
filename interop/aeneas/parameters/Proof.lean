/-! Appended to import-adjusted generated declarations, with no generated term
changes. These prove actual extracted accessors, not constructor correctness,
Rust compiler correctness, heap aliasing, or physical costs. -/
namespace HasteBootsExtractedParametersProof
open Aeneas Aeneas.Std
open formalproof4fhe_native_ntt_cache_fixture
abbrev Code := pcs.utils.code.block.BlockReedSolomonCode algebra.goldilocks.Goldilocks
abbrev Params := pcs.matrix_weighted.Parameters Code

theorem header_exact (parameters : Params) :
    header parameters = .ok (parameters.num_vars,parameters.width,parameters.left_vars,parameters.queries) := rfl

theorem retained_code_exact (parameters : Params) :
    retained_code parameters = .ok parameters.code := rfl

theorem generic_code_exact {C : Type} (parameters : pcs.matrix_weighted.Parameters C) :
    pcs.matrix_weighted.Parameters.impl.code parameters = .ok parameters.code := rfl

theorem code_fields (parameters : Params) (code : Code) (executed : retained_code parameters = .ok code) :
    code.message_len = parameters.code.message_len ∧ code.block_width = parameters.code.block_width ∧
    code.message_blocks = parameters.code.message_blocks ∧ code.codeword_blocks = parameters.code.codeword_blocks ∧
    code.modulus = parameters.code.modulus ∧ code.domain_root = parameters.code.domain_root := by
  have same : parameters.code = code := Result.ok.inj executed
  cases same
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem header_code_independent (parameters : Params) (code : Code) :
    header {parameters with code := code} = header parameters := rfl

theorem read_header_and_code (parameters : Params) :
    (do let dimensions ← header parameters
        let code ← retained_code parameters
        pure (dimensions,code)) =
      (Result.ok ((parameters.num_vars,parameters.width,parameters.left_vars,parameters.queries),parameters.code)) := rfl

end HasteBootsExtractedParametersProof
