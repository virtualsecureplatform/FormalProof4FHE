module
public import FormalProof4FHE.HasteBoots.SingleOpeningFixedResponseData
@[expose] public section

/-! One concrete single-opening response family computed from parsed raw
nonce data, fixed public parameters, one old source log and collector state.
Both random and structured tests share one source and ordered column vector.
No future Prepared work, scheduler or arbitrary response callback is input. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningConcreteColumnFamily
open NativeGoldPcsExecution (Context)
open SingleOpeningChallengeLink (View)
open NativeRootMessage (Digest)
open NativeRootFamilySourceSelection (Log)
open NativeFields (Goldilocks)
open NativeGoldBlockCode (logSize)
open NativeFieldVector (State)
open SingleOpeningFixedResponseData (left messages testMessages)
noncomputable section

abbrev Position (ctx : Context) := Fin (2^logSize ctx.parameters.code)
abbrev Symbol (ctx : Context) := Fin ctx.parameters.code.blockWidth.val → Goldilocks
abbrev Test (ctx : Context) := Fin ctx.parameters.width.val ⊕ Fin ctx.parameters.width.val

abbrev Domain (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1))) :=
  NTTButterfly.domain (logSize ctx.parameters.code) (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) primitive

def source (dummy : Digest) (ctx : Context) (decoded : View) (sourceLog : Log) :=
  SingleOpeningSelectedWord.word dummy decoded.field.data.context decoded.field.data.root ctx sourceLog

def raw (dummy : Digest) (ctx : Context) (decoded : View) (sourceLog : Log) (state : State) :
    Test ctx → Position ctx → Symbol ctx
  | .inl lane => StructuredOpening.combine (SingleOpeningRecoveredMatrix.random ctx state lane) (source dummy ctx decoded sourceLog)
  | .inr lane => StructuredOpening.combine
      (RectangularMatrixResponse.weights (left ctx.parameters decoded.field.data.query) lane) (source dummy ctx decoded sourceLog)

def claim (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (decoded : View) (_state : State) : Test ctx → Position ctx → Symbol ctx
  | .inl lane => BlockEncoder.encode (Domain ctx primitive)
      (RowLayout.padded (m := ctx.parameters.code.messageBlocks.val) (b := ctx.parameters.code.blockWidth.val)
        (testMessages ctx decoded.column.opening lane))
  | .inr lane => BlockEncoder.encode (Domain ctx primitive)
      (RowLayout.padded (m := ctx.parameters.code.messageBlocks.val) (b := ctx.parameters.code.blockWidth.val)
        (messages ctx decoded.column.opening lane))

theorem coded (ctx : Context) [NeZero ctx.parameters.code.blockWidth.val]
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (decoded : View) (state : State) (test : Test ctx) :
    claim ctx primitive decoded state test ∈ BlockCode.code (Domain ctx primitive)
      ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val := by
  cases test with
  | inl lane => exact BlockEncoder.encode_mem_code _ _
  | inr lane => exact BlockEncoder.encode_mem_code _ _

theorem random_witness (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (decoded : View) (sourceLog : Log) (state : State) (distance : ℕ)
    (witness : ∃ lane : Fin ctx.parameters.width.val, distance ≤
      hammingDist (StructuredOpening.combine (SingleOpeningRecoveredMatrix.random ctx state lane) (source dummy ctx decoded sourceLog))
        (BlockEncoder.encode (Domain ctx primitive)
          (RowLayout.padded (m := ctx.parameters.code.messageBlocks.val) (b := ctx.parameters.code.blockWidth.val)
            (testMessages ctx decoded.column.opening lane)))) :
    ∃ test : Test ctx, distance ≤ hammingDist (raw dummy ctx decoded sourceLog state test) (claim ctx primitive decoded state test) := by
  obtain ⟨lane,bounded⟩ := witness
  exact ⟨.inl lane,bounded⟩

theorem structured_witness (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (decoded : View) (sourceLog : Log) (state : State) (distance : ℕ)
    (witness : ∃ lane : Fin ctx.parameters.width.val, distance ≤
      hammingDist (StructuredOpening.combine (RectangularMatrixResponse.weights (left ctx.parameters decoded.field.data.query) lane)
        (source dummy ctx decoded sourceLog))
        (BlockEncoder.encode (Domain ctx primitive)
          (RowLayout.padded (m := ctx.parameters.code.messageBlocks.val) (b := ctx.parameters.code.blockWidth.val)
            (messages ctx decoded.column.opening lane)))) :
    ∃ test : Test ctx, distance ≤ hammingDist (raw dummy ctx decoded sourceLog state test) (claim ctx primitive decoded state test) := by
  obtain ⟨lane,bounded⟩ := witness
  exact ⟨.inr lane,bounded⟩

end
end FormalProof4FHE.HasteBoots.SingleOpeningConcreteColumnFamily
