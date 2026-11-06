module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchFalseClaimWitness
public import FormalProof4FHE.HasteBoots.NativeGoldBatchFirstFieldSource
@[expose] public section

/-! One concrete random/structured response family from parsed nonce data,
fixed parameters, a recovered source log and the actual collector state.
All tests share one source and ordered column vector. This definition has
no future Prepared work, scheduler or arbitrary response callback. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchConcreteColumnFamily
open NativeGoldBatchPcsProgram (Context)
open NativeGoldBatchChallengeLink (View)
open NativeRootMessage (Digest)
open NativeRootFamilySourceSelection (Log)
open NativeFields (Goldilocks)
open NativeGoldBlockCode (logSize)
open NativeFieldVector (State)
open NativeGoldBatchFixedResponseData (groupLeft messages testMessages)
noncomputable section

abbrev Position (ctx : Context) := Fin (2^(logSize ctx.parameters.code))
abbrev Symbol (ctx : Context) := Fin ctx.parameters.code.blockWidth.val → Goldilocks
abbrev Group (ctx : Context) (decoded : View) := Fin (NativeGoldQueryGroups.groupCount ctx.parameters.leftVariables.val decoded.field.data.queries)
abbrev Test (ctx : Context) (decoded : View) := Fin ctx.parameters.width.val ⊕ (Group ctx decoded × Fin ctx.parameters.width.val)

def source (dummy : Digest) (ctx : Context) (decoded : View) (sourceLog : Log) :=
  NativeGoldBatchSelectedWord.word dummy decoded.field.data.context decoded.field.data.root ctx sourceLog

def raw (dummy : Digest) (ctx : Context) (decoded : View) (sourceLog : Log) (state : State) :
    Test ctx decoded → Position ctx → Symbol ctx
  | .inl lane => StructuredOpening.combine (NativeGoldBatchRecoveredMatrix.random ctx state lane) (source dummy ctx decoded sourceLog)
  | .inr (group,lane) => StructuredOpening.combine
      (RectangularMatrixResponse.weights (groupLeft ctx.parameters decoded.field.data.queries group.val) lane)
      (source dummy ctx decoded sourceLog)

def claim (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (decoded : View) (_state : State) : Test ctx decoded → Position ctx → Symbol ctx
  | .inl lane => BlockEncoder.encode (NativeGoldBatchResponseMeaning.Domain ctx primitive)
      (RowLayout.padded (m := ctx.parameters.code.messageBlocks.val) (b := ctx.parameters.code.blockWidth.val)
        (testMessages ctx.parameters decoded.column.opening lane.val))
  | .inr (group,lane) => BlockEncoder.encode (NativeGoldBatchResponseMeaning.Domain ctx primitive)
      (RowLayout.padded (m := ctx.parameters.code.messageBlocks.val) (b := ctx.parameters.code.blockWidth.val)
        (messages ctx.parameters decoded.column.opening group.val lane.val))

theorem coded (ctx : Context) [NeZero ctx.parameters.code.blockWidth.val]
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (decoded : View) (state : State) (test : Test ctx decoded) :
    claim ctx primitive decoded state test ∈ BlockCode.code (NativeGoldBatchResponseMeaning.Domain ctx primitive)
      ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val := by
  cases test with
  | inl lane => exact BlockEncoder.encode_mem_code _ _
  | inr pair => exact BlockEncoder.encode_mem_code _ _

theorem random_witness (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (decoded : View) (sourceLog : Log) (state : State) (distance : ℕ)
    (witness : ∃ lane : Fin ctx.parameters.width.val, distance ≤
      hammingDist (StructuredOpening.combine (NativeGoldBatchRecoveredMatrix.random ctx state lane) (source dummy ctx decoded sourceLog))
        (BlockEncoder.encode (NativeGoldBatchResponseMeaning.Domain ctx primitive)
          (RowLayout.padded (m := ctx.parameters.code.messageBlocks.val) (b := ctx.parameters.code.blockWidth.val)
            (testMessages ctx.parameters decoded.column.opening lane.val)))) :
    ∃ test : Test ctx decoded, distance ≤ hammingDist (raw dummy ctx decoded sourceLog state test) (claim ctx primitive decoded state test) := by
  obtain ⟨lane,bounded⟩ := witness
  exact ⟨.inl lane,bounded⟩

theorem structured_witness (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (decoded : View) (sourceLog : Log) (state : State) (distance : ℕ)
    (witness : ∃ group : ℕ, group < NativeGoldQueryGroups.groupCount ctx.parameters.leftVariables.val decoded.field.data.queries ∧
      ∃ lane : Fin ctx.parameters.width.val, distance ≤
      hammingDist (StructuredOpening.combine
        (RectangularMatrixResponse.weights (groupLeft ctx.parameters decoded.field.data.queries group) lane) (source dummy ctx decoded sourceLog))
        (BlockEncoder.encode (NativeGoldBatchResponseMeaning.Domain ctx primitive)
          (RowLayout.padded (m := ctx.parameters.code.messageBlocks.val) (b := ctx.parameters.code.blockWidth.val)
            (messages ctx.parameters decoded.column.opening group lane.val)))) :
    ∃ test : Test ctx decoded, distance ≤ hammingDist (raw dummy ctx decoded sourceLog state test) (claim ctx primitive decoded state test) := by
  obtain ⟨group,inside,lane,bounded⟩ := witness
  exact ⟨.inr (⟨group,inside⟩,lane),bounded⟩
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchConcreteColumnFamily
