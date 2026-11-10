module
public import FormalProof4FHE.HasteBoots.SingleOpeningConcreteColumnFamily
@[expose] public section

/-! Actual accepted native checks are exactly the concrete parsed family.
The source log here is the acceptance view's retained log. Recovering that
specific log from the original causal prefix is a separate coverage step. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningConcreteColumnChecks
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open NativeRootMessage (Digest)
open InputIndexedOracle (World)
open TranscriptFrame (Frame)
open SingleOpeningConcreteColumnFamily (Test raw claim source)
noncomputable section

theorem accepted_checks {dummy : Digest} {ctx : Context} {world : World} {work : Prepared}
    {history : List NativeTranscript.Observation} {origin : CacheBackedSingleOpening.Origin ctx}
    (accepted : SingleOpeningRectangularAcceptance.View dummy ctx world work history origin)
    (receipt : SingleOpeningSamplingReceipt.Receipt ctx world work accepted.sample)
    (before : List Frame) (parent : ctx.transcript.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (fits : (NativeGoldPcsWire.opening ctx.root ctx.query ctx.claimed).length < TranscriptFrame.lengthLimit)
    (responseFits : (SingleOpeningColumnLaw.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (decoded : SingleOpeningChallengeLink.View)
    (parsed : SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input receipt world) = some decoded) :
    ∀ test : Test ctx, ColumnOpening.Agrees
      (raw dummy ctx decoded accepted.log
        (SingleOpeningFieldColumnLaw.collected ctx.transcript.profile ctx.fieldFuel decoded world).1 test)
      (claim ctx origin.primitive decoded
        (SingleOpeningFieldColumnLaw.collected ctx.transcript.profile ctx.fieldFuel decoded world).1 test) accepted.draw := by
  obtain ⟨_,_,_,_,testRow,evaluation,root,query,_,_,_,_,hashed⟩ :=
    SingleOpeningPreparedChallenge.parsed_origin receipt accepted.prepared before parent valid fits responseFits decoded parsed
  have contextEq : decoded.field.data.context = accepted.context := Option.some.inj (hashed.symm.trans accepted.hashed)
  have sourceEq : source dummy ctx decoded accepted.log =
      SingleOpeningRectangularChecks.source ctx world work accepted.prepared
        (SingleOpeningRectangularChecks.Frozen dummy accepted.context work accepted.log) := by
    unfold source
    rw [contextEq,root]
    exact (SingleOpeningSelectedWord.prepared_word dummy accepted.context ctx world work accepted.prepared origin accepted.log).symm
  have randomEq := SingleOpeningRecoveredMatrix.parsed_random receipt accepted.prepared before parent valid fits responseFits decoded parsed
  have leftEq : SingleOpeningFixedResponseData.left ctx.parameters decoded.field.data.query =
      SingleOpeningRectangularData.left ctx world work accepted.prepared := by
    rw [query]
    exact SingleOpeningFixedResponseData.left_native ctx world work accepted.prepared
  have testEq : SingleOpeningFixedResponseData.testMessages ctx decoded.column.opening =
      SingleOpeningRectangularData.messages ctx ctx.opening.test.val := by
    simp only [SingleOpeningFixedResponseData.testMessages,testRow]
  have evaluationEq : SingleOpeningFixedResponseData.messages ctx decoded.column.opening =
      SingleOpeningRectangularData.messages ctx ctx.opening.evaluation.val := by
    simp only [SingleOpeningFixedResponseData.messages,evaluation]
  intro test
  cases test with
  | inl lane =>
    change ColumnOpening.Agrees (StructuredOpening.combine
      (SingleOpeningRecoveredMatrix.random ctx
        (SingleOpeningFieldColumnLaw.collected ctx.transcript.profile ctx.fieldFuel decoded world).1 lane)
      (source dummy ctx decoded accepted.log)) _ accepted.draw
    rw [← randomEq,sourceEq]
    change ColumnOpening.Agrees _ (BlockEncoder.encode _ (RowLayout.padded
      (SingleOpeningFixedResponseData.testMessages ctx decoded.column.opening lane))) _
    rw [testEq]
    exact accepted.randomChecks lane
  | inr lane =>
    change ColumnOpening.Agrees (StructuredOpening.combine
      (RectangularMatrixResponse.weights (SingleOpeningFixedResponseData.left ctx.parameters decoded.field.data.query) lane)
      (source dummy ctx decoded accepted.log)) _ accepted.draw
    rw [leftEq,sourceEq]
    change ColumnOpening.Agrees _ (BlockEncoder.encode _ (RowLayout.padded
      (SingleOpeningFixedResponseData.messages ctx decoded.column.opening lane))) _
    rw [evaluationEq]
    exact accepted.structuredChecks lane

end
end FormalProof4FHE.HasteBoots.SingleOpeningConcreteColumnChecks
