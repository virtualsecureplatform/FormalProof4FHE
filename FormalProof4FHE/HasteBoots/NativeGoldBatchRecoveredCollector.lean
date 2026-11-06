module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchPreparedChallenge
public import FormalProof4FHE.HasteBoots.NativeEarlyReceiptBound
@[expose] public section

/-! Actual native preparation supplies the completed collector and true
quoted receipt needed by the early-receipt reduction. It also identifies
native Goldilocks words with the recovered coefficient state. No caller
completion, receipt-match or field-freshness certificate is required by the
first-column case split. Application/source soundness remains separate. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchRecoveredCollector
open InputIndexedOracle (Input World)
open NativeGoldBatchPcsProgram (Context Prepared)
open NativeIndexExposureRisk (Packet)
open TranscriptFrame (Frame)
open OracleProgram (run)
noncomputable section

theorem prepared_complete (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) :
    work.state.remaining = 0 := by
  obtain ⟨next,finished⟩ := NativeGoldBatchRandomLaw.prepared_request ctx world work prepared
  have status := NativeFieldVector.request_status NativeFields.goldilocksModulus ctx.fieldFuel
    (NativePrimeRequest.prepare work.binding.parent .vector) NativeGoldBatchPrelude.randomLabel work.geometry.randomCount.val world
  change (run (NativeFieldVector.request NativeFields.goldilocksModulus ctx.fieldFuel
    (NativePrimeRequest.prepare work.binding.parent .vector) NativeGoldBatchPrelude.randomLabel work.geometry.randomCount.val) world).run.1 = .finished work.state next at finished
  rw [finished] at status
  exact status

theorem prepared_count (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (width : 3 ≤ ctx.parameters.width.val) : 9 ≤ work.geometry.randomCount.val := by
  have geometry := NativeBrakedownParameters.build_spec NativeGoldBlockCode.description ctx.parameters work.geometry
    (NativeGoldBatchResponseMeaning.prepared_geometry ctx world work prepared)
  rw [geometry.computed]
  change 9 ≤ 2^ctx.parameters.leftVariables.val * ctx.parameters.width.val * ctx.parameters.width.val
  have lower : 1 ≤ 2^ctx.parameters.leftVariables.val := Nat.one_le_pow _ _ (by decide)
  have product := Nat.mul_le_mul (Nat.mul_le_mul lower width) width
  norm_num at product
  exact product

/-- This split is about the actual complete native column input at its first
positive read. If the actual field stream was unseen, native preparation
itself supplies the completed matching receipt event at its original budget. -/
theorem first_column_cases {S A : Type} (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (before : List Frame) (parent : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (fits : 128 + (NativeGoldBatchBinding.queriesCodec.encode ctx.queries).length +
      (NativeGoldBatchBinding.valuesCodec.encode ctx.values).length < TranscriptFrame.lengthLimit)
    (responseFits : (NativeGoldBatchResponseBinding.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (width : 3 ≤ ctx.parameters.width.val) (step : S → OracleMachine.Command S A) (packet : Packet S A)
    (first : CausalStreamExposure.firstRead step packet = some (NativeGoldBatchColumnRequestLaw.input ctx work world)) :
    CausalStreamExposure.seen packet.2 (NativeGoldBatchRandomLaw.phase work).pending.input = true ∨
      NativeEarlyReceiptBound.event ctx.parent.profile step packet world := by
  cases seen : CausalStreamExposure.seen packet.2 (NativeGoldBatchRandomLaw.phase work).pending.input with
  | true => exact Or.inl rfl
  | false =>
    right
    obtain ⟨context,_,parsed,phase,collected⟩ := NativeGoldBatchPreparedChallenge.prepared_link ctx world work prepared before parent valid fits responseFits
    let decoded := NativeGoldBatchPreparedChallenge.recovered ctx world work before context
    have geometry := NativeBrakedownParameters.build_spec NativeGoldBlockCode.description ctx.parameters work.geometry
      (NativeGoldBatchResponseMeaning.prepared_geometry ctx world work prepared)
    have positive : 0 < ctx.parameters.queries.val := Nat.pos_of_ne_zero geometry.basic.2.2.2
    have fieldInput : NativeEarlyReceiptPrefixRisk.fieldInput decoded = (NativeGoldBatchRandomLaw.phase work).pending.input := by
      rw [← phase]
      exact (NativeGoldBatchFieldInputView.phase_input decoded.field ctx.parent.profile).symm
    have selected : NativeEarlyReceiptPrefixRisk.select step packet = some decoded := by
      unfold NativeEarlyReceiptPrefixRisk.select
      simp only [first,Option.bind_eq_bind,Option.bind_some,parsed]
      have eligible : decoded.column.index.label = NativeGoldBatchColumns.label ∧ 0 < decoded.column.index.count.val ∧
          CausalStreamExposure.seen packet.2 (NativeEarlyReceiptPrefixRisk.fieldInput decoded) = false := by
        exact ⟨rfl,positive,by rw [fieldInput]; exact seen⟩
      exact ite_eq_left eligible
    refine ⟨ctx.fieldFuel,?_⟩
    unfold NativeEarlyReceiptBound.finiteEvent
    rw [NativeFreshReceiptDigest.run_some ctx.parent.profile ctx.fieldFuel step packet world decoded selected]
    change 9 ≤ decoded.field.count.val ∧ (NativeGoldBatchFieldColumnLaw.collected ctx.parent.profile ctx.fieldFuel decoded world).1.remaining = 0 ∧
      (NativeTranscript.receipt world (NativeGoldBatchFieldColumnLaw.collected ctx.parent.profile ctx.fieldFuel decoded world).1.phase.consumed).run.1 = decoded.receipt
    rw [collected]
    exact ⟨prepared_count ctx world work prepared width,prepared_complete ctx world work prepared,rfl⟩

/-- For any decoded actual input, the native random word is computed from
that same recovered state. This is a deterministic identity, not a claim of
independence from a future source or an efficient public extractor. -/
theorem parsed_word (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (before : List Frame) (parent : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (fits : 128 + (NativeGoldBatchBinding.queriesCodec.encode ctx.queries).length +
      (NativeGoldBatchBinding.valuesCodec.encode ctx.values).length < TranscriptFrame.lengthLimit)
    (responseFits : (NativeGoldBatchResponseBinding.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (decoded : NativeGoldBatchChallengeLink.View)
    (parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world) = some decoded)
    (index : Fin work.geometry.randomCount.val) :
    NativeGoldColumnChecks.view work.random index.val =
      (((NativeGoldBatchFieldColumnLaw.collected ctx.parent.profile ctx.fieldFuel decoded world).1.values[index.val]?).getD 0 : NativeFields.Goldilocks) := by
  have origin := NativeGoldBatchPreparedChallenge.parsed_origin ctx world work prepared before parent valid fits responseFits decoded parsed
  rw [origin.2.2.1]
  exact NativeGoldBatchRandomLaw.prepared_word ctx world work prepared index
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchRecoveredCollector
