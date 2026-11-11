module
public import FormalProof4FHE.HasteBoots.SingleOpeningEarlyReceiptBound
public import FormalProof4FHE.HasteBoots.SingleOpeningFieldProximityCoverage
@[expose] public section

/-! Actual native single-opening preparation supplies a completed matching
receipt when columns are exposed before the field stream. Width/count and
true quote follow from native data, not an extra receipt certificate. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningEarlyReceiptNative
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open InputIndexedOracle (World)
open NativeIndexExposureRisk (Packet)
open NativeRootMessage (Digest)
open TranscriptFrame (Frame)
open OracleProgram (run)
noncomputable section

theorem count (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work)
    (width : 3 ≤ ctx.parameters.width.val) : 9 ≤ work.geometry.randomCount.val := by
  rw [SingleOpeningFieldMatrix.prepared_count ctx world work prepared]
  change 9 ≤ 2^ctx.parameters.leftVariables.val*ctx.parameters.width.val*ctx.parameters.width.val
  have lower : 1 ≤ 2^ctx.parameters.leftVariables.val := Nat.one_le_pow _ _ (by decide)
  have product := Nat.mul_le_mul (Nat.mul_le_mul lower width) width
  norm_num at product
  exact product

theorem first_column_cases {S A : Type} {ctx : Context} {world : World} {work : Prepared} {sample : NativeIndexRequest.Result}
    (receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample)
    (prepared : (run ctx.prefix world).run.1 = .prepared work)
    (before : List Frame) (parent : ctx.transcript.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (fits : (NativeGoldPcsWire.opening ctx.root ctx.query ctx.claimed).length < TranscriptFrame.lengthLimit)
    (responseFits : (SingleOpeningColumnLaw.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (width : 3 ≤ ctx.parameters.width.val) (step : S → OracleMachine.Command S A) (packet : Packet S A)
    (first : CausalStreamExposure.firstRead step packet = some (SingleOpeningColumnLaw.input receipt world)) :
    CausalStreamExposure.seen packet.2 (SingleOpeningRandomLaw.phase receipt).pending.input = true ∨
      SingleOpeningEarlyReceiptBound.event ctx.transcript.profile step packet world := by
  cases seen : CausalStreamExposure.seen packet.2 (SingleOpeningRandomLaw.phase receipt).pending.input with
  | true => exact Or.inl rfl
  | false =>
    right
    obtain ⟨context,_,parsed,phase,collected⟩ := SingleOpeningPreparedChallenge.prepared_link receipt prepared before parent valid fits responseFits
    let decoded := SingleOpeningPreparedChallenge.recovered receipt before context
    have geometry := NativeBrakedownParameters.build_spec NativeGoldBlockCode.description ctx.parameters work.geometry
      (SingleOpeningRectangularData.geometry ctx world work prepared)
    have positive : 0 < ctx.parameters.queries.val := Nat.pos_of_ne_zero geometry.basic.2.2.2
    have fieldInput : SingleOpeningEarlyReceiptPrefixRisk.fieldInput decoded = (SingleOpeningRandomLaw.phase receipt).pending.input := by
      change TranscriptFrame.encodeMany decoded.field.frames = _
      rw [← phase]
      exact (SingleOpeningFieldInputView.phase_input decoded.field ctx.transcript.profile).symm
    have selected : SingleOpeningEarlyReceiptPrefixRisk.select step packet = some decoded := by
      unfold SingleOpeningEarlyReceiptPrefixRisk.select
      simp only [first,Option.bind_eq_bind,Option.bind_some,parsed]
      have eligible : decoded.column.index.label = NativeGoldPcsColumns.label ∧ 0 < decoded.column.index.count.val ∧
          CausalStreamExposure.seen packet.2 (SingleOpeningEarlyReceiptPrefixRisk.fieldInput decoded) = false :=
        ⟨rfl,positive,by rw [fieldInput]; exact seen⟩
      exact ite_eq_left eligible
    have same : (SingleOpeningFreshReceiptDigest.collected ctx.transcript.profile ctx.fieldFuel decoded world).1 = receipt.state := collected
    refine ⟨ctx.fieldFuel,?_⟩
    unfold SingleOpeningEarlyReceiptBound.finiteEvent
    rw [SingleOpeningFreshReceiptDigest.run_some ctx.transcript.profile ctx.fieldFuel step packet world decoded selected]
    change 9 ≤ decoded.field.count.val ∧ (SingleOpeningFreshReceiptDigest.collected ctx.transcript.profile ctx.fieldFuel decoded world).1.remaining = 0 ∧
      (NativeTranscript.receipt world (SingleOpeningFreshReceiptDigest.collected ctx.transcript.profile ctx.fieldFuel decoded world).1.phase.consumed).run.1 = decoded.receipt
    rw [same]
    exact ⟨count ctx world work prepared width,SingleOpeningFieldProximityCoverage.complete receipt,rfl⟩

/-- Any parse of the actual column nonce either exposes a matching early
receipt event or recovers its original field's first-read source log. -/
theorem first_column_sources {S A : Type} {ctx : Context} {world : World} {work : Prepared} {sample : NativeIndexRequest.Result}
    (dummy : Digest) (receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample)
    (prepared : (run ctx.prefix world).run.1 = .prepared work)
    (before : List Frame) (parent : ctx.transcript.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (fits : (NativeGoldPcsWire.opening ctx.root ctx.query ctx.claimed).length < TranscriptFrame.lengthLimit)
    (responseFits : (SingleOpeningColumnLaw.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (width : 3 ≤ ctx.parameters.width.val) (step : S → OracleMachine.Command S A) (packet : Packet S A)
    (first : CausalStreamExposure.firstRead step packet = some (SingleOpeningColumnLaw.input receipt world))
    (decoded : SingleOpeningChallengeLink.View)
    (parsed : SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input receipt world) = some decoded) :
    SingleOpeningEarlyReceiptBound.event ctx.transcript.profile step packet world ∨
      ∃ sourceLog, SingleOpeningFirstFieldSource.recover dummy packet.2 decoded.field = some sourceLog := by
  rcases first_column_cases receipt prepared before parent valid fits responseFits width step packet first with seen | early
  · right
    have phase := (SingleOpeningPreparedChallenge.parsed_origin receipt prepared before parent valid fits responseFits decoded parsed).2.1
    have inputEq : SingleOpeningFirstFieldSource.input decoded.field = (SingleOpeningRandomLaw.phase receipt).pending.input := by
      rw [← phase]
      exact (SingleOpeningFieldInputView.phase_input decoded.field ctx.transcript.profile).symm
    rw [← inputEq] at seen
    exact SingleOpeningFirstFieldSource.recover_exists dummy packet.2 decoded.field seen
  · exact Or.inl early

end
end FormalProof4FHE.HasteBoots.SingleOpeningEarlyReceiptNative
