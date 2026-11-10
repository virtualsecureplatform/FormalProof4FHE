module
public import FormalProof4FHE.HasteBoots.PrivateCoinByteAllRisk
@[expose] public section

/-! Replacing only the analysis metadata profile preserves parsed field-reader
execution. The absorbed transcript bytes (including the actual profile frames)
are unchanged. This does not identify transcripts with different byte inputs. -/
namespace FormalProof4FHE.HasteBoots.ProfileMetadataErasure
open InputIndexedOracle (World)
open NativeRootMessage (Digest)
open NativeTranscript (Transcript FieldPhase)
open CanonicalTranscriptSampler (Outcome)
open NativeFieldVector (State)

def transcript (before : Transcript) (profile : Digest) : Transcript := { before with profile := profile }
def phase (before : FieldPhase) (profile : Digest) : FieldPhase := { before with pending := transcript before.pending profile }
def outcome (before : Outcome) (profile : Digest) : Outcome := { before with phase := phase before.phase profile }
def state (before : State) (profile : Digest) : State := { before with phase := phase before.phase profile }

theorem draw (world : World) (before : FieldPhase) (profile : Digest) (count : ℕ) :
    (NativeTranscript.drawField world (phase before profile) count).run =
      (((NativeTranscript.drawField world before count).run.1.1,
        phase (NativeTranscript.drawField world before count).run.1.2 profile),
        (NativeTranscript.drawField world before count).run.2) := rfl

theorem sample (p fuel : ℕ) (before : FieldPhase) (profile : Digest) (world : World) :
    CanonicalTranscriptSampler.executePrefix p fuel (phase before profile) world =
      (outcome (CanonicalTranscriptSampler.executePrefix p fuel before world).1 profile,
        (CanonicalTranscriptSampler.executePrefix p fuel before world).2) := by
  induction fuel generalizing before with
  | zero => rfl
  | succ fuel ih =>
    simp only [CanonicalTranscriptSampler.executePrefix, draw]
    by_cases accepted : CanonicalTranscriptSampler.candidate p
        (NativeTranscript.drawField world before (CanonicalByteSampler.byteCount p)).run.1.1 < p
    · simp only [accepted, ite_true]; rfl
    · simp only [accepted, ite_false]
      rw [ih]
      rfl

theorem advance (p : ℕ) (before : State) (trial : Outcome) (profile : Digest) :
    NativeFieldVector.advance p (state before profile) (outcome trial profile) =
      state (NativeFieldVector.advance p before trial) profile := by
  cases accepted : trial.accepted <;> simp only [NativeFieldVector.advance, outcome, state, accepted]

theorem execute (p fuel : ℕ) (before : State) (profile : Digest) (world : World) :
    NativeFieldVector.execute p fuel (state before profile) world =
      (state (NativeFieldVector.execute p fuel before world).1 profile,
        (NativeFieldVector.execute p fuel before world).2) := by
  induction fuel generalizing before with
  | zero => rfl
  | succ fuel ih =>
    simp only [NativeFieldVector.execute, show (state before profile).remaining = before.remaining from rfl,
      show (state before profile).phase = phase before.phase profile from rfl]
    by_cases complete : before.remaining = 0
    · simp only [complete, ite_true]
    · simp only [complete, ite_false]
      rw [sample, advance, ih]

theorem field_phase (view : NativeGoldBatchFieldInputView.View) (first second : Digest) :
    view.phase second = phase (view.phase first) second := rfl

theorem values (p fuel count : ℕ) (before : FieldPhase) (profile : Digest) (world : World) :
    NativeFieldVectorLaw.values p fuel count (phase before profile) world =
      NativeFieldVectorLaw.values p fuel count before world := by
  unfold NativeFieldVectorLaw.values
  change NativeFieldVectorValues.project p count 0
    (NativeFieldVector.execute p fuel (state (NativeFieldVector.initial before count) profile) world).1 = _
  rw [execute]
  rfl

theorem collected (first second : Digest) (fuel : ℕ) (view : NativeGoldBatchChallengeLink.View) (world : World) :
    NativeFreshReceiptDigest.collected second fuel view world =
      (state (NativeFreshReceiptDigest.collected first fuel view world).1 second,
        (NativeFreshReceiptDigest.collected first fuel view world).2) := by
  unfold NativeFreshReceiptDigest.collected
  rw [field_phase view.field first second]
  exact execute NativeFields.goldilocksModulus fuel
    (NativeFieldVector.initial (view.field.phase first) view.field.count.val) second world

theorem field_event {S A : Type} (dummy : Digest) (ctx : NativeGoldBatchPcsProgram.Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot)
      (2^(NativeGoldBlockCode.logSize ctx.parameters.code+1)))
    (radius : ℕ) (first second : Digest) (step : S → OracleMachine.Command S A)
    (packet : NativeIndexExposureRisk.Packet S A) (world : World) :
    NativeGoldBatchFieldProximity.event dummy ctx primitive radius first step packet world ↔
      NativeGoldBatchFieldProximity.event dummy ctx primitive radius second step packet world := by
  unfold NativeGoldBatchFieldProximity.event NativeGoldBatchFieldExposure.event
  cases selected : NativeGoldBatchFieldExposure.select step packet with
  | none => rfl
  | some view =>
    simp only [field_phase view first second, values]

theorem receipt_event {S A : Type} (first second : Digest) (step : S → OracleMachine.Command S A)
    (packet : NativeIndexExposureRisk.Packet S A) (world : World) :
    NativeEarlyReceiptBound.event first step packet world ↔ NativeEarlyReceiptBound.event second step packet world := by
  unfold NativeEarlyReceiptBound.event NativeEarlyReceiptBound.finiteEvent
  apply exists_congr
  intro fuel
  cases selected : NativeEarlyReceiptPrefixRisk.select step packet with
  | none => simp only [NativeFreshReceiptDigest.run_none _ _ _ _ _ selected, NativeEarlyReceiptBound.matching]
  | some view =>
    simp only [NativeFreshReceiptDigest.run_some _ _ _ _ _ _ selected, collected first second]
    rfl


theorem index_values (bits : ℕ) (before : Transcript) (profile : Digest) (label : InputIndexedOracle.Input)
    (domain count : NativeUsizeMessage.Usize) (world : World) :
    NativeIndexFirstReadLaw.values bits (transcript before profile) label domain count world =
      NativeIndexFirstReadLaw.values bits before label domain count world := by
  unfold NativeIndexFirstReadLaw.values
  by_cases valid : NativeIndexRequest.check domain count = true
  · rw [NativeIndexRequest.run_request _ _ _ _ _ valid, NativeIndexRequest.run_request _ _ _ _ _ valid]
    rfl
  · rw [NativeIndexRequest.invalid_request _ _ _ _ _ valid, NativeIndexRequest.invalid_request _ _ _ _ _ valid]

theorem column_collected (first second : Digest) (fuel : ℕ) (view : NativeGoldBatchChallengeLink.View) (world : World) :
    NativeGoldBatchFieldColumnLaw.collected second fuel view world =
      (state (NativeGoldBatchFieldColumnLaw.collected first fuel view world).1 second,
        (NativeGoldBatchFieldColumnLaw.collected first fuel view world).2) := collected first second fuel view world

theorem column_event (dummy : Digest) (ctx : NativeGoldBatchPcsProgram.Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot)
      (2^(NativeGoldBlockCode.logSize ctx.parameters.code+1)))
    (first second : Digest) (decoded : NativeGoldBatchChallengeLink.View)
    (history : List NativeTranscript.Observation) (radius : ℕ) (world : World) :
    NativeGoldBatchConcreteColumnBound.event dummy ctx primitive first decoded history radius world ↔
      NativeGoldBatchConcreteColumnBound.event dummy ctx primitive second decoded history radius world := by
  unfold NativeGoldBatchConcreteColumnBound.event
  cases found : NativeGoldBatchFirstFieldSource.recover dummy history decoded.field with
  | none => rfl
  | some sourceLog =>
    apply exists_congr
    intro fuel
    unfold NativeGoldBatchFieldColumnLaw.event
    have request : (decoded.column.index.request second).transcript =
        transcript (decoded.column.index.request first).transcript second := rfl
    rw [request, index_values, column_collected first second]
    rfl

theorem profile_column_event {S A : Type} (dummy : Digest) (ctx : NativeGoldBatchPcsProgram.Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot)
      (2^(NativeGoldBlockCode.logSize ctx.parameters.code+1)))
    (first second : Digest) (step : S → OracleMachine.Command S A)
    (packet : NativeIndexExposureRisk.Packet S A) (radius : ℕ) (world : World) :
    NativeGoldBatchProfileColumnExposure.event dummy ctx primitive first step packet radius world ↔
      NativeGoldBatchProfileColumnExposure.event dummy ctx primitive second step packet radius world := by
  unfold NativeGoldBatchProfileColumnExposure.event
  cases selected : NativeGoldBatchProfileColumnExposure.select ctx step packet with
  | none => rfl
  | some decoded => exact column_event dummy ctx primitive first second decoded packet.2 radius world

end ProfileMetadataErasure
end FormalProof4FHE.HasteBoots
