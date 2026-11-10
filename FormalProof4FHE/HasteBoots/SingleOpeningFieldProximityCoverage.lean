module
public import FormalProof4FHE.HasteBoots.SingleOpeningFieldProximity
public import FormalProof4FHE.HasteBoots.SingleOpeningSelectedChecks
@[expose] public section

/-! A later native single-opening proximity obstruction belongs to the
original first field exposure, with the same selected source and actual
collector. Neither source-log replacement nor resampling is used. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningFieldProximityCoverage
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open NativeFields (Goldilocks goldilocksModulus)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open NativeIndexExposureRisk (Packet)
open InputIndexedOracle (Input World)
open TranscriptFrame (Frame)
open OracleProgram (run)
noncomputable section

theorem complete {ctx : Context} {world : World} {work : Prepared} {sample : NativeIndexRequest.Result}
    (receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample) : receipt.state.remaining = 0 := by
  have status := NativeFieldVector.request_status goldilocksModulus ctx.fieldFuel
    (NativePrimeRequest.prepare receipt.bound .vector) NativeGoldPcsPrelude.randomLabel work.geometry.randomCount.val world
  have finished := receipt.field
  change (run (NativeFieldVector.request goldilocksModulus ctx.fieldFuel
    (NativePrimeRequest.prepare receipt.bound .vector) NativeGoldPcsPrelude.randomLabel work.geometry.randomCount.val) world).run.1 =
      .finished receipt.state receipt.next at finished
  rw [finished] at status
  exact status

theorem later_proximity {S A : Type} {ctx : Context} {world : World} {work : Prepared} {sample : NativeIndexRequest.Result}
    (dummy : Digest) (receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample)
    (prepared : (run ctx.prefix world).run.1 = .prepared work)
    (before : List Frame) (parent : ctx.transcript.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (fits : (NativeGoldPcsWire.opening ctx.root ctx.query ctx.claimed).length < TranscriptFrame.lengthLimit)
    (responseFits : (SingleOpeningColumnLaw.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (decoded : SingleOpeningChallengeLink.View)
    (parsed : SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input receipt world) = some decoded)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot)
      (2^(NativeGoldBlockCode.logSize ctx.parameters.code+1)))
    (radius : ℕ) (step : S → OracleMachine.Command S A) (packet : Packet S A)
    (first : CausalStreamExposure.firstRead step packet = some (SingleOpeningFirstFieldSource.input decoded.field))
    (columnHistory : List Observation) (sourceLog : NativeRootFamilySourceSelection.Log)
    (found : SingleOpeningFirstFieldSource.recover dummy columnHistory decoded.field = some sourceLog)
    (offset : ℕ) (values : Input) (positive : values ≠ []) (middle : List Observation)
    (split : columnHistory = packet.2 ++ .output (SingleOpeningFirstFieldSource.input decoded.field) offset values :: middle)
    (proximity : SingleOpeningFieldProximity.matrixBad ctx primitive
      (SingleOpeningConcreteColumnFamily.source dummy ctx decoded sourceLog) radius
      (SingleOpeningRecoveredMatrix.random ctx receipt.state)) :
    SingleOpeningFieldProximity.event dummy ctx primitive radius ctx.transcript.profile step packet world := by
  have unseen : CausalStreamExposure.seen packet.2 (SingleOpeningFirstFieldSource.input decoded.field) = false := by
    unfold CausalStreamExposure.firstRead at first
    split at first <;> simp at first
    obtain ⟨eligible,rfl⟩ := first
    exact eligible.2
  have atFirst := SingleOpeningFirstFieldSource.recover_at dummy packet.2 middle decoded.field offset values unseen positive
  rw [← split] at atFirst
  have sourceLogEq := Option.some.inj (found.symm.trans atFirst)
  have sourceEq : SingleOpeningFieldProximity.word dummy ctx packet.2 decoded.field =
      SingleOpeningConcreteColumnFamily.source dummy ctx decoded sourceLog := by
    unfold SingleOpeningFieldProximity.word SingleOpeningConcreteColumnFamily.source
    rw [sourceLogEq]
  have origin := SingleOpeningPreparedChallenge.parsed_origin receipt prepared before parent valid fits responseFits decoded parsed
  have count : decoded.field.count.val = SingleOpeningFieldMatrix.count ctx := by
    rw [origin.1]
    exact SingleOpeningFieldMatrix.prepared_count ctx world work prepared
  have collected : (SingleOpeningFieldColumnLaw.collected ctx.transcript.profile ctx.fieldFuel decoded world).1 = receipt.state := origin.2.2.1
  have complete := complete receipt
  let vector : Fin decoded.field.count.val → Goldilocks := fun index => (receipt.state.values[index.val]?.getD 0 : ℕ)
  have sampled : NativeFieldVectorLaw.values goldilocksModulus ctx.fieldFuel decoded.field.count.val
      (decoded.field.phase ctx.transcript.profile) world = some vector := by
    change NativeFieldVectorValues.project goldilocksModulus decoded.field.count.val 0
      (SingleOpeningFieldColumnLaw.collected ctx.transcript.profile ctx.fieldFuel decoded world).1 = some vector
    rw [collected]
    simp only [NativeFieldVectorValues.project,complete,ite_true,Nat.zero_add]
    rfl
  have reshaped : SingleOpeningFieldMatrix.reshape ctx decoded.field.count.val count vector =
      SingleOpeningRecoveredMatrix.random ctx receipt.state := by
    have projected := SingleOpeningFieldMatrix.project_random ctx decoded.field.count.val count receipt.state complete
    simp only [NativeFieldVectorValues.project,complete,ite_true,Nat.zero_add,Option.map_some] at projected
    exact Option.some.inj projected
  have bad : SingleOpeningFieldProximity.bad dummy ctx primitive radius packet.2 decoded.field vector := by
    simp only [SingleOpeningFieldProximity.bad,count,dite_true]
    rw [reshaped,sourceEq]
    exact proximity
  have selected : SingleOpeningFieldExposure.select step packet = some decoded.field := by
    unfold SingleOpeningFieldExposure.select
    simp only [first,Option.bind_some]
    exact SingleOpeningFirstFieldSource.linked_field_parsed _ decoded parsed
  unfold SingleOpeningFieldProximity.event SingleOpeningFieldExposure.event
  rw [selected]
  refine ⟨ctx.fieldFuel,?_⟩
  rw [sampled]
  exact bad

end
end FormalProof4FHE.HasteBoots.SingleOpeningFieldProximityCoverage
