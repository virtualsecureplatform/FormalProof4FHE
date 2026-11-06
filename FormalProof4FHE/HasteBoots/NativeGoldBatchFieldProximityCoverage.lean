module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchFieldProximity
public import FormalProof4FHE.HasteBoots.NativeGoldBatchConcreteExposureCoverage
@[expose] public section

/-! The later concrete proximity obstruction belongs to the earlier first
field exposure, on its actual native sampler. The recorded first-read split
fixes the same source log; no future source is substituted at that boundary. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchFieldProximityCoverage
open NativeGoldBatchPcsProgram (Context Prepared)
open NativeGoldBatchChallengeLink (View)
open NativeFields (Goldilocks goldilocksModulus)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open NativeIndexExposureRisk (Packet)
open InputIndexedOracle (World Input)
open TranscriptFrame (Frame)
open OracleProgram (run)
noncomputable section

theorem later_proximity {S A : Type} (dummy : Digest) (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (before : List Frame) (parent : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (fits : 128 + (NativeGoldBatchBinding.queriesCodec.encode ctx.queries).length +
      (NativeGoldBatchBinding.valuesCodec.encode ctx.values).length < TranscriptFrame.lengthLimit)
    (responseFits : (NativeGoldBatchResponseBinding.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (decoded : View)
    (parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world) = some decoded)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot)
      (2^(NativeGoldBlockCode.logSize ctx.parameters.code+1)))
    (radius : ℕ) (step : S → OracleMachine.Command S A) (packet : Packet S A)
    (first : CausalStreamExposure.firstRead step packet = some (NativeGoldBatchFirstFieldSource.input decoded.field))
    (columnHistory : List Observation) (sourceLog : NativeRootFamilySourceSelection.Log)
    (found : NativeGoldBatchFirstFieldSource.recover dummy columnHistory decoded.field = some sourceLog)
    (offset : ℕ) (values : Input) (positive : values ≠ []) (middle : List Observation)
    (split : columnHistory = packet.2 ++ .output (NativeGoldBatchFirstFieldSource.input decoded.field) offset values :: middle)
    (proximity : NativeGoldBatchConcreteCoverage.Proximity dummy ctx primitive decoded sourceLog work.state radius) :
    NativeGoldBatchFieldProximity.event dummy ctx primitive radius ctx.parent.profile step packet world := by
  have unseen : CausalStreamExposure.seen packet.2 (NativeGoldBatchFirstFieldSource.input decoded.field) = false := by
    unfold CausalStreamExposure.firstRead at first
    split at first <;> simp at first
    obtain ⟨eligible,rfl⟩ := first
    exact eligible.2
  have atFirst := NativeGoldBatchFirstFieldSource.recover_at dummy packet.2 middle decoded.field offset values unseen positive
  rw [← split] at atFirst
  have sourceLogEq := Option.some.inj (found.symm.trans atFirst)
  have sourceEq : NativeGoldBatchFieldProximity.word dummy ctx packet.2 decoded.field =
      NativeGoldBatchConcreteColumnFamily.source dummy ctx decoded sourceLog := by
    unfold NativeGoldBatchFieldProximity.word NativeGoldBatchConcreteColumnFamily.source
    rw [sourceLogEq]
  have origin := NativeGoldBatchPreparedChallenge.parsed_origin ctx world work prepared before parent valid fits responseFits decoded parsed
  have geometry := NativeBrakedownParameters.build_spec NativeGoldBlockCode.description ctx.parameters work.geometry
    (NativeGoldBatchResponseMeaning.prepared_geometry ctx world work prepared)
  have count : decoded.field.count.val = NativeGoldBatchFieldMatrix.count ctx := by
    rw [origin.1,geometry.computed]
    rfl
  have complete := NativeGoldBatchRecoveredCollector.prepared_complete ctx world work prepared
  let vector : Fin decoded.field.count.val → Goldilocks := fun index => (work.state.values[index.val]?.getD 0 : ℕ)
  have sampled : NativeFieldVectorLaw.values goldilocksModulus ctx.fieldFuel decoded.field.count.val
      (decoded.field.phase ctx.parent.profile) world = some vector := by
    change NativeFieldVectorValues.project goldilocksModulus decoded.field.count.val 0
      (NativeGoldBatchFieldColumnLaw.collected ctx.parent.profile ctx.fieldFuel decoded world).1 = some vector
    rw [origin.2.2.1]
    simp only [NativeFieldVectorValues.project,complete,ite_true,Nat.zero_add]
    rfl
  have reshaped : NativeGoldBatchFieldMatrix.reshape ctx decoded.field.count.val count vector =
      NativeGoldBatchRecoveredMatrix.random ctx work.state := by
    have projected := NativeGoldBatchFieldMatrix.project_random ctx decoded.field.count.val count work.state complete
    simp only [NativeFieldVectorValues.project,complete,ite_true,Nat.zero_add,Option.map_some] at projected
    exact Option.some.inj projected
  have bad : NativeGoldBatchFieldProximity.bad dummy ctx primitive radius packet.2 decoded.field vector := by
    simp only [NativeGoldBatchFieldProximity.bad,count,dite_true]
    rw [reshaped]
    rw [sourceEq]
    exact proximity
  have selected : NativeGoldBatchFieldExposure.select step packet = some decoded.field := by
    unfold NativeGoldBatchFieldExposure.select
    simp only [first,Option.bind_some]
    exact NativeGoldBatchFirstFieldSource.linked_field_parsed _ decoded parsed
  unfold NativeGoldBatchFieldProximity.event NativeGoldBatchFieldExposure.event
  rw [selected]
  refine ⟨ctx.fieldFuel,?_⟩
  rw [sampled]
  exact bad
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchFieldProximityCoverage
