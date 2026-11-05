module

public import FormalProof4FHE.HasteBoots.NativeGoldPcsColumns
public import FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning
public import FormalProof4FHE.HasteBoots.NativeGoldBlockCodeContext

@[expose] public section

/-! Single-opening PCS execution through computed scalar response encoding.
The retained code supplies both transcript bytes and encoder dimensions.
Unavailable loading/encoding models the native trusted-cache/assert boundary,
not a verifier Err. This boundary is not PCS acceptance. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldPcsEncoding

open NativeGoldBlockCode (Stored Tables description encoding logSize)
open NativeBrakedownContext (Parameters)
open NativeBrakedownParameters (Geometry)
open NativeFieldRepresentation (GoldWord goldValue)
open NativeGoldPcsOpening (Opening)
open NativeGoldPcsWire (Query)
open NativeLookupRequestWire (Row)
open NativeRootMessage (Digest)
open NativeTranscript (Transcript)
open InputIndexedOracle (World)
open OracleProgram (Program bind run)

inductive Outcome where
  | prefix (result : NativeGoldPcsColumns.Outcome)
  | encodingUnavailable
  | encoded (geometry : Geometry) (state : NativeFieldVector.State)
      (weights : List GoldWord) (sample : NativeIndexRequest.Result)
      (planRoot : NativeGoldSolinas.Word) (test evaluation : List GoldWord)

def continueColumns (tables : Tables) (parameters : Parameters Stored) (opening : Opening) :
    NativeGoldPcsColumns.Outcome → Outcome
  | .columns geometry state weights sample =>
    match tables.load (logSize parameters.code) with
    | none => .encodingUnavailable
    | some root =>
      match NativeGoldRowEncoding.encodeResponses (encoding parameters.code root) parameters.width.val opening.test.val with
      | none => .encodingUnavailable
      | some test =>
        match NativeGoldRowEncoding.encodeResponses (encoding parameters.code root) parameters.width.val opening.evaluation.val with
        | none => .encodingUnavailable
        | some evaluation => .encoded geometry state weights sample root test evaluation
  | prior => .prefix prior

def protocol (tables : Tables) (parameters : Parameters Stored) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (opening : Opening) (fuel : ℕ) : Program Outcome :=
  bind (NativeGoldPcsColumns.protocol description parameters transcript root query values opening fuel)
    (fun prior => .pure (continueColumns tables parameters opening prior))

theorem run_protocol (tables : Tables) (parameters : Parameters Stored) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (opening : Opening) (fuel : ℕ) (world : World) :
    (run (protocol tables parameters transcript root query values opening fuel) world).run =
      let prior := (run (NativeGoldPcsColumns.protocol description parameters transcript root query values opening fuel) world).run
      (continueColumns tables parameters opening prior.1,prior.2) := by
  rw [protocol,OracleProgram.run_bind,ObservationReplay.run_bind]
  simp only [OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]

/-- Encoding adds no oracle observations and preserves the atomic boundary's
actual sampled indices and structured/random test state. -/
theorem observations (tables : Tables) (parameters : Parameters Stored) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (opening : Opening) (fuel : ℕ) (world : World) :
    (run (protocol tables parameters transcript root query values opening fuel) world).run.2 =
      (run (NativeGoldPcsColumns.protocol description parameters transcript root query values opening fuel) world).run.2 := by
  rw [run_protocol]

theorem encoded_origin (tables : Tables) (parameters : Parameters Stored) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (opening : Opening) (fuel : ℕ) (world : World)
    (geometry : Geometry) (state : NativeFieldVector.State) (weights : List GoldWord) (sample : NativeIndexRequest.Result)
    (planRoot : NativeGoldSolinas.Word) (test evaluation : List GoldWord)
    (success : (run (protocol tables parameters transcript root query values opening fuel) world).run.1 =
      .encoded geometry state weights sample planRoot test evaluation) :
    (run (NativeGoldPcsColumns.protocol description parameters transcript root query values opening fuel) world).run.1 =
      .columns geometry state weights sample ∧
    tables.load (logSize parameters.code) = some planRoot ∧
    NativeGoldRowEncoding.encodeResponses (encoding parameters.code planRoot) parameters.width.val opening.test.val = some test ∧
    NativeGoldRowEncoding.encodeResponses (encoding parameters.code planRoot) parameters.width.val opening.evaluation.val = some evaluation := by
  rw [run_protocol] at success
  cases prior : (run (NativeGoldPcsColumns.protocol description parameters transcript root query values opening fuel) world).run.1 <;>
    simp only [prior,continueColumns] at success
  all_goals try contradiction
  split at success
  next => contradiction
  next actualRoot loaded =>
    split at success
    next => contradiction
    next actualTest testRead =>
      split at success
      next => contradiction
      next actualEvaluation evaluationRead =>
        obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := Outcome.encoded.inj success
        exact ⟨rfl,loaded,testRead,evaluationRead⟩

noncomputable section

/-- With the constructor's own primitive backend root, a completed checked
column prefix always computes both responses. Cache loading and all response
shapes are derived from constructor/prefix success, not caller certificates. -/
theorem columns_complete (tables : Tables) (parameters : Parameters Stored) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (opening : Opening) (fuel : ℕ) (world : World)
    (geometry : Geometry) (state : NativeFieldVector.State) (weights : List GoldWord) (sample : NativeIndexRequest.Result)
    (success : (run (NativeGoldPcsColumns.protocol description parameters transcript root query values opening fuel) world).run.1 =
      .columns geometry state weights sample)
    (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok parameters.code)
    (primitive : IsPrimitiveRoot (goldValue parameters.code.domainRoot) (2^(logSize parameters.code+1))) :
    ∃ planRoot test evaluation,
      (run (protocol tables parameters transcript root query values opening fuel) world).run.1 =
        .encoded geometry state weights sample planRoot test evaluation := by
  obtain ⟨next,prior,_,_,_⟩ := NativeGoldPcsColumns.columns_origin description parameters transcript root query values opening fuel world geometry state weights sample success
  obtain ⟨parametersRead,shape,_,_,_⟩ := NativeGoldPcsPrelude.sampling_origin description parameters transcript root query values opening fuel world geometry (.finished state next) prior
  have checked := (NativeGoldPcsOpening.check_iff geometry parameters.queries opening).mp shape
  have sizes := NativeBrakedownParameters.computed_sizes description parameters geometry parametersRead
  have matching := (NativeBrakedownParameters.build_spec description parameters geometry parametersRead).code.1
  change parameters.code.messageLength.val = 2^(parameters.numVariables.val-parameters.leftVariables.val) at matching
  have responseWords : geometry.responseWords = parameters.width.val*parameters.code.messageLength.val := by
    rw [sizes.2.2.2.2.2.2.1]
    rw [sizes.1,matching]
  obtain ⟨planRoot,loaded,_⟩ := (NativeGoldBlockCode.build_spec tables message block blowup parameters.code constructed).loaded
  obtain ⟨test,testRead⟩ := NativeGoldBlockCodeMeaning.constructor_responses_complete tables message block blowup parameters.code constructed
    planRoot loaded primitive parameters.width.val opening.test.val (checked.test.trans responseWords)
  obtain ⟨evaluation,evaluationRead⟩ := NativeGoldBlockCodeMeaning.constructor_responses_complete tables message block blowup parameters.code constructed
    planRoot loaded primitive parameters.width.val opening.evaluation.val (checked.evaluation.trans responseWords)
  refine ⟨planRoot,test,evaluation,?_⟩
  rw [run_protocol]
  simp only [success,continueColumns,loaded,testRead,evaluationRead]

/-- Both actual response vectors are codewords of their original message
chunks, using the padded coefficient count of the constructed retained code.
No encoder output, degree bound or padding certificate is a protocol input. -/
theorem encoded_coded (tables : Tables) (parameters : Parameters Stored) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (opening : Opening) (fuel : ℕ) (world : World)
    (geometry : Geometry) (state : NativeFieldVector.State) (weights : List GoldWord) (sample : NativeIndexRequest.Result)
    (planRoot : NativeGoldSolinas.Word) (test evaluation : List GoldWord)
    (success : (run (protocol tables parameters transcript root query values opening fuel) world).run.1 =
      .encoded geometry state weights sample planRoot test evaluation)
    (constructorTables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build constructorTables message block blowup = .ok parameters.code)
    (primitive : IsPrimitiveRoot (goldValue parameters.code.domainRoot) (2^(logSize parameters.code+1))) :
    ∀ response ∈ [(opening.test.val,test),(opening.evaluation.val,evaluation)], ∀ lane < parameters.width.val,
      NativeGoldResponseMeaning.laneWord (encoding parameters.code planRoot) response.2 lane = BlockEncoder.encode
        (NTTButterfly.domain (logSize parameters.code) (goldValue parameters.code.domainRoot) primitive)
        (NativeGoldRowMeaning.coefficients (encoding parameters.code planRoot) parameters.code.messageBlocks.val
          ((response.1.drop (lane*parameters.code.messageLength.val)).take parameters.code.messageLength.val)) ∧
      NativeGoldResponseMeaning.laneWord (encoding parameters.code planRoot) response.2 lane ∈ BlockCode.code
        (NTTButterfly.domain (logSize parameters.code) (goldValue parameters.code.domainRoot) primitive)
        parameters.code.messageBlocks.val parameters.code.blockWidth.val := by
  have origin := encoded_origin tables parameters transcript root query values opening fuel world geometry state weights sample planRoot test evaluation success
  intro response member
  rcases List.mem_cons.mp member with rfl | member
  · exact NativeGoldBlockCodeMeaning.response_lanes constructorTables message block blowup parameters.code constructed planRoot _ _ _ origin.2.2.1 primitive
  · have same := List.mem_singleton.mp member
    subst response
    exact NativeGoldBlockCodeMeaning.response_lanes constructorTables message block blowup parameters.code constructed planRoot _ _ _ origin.2.2.2 primitive

end
end FormalProof4FHE.HasteBoots.NativeGoldPcsEncoding
