module
public import FormalProof4FHE.HasteBoots.RegistryPublicSource
public import FormalProof4FHE.HasteBoots.BatchClaimShape
@[expose] public section

/-! A wrong original row on the allocated public cube yields the native batch
obligation. Query interpretation is transported using the entire retained
parameter record; row words keep their native field interpretation. -/
namespace FormalProof4FHE.HasteBoots.RegistryPublicSourceObligation
open NativeBrakedownContext (Parameters)
open NativeGoldBlockCode (Stored)
open NativeFields (Goldilocks)
open NativeGoldBatchPcsProgram (Context Prepared)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

def query {first second : Parameters Stored} (same : first = second)
    (value : ExtensionQuery.Broadcast Goldilocks first.width.val first.numVariables.val) :
    ExtensionQuery.Broadcast Goldilocks second.width.val second.numVariables.val := same ▸ value

theorem query_heq {first second : Parameters Stored} (same : first = second)
    (value : ExtensionQuery.Broadcast Goldilocks first.width.val first.numVariables.val) : HEq value (query same value) := by
  cases same
  rfl

def rowValue (parameters : Parameters Stored) (row : NativeLookupRequestWire.Row) :=
  fun lane : Fin parameters.width.val => NativeFieldRepresentation.goldValue (row.val[lane.val]?.getD 0)

theorem rowValue_heq {first second : Parameters Stored} (same : first = second) (row : NativeLookupRequestWire.Row) :
    HEq (rowValue first row) (rowValue second row) := by
  cases same
  rfl

theorem read_transport {first second : Parameters Stored} (same : first = second)
    (raw : NativeGoldCoefficientsQuery.Query)
    (value : ExtensionQuery.Broadcast Goldilocks first.width.val first.numVariables.val)
    (read : NativeGoldCoefficientsQuery.interpret first.width.val first.numVariables.val raw = some value) :
    NativeGoldCoefficientsQuery.interpret second.width.val second.numVariables.val raw = some (query same value) := by
  cases same
  exact read

/-- The transported query is the interpretation of the original raw lookup
query at this exact original batch index, including non-owner group members. -/
theorem query_read (candidate reference : Context) (parameters : candidate.parameters = reference.parameters)
    (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram candidate) world).run.1 = .prepared work)
    (index : NativeGoldBatchRectangularData.Query work) (raw : NativeGoldPcsWire.Query)
    (found : work.binding.queries.val[index.val]? = some raw) :
    NativeGoldCoefficientsQuery.interpret reference.parameters.width.val reference.parameters.numVariables.val ⟨raw.models,none⟩ =
      some (query parameters (BatchOpeningNativeObligation.query candidate world work prepared index)) := by
  have original : work.binding.queries.val.get index = raw :=
    Option.some.inj ((List.getElem?_eq_getElem index.isLt).symm.trans found)
  have read := BatchOpeningNativeObligation.query_read candidate world work prepared index
  rw [original] at read
  exact read_transport parameters _ _ read

theorem fold_mismatch {first second : Parameters Stored} (same : first = second)
    (firstQuery : ExtensionQuery.Broadcast Goldilocks first.width.val first.numVariables.val)
    (secondQuery : ExtensionQuery.Broadcast Goldilocks second.width.val second.numVariables.val)
    (firstSource : MatrixFold.Cube first.numVariables.val → Fin first.width.val → Goldilocks)
    (secondSource : MatrixFold.Cube second.numVariables.val → Fin second.width.val → Goldilocks)
    (firstExpected : Fin first.width.val → Goldilocks) (secondExpected : Fin second.width.val → Goldilocks)
    (queries : HEq firstQuery secondQuery) (sources : HEq firstSource secondSource) (values : HEq firstExpected secondExpected)
    (wrong : secondExpected ≠ secondQuery.query.fold secondSource) : firstExpected ≠ firstQuery.query.fold firstSource := by
  cases same
  cases queries
  cases sources
  cases values
  exact wrong

/-- This is the remaining source-row semantic premise expressed on the
original allocated executable cube, independent of parsed nonce or source-log
choice. Native falsity follows for every actual parsed/recovered view. -/
theorem wrong_at (candidate reference : Context)
    (candidateOrigin : CacheBackedCodeOrigin.Origin candidate) (referenceOrigin : CacheBackedCodeOrigin.Origin reference)
    (parameters : candidate.parameters = reference.parameters) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram candidate) world).run.1 = .prepared work)
    (dummy : Digest) (history : List Observation) (sizes : GoldHistorySourceTable.Geometry reference.parameters)
    (compatible : RegistryPublicSource.Compatible candidate reference candidateOrigin referenceOrigin world work prepared dummy history sizes)
    (radius : ℕ) (small : 3*radius < reference.parameters.code.blocks.val-reference.parameters.code.messageBlocks.val+1)
    (framed : NativeGoldBatchSourceRisk.Framed candidate)
    (responseFits : (NativeGoldBatchResponseBinding.payload candidate.opening).length < TranscriptFrame.lengthLimit)
    (decoded : NativeGoldBatchChallengeLink.View)
    (parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input candidate work world) = some decoded)
    (index : NativeGoldBatchRectangularData.Query work) (received : NativeLookupRequestWire.Row)
    (wrong : rowValue reference.parameters received ≠
      (query parameters (BatchOpeningNativeObligation.query candidate world work prepared index)).query.fold
        (GoldHistoryPublicExtraction.cube reference dummy (InputIndexedOracle.sha512 world (GoldContextInput.bytes reference.parameters))
          reference.root history radius (referenceOrigin.capacityAt reference rfl) sizes)) :
    BatchOpeningNativeObligation.WrongAt dummy candidate (candidateOrigin.primitiveAt candidate rfl) (candidateOrigin.capacityAt candidate rfl)
      world work prepared decoded history radius index (rowValue candidate.parameters received) := by
  intro sourceLog recovered
  exact fold_mismatch parameters _ _ _ _ _ _ (query_heq parameters _) (compatible radius small framed responseFits decoded parsed sourceLog recovered)
    (rowValue_heq parameters received) wrong

/-- The actual original batch getter and native alias comparison discharge
raw-row width and field encoding. A wrong received outer row on the allocated
public cube is therefore a false original native batch claim. -/
theorem false_claim (candidate reference : Context)
    (candidateOrigin : CacheBackedCodeOrigin.Origin candidate) (referenceOrigin : CacheBackedCodeOrigin.Origin reference)
    (parameters : candidate.parameters = reference.parameters) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram candidate) world).run.1 = .prepared work)
    (dummy : Digest) (history : List Observation) (sizes : GoldHistorySourceTable.Geometry reference.parameters)
    (compatible : RegistryPublicSource.Compatible candidate reference candidateOrigin referenceOrigin world work prepared dummy history sizes)
    (radius : ℕ) (small : 3*radius < reference.parameters.code.blocks.val-reference.parameters.code.messageBlocks.val+1)
    (framed : NativeGoldBatchSourceRisk.Framed candidate)
    (responseFits : (NativeGoldBatchResponseBinding.payload candidate.opening).length < TranscriptFrame.lengthLimit)
    (decoded : NativeGoldBatchChallengeLink.View)
    (parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input candidate work world) = some decoded)
    (index : NativeGoldBatchRectangularData.Query work) (inserted received : NativeLookupRequestWire.Row)
    (found : work.binding.values.val[index.val]? = some inserted)
    (matched : NativeGoldPcsClaim.equal inserted.val received.val = true)
    (wrong : rowValue reference.parameters received ≠
      (query parameters (BatchOpeningNativeObligation.query candidate world work prepared index)).query.fold
        (GoldHistoryPublicExtraction.cube reference dummy (InputIndexedOracle.sha512 world (GoldContextInput.bytes reference.parameters))
          reference.root history radius (referenceOrigin.capacityAt reference rfl) sizes)) :
    NativeGoldBatchCausalCoverage.FalseClaim dummy candidate (candidateOrigin.primitiveAt candidate rfl) work decoded history
      (candidateOrigin.capacityAt candidate rfl) radius := by
  have insertedWidth := BatchClaimShape.prepared_width candidate world work prepared index inserted found
  have fields := (NativeGoldPcsClaim.equal_iff inserted.val received.val).mp matched
  have lengths := congrArg List.length fields
  simp only [List.length_map] at lengths
  have receivedWidth : received.val.length = candidate.parameters.width.val := lengths.symm.trans insertedWidth
  have encoded := fields.trans (BatchClaimShape.row_encoding candidate.parameters.width.val received receivedWidth)
  have wrongAt := wrong_at candidate reference candidateOrigin referenceOrigin parameters world work prepared dummy history sizes compatible
    radius small framed responseFits decoded parsed index received wrong
  exact (BatchOpeningNativeObligation.false_claim_iff dummy candidate _ _ world work prepared decoded history radius framed responseFits parsed).mpr
    (BatchOpeningNativeObligation.wrong_of_at dummy candidate _ _ world work prepared decoded history radius index inserted found
      (rowValue candidate.parameters received) encoded wrongAt)

end
end FormalProof4FHE.HasteBoots.RegistryPublicSourceObligation
