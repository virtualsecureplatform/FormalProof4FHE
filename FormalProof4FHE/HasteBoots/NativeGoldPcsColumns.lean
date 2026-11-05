module

public import FormalProof4FHE.HasteBoots.NativeGoldPcsPrelude
public import FormalProof4FHE.HasteBoots.NativeGoldPcsArithmetic
public import FormalProof4FHE.HasteBoots.NativeIndexRequest

@[expose] public section

/-! Single-opening execution through the schedule-5 atomic column boundary.
Structured weights are computed after the actual field request finishes and
before binding the original responses. A column-boundary result is not PCS
acceptance. Atomic precondition failure models the native `expect` boundary,
separately from verifier rejection and analysis suspension. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldPcsColumns

open NativeBrakedownContext (Parameters)
open NativeBrakedownParameters (Description Geometry)
open NativeGoldPcsWire (Query)
open NativeGoldPcsOpening (Opening)
open NativeLookupRequestWire (Row)
open NativeRootMessage (Digest)
open NativeTranscript (Transcript)
open NativeFieldRepresentation (GoldWord)
open InputIndexedOracle (World)
open OracleProgram (Program bind run)

inductive Error where
  | prelude (reason : NativeGoldPcsPrelude.Error)
  | structured | distinctCount
  deriving DecidableEq

inductive Outcome where
  | rejected (reason : Error)
  | suspended (geometry : Geometry) (state : NativeFieldVector.State)
  | atomicUnavailable (bound : Transcript)
  | columns (geometry : Geometry) (state : NativeFieldVector.State)
      (structured : List GoldWord) (sample : NativeIndexRequest.Result)

def random (state : NativeFieldVector.State) : List GoldWord := state.values.map NativePrimeRequest.goldWord

def label : InputIndexedOracle.Input := NativeTranscript.utf8 "mw atomic column block v5"

def afterField {C : Type} (description : Description C) (parameters : Parameters C) (query : Query)
    (opening : Opening) (geometry : Geometry) : NativeFieldVector.Status → Program Outcome
  | .suspended state => .pure (.suspended geometry state)
  | .finished state next =>
    match NativeGoldPcsArithmetic.structured parameters.width.val parameters.leftVariables.val query.models with
    | none => .pure (.rejected .structured)
    | some weights =>
      let bound := NativeGoldPcsWire.bindResponses next opening.test opening.evaluation
      bind (NativeIndexRequest.request bound label (description.row.blocks parameters.code) parameters.queries) (fun sampled =>
        match sampled with
        | none => .pure (.atomicUnavailable bound)
        | some sample => if opening.columns.val.length = sample.indices.length then
            .pure (.columns geometry state weights sample)
          else .pure (.rejected .distinctCount))

def continuePrelude {C : Type} (description : Description C) (parameters : Parameters C) (query : Query)
    (opening : Opening) : NativeGoldPcsPrelude.Outcome → Program Outcome
  | .rejected reason => .pure (.rejected (.prelude reason))
  | .sampling geometry field => afterField description parameters query opening geometry field

def protocol {C : Type} (description : Description C) (parameters : Parameters C) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (opening : Opening) (fuel : ℕ) : Program Outcome :=
  bind (NativeGoldPcsPrelude.protocol description parameters transcript root query values opening fuel)
    (continuePrelude description parameters query opening)

theorem run_protocol {C : Type} (description : Description C) (parameters : Parameters C) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (opening : Opening) (fuel : ℕ) (world : World) :
    (run (protocol description parameters transcript root query values opening fuel) world).run =
      let prior := (run (NativeGoldPcsPrelude.protocol description parameters transcript root query values opening fuel) world).run
      let tail := (run (continuePrelude description parameters query opening prior.1) world).run
      (tail.1,prior.2 ++ tail.2) := by
  rw [protocol,OracleProgram.run_bind,ObservationReplay.run_bind]

theorem run_afterField {C : Type} (description : Description C) (parameters : Parameters C) (query : Query)
    (opening : Opening) (geometry : Geometry) (state : NativeFieldVector.State) (next : Transcript) (world : World) :
    (run (afterField description parameters query opening geometry (.finished state next)) world).run =
      match NativeGoldPcsArithmetic.structured parameters.width.val parameters.leftVariables.val query.models with
      | none => (.rejected .structured,[])
      | some weights =>
        let bound := NativeGoldPcsWire.bindResponses next opening.test opening.evaluation
        let sampled := (run (NativeIndexRequest.request bound label (description.row.blocks parameters.code) parameters.queries) world).run
        match sampled.1 with
        | none => (.atomicUnavailable bound,sampled.2)
        | some sample =>
          (if opening.columns.val.length = sample.indices.length then .columns geometry state weights sample
            else .rejected .distinctCount,sampled.2) := by
  simp only [afterField]
  cases computed : NativeGoldPcsArithmetic.structured parameters.width.val parameters.leftVariables.val query.models with
  | none => rfl
  | some weights =>
    rw [OracleProgram.run_bind,ObservationReplay.run_bind]
    cases (run (NativeIndexRequest.request _ _ _ _) world).run.1 <;>
      simp only [OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]
    split <;> simp only [OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]

/-- Suspension performs no structured work or response/index request. -/
theorem suspended {C : Type} (description : Description C) (parameters : Parameters C) (query : Query)
    (opening : Opening) (geometry : Geometry) (state : NativeFieldVector.State) (world : World) :
    (run (afterField description parameters query opening geometry (.suspended state)) world).run =
      (.suspended geometry state,[]) := rfl

/-- Every column-boundary output comes from the original completed prelude,
computed weights and the actual response-bound atomic request in one world. -/
theorem columns_origin {C : Type} (description : Description C) (parameters : Parameters C) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (opening : Opening) (fuel : ℕ) (world : World)
    (geometry : Geometry) (state : NativeFieldVector.State) (weights : List GoldWord) (sample : NativeIndexRequest.Result)
    (success : (run (protocol description parameters transcript root query values opening fuel) world).run.1 =
      .columns geometry state weights sample) :
    ∃ next, (run (NativeGoldPcsPrelude.protocol description parameters transcript root query values opening fuel) world).run.1 =
        .sampling geometry (.finished state next) ∧
      NativeGoldPcsArithmetic.structured parameters.width.val parameters.leftVariables.val query.models = some weights ∧
      (run (NativeIndexRequest.request (NativeGoldPcsWire.bindResponses next opening.test opening.evaluation)
        label (description.row.blocks parameters.code) parameters.queries) world).run.1 = some sample ∧
      opening.columns.val.length = sample.indices.length := by
  rw [run_protocol] at success
  cases prior : (run (NativeGoldPcsPrelude.protocol description parameters transcript root query values opening fuel) world).run.1 with
  | rejected reason => simp only [prior,continuePrelude,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
  | sampling actual field =>
    cases field with
    | suspended pending => simp only [prior,continuePrelude,suspended] at success; contradiction
    | finished collected next =>
      simp only [prior,continuePrelude,run_afterField] at success
      cases computed : NativeGoldPcsArithmetic.structured parameters.width.val parameters.leftVariables.val query.models with
      | none => simp only [computed] at success; contradiction
      | some actualWeights =>
        simp only [computed] at success
        cases drawn : (run (NativeIndexRequest.request (NativeGoldPcsWire.bindResponses next opening.test opening.evaluation)
            label (description.row.blocks parameters.code) parameters.queries) world).run.1 with
        | none => simp only [drawn] at success; contradiction
        | some actualSample =>
          simp only [drawn] at success
          split at success
          · rename_i count
            obtain ⟨rfl,rfl,rfl,rfl⟩ := Outcome.columns.inj success
            exact ⟨next,rfl,rfl,drawn,count⟩
          · contradiction

/-- The only observations after the prelude are the single atomic reader start
and its whole byte block. Pure structured work and response framing add none. -/
theorem columns_observations {C : Type} (description : Description C) (parameters : Parameters C) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (opening : Opening) (fuel : ℕ) (world : World)
    (geometry : Geometry) (state : NativeFieldVector.State) (weights : List GoldWord) (sample : NativeIndexRequest.Result)
    (success : (run (protocol description parameters transcript root query values opening fuel) world).run.1 =
      .columns geometry state weights sample) :
    ∃ next, (run (NativeGoldPcsPrelude.protocol description parameters transcript root query values opening fuel) world).run.1 =
        .sampling geometry (.finished state next) ∧
      let bound := NativeGoldPcsWire.bindResponses next opening.test opening.evaluation
      let input := NativeTranscript.requestInput (NativeIndexRequest.prepare bound (description.row.blocks parameters.code)) label (parameters.queries.val*8)
      (run (protocol description parameters transcript root query values opening fuel) world).run.2 =
        (run (NativeGoldPcsPrelude.protocol description parameters transcript root query values opening fuel) world).run.2 ++
          [.start input,.output input 0 (InputIndexedOracle.bytes world input 0 (parameters.queries.val*8))] := by
  obtain ⟨next,prior,computed,drawn,count⟩ := columns_origin description parameters transcript root query values opening fuel world geometry state weights sample success
  have valid := NativeIndexRequest.accepted_check _ _ _ _ world sample drawn
  refine ⟨next,prior,?_⟩
  rw [run_protocol]
  simp only [prior,continuePrelude,run_afterField,computed,drawn,ite_eq_left count]
  rw [NativeIndexRequest.run_request _ _ _ _ world valid]

/-- An unusable atomic request stops after response binding and emits no index
observations. This is the native trusted-precondition failure, not an Err. -/
theorem atomic_unavailable {C : Type} (description : Description C) (parameters : Parameters C) (query : Query)
    (opening : Opening) (geometry : Geometry) (state : NativeFieldVector.State) (next : Transcript) (world : World)
    (weights : List GoldWord)
    (computed : NativeGoldPcsArithmetic.structured parameters.width.val parameters.leftVariables.val query.models = some weights)
    (invalid : NativeIndexRequest.check (description.row.blocks parameters.code) parameters.queries ≠ true) :
    (run (afterField description parameters query opening geometry (.finished state next)) world).run =
      (.atomicUnavailable (NativeGoldPcsWire.bindResponses next opening.test opening.evaluation),[]) := by
  simp only [run_afterField,computed,NativeIndexRequest.invalid_request _ _ _ _ _ invalid]

end FormalProof4FHE.HasteBoots.NativeGoldPcsColumns
