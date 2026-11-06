module

public import FormalProof4FHE.HasteBoots.NativeGoldBatchPrelude
public import FormalProof4FHE.HasteBoots.NativeGoldPcsColumns
@[expose] public section

/-! One shared native batch random matrix, first-original-prefix structured
responses, one response frame and one schedule-5 atomic column request.
Ordered draws are retained separately from distinct transmitted columns.
Errors retain their actual parent, and analysis suspension issues no later
response/index request. This boundary does not encode responses, authenticate
columns, finish claims, assert coin freshness or prove application security. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchColumns
open NativeBrakedownContext (Parameters)
open NativeBrakedownParameters (Description Geometry)
open NativeGoldPcsWire (Query)
open NativeGoldBatchOpening (Opening)
open NativeGoldBatchBinding (Bound)
open NativeLookupRequestWire (Row)
open NativeRootMessage (Digest)
open NativeTranscript (Transcript)
open NativeFieldRepresentation (GoldWord)
open NativePrefixCodec (Vector)
open InputIndexedOracle (World)
open OracleProgram (Program bind run)

/-- First original query per exact ordered prefix group, in native insertion order. -/
def representatives {C : Type} (parameters : Parameters C) (queries : Vector Query) : List Query :=
  List.ofFn (fun index : Fin (NativeGoldQueryGroups.groupCount parameters.leftVariables.val queries) =>
    queries.val.get (NativeGoldQueryGroups.representative parameters.leftVariables.val queries index))

def collect (width left : ℕ) : List Query → Option (List (List GoldWord))
  | [] => some []
  | query::rest => (NativeGoldPcsArithmetic.structured width left query.models).bind (fun weights =>
      (collect width left rest).map (List.cons weights))

def structured {C : Type} (parameters : Parameters C) (queries : Vector Query) : Option (List (List GoldWord)) :=
  collect parameters.width.val parameters.leftVariables.val (representatives parameters queries)

theorem collect_spec (width left : ℕ) (queries : List Query) (weights : List (List GoldWord))
    (computed : collect width left queries = some weights) :
    List.Forall₂ (fun query weight => NativeGoldPcsArithmetic.structured width left query.models = some weight) queries weights := by
  induction queries generalizing weights with
  | nil => have same := Option.some.inj computed; subst weights; exact .nil
  | cons query rest ih =>
    simp only [collect] at computed
    obtain ⟨first,read,tail⟩ := Option.bind_eq_some_iff.mp computed
    obtain ⟨remaining,continued,same⟩ := Option.map_eq_some_iff.mp tail
    rw [← same]
    exact .cons read (ih remaining continued)

theorem structured_spec {C : Type} (parameters : Parameters C) (queries : Vector Query) (weights : List (List GoldWord))
    (computed : structured parameters queries = some weights) :
    weights.length = NativeGoldQueryGroups.groupCount parameters.leftVariables.val queries ∧
      List.Forall₂ (fun query weight => NativeGoldPcsArithmetic.structured parameters.width.val parameters.leftVariables.val query.models = some weight)
        (representatives parameters queries) weights := by
  have facts := collect_spec _ _ _ _ computed
  exact ⟨by simpa only [representatives,List.length_ofFn] using facts.length_eq.symm,facts⟩

/-- Each group uses structured weights computed from its first original query. -/
theorem structured_group {C : Type} (parameters : Parameters C) (queries : Vector Query) (weights : List (List GoldWord))
    (computed : structured parameters queries = some weights)
    (index : Fin (NativeGoldQueryGroups.groupCount parameters.leftVariables.val queries)) :
    ∃ bounded : index.val < weights.length,
      NativeGoldPcsArithmetic.structured parameters.width.val parameters.leftVariables.val
        (queries.val.get (NativeGoldQueryGroups.representative parameters.leftVariables.val queries index)).models = some weights[index.val] := by
  have facts := structured_spec parameters queries weights computed
  have original : index.val < (representatives parameters queries).length := by
    simpa only [representatives,List.length_ofFn] using index.isLt
  have bounded : index.val < weights.length := by rw [facts.1]; exact index.isLt
  refine ⟨bounded,?_⟩
  simpa only [representatives,List.get_eq_getElem,List.getElem_ofFn] using facts.2.get original bounded

inductive Error where
  | prelude (reason : NativeGoldBatchPrelude.Error)
  | structured | distinctCount
  deriving DecidableEq
inductive Outcome where
  | rejected (reason : Error) (parent : Transcript)
  | suspended (geometry : Geometry) (bound : Bound) (state : NativeFieldVector.State)
  | atomicUnavailable (parent : Transcript)
  | columns (geometry : Geometry) (bound : Bound) (state : NativeFieldVector.State)
      (structured : List (List GoldWord)) (sample : NativeIndexRequest.Result)

def label : InputIndexedOracle.Input := NativeTranscript.utf8 "mw atomic column block v5"

def afterField {C : Type} (description : Description C) (parameters : Parameters C) (opening : Opening)
    (geometry : Geometry) (binding : Bound) : NativeFieldVector.Status → Program Outcome
  | .suspended state => .pure (.suspended geometry binding state)
  | .finished state next => match structured parameters binding.queries with
    | none => .pure (.rejected .structured next)
    | some weights =>
      let parent := NativeGoldBatchOpening.bindResponses next opening
      bind (NativeIndexRequest.request parent label (description.row.blocks parameters.code) parameters.queries) (fun drawn => match drawn with
        | none => .pure (.atomicUnavailable parent)
        | some sample => if opening.columns.val.length = sample.indices.length then
            .pure (.columns geometry binding state weights sample)
          else .pure (.rejected .distinctCount sample.transcript))

def continuePrelude {C : Type} (description : Description C) (parameters : Parameters C) (opening : Opening) :
    NativeGoldBatchPrelude.Outcome → Program Outcome
  | .rejected reason parent => .pure (.rejected (.prelude reason) parent)
  | .sampling geometry binding field => afterField description parameters opening geometry binding field

def protocol {C : Type} (description : Description C) (parameters : Parameters C) (parent : Transcript)
    (root : Digest) (queries : Vector Query) (values : Vector Row) (opening : Opening) (fuel : ℕ) : Program Outcome :=
  bind (NativeGoldBatchPrelude.protocol description parameters parent root queries values opening fuel)
    (continuePrelude description parameters opening)

theorem run_protocol {C : Type} (description : Description C) (parameters : Parameters C) (parent : Transcript)
    (root : Digest) (queries : Vector Query) (values : Vector Row) (opening : Opening) (fuel : ℕ) (world : World) :
    (run (protocol description parameters parent root queries values opening fuel) world).run =
      let prior := (run (NativeGoldBatchPrelude.protocol description parameters parent root queries values opening fuel) world).run
      let tail := (run (continuePrelude description parameters opening prior.1) world).run
      (tail.1,prior.2 ++ tail.2) := by
  rw [protocol,OracleProgram.run_bind,ObservationReplay.run_bind]

theorem run_afterField {C : Type} (description : Description C) (parameters : Parameters C) (opening : Opening)
    (geometry : Geometry) (binding : Bound) (state : NativeFieldVector.State) (next : Transcript) (world : World) :
    (run (afterField description parameters opening geometry binding (.finished state next)) world).run =
      match structured parameters binding.queries with
      | none => (.rejected .structured next,[])
      | some weights =>
        let parent := NativeGoldBatchOpening.bindResponses next opening
        let drawn := (run (NativeIndexRequest.request parent label (description.row.blocks parameters.code) parameters.queries) world).run
        match drawn.1 with
        | none => (.atomicUnavailable parent,drawn.2)
        | some sample => (if opening.columns.val.length = sample.indices.length then .columns geometry binding state weights sample
            else .rejected .distinctCount sample.transcript,drawn.2) := by
  simp only [afterField]
  cases structured parameters binding.queries with
  | none => rfl
  | some weights =>
    rw [OracleProgram.run_bind,ObservationReplay.run_bind]
    cases (run (NativeIndexRequest.request _ _ _ _) world).run.1 with
    | none => simp only [OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]
    | some sample =>
      dsimp only
      split <;> simp only [OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]

theorem suspended {C : Type} (description : Description C) (parameters : Parameters C) (opening : Opening)
    (geometry : Geometry) (bound : Bound) (state : NativeFieldVector.State) (world : World) :
    (run (afterField description parameters opening geometry bound (.suspended state)) world).run =
      (.suspended geometry bound state,[]) := rfl

theorem columns_origin {C : Type} (description : Description C) (parameters : Parameters C) (parent : Transcript)
    (root : Digest) (queries : Vector Query) (values : Vector Row) (opening : Opening) (fuel : ℕ) (world : World)
    (geometry : Geometry) (binding : Bound) (state : NativeFieldVector.State) (weights : List (List GoldWord)) (sample : NativeIndexRequest.Result)
    (executed : (run (protocol description parameters parent root queries values opening fuel) world).run.1 = .columns geometry binding state weights sample) :
    ∃ next, (run (NativeGoldBatchPrelude.protocol description parameters parent root queries values opening fuel) world).run.1 =
        .sampling geometry binding (.finished state next) ∧
      structured parameters binding.queries = some weights ∧
      (run (NativeIndexRequest.request (NativeGoldBatchOpening.bindResponses next opening) label (description.row.blocks parameters.code) parameters.queries) world).run.1 = some sample ∧
      opening.columns.val.length = sample.indices.length := by
  rw [run_protocol] at executed
  cases prior : (run (NativeGoldBatchPrelude.protocol description parameters parent root queries values opening fuel) world).run.1 with
  | rejected reason failed => simp only [prior,continuePrelude,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed; contradiction
  | sampling actual bound field =>
    cases field with
    | suspended pending => simp only [prior,continuePrelude,suspended] at executed; contradiction
    | finished collected next =>
      simp only [prior,continuePrelude,run_afterField] at executed
      cases computed : structured parameters bound.queries with
      | none => simp only [computed] at executed; contradiction
      | some actualWeights =>
        simp only [computed] at executed
        cases drawn : (run (NativeIndexRequest.request (NativeGoldBatchOpening.bindResponses next opening) label (description.row.blocks parameters.code) parameters.queries) world).run.1 with
        | none => simp only [drawn] at executed; contradiction
        | some actualSample =>
          simp only [drawn] at executed
          split at executed
          next count =>
            obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := Outcome.columns.inj executed
            exact ⟨next,rfl,computed,drawn,count⟩
          next rejected => contradiction

theorem columns_log {C : Type} (description : Description C) (parameters : Parameters C) (parent : Transcript)
    (root : Digest) (queries : Vector Query) (values : Vector Row) (opening : Opening) (fuel : ℕ) (world : World)
    (geometry : Geometry) (binding : Bound) (state : NativeFieldVector.State) (weights : List (List GoldWord)) (sample : NativeIndexRequest.Result)
    (executed : (run (protocol description parameters parent root queries values opening fuel) world).run.1 = .columns geometry binding state weights sample) :
    ∃ next, (run (NativeGoldBatchPrelude.protocol description parameters parent root queries values opening fuel) world).run.1 =
        .sampling geometry binding (.finished state next) ∧
      (run (protocol description parameters parent root queries values opening fuel) world).run.2 =
        (run (NativeGoldBatchPrelude.protocol description parameters parent root queries values opening fuel) world).run.2 ++
          (run (NativeIndexRequest.request (NativeGoldBatchOpening.bindResponses next opening) label (description.row.blocks parameters.code) parameters.queries) world).run.2 := by
  obtain ⟨next,prior,computed,drawn,count⟩ := columns_origin description parameters parent root queries values opening fuel world geometry binding state weights sample executed
  refine ⟨next,prior,?_⟩
  rw [run_protocol]
  simp only [prior,continuePrelude,run_afterField,computed,drawn,ite_eq_left count]
/-- Keep all ordered draws even though transport sends only ascending distinct columns. -/
theorem columns_draws {C : Type} (description : Description C) (parameters : Parameters C) (parent : Transcript)
    (root : Digest) (queries : Vector Query) (values : Vector Row) (opening : Opening) (fuel : ℕ) (world : World)
    (geometry : Geometry) (binding : Bound) (state : NativeFieldVector.State) (weights : List (List GoldWord)) (sample : NativeIndexRequest.Result)
    (executed : (run (protocol description parameters parent root queries values opening fuel) world).run.1 = .columns geometry binding state weights sample) :
    sample.draws.length = parameters.queries.val ∧ sample.indices = NativeIndexRequest.distinct sample.draws ∧
      sample.indices.Nodup ∧ sample.indices.Pairwise (fun left right => left ≤ right) ∧
      ∀ index ∈ sample.draws, index < (description.row.blocks parameters.code).val ∧ index ∈ sample.indices := by
  obtain ⟨_,_,_,drawn,_⟩ := columns_origin description parameters parent root queries values opening fuel world geometry binding state weights sample executed
  have shape := NativeIndexRequest.accepted_shape _ _ _ _ world sample drawn
  refine ⟨shape.1,shape.2.1,?_,?_,?_⟩
  · rw [shape.2.1]; exact NativeIndexRequest.distinct_nodup _
  · rw [shape.2.1]; exact NativeIndexRequest.distinct_sorted _
  · intro index member
    exact ⟨shape.2.2.2.2.1 index member,by rw [shape.2.1]; exact (NativeIndexRequest.mem_distinct _ _).mpr member⟩

end FormalProof4FHE.HasteBoots.NativeGoldBatchColumns
