module

public import FormalProof4FHE.HasteBoots.NativeGoldPcsColumns

@[expose] public section

/-! Dimensions and sampling properties derived from actual completed runs.
No prepared geometry, valid-query certificate or canonical random matrix is
an input to the entry-point program. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldPcsColumnsShape

open NativeBrakedownContext (Parameters)
open NativeBrakedownParameters (Description Geometry)
open NativeGoldPcsWire (Query)
open NativeGoldPcsOpening (Opening)
open NativeLookupRequestWire (Row)
open NativeRootMessage (Digest)
open NativeTranscript (Transcript)
open NativeFieldRepresentation (GoldWord)
open InputIndexedOracle (World)
open OracleProgram (run)

/-- The constructor's random-test allocation bound also bounds a square matrix. -/
theorem square_bound {C : Type} (description : Description C) (parameters : Parameters C) (geometry : Geometry)
    (constructed : NativeBrakedownParameters.build description parameters = some geometry) :
    parameters.width.val*parameters.width.val < 2^64 := by
  have spec := NativeBrakedownParameters.build_spec description parameters geometry constructed
  have positive : 0 < 2^parameters.leftVariables.val := by positivity
  have base : parameters.width.val ≤ 2^parameters.leftVariables.val*parameters.width.val := by nlinarith
  exact lt_of_le_of_lt (Nat.mul_le_mul_right parameters.width.val base) spec.allocations.2.2.2.2.1

/-- Binding checks transfer to the original ordered raw query models. -/
theorem binding_models {C : Type} (parameters : Parameters C) (query : Query) (values : Row)
    (checked : NativeGoldPcsBinding.check parameters query values = true) :
    query.models.length = parameters.numVariables.val ∧ NativeGoldMatrixWeights.QueryValid parameters.width.val query.models := by
  have facts := (NativeGoldPcsBinding.check_iff parameters query values).mp checked
  refine ⟨by simpa only [NativeGoldPcsWire.Query.models,List.length_map] using facts.1,?_⟩
  intro pair member
  obtain ⟨raw,inside,same⟩ := List.mem_map.mp member
  subst pair
  exact facts.2.2 raw inside

/-- Structured computation cannot fail after an actual completed checked prefix.
Its shape is the same computed matrix size as the random test. -/
theorem finished_structure {C : Type} (description : Description C) (parameters : Parameters C) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (opening : Opening) (fuel : ℕ) (world : World)
    (geometry : Geometry) (state : NativeFieldVector.State) (next : Transcript)
    (success : (run (NativeGoldPcsPrelude.protocol description parameters transcript root query values opening fuel) world).run.1 =
      .sampling geometry (.finished state next)) :
    ∃ weights, NativeGoldPcsArithmetic.structured parameters.width.val parameters.leftVariables.val query.models = some weights ∧
      weights.length = geometry.rows*parameters.width.val := by
  obtain ⟨constructed,_,bound,boundRead,_⟩ := NativeGoldPcsPrelude.sampling_origin description parameters transcript root query values opening fuel world geometry (.finished state next) success
  have checked := NativeGoldPcsBinding.bound_check description.row parameters transcript root query values world bound boundRead
  have models := binding_models parameters query values checked
  have spec := NativeBrakedownParameters.build_spec description parameters geometry constructed
  have leftBound : parameters.leftVariables.val ≤ query.models.length := by rw [models.1]; exact spec.basic.2.1
  obtain ⟨weights,computed,size⟩ := NativeGoldPcsArithmetic.structured_complete parameters.width.val parameters.leftVariables.val
    query.models spec.basic.1 (square_bound _ _ _ constructed) leftBound models.2
  refine ⟨weights,computed,?_⟩
  have rows := (NativeBrakedownParameters.computed_sizes description parameters geometry constructed).2.2.2.1
  rw [size,rows]
  ac_rfl

/-- Both actual matrices have the constructor's size, and every random word is
canonical. Distinct column indices are sorted, bounded and drawn from the
original quota-sized vector. The received column count is checked exactly. -/
theorem columns_shape {C : Type} (description : Description C) (parameters : Parameters C) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (opening : Opening) (fuel : ℕ) (world : World)
    (geometry : Geometry) (state : NativeFieldVector.State) (weights : List GoldWord) (sample : NativeIndexRequest.Result)
    (success : (run (NativeGoldPcsColumns.protocol description parameters transcript root query values opening fuel) world).run.1 =
      .columns geometry state weights sample) :
    (NativeGoldPcsColumns.random state).length = geometry.rows*parameters.width.val ∧
    (∀ word ∈ NativeGoldPcsColumns.random state, word.val < NativeFields.goldilocksModulus) ∧
    weights.length = geometry.rows*parameters.width.val ∧ sample.draws.length = parameters.queries.val ∧
    sample.indices = NativeIndexRequest.distinct sample.draws ∧ sample.indices.Nodup ∧
    sample.indices.Pairwise (fun left right => left ≤ right) ∧
    (∀ index ∈ sample.indices, index < geometry.blocks) ∧ opening.columns.val.length = sample.indices.length := by
  obtain ⟨next,prior,computed,drawn,count⟩ := NativeGoldPcsColumns.columns_origin description parameters transcript root query values opening fuel world geometry state weights sample success
  have fields := NativeGoldPcsPrelude.finished_values description parameters transcript root query values opening fuel world geometry state next prior
  obtain ⟨actual,read,size⟩ := finished_structure description parameters transcript root query values opening fuel world geometry state next prior
  have same := Option.some.inj (computed.symm.trans read)
  subst actual
  have indices := NativeIndexRequest.accepted_shape _ _ _ _ world sample drawn
  have constructed := (NativeGoldPcsPrelude.sampling_origin description parameters transcript root query values opening fuel world geometry (.finished state next) prior).1
  have blocks := (NativeBrakedownParameters.computed_sizes description parameters geometry constructed).2.1
  refine ⟨by simpa only [NativeGoldPcsColumns.random,List.length_map] using fields.1,?_,size,indices.1,
    indices.2.1,indices.2.2.1,indices.2.2.2.1,?_,count⟩
  · intro word member
    obtain ⟨value,inside,same⟩ := List.mem_map.mp member
    subst word
    rw [(fields.2 value inside).1]
    exact (fields.2 value inside).2
  · intro index member
    rw [blocks]
    exact indices.2.2.2.2.1 index (indices.2.2.2.2.2 index member)

end FormalProof4FHE.HasteBoots.NativeGoldPcsColumnsShape
