module

public import FormalProof4FHE.HasteBoots.NativeGoldPcsArithmetic
public import FormalProof4FHE.HasteBoots.NativeGoldPcsWorkers

@[expose] public section

/-! The native suffix fold is total after the existing checked PCS prefix.
No finished result, query-shape certificate or suffix certificate is a
protocol input. Rust memory/instruction refinement remains separate. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldPcsFinishComplete

open NativeFieldRepresentation (GoldWord)
open NativeGoldCoefficientsQuery (Pair)
open NativeGoldPackedFold (Table validate loop evaluate)

theorem loop_complete (table : Table) (query : List Pair) (valid : validate table = true)
    (size : query.length = table.numVars) (queryValid : NativeGoldMatrixWeights.QueryValid table.width query) :
    ∃ result, loop table query = some result := by
  induction query generalizing table with
  | nil => exact ⟨table,rfl⟩
  | cons pair tail ih =>
    have matrices := queryValid pair List.mem_cons_self
    have positive : table.numVars ≠ 0 := by simp only [List.length_cons] at size; omega
    let next : Table := ⟨table.numVars-1,table.width,NativeGoldPackedFold.foldedValues table pair⟩
    have step : NativeGoldPackedFold.fold table pair = some next :=
      NativeGoldPackedFold.fold_success table pair valid matrices.1 matrices.2 positive
    have spec := NativeGoldPackedFold.fold_spec table next pair step
    have tailSize : tail.length = next.numVars := by simp only [List.length_cons] at size; omega
    have tailValid : NativeGoldMatrixWeights.QueryValid next.width tail := by
      rw [spec.2.2]
      exact fun item member => queryValid item (List.mem_cons_of_mem pair member)
    obtain ⟨result,rest⟩ := ih next spec.1 tailSize tailValid
    exact ⟨result,by simp only [loop,step,Option.bind_some,rest]⟩

theorem evaluate_complete (table : Table) (query : List Pair) (valid : validate table = true)
    (size : query.length = table.numVars) (queryValid : NativeGoldMatrixWeights.QueryValid table.width query) :
    ∃ result, evaluate table query = some result := by
  obtain ⟨result,read⟩ := loop_complete table query valid size queryValid
  exact ⟨result.values,by simp only [evaluate,valid,size,decide_true,Bool.true_and,ite_true,read,Option.map_some]⟩

theorem finish_complete (numVars width leftVars : ℕ) (query : List Pair) (response : List GoldWord)
    (variablesBound : numVars < 64) (left : leftVars ≤ numVars) (positive : width ≠ 0)
    (fits : 2^(numVars-leftVars)*width < 2^64) (querySize : query.length = numVars)
    (responseSize : response.length = width*2^(numVars-leftVars))
    (queryValid : NativeGoldMatrixWeights.QueryValid width query) :
    ∃ result, NativeGoldPcsArithmetic.finish numVars width leftVars query response = some result := by
  have valid : validate ⟨numVars-leftVars,width,NativeGoldPcsArithmetic.transpose width (2^(numVars-leftVars)) response⟩ = true := by
    apply (NativeGoldPackedFold.validate_iff _).mpr
    exact ⟨by change numVars-leftVars < 64; omega,positive,fits,NativeGoldPcsArithmetic.transpose_length _ _ _⟩
  have size : (query.drop leftVars).length = numVars-leftVars := by rw [List.length_drop,querySize]
  obtain ⟨result,read⟩ := evaluate_complete _ (query.drop leftVars) valid size
    (fun pair member => queryValid pair (List.mem_of_mem_drop member))
  exact ⟨result,by simp only [NativeGoldPcsArithmetic.finish,variablesBound,left,querySize,and_self,ite_true,responseSize,read]⟩

open NativeGoldBlockCode (Stored Tables description)
open NativeBrakedownContext (Parameters)
open NativeGoldPcsWire (Query)
open NativeGoldPcsOpening (Opening)
open NativeLookupRequestWire (Row)
open NativeRootMessage (Digest)
open NativeTranscript (Transcript)
open NativeGoldPcsWorkers (Prepared)
open InputIndexedOracle (World)
open OracleProgram (run)

/-- All native suffix guards and matrix validation are derived from the actual
completed prefix, including original response length and allocation bounds. -/
theorem prepared_finish (tables : Tables) (parameters : Parameters Stored) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (opening : Opening) (fuel : ℕ) (world : World) (work : Prepared)
    (success : (run (NativeGoldPcsWorkers.protocol tables parameters transcript root query values opening fuel) world).run.1 = .prepared work) :
    NativeGoldMatrixWeights.QueryValid parameters.width.val query.models ∧
      ∃ result, NativeGoldPcsArithmetic.finish parameters.numVariables.val parameters.width.val parameters.leftVariables.val query.models opening.evaluation.val = some result := by
  obtain ⟨geometry,state,weights,sample,planRoot,test,evaluation,jobs,encoded,_,rfl⟩ :=
    NativeGoldPcsWorkers.prepared_origin tables parameters transcript root query values opening fuel world work success
  have original := (NativeGoldPcsEncoding.encoded_origin tables parameters transcript root query values opening fuel world geometry state weights sample planRoot test evaluation encoded).1
  obtain ⟨next,prior,_,_,_⟩ := NativeGoldPcsColumns.columns_origin description parameters transcript root query values opening fuel world geometry state weights sample original
  obtain ⟨parametersRead,shape,bound,boundRead,_⟩ := NativeGoldPcsPrelude.sampling_origin description parameters transcript root query values opening fuel world geometry (.finished state next) prior
  have spec := NativeBrakedownParameters.build_spec description parameters geometry parametersRead
  have checked := NativeGoldPcsBinding.bound_check description.row parameters transcript root query values world bound boundRead
  have models := NativeGoldPcsColumnsShape.binding_models parameters query values checked
  have responseSize := (NativeGoldPcsOpening.check_iff geometry parameters.queries opening).mp shape |>.evaluation
  have sizes := NativeBrakedownParameters.computed_sizes description parameters geometry parametersRead
  have smaller : 2^(parameters.numVariables.val-parameters.leftVariables.val) ≤ 2^parameters.numVariables.val :=
    Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have fits := lt_of_le_of_lt (Nat.mul_le_mul_right parameters.width.val smaller) spec.allocations.1
  refine ⟨models.2,finish_complete _ _ _ _ _ spec.basic.2.2.1 spec.basic.2.1 spec.basic.1 fits models.1 ?_ models.2⟩
  rw [responseSize,sizes.2.2.2.2.2.2.1,sizes.1]

end FormalProof4FHE.HasteBoots.NativeGoldPcsFinishComplete
