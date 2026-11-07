module
public import FormalProof4FHE.HasteBoots.StoredGoldContextObservationCost
public import FormalProof4FHE.HasteBoots.ValidatedGoldFieldExtraction
@[expose] public section

/-! Checked native field count and complete observed parameter-context binding
before stored public-source extraction. A truthful shared history identifies the
parameter object outside the existing global hash-collision event. This does
not yet connect the supplied context to the original application registry slot,
prove code-root validity, or refine native/physical initialization and execution. -/
namespace FormalProof4FHE.HasteBoots.ObservedGoldFieldExtraction
open InputIndexedOracle (Input Byte World)
open NativeTranscript (Observation)
open NativeGoldBatchPcsProgram (Context)
open SolverOperationCost (Run)
open StoredGoldFieldSourceRecovery (Recovered)

def run (history : List Observation) (input : Input) (dummy : Vector Byte 64) (ctx : Context) (radius : ℕ) :=
  let validated := ValidatedGoldFieldExtraction.validate ctx.parameters
  match validated.value with
  | none => Run.mk none (validated.cost+2)
  | some checked =>
    let recovered := StoredGoldFieldSourceRecovery.run history input
    match recovered.value with
    | none => Run.mk none (validated.cost+recovered.cost+3)
    | some result =>
      if result.field.count = checked.geometry.randomCount then
        let associated := StoredGoldContextObservationCost.verify ctx.parameters result.field.data.source.1 history
        if associated.value then
          let root := StoredDigestView.fromVector result.field.data.source.2
          let extracted := StoredGoldPublicSource.extract dummy root.value ctx result.log radius checked.capacity
          Run.mk (some (result.field,extracted.value))
            (validated.cost+recovered.cost+associated.cost+root.cost+extracted.cost+8)
        else Run.mk none (validated.cost+recovered.cost+associated.cost+7)
      else Run.mk none (validated.cost+recovered.cost+5)

theorem run_sound (history : List Observation) (input : Input) (dummy : Vector Byte 64) (ctx : Context) (radius : ℕ)
    (output) (accepted : (run history input dummy ctx radius).value = some output) :
    ∃ checked : ValidatedGoldFieldExtraction.Checked ctx.parameters, ∃ result : Recovered,
      (ValidatedGoldFieldExtraction.validate ctx.parameters).value = some checked ∧
      (StoredGoldFieldSourceRecovery.run history input).value = some result ∧
      result.field = output.1 ∧ result.field.count = checked.geometry.randomCount ∧
      (StoredGoldContextObservationCost.verify ctx.parameters result.field.data.source.1 history).value = true := by
  simp only [run] at accepted
  split at accepted
  · cases accepted
  · rename_i checked validated
    split at accepted
    · cases accepted
    · rename_i result recovered
      split at accepted
      · rename_i countMatches
        split at accepted
        · rename_i associated
          have same := Option.some.inj accepted
          exact ⟨checked,result,validated,recovered,congrArg Prod.fst same,countMatches,associated⟩
        · cases accepted
      · cases accepted

theorem run_cost (history : List Observation) (input : Input) (dummy : Vector Byte 64) (ctx : Context) (radius : ℕ) :
    (run history input dummy ctx radius).cost ≤
      1519+ValidatedGoldFieldExtraction.extractionBound history input ctx radius+
      StoredGoldContextObservationCost.bound ctx.parameters history+5 := by
  have validated := ValidatedGoldFieldExtraction.validate_cost ctx.parameters
  have recovered := StoredGoldFieldSourceRecovery.run_cost history input
  simp only [run]
  split
  · dsimp only; omega
  · rename_i checked valid
    split
    · dsimp only [ValidatedGoldFieldExtraction.extractionBound]; omega
    · rename_i result found
      have associated := StoredGoldContextObservationCost.verify_bound ctx.parameters result.field.data.source.1 history
      split
      · split
        · have extracted := StoredGoldPublicSource.extract_cost dummy
            (StoredDigestView.fromVector result.field.data.source.2).value ctx result.log radius checked.capacity
          simp only [ValidatedGoldFieldExtraction.extractionBound,found,Option.map_some,Option.getD_some]
          dsimp only [StoredDigestView.fromVector,CausalStoredGoldExtraction.sourceBound] at extracted ⊢
          omega
        · dsimp only [ValidatedGoldFieldExtraction.extractionBound]; omega
      · dsimp only [ValidatedGoldFieldExtraction.extractionBound]; omega

noncomputable section
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq

theorem parameters_eq_verified_original (history : List Observation) (input : Input) (dummy : Vector Byte 64)
    (ctx : Context) (radius : ℕ) (output)
    (accepted : (run history input dummy ctx radius).value = some output)
    (original : StoredGoldContextEncodingCost.Parameters) (world : World)
    (truthful : ObservationReplay.Agrees world history)
    (observed : (StoredGoldContextObservationCost.verify original output.1.data.source.1 history).value = true)
    (noCollision : ¬OracleComp.CacheHasCollision (JointHashCache.project history).cache) : ctx.parameters = original := by
  obtain ⟨checked,result,_,_,fieldEq,_,associated⟩ := run_sound history input dummy ctx radius output accepted
  rw [fieldEq] at associated
  exact StoredGoldContextObservationCost.verified_parameters_eq ctx.parameters original output.1.data.source.1 history world
    truthful associated observed noCollision
theorem parameters_eq_native_initializer (history : List Observation) (input : Input) (dummy : Vector Byte 64)
    (ctx : Context) (radius : ℕ) (output)
    (accepted : (run history input dummy ctx radius).value = some output)
    (original : StoredGoldContextEncodingCost.Parameters) (world : World)
    (truthful : ObservationReplay.Agrees world history)
    (returned : (OracleProgram.run (NativeBrakedownContext.context NativeGoldBlockCode.description.row original) world).run.1 =
      some output.1.data.source.1.get)
    (included : (OracleProgram.run (NativeBrakedownContext.context NativeGoldBlockCode.description.row original) world).run.2.Sublist history)
    (noCollision : ¬OracleComp.CacheHasCollision (JointHashCache.project history).cache) : ctx.parameters = original := by
  apply parameters_eq_verified_original history input dummy ctx radius output accepted original world truthful
  · exact StoredGoldContextObservationCost.verify_native_complete original output.1.data.source.1 history world returned included
  · exact noCollision

end
end FormalProof4FHE.HasteBoots.ObservedGoldFieldExtraction
