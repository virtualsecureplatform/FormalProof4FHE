module
import all FormalProof4FHE.HasteBoots.HelperOpeningObligationLifetime
import all FormalProof4FHETest.HasteBootsSingleSelectedSmoke
import all FormalProof4FHETest.HasteBootsExtractedTableMeaningSmoke

namespace FormalProof4FHE.HasteBoots.HelperObligationSmoke
open SingleSelectedSmoke (ctx world work prepared)
open OracleProgram (run)
open NativeFields (Goldilocks)
open HasteBootsBatchMeaningSmoke (root)
noncomputable section

/-- The real native single-opening prefix supplies its own interpretation. -/
example : ∃ query : ExtensionQuery.Broadcast Goldilocks ctx.parameters.width.val ctx.parameters.numVariables.val,
    NativeGoldCoefficientsQuery.interpret ctx.parameters.width.val ctx.parameters.numVariables.val ⟨ctx.query.models,none⟩ = some query :=
  QueryNativeInterpretationComplete.prepared ctx world work prepared

/-- The choice-based analysis value is the unique actual deterministic decode. -/
def interpreted := NativeGoldCoefficientsQuery.interpret ctx.parameters.width.val ctx.parameters.numVariables.val ⟨ctx.query.models,none⟩
def decoded := interpreted.get (by decide +kernel)
example : SingleOpeningNativeObligation.query ctx world work prepared = decoded :=
  SingleOpeningNativeObligation.query_unique ctx world work prepared decoded (Option.some_get _).symm

/-- Different oracle worlds and prepared worker data cannot alter the same
original query's deterministic field interpretation. -/
example (other : InputIndexedOracle.World) (otherWork : NativeGoldPcsWorkers.Prepared)
    (otherPrepared : (run ctx.prefix other).run.1 = .prepared otherWork) :
    SingleOpeningNativeObligation.query ctx world work prepared = SingleOpeningNativeObligation.query ctx other otherWork otherPrepared :=
  SingleOpeningNativeObligation.query_unique ctx world work prepared _ (SingleOpeningNativeObligation.query_read ctx other otherWork otherPrepared)

/-- Reader completeness does not bypass a malformed original matrix width. -/
def badMatrix : NativeGoldPcsWire.Matrix := {HasteBootsBatchMeaningSmoke.matrix with width := HasteBootsBatchMeaningSmoke.usize 4}
def badQuery : NativeGoldPcsWire.Query := ⟨[(badMatrix,badMatrix)],by decide⟩
example : (NativeGoldCoefficientsQuery.interpret 3 1 ⟨badQuery.models,none⟩).isNone = true := by decide +kernel

/-- The original pair count remains exact, rather than silently truncated. -/
example : (NativeGoldCoefficientsQuery.interpret 3 1 ⟨ctx.query.models,none⟩).isNone = true := by decide +kernel

example : ∃ query : ExtensionQuery.Broadcast Goldilocks 3 0,
    NativeGoldCoefficientsQuery.interpret 3 0 ⟨[],none⟩ = some query :=
  ⟨⟨.nil,none⟩,rfl⟩

/-- Actual sampling, framing and nonce parsing yield the false-obligation
identity on the same original call and exact selected source logs. -/
example (origin : CacheBackedSingleOpening.Origin ctx) (history : List NativeTranscript.Observation) (radius : ℕ) :
    ∃ sample, ∃ receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample,
      ∃ decoded, SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input receipt world) = some decoded ∧
        (SingleOpeningCausalCoverage.FalseClaim root ctx origin decoded history radius ↔
          SingleOpeningNativeObligation.Wrong root ctx origin world work prepared decoded history radius (fun _ => 0)) := by
  obtain ⟨sample,⟨receipt⟩⟩ := SingleOpeningSamplingReceipt.ofPreparation ctx world work prepared
  obtain ⟨context,_,parsed,_,_⟩ := SingleOpeningPreparedChallenge.prepared_link receipt prepared [] rfl (by simp)
    (by decide +kernel) (by decide +kernel)
  refine ⟨sample,receipt,_,parsed,?_⟩
  exact SingleOpeningNativeObligation.false_claim_iff receipt prepared
    ⟨[],rfl,by simp,by decide +kernel⟩ (by decide +kernel) root origin _ parsed history radius _ (by decide +kernel)

end
end FormalProof4FHE.HasteBoots.HelperObligationSmoke
