module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchProfileColumnNative
public import FormalProof4FHE.HasteBoots.CausalStreamLineage
public import FormalProof4FHE.HasteBoots.NativeGoldBatchChallengeHistory
public import FormalProof4FHE.HasteBoots.NativeGoldBatchFieldProximityCoverage
@[expose] public section

/-! Accepted native false claims in complete causal machine histories enter
inherited exposures or actual earlier disagreement/receipt/field/column
branches. Earlier packets and first-read splits are derived, not supplied.
Falsity still refers to the common-source analysis extractor; public PBS
semantics, trusted registry binding and physical work remain separate. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchCausalCoverage
open NativeGoldBatchPcsProgram (Context Prepared Scheduler)
open NativeGoldBlockCode (Tables logSize)
open NativeGoldBatchChallengeLink (View)
open NativeGoldColumnAuthentication (encoding)
open NativeRootMessage (Digest)
open NativeTranscript (Observation Execution)
open InputIndexedOracle (World)
open CausalExposureLifetime (history)
open OracleProgram (run)
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

def FalseClaim (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (work : Prepared) (decoded : View) (log : List Observation)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val)
    (radius : ℕ) : Prop :=
  ∀ sourceLog,
      NativeGoldBatchFirstFieldSource.recover dummy log decoded.field = some sourceLog →
      ∃ query : NativeGoldBatchRectangularData.Query work,
        (fun lane : Fin ctx.parameters.width.val => NativeGoldBatchFixedResponseData.claimed decoded.field.data.values query.val lane.val) ≠
          matrixEvaluation (NativeGoldBatchFixedResponseData.leftAt ctx.parameters decoded.field.data.queries query.val)
            (NativeGoldBatchFixedResponseData.rightAt ctx.parameters decoded.field.data.queries query.val)
            (RectangularMatrixOpeningKernel.extract (NativeGoldBatchResponseMeaning.Domain ctx primitive) capacity radius
              (NativeGoldBatchConcreteColumnFamily.source dummy ctx decoded sourceLog))

def Covered {P S A : Type} (past : World → Execution P) (initial : P → S)
    (step : S → OracleMachine.Command S A) (machineFuel : ℕ) (world : World)
    (dummy : Digest) (ctx : Context) (work : Prepared) (decoded : View)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (radius : ℕ) : Prop :=
    CausalStreamExposure.seen (past world).run.2 (NativeGoldBatchColumnRequestLaw.input ctx work world) = true ∨
    CausalStreamExposure.seen (past world).run.2 (NativeGoldBatchFirstFieldSource.input decoded.field) = true ∨
    CheckpointAvailability.Disagreement encoding dummy NativeMerkleShapeFamily.shape
      (NativeGoldBatchFamilyAvailability.reconstructed dummy (history past initial step machineFuel world).run.2) ∨
    (∃ index < machineFuel, NativeEarlyReceiptBound.event ctx.parent.profile step (history past initial step index world).run world) ∨
    (∃ index < machineFuel, NativeGoldBatchFieldProximity.event dummy ctx primitive radius ctx.parent.profile step
      (history past initial step index world).run world) ∨
    (∃ index < machineFuel, NativeGoldBatchProfileColumnExposure.event dummy ctx primitive ctx.parent.profile step
      (history past initial step index world).run radius world)

theorem accepted_coverage {P S A Memory : Type} (past : World → Execution P) (replay : ObservationReplay.Replayable past) (initial : P → S)
    (step : S → OracleMachine.Command S A) (machineFuel : ℕ) (world : World)
    (dummy : Digest) (ctx : Context) (work : Prepared)
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (choose : Scheduler Memory) (verifierFuel : ℕ) (memory : Memory)
    (decoded : View)
    (parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world) = some decoded)
    (responseFits : (NativeGoldBatchResponseBinding.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (accepted : NativeGoldBatchAnySourceRisk.Accepted world (history past initial step machineFuel world).run.2 ctx choose verifierFuel memory work)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val)
    (radius : ℕ) (width : 3 ≤ ctx.parameters.width.val)
    (falseClaim : FalseClaim dummy ctx primitive work decoded (history past initial step machineFuel world).run.2 capacity radius) :
    Covered past initial step machineFuel world dummy ctx work decoded primitive radius := by
  have truthful := (CausalExposureLifetime.history_replay replay initial step machineFuel).truthful world
  have nativeAccepted := accepted
  obtain ⟨⟨frames,parent,valid,fits⟩,completion,_,executed,_,_⟩ := accepted
  have prepared := (NativeGoldBatchPcsProgram.completed_origin ctx choose verifierFuel memory world work completion executed).prepared
  have touched := (NativeGoldBatchChallengeHistory.accepted_exposures ctx world work _ choose verifierFuel memory nativeAccepted).1
  obtain inherited | ⟨columnIndex,columnLt,columnFirst,_,offset,values,after,positive,split⟩ :=
    CausalStreamLineage.coverage past initial step machineFuel world _ touched
  · exact Or.inl inherited
  · have acceptedAt : NativeGoldBatchAnySourceRisk.Accepted world
        ((history past initial step columnIndex world).run.2 ++
          .output (NativeGoldBatchColumnRequestLaw.input ctx work world) offset values :: after) ctx choose verifierFuel memory work := by
      rw [← split]
      exact nativeAccepted
    have truthfulAt : ObservationReplay.Agrees world
        ((history past initial step columnIndex world).run.2 ++
          .output (NativeGoldBatchColumnRequestLaw.input ctx work world) offset values :: after) := by
      rw [← split]
      exact truthful
    have falseAt : ∀ sourceLog,
        NativeGoldBatchFirstFieldSource.recover dummy (history past initial step columnIndex world).run.2 decoded.field = some sourceLog →
        ∃ query : NativeGoldBatchRectangularData.Query work,
          (fun lane : Fin ctx.parameters.width.val => NativeGoldBatchFixedResponseData.claimed decoded.field.data.values query.val lane.val) ≠
            matrixEvaluation (NativeGoldBatchFixedResponseData.leftAt ctx.parameters decoded.field.data.queries query.val)
              (NativeGoldBatchFixedResponseData.rightAt ctx.parameters decoded.field.data.queries query.val)
              (RectangularMatrixOpeningKernel.extract (NativeGoldBatchResponseMeaning.Domain ctx primitive) capacity radius
                (NativeGoldBatchConcreteColumnFamily.source dummy ctx decoded sourceLog)) := by
      intro sourceLog found
      apply falseClaim sourceLog
      rw [split]
      exact NativeGoldBatchFirstFieldSource.recover_append dummy _ _ decoded.field sourceLog found
    obtain failed | early | ⟨sourceLog,found,proximity | column⟩ :=
      NativeGoldBatchConcreteExposureCoverage.accepted_first_column_cover dummy ctx world work tables message block blowup constructed primitive
        choose verifierFuel memory step (history past initial step columnIndex world).run columnFirst _ decoded parsed responseFits
        acceptedAt truthfulAt capacity radius width falseAt
    · right; right; left
      rw [← split] at failed
      exact failed
    · right; right; right; left
      exact ⟨columnIndex,columnLt,early⟩
    · have fieldSeen : CausalStreamExposure.seen (history past initial step columnIndex world).run.2
          (NativeGoldBatchFirstFieldSource.input decoded.field) = true := by
        cases seen : CausalStreamExposure.seen (history past initial step columnIndex world).run.2 (NativeGoldBatchFirstFieldSource.input decoded.field) with
        | true => rfl
        | false =>
          have absent := (NativeGoldBatchFirstFieldSource.recover_none dummy _ decoded.field).mpr seen
          rw [absent] at found
          contradiction
      obtain inheritedField | ⟨fieldIndex,fieldLt,fieldFirst,_,fieldOffset,fieldValues,middle,fieldPositive,fieldSplit⟩ :=
        CausalStreamLineage.coverage past initial step columnIndex world _ fieldSeen
      · exact Or.inr (Or.inl inheritedField)
      · right; right; right; right; left
        refine ⟨fieldIndex,fieldLt.trans columnLt,?_⟩
        exact NativeGoldBatchFieldProximityCoverage.later_proximity dummy ctx world work prepared frames parent valid fits responseFits decoded parsed
          primitive radius step (history past initial step fieldIndex world).run fieldFirst _ sourceLog found fieldOffset fieldValues fieldPositive middle fieldSplit proximity
    · right; right; right; right; right
      refine ⟨columnIndex,columnLt,?_⟩
      exact NativeGoldBatchProfileColumnNative.event_of_native ctx world work prepared frames parent valid fits responseFits decoded parsed
        tables message block blowup constructed step (history past initial step columnIndex world).run columnFirst dummy primitive radius column
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchCausalCoverage
