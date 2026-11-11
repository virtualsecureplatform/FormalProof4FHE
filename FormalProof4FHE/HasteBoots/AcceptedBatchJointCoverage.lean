module
public import FormalProof4FHE.HasteBoots.AcceptedBatchColumnCandidate
@[expose] public section

/-! Original native accepted false claims cover the adaptive field and column events.
Hash and early receipt alternatives remain explicit. -/
namespace FormalProof4FHE.HasteBoots.AcceptedBatchJointCoverage
open InputIndexedOracle (World)
open OracleProgram (Program run runPrefix)
open NativeGoldBatchPcsProgram (Context Prepared Scheduler)
open NativeGoldBlockCode (logSize)
open NativeRootMessage (Digest)
open NativeGoldBatchChallengeLink (View)
open NativeGoldBatchCausalCoverage (FalseClaim)
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

def Covered {A : Type} (program : Program A) (world : World) (dummy : Digest) (profile : Digest) : Prop :=
  CheckpointAvailability.Disagreement NativeGoldColumnAuthentication.encoding dummy NativeMerkleShapeFamily.shape
    (NativeGoldBatchFamilyAvailability.reconstructed dummy (run program world).run.2) ∨
  (∃ position, NativeEarlyReceiptBound.event profile OracleProgramMachine.step (runPrefix position program world).run world) ∨
  (∃ position, AdaptiveBatchFieldKernel.Occurs program position profile dummy world) ∨
  ∃ position, AdaptiveBatchColumnKernel.Occurs program position profile dummy world

theorem accepted_coverage {A Memory : Type} (program : Program A) (world : World)
    (dummy : Digest) (ctx : Context) (work : Prepared) (origin : CacheBackedCodeOrigin.Origin ctx)
    (role : NativeBrakedownCalibration.Role) (admitted : NativeGoldBatchCalibration.Matches ctx role)
    (choose : Scheduler Memory) (verifierFuel : ℕ) (memory : Memory) (decoded : View)
    (parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world) = some decoded)
    (responseFits : (NativeGoldBatchResponseBinding.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (accepted : NativeGoldBatchAnySourceRisk.Accepted world (run program world).run.2 ctx choose verifierFuel memory work)
    (falseClaim : FalseClaim dummy ctx (origin.primitiveAt ctx rfl) work decoded (run program world).run.2
      (origin.capacityAt ctx rfl) (NativeBrakedownCalibration.radius .goldilocks role)) :
    Covered program world dummy ctx.parent.profile := by
  let primitive := origin.primitiveAt ctx rfl
  let radius := NativeBrakedownCalibration.radius .goldilocks role
  let capacity := origin.capacityAt ctx rfl
  let tables := origin.tables
  let message := origin.request.message
  let block := origin.request.block
  let blowup := origin.request.blowup
  have constructed := origin.constructedAt ctx rfl
  have width : 3 ≤ ctx.parameters.width.val := by
    rw [admitted.width]
    cases role <;> decide +kernel
  have truthful := (OracleProgram.run_replay program).truthful world
  have nativeAccepted := accepted
  obtain ⟨⟨frames,parent,valid,fits⟩,completion,_,executed,_,_⟩ := accepted
  have prepared := (NativeGoldBatchPcsProgram.completed_origin ctx choose verifierFuel memory world work completion executed).prepared
  have touched := (NativeGoldBatchChallengeHistory.accepted_exposures ctx world work _ choose verifierFuel memory nativeAccepted).1
  obtain ⟨columnIndex,columnLt,columnFirst,offset,values,after,positive,split⟩ :=
    ProgramStreamReadCoverage.coverage program world _ touched
  have acceptedAt : NativeGoldBatchAnySourceRisk.Accepted world
      ((runPrefix columnIndex program world).run.2 ++
        .output (NativeGoldBatchColumnRequestLaw.input ctx work world) offset values :: after) ctx choose verifierFuel memory work := by
    rw [← split]
    exact nativeAccepted
  have truthfulAt : ObservationReplay.Agrees world
      ((runPrefix columnIndex program world).run.2 ++
        .output (NativeGoldBatchColumnRequestLaw.input ctx work world) offset values :: after) := by
    rw [← split]
    exact truthful
  have falseAt : ∀ sourceLog,
      NativeGoldBatchFirstFieldSource.recover dummy (runPrefix columnIndex program world).run.2 decoded.field = some sourceLog →
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
      choose verifierFuel memory OracleProgramMachine.step (runPrefix columnIndex program world).run columnFirst _ decoded parsed responseFits
      acceptedAt truthfulAt capacity radius width falseAt
  · left
    rw [← split] at failed
    exact failed
  · right; left
    exact ⟨columnIndex,early⟩
  · have fieldSeen : CausalStreamExposure.seen (runPrefix columnIndex program world).run.2
        (NativeGoldBatchFirstFieldSource.input decoded.field) = true := by
      cases seen : CausalStreamExposure.seen (runPrefix columnIndex program world).run.2 (NativeGoldBatchFirstFieldSource.input decoded.field) with
      | true => rfl
      | false =>
        have absent := (NativeGoldBatchFirstFieldSource.recover_none dummy _ decoded.field).mpr seen
        rw [absent] at found
        contradiction
    obtain ⟨fieldIndex,fieldLt,fieldFirst,fieldOffset,fieldValues,middle,fieldPositive,fieldSplit⟩ :=
      ProgramStreamReadCoverage.prefix_coverage program world columnIndex _ fieldSeen
    right; right; left
    refine ⟨fieldIndex,?_⟩
    apply AcceptedBatchFieldCandidate.occurs program world fieldIndex dummy ctx origin role admitted choose verifierFuel memory work decoded parsed responseFits nativeAccepted fieldFirst
    exact NativeGoldBatchFieldProximityCoverage.later_proximity dummy ctx world work prepared frames parent valid fits responseFits decoded parsed
        primitive radius OracleProgramMachine.step (runPrefix fieldIndex program world).run fieldFirst _ sourceLog found fieldOffset fieldValues fieldPositive middle fieldSplit proximity
  · right; right; right
    refine ⟨columnIndex,?_⟩
    apply AcceptedBatchColumnCandidate.occurs program world columnIndex dummy ctx origin role admitted choose verifierFuel memory work decoded parsed responseFits nativeAccepted columnFirst
    exact NativeGoldBatchProfileColumnNative.event_of_native ctx world work prepared frames parent valid fits responseFits decoded parsed
      tables message block blowup constructed OracleProgramMachine.step (runPrefix columnIndex program world).run columnFirst dummy primitive radius column
end
end FormalProof4FHE.HasteBoots.AcceptedBatchJointCoverage
