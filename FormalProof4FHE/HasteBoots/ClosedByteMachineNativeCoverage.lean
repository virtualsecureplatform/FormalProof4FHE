module
public import FormalProof4FHE.HasteBoots.ClosedByteMachineLineage
public import FormalProof4FHE.HasteBoots.NativeGoldBatchCausalCoverage
@[expose] public section

/-! Accepted native false analysis claims in the actual closed interpreter
history enter the already priced source/receipt/field/column branches.
First-read packets and history splits are derived on the instruction clock.
This retains the analysis extractor and explicit native acceptance premises;
public PBS extraction and strict verifier execution refinement remain open. -/
namespace FormalProof4FHE.HasteBoots.ClosedByteMachineNativeCoverage
open NativeGoldBatchPcsProgram (Context Prepared Scheduler)
open NativeGoldBlockCode (Tables logSize)
open NativeGoldBatchChallengeLink (View)
open NativeGoldColumnAuthentication (encoding)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (Input World)
open ClosedByteMachine (Instruction Tape)
open ClosedByteMachineGoldRisk (history)
open ClosedByteMachineRequest (command)
open NativeGoldBatchCausalCoverage (FalseClaim)
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

def Covered (code : List Instruction) (publicData : Input) (privateData : Tape → Input) (machineFuel : ℕ) (world : World)
    (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (radius : ℕ) : Prop :=
    CheckpointAvailability.Disagreement encoding dummy NativeMerkleShapeFamily.shape
      (NativeGoldBatchFamilyAvailability.reconstructed dummy (history code publicData privateData machineFuel world).run.2) ∨
    (∃ index < machineFuel, NativeEarlyReceiptBound.event ctx.parent.profile (command code publicData) (history code publicData privateData index world).run world) ∨
    (∃ index < machineFuel, NativeGoldBatchFieldProximity.event dummy ctx primitive radius ctx.parent.profile (command code publicData)
      (history code publicData privateData index world).run world) ∨
    (∃ index < machineFuel, NativeGoldBatchProfileColumnExposure.event dummy ctx primitive ctx.parent.profile (command code publicData)
      (history code publicData privateData index world).run radius world)

theorem accepted_coverage {Memory : Type} (code : List Instruction) (publicData : Input) (privateData : Tape → Input)
    (machineFuel : ℕ) (world : World)
    (dummy : Digest) (ctx : Context) (work : Prepared)
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (choose : Scheduler Memory) (verifierFuel : ℕ) (memory : Memory)
    (decoded : View)
    (parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world) = some decoded)
    (responseFits : (NativeGoldBatchResponseBinding.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (accepted : NativeGoldBatchAnySourceRisk.Accepted world (history code publicData privateData machineFuel world).run.2 ctx choose verifierFuel memory work)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val)
    (radius : ℕ) (width : 3 ≤ ctx.parameters.width.val)
    (falseClaim : FalseClaim dummy ctx primitive work decoded (history code publicData privateData machineFuel world).run.2 capacity radius) :
    Covered code publicData privateData machineFuel world dummy ctx primitive radius := by
  have truthful := (ClosedByteMachineGoldRisk.history_replay code publicData privateData machineFuel).truthful world
  have nativeAccepted := accepted
  obtain ⟨⟨frames,parent,valid,fits⟩,completion,_,executed,_,_⟩ := accepted
  have prepared := (NativeGoldBatchPcsProgram.completed_origin ctx choose verifierFuel memory world work completion executed).prepared
  have touched := (NativeGoldBatchChallengeHistory.accepted_exposures ctx world work _ choose verifierFuel memory nativeAccepted).1
  obtain ⟨columnIndex,columnLt,columnFirst,_,offset,values,after,positive,split⟩ :=
    ClosedByteMachineLineage.coverage code publicData privateData machineFuel world _ touched
  have acceptedAt : NativeGoldBatchAnySourceRisk.Accepted world
      ((history code publicData privateData columnIndex world).run.2 ++
        .output (NativeGoldBatchColumnRequestLaw.input ctx work world) offset values :: after) ctx choose verifierFuel memory work := by
    rw [← split]
    exact nativeAccepted
  have truthfulAt : ObservationReplay.Agrees world
      ((history code publicData privateData columnIndex world).run.2 ++
        .output (NativeGoldBatchColumnRequestLaw.input ctx work world) offset values :: after) := by
    rw [← split]
    exact truthful
  have falseAt : ∀ sourceLog,
      NativeGoldBatchFirstFieldSource.recover dummy (history code publicData privateData columnIndex world).run.2 decoded.field = some sourceLog →
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
      choose verifierFuel memory (command code publicData) (history code publicData privateData columnIndex world).run columnFirst _ decoded parsed responseFits
      acceptedAt truthfulAt capacity radius width falseAt
  · left
    rw [← split] at failed
    exact failed
  · right; left
    exact ⟨columnIndex,columnLt,early⟩
  · have fieldSeen : CausalStreamExposure.seen (history code publicData privateData columnIndex world).run.2
        (NativeGoldBatchFirstFieldSource.input decoded.field) = true := by
      cases seen : CausalStreamExposure.seen (history code publicData privateData columnIndex world).run.2 (NativeGoldBatchFirstFieldSource.input decoded.field) with
      | true => rfl
      | false =>
        have absent := (NativeGoldBatchFirstFieldSource.recover_none dummy _ decoded.field).mpr seen
        rw [absent] at found
        contradiction
    obtain ⟨fieldIndex,fieldLt,fieldFirst,_,fieldOffset,fieldValues,middle,fieldPositive,fieldSplit⟩ :=
      ClosedByteMachineLineage.coverage code publicData privateData columnIndex world _ fieldSeen
    right; right; left
    refine ⟨fieldIndex,fieldLt.trans columnLt,?_⟩
    exact NativeGoldBatchFieldProximityCoverage.later_proximity dummy ctx world work prepared frames parent valid fits responseFits decoded parsed
        primitive radius (command code publicData) (history code publicData privateData fieldIndex world).run fieldFirst _ sourceLog found fieldOffset fieldValues fieldPositive middle fieldSplit proximity
  · right; right; right
    refine ⟨columnIndex,columnLt,?_⟩
    exact NativeGoldBatchProfileColumnNative.event_of_native ctx world work prepared frames parent valid fits responseFits decoded parsed
      tables message block blowup constructed (command code publicData) (history code publicData privateData columnIndex world).run columnFirst dummy primitive radius column
end
end FormalProof4FHE.HasteBoots.ClosedByteMachineNativeCoverage
