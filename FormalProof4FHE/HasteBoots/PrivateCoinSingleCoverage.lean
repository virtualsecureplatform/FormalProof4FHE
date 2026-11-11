module
public import FormalProof4FHE.HasteBoots.PrivateCoinOpeningWitness
public import FormalProof4FHE.HasteBoots.PrivateCoinHelperGoldRisk
@[expose] public section

/-! Accepted helper single openings enter actual runtime instruction hazards.
First reads are recovered from the original mixed log, including silent steps. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinSingleCoverage
open InputIndexedOracle (Input World)
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open NativeGoldPcsProgram (Scheduler)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction)
open PrivateCoinByteLineage (history)
open PrivateCoinByteRequest (command)
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

def Covered (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (tape : Tape)
    (fuel : ℕ) (world : World) (dummy : Digest) (ctx : Context) (origin : CacheBackedSingleOpening.Origin ctx) (radius : ℕ) : Prop :=
  CheckpointAvailability.Disagreement NativeGoldColumnAuthentication.encoding dummy NativeMerkleShapeFamily.shape
    (NativeGoldBatchFamilyAvailability.reconstructed dummy (history code publicData privateData tape fuel world).run.2) ∨
  (∃ index < fuel, SingleOpeningEarlyReceiptBound.event ctx.transcript.profile (command code publicData tape) (history code publicData privateData tape index world).run world) ∨
  (∃ index < fuel, SingleOpeningFieldProximity.event dummy ctx origin.primitive radius ctx.transcript.profile (command code publicData tape)
    (history code publicData privateData tape index world).run world) ∨
  ∃ index < fuel, SingleOpeningProfileColumnExposure.event dummy ctx origin.primitive ctx.transcript.profile (command code publicData tape)
    (history code publicData privateData tape index world).run radius world

theorem accepted_coverage {Memory : Type} (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (tape : Tape) (fuel : ℕ) (world : World) (dummy : Digest)
    {ctx : Context} {work : Prepared} {sample : NativeIndexRequest.Result}
    (receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample) (origin : CacheBackedSingleOpening.Origin ctx)
    (choose : Scheduler Memory) (verifierFuel : ℕ) (memory : Memory) (decoded : SingleOpeningChallengeLink.View)
    (parsed : SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input receipt world) = some decoded)
    (responseFits : (SingleOpeningColumnLaw.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (accepted : SingleOpeningAvailability.Accepted world (history code publicData privateData tape fuel world).run.2 ctx choose verifierFuel memory work)
    (radius : ℕ) (width : 3 ≤ ctx.parameters.width.val)
    (falseClaim : SingleOpeningCausalCoverage.FalseClaim dummy ctx origin decoded (history code publicData privateData tape fuel world).run.2 radius) :
    Covered code publicData privateData tape fuel world dummy ctx origin radius := by
  have truthful := (PrivateCoinByteLineage.history_replay code publicData privateData tape fuel).truthful world
  have nativeAccepted := accepted
  obtain ⟨⟨frames,parent,valid,fits⟩,completion,_,executed,_,_⟩ := accepted
  have prepared := (NativeGoldPcsProgram.completed_origin ctx choose verifierFuel memory world work completion executed).prepared
  have touched := (SingleOpeningChallengeHistory.accepted_exposures receipt _ choose verifierFuel memory nativeAccepted).1
  obtain ⟨columnIndex,columnLt,columnFirst,_,offset,values,after,_,split⟩ :=
    PrivateCoinByteLineage.coverage code publicData privateData tape fuel world _ touched
  have acceptedAt : SingleOpeningAvailability.Accepted world
      ((history code publicData privateData tape columnIndex world).run.2 ++
        .output (SingleOpeningColumnLaw.input receipt world) offset values :: after) ctx choose verifierFuel memory work := by
    rw [← split]
    exact nativeAccepted
  have truthfulAt : ObservationReplay.Agrees world
      ((history code publicData privateData tape columnIndex world).run.2 ++
        .output (SingleOpeningColumnLaw.input receipt world) offset values :: after) := by
    rw [← split]
    exact truthful
  have falseAt : ∀ sourceLog, SingleOpeningFirstFieldSource.recover dummy
      (history code publicData privateData tape columnIndex world).run.2 decoded.field = some sourceLog →
      SingleOpeningFixedResponseData.claimed ctx decoded.field.data.claimed ≠ matrixEvaluation
        (SingleOpeningFixedResponseData.left ctx.parameters decoded.field.data.query)
        (SingleOpeningFixedResponseData.right ctx.parameters decoded.field.data.query)
        (RectangularMatrixOpeningKernel.extract (SingleOpeningConcreteColumnFamily.Domain ctx origin.primitive) origin.capacity radius
          (SingleOpeningConcreteColumnFamily.source dummy ctx decoded sourceLog)) := by
    intro sourceLog found
    apply falseClaim sourceLog
    rw [split]
    exact SingleOpeningFirstFieldSource.recover_append dummy _ _ decoded.field sourceLog found
  obtain failed | early | ⟨sourceLog,found,column | proximity⟩ := SingleOpeningFirstColumnCoverage.accepted_first_column_cover dummy receipt origin
    choose verifierFuel memory (command code publicData tape) (history code publicData privateData tape columnIndex world).run columnFirst _ decoded parsed responseFits
    acceptedAt truthfulAt radius width falseAt
  · left
    rw [← split] at failed
    exact failed
  · right; left
    exact ⟨columnIndex,columnLt,early⟩
  · right; right; right
    exact ⟨columnIndex,columnLt,column⟩
  · have seen : CausalStreamExposure.seen (history code publicData privateData tape columnIndex world).run.2
        (SingleOpeningFirstFieldSource.input decoded.field) = true := by
      cases seen : CausalStreamExposure.seen (history code publicData privateData tape columnIndex world).run.2 (SingleOpeningFirstFieldSource.input decoded.field) with
      | true => rfl
      | false =>
        have absent := (SingleOpeningFirstFieldSource.recover_none dummy _ decoded.field).mpr seen
        rw [absent] at found
        contradiction
    obtain ⟨fieldIndex,fieldLt,fieldFirst,_,fieldOffset,fieldValues,middle,fieldPositive,fieldSplit⟩ :=
      PrivateCoinByteLineage.coverage code publicData privateData tape columnIndex world _ seen
    right; right; left
    exact ⟨fieldIndex,fieldLt.trans columnLt,SingleOpeningFieldProximityCoverage.later_proximity dummy receipt prepared frames parent valid fits responseFits decoded parsed
      origin.primitive radius (command code publicData tape) (history code publicData privateData tape fieldIndex world).run fieldFirst _ sourceLog found
        fieldOffset fieldValues fieldPositive middle fieldSplit proximity⟩

end
end FormalProof4FHE.HasteBoots.PrivateCoinSingleCoverage
