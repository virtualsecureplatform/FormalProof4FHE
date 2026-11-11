module
public import FormalProof4FHE.HasteBoots.SingleOpeningFirstColumnCoverage
public import FormalProof4FHE.HasteBoots.CausalStreamLineage
public import FormalProof4FHE.HasteBoots.SingleOpeningChallengeHistory
@[expose] public section

/-! Actual accepted false single openings in complete causal histories enter
inherited, disagreement, early-receipt, field or column branches. Earlier
packets and first-read splits are derived from the machine, not supplied.
Falsity is against the common-source analysis extractor, not full PBS semantics. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningCausalCoverage
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open NativeGoldPcsProgram (Scheduler)
open NativeGoldColumnAuthentication (encoding)
open NativeRootMessage (Digest)
open NativeTranscript (Observation Execution)
open InputIndexedOracle (World)
open CausalExposureLifetime (history)
open SingleOpeningChallengeLink (View)
open SingleOpeningConcreteColumnFamily (source Domain)
open SingleOpeningFixedResponseData (left right claimed)
open OracleProgram (run)
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

def FalseClaim (dummy : Digest) (ctx : Context) (origin : CacheBackedSingleOpening.Origin ctx)
    (decoded : View) (log : List Observation) (radius : ℕ) : Prop :=
  ∀ sourceLog, SingleOpeningFirstFieldSource.recover dummy log decoded.field = some sourceLog →
    claimed ctx decoded.field.data.claimed ≠ matrixEvaluation (left ctx.parameters decoded.field.data.query)
      (right ctx.parameters decoded.field.data.query)
      (RectangularMatrixOpeningKernel.extract (Domain ctx origin.primitive) origin.capacity radius (source dummy ctx decoded sourceLog))

def Covered {P S A : Type} (past : World → Execution P) (initial : P → S)
    (step : S → OracleMachine.Command S A) (machineFuel : ℕ) (world : World) (dummy : Digest)
    {ctx : Context} {work : Prepared} {sample : NativeIndexRequest.Result}
    (receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample) (decoded : View)
    (origin : CacheBackedSingleOpening.Origin ctx) (radius : ℕ) : Prop :=
  CausalStreamExposure.seen (past world).run.2 (SingleOpeningColumnLaw.input receipt world) = true ∨
  CausalStreamExposure.seen (past world).run.2 (SingleOpeningFirstFieldSource.input decoded.field) = true ∨
  CheckpointAvailability.Disagreement encoding dummy NativeMerkleShapeFamily.shape
    (NativeGoldBatchFamilyAvailability.reconstructed dummy (history past initial step machineFuel world).run.2) ∨
  (∃ index < machineFuel, SingleOpeningEarlyReceiptBound.event ctx.transcript.profile step (history past initial step index world).run world) ∨
  (∃ index < machineFuel, SingleOpeningFieldProximity.event dummy ctx origin.primitive radius ctx.transcript.profile step
    (history past initial step index world).run world) ∨
  (∃ index < machineFuel, SingleOpeningProfileColumnExposure.event dummy ctx origin.primitive ctx.transcript.profile step
    (history past initial step index world).run radius world)

theorem accepted_coverage {P S A Memory : Type} (past : World → Execution P) (replay : ObservationReplay.Replayable past)
    (initial : P → S) (step : S → OracleMachine.Command S A) (machineFuel : ℕ) (world : World) (dummy : Digest)
    {ctx : Context} {work : Prepared} {sample : NativeIndexRequest.Result}
    (receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample) (origin : CacheBackedSingleOpening.Origin ctx)
    (choose : Scheduler Memory) (verifierFuel : ℕ) (memory : Memory) (decoded : View)
    (parsed : SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input receipt world) = some decoded)
    (responseFits : (SingleOpeningColumnLaw.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (accepted : SingleOpeningAvailability.Accepted world (history past initial step machineFuel world).run.2 ctx choose verifierFuel memory work)
    (radius : ℕ) (width : 3 ≤ ctx.parameters.width.val)
    (falseClaim : FalseClaim dummy ctx origin decoded (history past initial step machineFuel world).run.2 radius) :
    Covered past initial step machineFuel world dummy receipt decoded origin radius := by
  have truthful := (CausalExposureLifetime.history_replay replay initial step machineFuel).truthful world
  have nativeAccepted := accepted
  obtain ⟨⟨frames,parent,valid,fits⟩,completion,_,executed,_,_⟩ := accepted
  have prepared := (NativeGoldPcsProgram.completed_origin ctx choose verifierFuel memory world work completion executed).prepared
  have touched := (SingleOpeningChallengeHistory.accepted_exposures receipt _ choose verifierFuel memory nativeAccepted).1
  obtain inherited | ⟨columnIndex,columnLt,columnFirst,_,offset,values,after,_,split⟩ :=
    CausalStreamLineage.coverage past initial step machineFuel world _ touched
  · exact Or.inl inherited
  · have acceptedAt : SingleOpeningAvailability.Accepted world
        ((history past initial step columnIndex world).run.2 ++
          .output (SingleOpeningColumnLaw.input receipt world) offset values :: after) ctx choose verifierFuel memory work := by
      rw [← split]
      exact nativeAccepted
    have truthfulAt : ObservationReplay.Agrees world
        ((history past initial step columnIndex world).run.2 ++
          .output (SingleOpeningColumnLaw.input receipt world) offset values :: after) := by
      rw [← split]
      exact truthful
    have falseAt : ∀ sourceLog, SingleOpeningFirstFieldSource.recover dummy
        (history past initial step columnIndex world).run.2 decoded.field = some sourceLog →
        claimed ctx decoded.field.data.claimed ≠ matrixEvaluation (left ctx.parameters decoded.field.data.query)
          (right ctx.parameters decoded.field.data.query)
          (RectangularMatrixOpeningKernel.extract (Domain ctx origin.primitive) origin.capacity radius (source dummy ctx decoded sourceLog)) := by
      intro sourceLog found
      apply falseClaim sourceLog
      rw [split]
      exact SingleOpeningFirstFieldSource.recover_append dummy _ _ decoded.field sourceLog found
    obtain failed | early | ⟨sourceLog,found,column | proximity⟩ :=
      SingleOpeningFirstColumnCoverage.accepted_first_column_cover dummy receipt origin choose verifierFuel memory step
        (history past initial step columnIndex world).run columnFirst _ decoded parsed responseFits acceptedAt truthfulAt radius width falseAt
    · right; right; left
      rw [← split] at failed
      exact failed
    · right; right; right; left
      exact ⟨columnIndex,columnLt,early⟩
    · right; right; right; right; right
      exact ⟨columnIndex,columnLt,column⟩
    · have fieldSeen : CausalStreamExposure.seen (history past initial step columnIndex world).run.2
          (SingleOpeningFirstFieldSource.input decoded.field) = true := by
        cases seen : CausalStreamExposure.seen (history past initial step columnIndex world).run.2 (SingleOpeningFirstFieldSource.input decoded.field) with
        | true => rfl
        | false =>
          have absent := (SingleOpeningFirstFieldSource.recover_none dummy _ decoded.field).mpr seen
          rw [absent] at found
          contradiction
      obtain inheritedField | ⟨fieldIndex,fieldLt,fieldFirst,_,fieldOffset,fieldValues,middle,fieldPositive,fieldSplit⟩ :=
        CausalStreamLineage.coverage past initial step columnIndex world _ fieldSeen
      · exact Or.inr (Or.inl inheritedField)
      · right; right; right; right; left
        refine ⟨fieldIndex,fieldLt.trans columnLt,?_⟩
        exact SingleOpeningFieldProximityCoverage.later_proximity dummy receipt prepared frames parent valid fits responseFits decoded parsed
          origin.primitive radius step (history past initial step fieldIndex world).run fieldFirst _ sourceLog found
            fieldOffset fieldValues fieldPositive middle fieldSplit proximity

end
end FormalProof4FHE.HasteBoots.SingleOpeningCausalCoverage
