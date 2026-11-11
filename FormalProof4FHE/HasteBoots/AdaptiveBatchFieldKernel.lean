module
public import FormalProof4FHE.HasteBoots.BatchParameterCandidate
@[expose] public section

/-! An attained source family fixes full parameters on the selecting fiber.
All competing original families share one field loss, not a family-size fee. -/
namespace FormalProof4FHE.HasteBoots.AdaptiveBatchFieldKernel
open InputIndexedOracle (Input World law)
open OracleProgram (Program runPrefix)
open NativeRootMessage (Digest)
open BatchParameterCandidate (Candidate)
open MeasureTheory ProbabilityTheory
noncomputable section

def rate : ENNReal := (17 : ENNReal)/2^141

def Occurs {A : Type} (program : Program A) (position : ℕ) (profile dummy : Digest) (world : World) : Prop :=
  ∃ candidate : Candidate program position profile world,
    NativeGoldBatchFieldProximity.event dummy candidate.ctx (candidate.origin.primitiveAt _ rfl)
      (NativeBrakedownCalibration.radius .goldilocks candidate.role) profile OracleProgramMachine.step
      (runPrefix position program world).run world

def Event {A : Type} (program : Program A) (position : ℕ) (profile dummy : Digest) (world : World) : Prop :=
  Occurs program position profile dummy world ∧ ¬GlobalReferenceBad.Bad program dummy world

def score {A : Type} (packet : (Program A ⊕ A) × List NativeTranscript.Observation) : ENNReal :=
  match NativeGoldBatchFieldExposure.select OracleProgramMachine.step packet with
  | none => 0
  | some _ => rate

theorem conditional {A : Type} (program : Program A) (position : ℕ) (profile dummy : Digest) (world : World) :
    (law[|{other | (runPrefix position program other).run = (runPrefix position program world).run}])
      {other | Event program position profile dummy other} ≤ score (runPrefix position program world).run := by
  let replay := OracleProgram.prefix_replay position program
  by_cases attained : ∃ reference, (runPrefix position program reference).run = (runPrefix position program world).run ∧
      Event program position profile dummy reference
  · obtain ⟨reference,same,⟨⟨candidate,_⟩,safe⟩⟩ := attained
    have chosen := BatchParameterCandidate.selected candidate
    rw [same] at chosen
    simp only [score,chosen]
    have included := FactorPosteriorMismatch.conditional_mono replay world
      (Event program position profile dummy)
      (fun other => NativeGoldBatchFieldProximity.event dummy candidate.ctx (candidate.origin.primitiveAt _ rfl)
        (NativeBrakedownCalibration.radius .goldilocks candidate.role) profile OracleProgramMachine.step
        (runPrefix position program other).run other) (by
        intro other fiber occurred
        obtain ⟨⟨competing,proximity⟩,otherSafe⟩ := occurred
        have parameters := BatchParameterCandidate.parameters program position profile dummy reference other candidate competing
          (fiber.trans same.symm) safe otherSafe
        have radius := BatchParameterCandidate.radius_eq candidate competing parameters
        have moved := (NativeGoldBatchEventContext.field_event dummy competing.ctx candidate.ctx parameters.symm
          (competing.origin.primitiveAt _ rfl) (candidate.origin.primitiveAt _ rfl)
          (NativeBrakedownCalibration.radius .goldilocks competing.role) profile OracleProgramMachine.step _ other).mp proximity
        rw [← radius] at moved
        exact moved)
    have dimensions := NativeGoldBatchCalibration.radius_valid candidate.ctx candidate.origin.tables candidate.origin.request.message
      candidate.origin.request.block candidate.origin.request.blowup (candidate.origin.constructedAt _ rfl)
      (candidate.origin.primitiveAt _ rfl) candidate.role candidate.admitted
    have bounded := NativeGoldBatchFieldProximity.conditional_bound dummy candidate.ctx (candidate.origin.primitiveAt _ rfl)
      (NativeBrakedownCalibration.radius .goldilocks candidate.role) profile OracleProgramMachine.step replay world dimensions.1 dimensions.2
    have loss := NativeGoldBatchCalibration.loss_bound candidate.ctx candidate.origin.tables candidate.origin.request.message
      candidate.origin.request.block candidate.origin.request.blowup (candidate.origin.constructedAt _ rfl)
      (candidate.origin.primitiveAt _ rfl) candidate.role candidate.admitted
    exact included.trans (bounded.trans ((NativeGoldBatchCalibration.field_risk_le_loss dummy candidate.ctx _ _ _ _).trans
      ((le_add_of_nonneg_right (by exact zero_le)).trans loss)))
  · have included := FactorPosteriorMismatch.conditional_mono replay world
      (Event program position profile dummy) (fun _ => False) (by
        intro other fiber occurred
        exact attained ⟨other,fiber,occurred⟩)
    have zero : (law[|{other | (runPrefix position program other).run = (runPrefix position program world).run}])
        {other | Event program position profile dummy other} ≤ 0 := by simpa only [Set.ofPred_false,measure_empty] using included
    exact zero.trans (by exact zero_le)

theorem position_bound {A : Type} (program : Program A) (position : ℕ) (profile dummy : Digest) :
    law {world | Event program position profile dummy world} ≤ ∫⁻ world, score (runPrefix position program world).run ∂law :=
  OracleFiberOuterBound.score_bound (OracleProgram.prefix_replay position program) _ score
    (conditional program position profile dummy)

def totalCharge {A : Type} (program : Program A) (world : World) : ENNReal :=
  ∑' position : ℕ, score (runPrefix position program world).run

theorem safe_lifetime_bound {A : Type} (program : Program A) (profile dummy : Digest) :
    law {world | ∃ position, Event program position profile dummy world} ≤ ∫⁻ world, totalCharge program world ∂law := by
  have union : {world | ∃ position, Event program position profile dummy world} = ⋃ position : ℕ,
      {world | Event program position profile dummy world} := by ext world; simp
  rw [union]
  calc
    _ ≤ ∑' position : ℕ, law {world | Event program position profile dummy world} := measure_iUnion_le _
    _ ≤ ∑' position : ℕ, ∫⁻ world, score (runPrefix position program world).run ∂law :=
      ENNReal.tsum_le_tsum (fun position => position_bound program position profile dummy)
    _ = _ := (lintegral_tsum (fun position =>
      (OracleExecutionLaw.score_measurable (OracleProgram.prefix_replay position program) score).aemeasurable)).symm

theorem score_le {A : Type} (packet : (Program A ⊕ A) × List NativeTranscript.Observation) : score packet ≤ rate := by
  unfold score
  split <;> simp

theorem score_absent {A : Type} (packet : (Program A ⊕ A) × List NativeTranscript.Observation)
    (absent : CausalSeedExposure.request OracleProgramMachine.step packet.1 = none) : score packet = 0 := by
  simp only [score,NativeGoldBatchFieldExposure.select,CausalStreamExposure.firstRead,absent,Option.bind_none]

theorem total_le_log {A : Type} (program : Program A) (world : World) : totalCharge program world ≤
    (OracleProgram.run program world).run.2.length * rate :=
  ProgramObservationClock.score_sum program world score rate score_le score_absent

theorem occurs_extend {A B : Type} (program : Program A) (next : A → Program B) (position : ℕ) (profile dummy : Digest) (world : World)
    (occurred : Occurs program position profile dummy world) : Occurs (OracleProgram.bind program next) position profile dummy world := by
  obtain ⟨candidate,proximity⟩ := occurred
  let extended := BatchParameterCandidate.extend candidate next
  refine ⟨extended,?_⟩
  have same : (runPrefix position (OracleProgram.bind program next) world).run.2 = (runPrefix position program world).run.2 := by
    rw [← candidate.atFirst]
    exact congrArg Prod.snd (ProgramContinuationPrefix.active_bind program next candidate.first.position world _ candidate.first.active)
  unfold NativeGoldBatchFieldProximity.event NativeGoldBatchFieldExposure.event at proximity ⊢
  rw [BatchParameterCandidate.selected candidate] at proximity
  rw [BatchParameterCandidate.selected extended]
  change (∃ fuel, (NativeFieldVectorLaw.values NativeFields.goldilocksModulus fuel candidate.field.count.val
    (candidate.field.phase profile) world).elim False (NativeGoldBatchFieldProximity.bad dummy candidate.ctx
      (candidate.origin.primitiveAt _ rfl) (NativeBrakedownCalibration.radius .goldilocks candidate.role)
      (runPrefix position (OracleProgram.bind program next) world).run.2 candidate.field))
  rw [same]
  exact proximity

theorem private_prefix_bound (code : List PrivateCoinByteMachine.Instruction) (publicData : Input) (tape : PrivateCoinReplay.Tape)
    (privateData : ClosedByteMachine.Tape → Input) (fuel : ℕ) (profile dummy : Digest) :
    law {world | ∃ position, Event (InterpreterScalarLifetime.privateProgram code publicData tape privateData fuel) position profile dummy world} ≤
      PrivateCoinByteFixed.expectedWork code publicData tape privateData * rate := by
  apply (safe_lifetime_bound _ profile dummy).trans
  calc
    _ ≤ ∫⁻ world, PrivateCoinByteFixed.lifetimeWork code publicData tape privateData world * rate ∂law := by
      apply lintegral_mono
      intro world
      apply (total_le_log _ world).trans
      apply mul_le_mul' _ le_rfl
      exact (Nat.cast_le.mpr (PrivateCoinByteLogWork.log_le_work code publicData tape fuel _ world)).trans
        (le_iSup (fun index => PrivateCoinByteWork.prefixWork code publicData privateData index (tape,world)) fuel)
    _ = _ := lintegral_mul_const rate (PrivateCoinByteFixed.lifetimeWork_measurable code publicData tape privateData)

end
end FormalProof4FHE.HasteBoots.AdaptiveBatchFieldKernel
