module
public import FormalProof4FHE.HasteBoots.PrivateCoinByteNativeCoverage
public import FormalProof4FHE.HasteBoots.PrivateCoinExecutableSoundness
@[expose] public section

/-! Executable-extractor failures on runtime-coin histories are jointly
measurable and covered by the source/receipt/field/column hazards of that same
execution. Hazard pricing on this extension is still a separate connection. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinByteFailure
open MeasureTheory
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open NativeBrakedownCalibration (radius)
open NativeGoldBlockCode (logSize)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction initialise take)
open PrivateCoinByteLineage (history history_run packet history_replay)
open PrivateCoinByteRequest (command)
open PrivateCoinExecutableSoundness (Target)
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

def Failure (Memory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (target : Target)
    (execution : Tape × World) : Prop :=
  ∃ fuel, Nonempty (ClosedByteMachineExecutableSoundness.Witness Memory dummy target.ctx
    (radius .goldilocks target.role) execution.2 (history code publicData privateData execution.1 fuel execution.2).run.2)

def Hazards (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (dummy : Digest) (target : Target) (execution : Tape × World) : Prop :=
  (∃ fuel, NativeRootFamilyLifetime.Bad dummy (history code publicData privateData execution.1 fuel execution.2).run.2) ∨
  ∃ fuel, NativeEarlyReceiptBound.event target.ctx.parent.profile (command code publicData execution.1)
      (history code publicData privateData execution.1 fuel execution.2).run execution.2 ∨
    NativeGoldBatchFieldProximity.event dummy target.ctx target.primitive (radius .goldilocks target.role)
      target.ctx.parent.profile (command code publicData execution.1)
      (history code publicData privateData execution.1 fuel execution.2).run execution.2 ∨
    NativeGoldBatchProfileColumnExposure.event dummy target.ctx target.primitive target.ctx.parent.profile
      (command code publicData execution.1) (history code publicData privateData execution.1 fuel execution.2).run
      (radius .goldilocks target.role) execution.2

theorem witness_iff_analysis (Memory : Type) (dummy : Digest) (target : Target) (world : World) (log : List Observation) :
    Nonempty (ClosedByteMachineExecutableSoundness.Witness Memory dummy target.ctx (radius .goldilocks target.role) world log) ↔
      Nonempty (NativeGoldBatchLifetimeSoundness.Witness Memory dummy target.ctx (radius .goldilocks target.role) world log) := by
  have unique : 2 * radius .goldilocks target.role <
      2^(logSize target.ctx.parameters.code)-target.ctx.parameters.code.messageBlocks.val+1 := by
    rw [target.compatible.height, target.compatible.message]
    cases target.role <;> decide +kernel
  constructor
  · rintro ⟨witness⟩
    have built : NativeGoldBlockCode.build target.tables target.message target.block target.blowup =
        .ok witness.candidate.parameters.code := by rw [witness.sameParameters]; exact target.constructed
    have distinct : 2 * radius .goldilocks target.role <
        2^(logSize witness.candidate.parameters.code)-witness.candidate.parameters.code.messageBlocks.val+1 := by
      rwa [witness.sameParameters]
    exact ⟨ClosedByteMachineExecutableSoundness.toAnalysis witness target.tables target.message target.block target.blowup built distinct⟩
  · rintro ⟨witness⟩
    have built : NativeGoldBlockCode.build target.tables target.message target.block target.blowup =
        .ok witness.candidate.parameters.code := by rw [witness.sameParameters]; exact target.constructed
    have distinct : 2 * radius .goldilocks target.role <
        2^(logSize witness.candidate.parameters.code)-witness.candidate.parameters.code.messageBlocks.val+1 := by
      rwa [witness.sameParameters]
    exact ⟨ClosedByteMachineExecutableSoundness.ofAnalysis witness target.tables target.message target.block target.blowup built distinct⟩

theorem failure_covered (Memory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (target : Target)
    (execution : Tape × World) (failed : Failure Memory code publicData privateData dummy target execution) :
    Hazards code publicData privateData dummy target execution := by
  obtain ⟨fuel, executable⟩ := failed
  obtain ⟨witness⟩ := (witness_iff_analysis Memory dummy target execution.2 _).mp executable
  have built : NativeGoldBlockCode.build target.tables target.message target.block target.blowup =
      .ok witness.candidate.parameters.code := by rw [witness.sameParameters]; exact target.constructed
  have width : 3 ≤ witness.candidate.parameters.width.val := by
    rw [witness.sameParameters, target.compatible.width]
    cases target.role <;> decide +kernel
  have covered := PrivateCoinByteNativeCoverage.accepted_coverage code publicData privateData execution.1 fuel execution.2
    dummy witness.candidate witness.work target.tables target.message target.block target.blowup built witness.primitive
    witness.choose witness.verifierFuel witness.memory witness.decoded witness.parsed witness.responseFits witness.accepted
    witness.capacity (radius .goldilocks target.role) width witness.falseClaim
  rcases covered with different | early | field | column
  · left
    have audit := NativeRootFamilyAudit.disagreement_implies_bad dummy execution.2 _
      ((history_replay code publicData privateData execution.1 fuel).truthful execution.2)
    have decisions : (fun first second : Digest => Fintype.decidablePiFintype first second) =
        (inferInstance : DecidableEq Digest) := Subsingleton.elim _ _
    rw [decisions] at audit
    exact ⟨fuel, audit different⟩
  · obtain ⟨index, _, event⟩ := early
    rw [witness.sameProfile] at event
    exact Or.inr ⟨index, Or.inl event⟩
  · obtain ⟨index, _, event⟩ := field
    have transferred := (NativeGoldBatchEventContext.field_event dummy witness.candidate target.ctx witness.sameParameters
      witness.primitive target.primitive (radius .goldilocks target.role) witness.candidate.parent.profile
      (command code publicData execution.1) _ execution.2).mp event
    rw [witness.sameProfile] at transferred
    exact Or.inr ⟨index, Or.inr (Or.inl transferred)⟩
  · obtain ⟨index, _, event⟩ := column
    have transferred := (NativeGoldBatchEventContext.profile_column_event dummy witness.candidate target.ctx witness.sameParameters
      witness.primitive target.primitive (radius .goldilocks target.role) witness.candidate.parent.profile
      (command code publicData execution.1) _ execution.2).mp event
    rw [witness.sameProfile] at transferred
    exact Or.inr ⟨index, Or.inr (Or.inr transferred)⟩

theorem finite_measurable (Memory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (target : Target) (fuel : ℕ) :
    MeasurableSet {execution : Tape × World | Nonempty (ClosedByteMachineExecutableSoundness.Witness Memory dummy target.ctx
      (radius .goldilocks target.role) execution.2 (history code publicData privateData execution.1 fuel execution.2).run.2)} := by
  have equal : {execution : Tape × World | Nonempty (ClosedByteMachineExecutableSoundness.Witness Memory dummy target.ctx
      (radius .goldilocks target.role) execution.2 (history code publicData privateData execution.1 fuel execution.2).run.2)} =
      {execution : Tape × World | NativeGoldBatchLifetimeMeasurable.HistoryFailure Memory dummy target.ctx
        (radius .goldilocks target.role) (history code publicData privateData execution.1 fuel execution.2).run.2} := by
    ext execution
    exact (witness_iff_analysis Memory dummy target execution.2 _).trans
      (NativeGoldBatchLifetimeMeasurable.witness_iff_history Memory dummy target.ctx (radius .goldilocks target.role) _ _
        ((history_replay code publicData privateData execution.1 fuel).truthful execution.2))
  rw [equal]
  simpa only [history_run, packet] using
    PrivateCoinScores.event_measurable (fun _ => OracleProgram.run_replay _)
      (PrivateCoinByteMachine.take_finiteResult code publicData fuel (initialise code privateData))
      (fun result => NativeGoldBatchLifetimeMeasurable.HistoryFailure Memory dummy target.ctx (radius .goldilocks target.role) result.2)

theorem failure_measurable (Memory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (target : Target) :
    MeasurableSet {execution | Failure Memory code publicData privateData dummy target execution} := by
  have union : {execution | Failure Memory code publicData privateData dummy target execution} =
      ⋃ fuel : ℕ, {execution : Tape × World | Nonempty (ClosedByteMachineExecutableSoundness.Witness Memory dummy target.ctx
        (radius .goldilocks target.role) execution.2 (history code publicData privateData execution.1 fuel execution.2).run.2)} := by
    ext execution
    simp [Failure]
  rw [union]
  exact MeasurableSet.iUnion (finite_measurable Memory code publicData privateData dummy target)
end
end FormalProof4FHE.HasteBoots.PrivateCoinByteFailure
