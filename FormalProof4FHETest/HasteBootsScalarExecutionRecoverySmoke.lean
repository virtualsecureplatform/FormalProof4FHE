module
import all FormalProof4FHE.HasteBoots.ScalarExecutionPrefixAgreement
import all FormalProof4FHETest.HasteBootsScalarRecoverySmoke

namespace FormalProof4FHE.HasteBoots.ScalarExecutionRecoverySmoke
open ScalarReplaySmoke (statement proof machine)
open HasteBootsScalarFinishAncestrySmoke (message firstPacket)
open HasteBootsSamplerAncestrySmoke (child worldZero worldReject)
open InputIndexedOracle (World)
noncomputable section

def before := (TranscriptFrame.decodeAll child.input).get (by decide +kernel)
theorem decoded : TranscriptFrame.decodeAll child.input = some before := (Option.some_get _).symm

theorem domain : NativeScalarTranscriptExtension.RoundDomain proof := by
  intro round packet computed
  obtain ⟨index,bounded⟩ := round
  cases index with
  | zero =>
    have same : firstPacket message = packet := Option.some.inj computed
    rw [← same]
    decide +kernel
  | succ index =>
    cases index with
    | zero =>
      have same : ScalarReplaySmoke.secondPacket = packet := Option.some.inj computed
      rw [← same]
      decide +kernel
    | succ index =>
      have missing : NativeScalarBatchRoundPacket.collect (index + 1 + 1) proof.val = none := by
        simp only [proof,ScalarReplaySmoke.proof,NativeScalarBatchRoundPacket.collect]
        rw [List.getElem?_eq_none (by simp)]
        rfl
      unfold NativeScalarBatchRoundPacket.packet at computed
      rw [missing,Option.bind_none] at computed
      contradiction

def execution (fuel : ℕ) (world : World) := NativeScalarBatchVerifier.execute statement proof fuel machine world

/-- All original native analysis prefixes, with arbitrary ideal worlds and
arbitrary rejections, derive recovery and exact reconstructed execution. -/
theorem all_sampling (fuel : ℕ) (world : World) :
    match (execution fuel world).1.control with
    | .sampling packet field => ∃ configuration : ScalarRecoveredReplay.Configuration,
        ScalarRecoveredReplay.recover field.phase.pending.input = some configuration ∧
        configuration.view.history.statement = statement ∧ configuration.view.packet = packet ∧
        execution fuel world = NativeScalarBatchVerifier.execute statement configuration.proof fuel
          (configuration.initial child.profile) world
    | _ => True := by
  cases active : (execution fuel world).1.control with
  | ready => trivial
  | finished claims => trivial
  | failed error => trivial
  | sampling packet field =>
    exact ScalarExecutionPrefixAgreement.sampling child (NativeScalarBatchWire.bindStatement child statement)
      before statement proof decoded rfl (by decide +kernel) domain fuel world packet field active

/-- The exact history invariant holds before first start, during sampling,
after successful completion, and during arbitrarily long rejection prefixes. -/
example (fuel : ℕ) (world : World) : ScalarExecutionTranscript.Aligned before statement child.profile (execution fuel world).1 :=
  ScalarExecutionTranscript.initialized child (NativeScalarBatchWire.bindStatement child statement)
    before statement proof decoded rfl fuel world

example : (execution 1 worldZero).2.length = 1 ∧ (execution 1 worldZero).1.completed = [] := by decide +kernel
example : (execution 3 worldZero).2.length = 3 ∧ (execution 3 worldZero).1.completed = [] := by decide +kernel
example : (execution 5 worldZero).2.length = 7 ∧ (execution 5 worldZero).1.completed.length = 1 := by decide +kernel
example : (execution 7 worldZero).2.length = 9 ∧ (execution 7 worldZero).1.completed.length = 1 := by decide +kernel
example : (execution 5 worldReject).2.length = 5 ∧ (execution 5 worldReject).1.completed = [] := by decide +kernel

def recoveredCount (machine : NativeScalarBatchVerifier.Machine) : Option ℕ :=
  match machine.control with
  | .sampling _ field => (ScalarRecoveredReplay.recover field.phase.pending.input).map (fun config => config.view.history.rounds.length)
  | _ => none

/-- No completed history is invented for an initial or rejected round. -/
example : recoveredCount (execution 1 worldZero).1 = some 0 := by decide +kernel
example : recoveredCount (execution 5 worldReject).1 = some 0 := by decide +kernel

/-- Recovery counts the same original completed round through every partial
read of the next reader, and stops claiming an active request at termination. -/
example : recoveredCount (execution 5 worldZero).1 = some 1 := by decide +kernel
example : recoveredCount (execution 7 worldZero).1 = some 1 := by decide +kernel
example : recoveredCount (execution 9 worldZero).1 = none := by decide +kernel

/-- Native counters used by the coverage proof are monotone through any
resumed/rejected prefix, without a field-completion assumption. -/
example (first later : ℕ) (ordered : first ≤ later) (world : World) :
    (execution first world).1.state.round ≤ (execution later world).1.state.round :=
  ScalarExecutionPrefixAgreement.earlier_round statement proof first later ordered machine world

/-- The literal completion receipt has the real consumed byte count and 80
bytes total; finalization does not add a made-up challenge to the transcript. -/
example : ScalarRecoverySmoke.firstReceipt.length = 80 ∧ ScalarRecoverySmoke.firstReceipt.take 16 = TranscriptFrame.littleEndian 16 24 := by decide +kernel

/-- Reconstruction completeness applies without a success premise on its
checker, deriving success from actual native row widths and ordinals. -/
example : ∃ restored, ScalarPrefixProof.reconstruct ScalarRecoverySmoke.expectedView = some restored := by
  apply ScalarReconstructionCompleteness.reconstruct ScalarRecoverySmoke.expectedView ScalarReplaySmoke.info rfl
    (by decide +kernel) rfl rfl (by decide +kernel)
  intro packet member
  have cases : packet = firstPacket message ∨ packet = ScalarReplaySmoke.secondPacket := by simpa [ScalarRecoverySmoke.expectedView,ScalarRecoverySmoke.history] using member
  rcases cases with rfl | rfl
  all_goals exact List.Forall₂.cons rfl .nil

end
end FormalProof4FHE.HasteBoots.ScalarExecutionRecoverySmoke
