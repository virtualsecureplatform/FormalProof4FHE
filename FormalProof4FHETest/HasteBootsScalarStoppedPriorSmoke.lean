module
import all FormalProof4FHE.HasteBoots.ScalarRecoveredStoppedAgreement
import all FormalProof4FHETest.HasteBootsScalarExecutionRecoverySmoke

namespace FormalProof4FHE.HasteBoots.ScalarStoppedPriorSmoke
open ScalarReplaySmoke (statement proof machine target)
open HasteBootsSamplerAncestrySmoke (child worldZero worldReject)
open HasteBootsScalarFinishAncestrySmoke (message firstPacket)
open ScalarExecutionRecoverySmoke (before decoded domain execution)
open InputIndexedOracle (World)
noncomputable section

/-- Every original active sampler derives a causally recovered stopped prior,
with no supplied prior-sum, common-point or reconstruction association. -/
theorem all_sampling_prior (fuel : ℕ) (world : World) :
    match (execution fuel world).1.control with
    | .sampling packet field => ∃ configuration : ScalarRecoveredReplay.Configuration,
        ScalarRecoveredReplay.recover field.phase.pending.input = some configuration ∧
        configuration.view.history.statement = statement ∧ configuration.view.packet = packet ∧
        (ScalarStoppedReplay.execute field.phase.pending.input statement configuration.proof fuel
          (configuration.initial child.profile) world).1.1 = true ∧
        ScalarPriorStability.prior (ScalarStoppedReplay.execute field.phase.pending.input statement configuration.proof fuel
          (configuration.initial child.profile) world).1.2 = ScalarPriorStability.prior (execution fuel world).1
    | _ => True := by
  cases active : (execution fuel world).1.control with
  | ready => trivial
  | finished claims => trivial
  | failed error => trivial
  | sampling packet field =>
    exact ScalarRecoveredStoppedAgreement.sampler_prior child (NativeScalarBatchWire.bindStatement child statement)
      before statement proof decoded rfl (by decide +kernel) domain fuel world packet field active

def stopped (budget : ℕ) (world : World) :=
  (OracleProgram.run (ScalarRecoveredReplay.program target child.profile budget) world).run

def summary (result : Option (Bool × NativeScalarBatchVerifier.Machine)) := result.map (fun pair =>
  (pair.1,pair.2.state.round,pair.2.state.point.length,pair.2.completed.length))

/-- The actual second-round sampler at fuel seven already consumed two
coefficients; recovered replay stops at the same round's entry. -/
example : summary (stopped 7 worldZero).1 = some (true,1,1,1) := by decide +kernel
example : (execution 7 worldZero).2.length = 9 ∧ (stopped 7 worldZero).2.length = 7 := by decide +kernel

example : ScalarPriorStability.prior (execution 7 worldZero).1 = ScalarPriorStability.prior (execution 5 worldZero).1 :=
  ScalarPriorStability.earlier statement proof 5 7 (by decide) machine worldZero (by decide +kernel)

example : (match (execution 7 worldZero).1.control with | .sampling _ field => field.values.length | _ => 99) = 2 ∧
    ((stopped 7 worldZero).1.map (fun pair => match pair.2.control with | .sampling _ field => field.values.length | _ => 99)) = some 0 := by decide +kernel

/-- More auxiliary budget cannot advance past a found request or add reads. -/
example (later : ℕ) (enough : 5 ≤ later) :
    ScalarStoppedReplay.execute target statement proof later machine worldZero =
      ScalarStoppedReplay.execute target statement proof 5 machine worldZero :=
  ScalarFirstMatch.stable target statement proof 5 later enough machine worldZero (by decide +kernel)

example : summary (stopped 50 worldZero).1 = summary (stopped 5 worldZero).1 ∧
    (stopped 50 worldZero).2.length = 7 := by decide +kernel

/-- Budget exhaustion before the match remains visible; it is not converted
into successful or empty-history sampling. -/
example : summary (stopped 2 worldZero).1 = some (false,0,0,0) ∧ (stopped 2 worldZero).2.length = 2 := by decide +kernel
example : summary (stopped 4 worldZero).1 = some (false,1,1,1) ∧ (stopped 4 worldZero).2.length = 6 := by decide +kernel

/-- A wrong guessed future receipt can leave the target unmatched. -/
example : summary ((OracleProgram.run
    (ScalarRecoveredReplay.program ScalarRecoverySmoke.guessedInput child.profile 20) worldZero).run.1) = some (false,2,2,2) := by decide +kernel

/-- Rejected candidates in the preceding round do not reach the later target. -/
example : summary (stopped 8 worldReject).1 = some (false,0,0,0) ∧ (stopped 8 worldReject).2.length = 8 := by decide +kernel

def firstInput := (ScalarRoundChallengeMeaning.phase (NativeScalarBatchWire.bindStatement child statement) (firstPacket message)).pending.input

def firstStopped := (OracleProgram.run (ScalarRecoveredReplay.program firstInput child.profile 8) worldReject).run

/-- For that original rejection-only active request, stopping still finds the
correct first-round prior and emits only its actual reader start. -/
example : summary firstStopped.1 = some (true,0,0,0) ∧ firstStopped.2.length = 1 := by decide +kernel
example : CausalStreamExposure.seen firstStopped.2 firstInput = false :=
  ScalarRecoveredReplay.unseen firstInput child.profile 8 worldReject

/-- Reaching the selected request yields a bounded least native matching time,
with exact state/log identity for the full stopped result. -/
example : ∃ used ≤ 7,
    ScalarStoppedReplay.blocked target (execution used worldZero).1 = true ∧
    (∀ index < used, ScalarStoppedReplay.blocked target (execution index worldZero).1 = false) ∧
    ScalarStoppedReplay.execute target statement proof 7 machine worldZero =
      ((true,(execution used worldZero).1),(execution used worldZero).2) :=
  ScalarFirstMatch.exists_first target statement proof 7 machine worldZero (by decide +kernel)

/-- The target remains unexposed in recovered replay although the original
partially consumed sampler already exposed it. -/
example : CausalStreamExposure.seen (execution 7 worldZero).2 target = true ∧
    CausalStreamExposure.seen (stopped 7 worldZero).2 target = false := by decide +kernel

end
end FormalProof4FHE.HasteBoots.ScalarStoppedPriorSmoke
