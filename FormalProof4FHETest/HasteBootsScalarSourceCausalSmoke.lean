module
import all FormalProof4FHE.HasteBoots.ScalarSourceChallengeBound
import all FormalProof4FHETest.HasteBootsScalarSourceSmoke

namespace FormalProof4FHE.HasteBoots.ScalarSourceCausalSmoke
open InputIndexedOracle (World)
open NativeScalarBatchVerifier (CompletedRound)
open ScalarReplaySmoke (statement proof machine)
open HasteBootsSamplerAncestrySmoke (child worldZero worldReject)
open ScalarExecutionRecoverySmoke (before decoded domain)
open ScalarCompletedSmoke (execution firstEntry secondEntry firstMember secondMember)
open ScalarSourceSmoke (oneArity oneCoefficientG oneIndex jointTable)
open MeasureTheory ProbabilityTheory
noncomputable section

/-- Persistence is independent of world, budget, and termination. -/
example (fuel : ℕ) (world : World) : machine.completed <+: (execution fuel world).1.completed :=
  ScalarCompletedPrefix.execute statement proof fuel machine world

example (first later : ℕ) (ordered : first ≤ later) (world : World) :
    (execution first world).1.completed <+: (execution later world).1.completed :=
  ScalarCompletedPrefix.earlier statement proof first later ordered machine world

/-- The actual completed occurrence determines its prior native list and
common point without a supplied point equality or assumed producer time. -/
example (fuel : ℕ) (world : World) (old : List CompletedRound) (entry : CompletedRound) (tail : List CompletedRound)
    (parts : (execution fuel world).1.completed = old ++ entry :: tail) :
    ∃ index < fuel, ScalarCompletedOrigin.Produced (execution index world).1 world entry ∧
      (execution index world).1.completed = old ∧
      (execution index world).1.state.point = old.map (fun item => item.challenge) := by
  have member : entry ∈ (execution fuel world).1.completed := by rw [parts]; simp
  obtain ⟨index,bound,produced⟩ := ScalarCompletedOrigin.initialized child statement proof fuel world entry member
  exact ⟨index,bound,produced,
    ScalarCompletedPrefix.producing_before child (NativeScalarBatchWire.bindStatement child statement) statement proof rfl
      fuel index (Nat.le_of_lt bound) world entry produced old tail parts,
    ScalarCompletedPrefix.producing_point child (NativeScalarBatchWire.bindStatement child statement) statement proof rfl
      fuel index (Nat.le_of_lt bound) world entry produced old tail parts⟩

theorem firstParts : (execution 9 worldZero).1.completed = [] ++ firstEntry :: [secondEntry] := rfl
theorem secondParts : (execution 9 worldZero).1.completed = [firstEntry] ++ secondEntry :: [] := rfl

example : firstEntry.packet.round.val = 0 :=
  ScalarCompletedPrefix.ordinal statement proof _ _
    (NativeScalarBatchHistory.initialized_linked child (NativeScalarBatchWire.bindStatement child statement) statement proof rfl 9 worldZero).1
    [] firstEntry [secondEntry] firstParts

example : secondEntry.packet.round.val = 1 :=
  ScalarCompletedPrefix.ordinal statement proof _ _
    (NativeScalarBatchHistory.initialized_linked child (NativeScalarBatchWire.bindStatement child statement) statement proof rfl 9 worldZero).1
    [firstEntry] secondEntry [] secondParts

/-- Equal membership alone cannot substitute another occurrence: the original
round ordinal also fixes the prefix length. -/
example (old tail : List CompletedRound) (parts : (execution 9 worldZero).1.completed = old ++ firstEntry :: tail) : old = [] := by
  have ordinal := ScalarCompletedPrefix.ordinal statement proof _ _
    (NativeScalarBatchHistory.initialized_linked child (NativeScalarBatchWire.bindStatement child statement) statement proof rfl 9 worldZero).1
    old firstEntry tail parts
  have zero : firstEntry.packet.round.val = 0 := by decide +kernel
  exact List.length_eq_zero_iff.mp (ordinal.symm.trans zero)

/-- The source-derived root at the actual first native completed draw supplies
an all-budget event after successful original-input recovery. -/
example : ∃ configuration : ScalarRecoveredReplay.Configuration,
    ScalarRecoveredReplay.recover firstEntry.coefficients.phase.pending.input = some configuration ∧
    ScalarRecoveredUnboundedLaw.event firstEntry.coefficients.phase.pending.input configuration child.profile
      (ScalarSourceChallengeBound.test ScalarReplaySmoke.info HasteBootsScalarFinishAncestrySmoke.message
        oneArity oneCoefficientG oneIndex 2 jointTable) worldZero := by
  obtain ⟨configuration,found,_,_,_⟩ := ScalarCompletedChallenge.recover_completed child
    (NativeScalarBatchWire.bindStatement child statement) before statement proof decoded rfl (by decide +kernel)
    domain 9 worldZero firstEntry firstMember
  refine ⟨configuration,found,?_⟩
  exact ScalarSourceChallengeBound.completed_event _ configuration found child
    (NativeScalarBatchWire.bindStatement child statement) before statement proof decoded rfl (by decide +kernel)
    domain ScalarReplaySmoke.info rfl 9 worldZero [] firstEntry [secondEntry] firstParts rfl
    oneArity oneCoefficientG oneIndex jointTable 0 ScalarReplaySmoke.info HasteBootsScalarFinishAncestrySmoke.message
    NativeGoldLookup.zero NativeGoldLookup.zero rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro term; exact Nat.le_refl 1) ScalarSourceSmoke.first_heals

/-- The actual source-derived family, rather than a supplied toy polynomial
pair, has the one-exposure cubic root bound. -/
example {S A : Type} {past : World → NativeTranscript.Execution (S ⊕ A)}
    (replay : ObservationReplay.Replayable past) (step : S → OracleMachine.Command S A)
    (world : World) (input : InputIndexedOracle.Input) (configuration : ScalarRecoveredReplay.Configuration)
    (found : ScalarRecoveredReplay.recover input = some configuration)
    (selected : CausalStreamExposure.firstRead step (past world).run = some input) :
    (InputIndexedOracle.law[|{other | (past other).run = (past world).run}])
      {other | ScalarRecoveredUnboundedLaw.event input configuration child.profile
        (ScalarSourceChallengeBound.test ScalarReplaySmoke.info HasteBootsScalarFinishAncestrySmoke.message
          oneArity oneCoefficientG oneIndex 2 jointTable) other} ≤
            (1 : ENNReal) / (NativeFields.goldilocksModulus^3 : ℕ) := by
  have bound := ScalarSourceChallengeBound.bound replay step world (fun _ => 0) child.profile input configuration found selected
    ScalarReplaySmoke.info HasteBootsScalarFinishAncestrySmoke.message oneArity oneCoefficientG oneIndex 2 jointTable
  have degree : ScalarReplaySmoke.info.maxMultiplicands.val = 1 := rfl
  simpa only [degree,Nat.cast_one] using bound

/-- No artificial budget cap is added for rejection-only executions. -/
example : (execution 10 worldReject).1.completed <+: (execution 100 worldReject).1.completed :=
  ScalarCompletedPrefix.earlier statement proof 10 100 (by decide) machine worldReject

/-- The wrapper derives the completed bad input directly from the original
false claim; no healing occurrence or message getters are caller premises. -/
theorem false_or_bad : ScalarChainHealing.value 0 (execution 9 worldZero).1.state.expected ≠
      some (ScalarSourceSmoke.sourceTruth ((execution 9 worldZero).1.completed.map (fun entry => entry.challenge))) ∨
    ∃ entry ∈ (execution 9 worldZero).1.completed, ∃ message, entry.packet.messages.val[0]? = some message ∧
      ∃ configuration : ScalarRecoveredReplay.Configuration,
        ScalarRecoveredReplay.recover entry.coefficients.phase.pending.input = some configuration ∧
        ScalarRecoveredUnboundedLaw.event entry.coefficients.phase.pending.input configuration child.profile
          (ScalarSourceChallengeBound.test ScalarReplaySmoke.info message oneArity oneCoefficientG oneIndex 2 jointTable) worldZero :=
  ScalarSourceChallengeBound.false_or_event child (NativeScalarBatchWire.bindStatement child statement) before statement proof
    decoded rfl (by decide +kernel) domain ScalarReplaySmoke.info rfl 9 worldZero oneArity oneCoefficientG oneIndex jointTable
    0 ScalarReplaySmoke.info rfl (by intro term; exact Nat.le_refl 1) ScalarSourceSmoke.initial_false

/-- Truth at the actual returned zero point excludes the false-terminal branch,
forcing an original completed input's source-derived causal event. -/
example : ∃ entry ∈ (execution 9 worldZero).1.completed, ∃ message, entry.packet.messages.val[0]? = some message ∧
    ∃ configuration : ScalarRecoveredReplay.Configuration,
      ScalarRecoveredReplay.recover entry.coefficients.phase.pending.input = some configuration ∧
      ScalarRecoveredUnboundedLaw.event entry.coefficients.phase.pending.input configuration child.profile
        (ScalarSourceChallengeBound.test ScalarReplaySmoke.info message oneArity oneCoefficientG oneIndex 2 jointTable) worldZero := by
  have getter : (execution 9 worldZero).1.state.expected[0]? = some NativeGoldLookup.zero := by decide +kernel
  have point : (execution 9 worldZero).1.completed.map (fun entry => entry.challenge) =
      [NativeGoldLookup.zero,NativeGoldLookup.zero] := by decide +kernel
  have truthful : ScalarChainHealing.value 0 (execution 9 worldZero).1.state.expected =
      some (ScalarSourceSmoke.sourceTruth ((execution 9 worldZero).1.completed.map (fun entry => entry.challenge))) := by
    simp only [ScalarChainHealing.value,getter,Option.map_some,point,ScalarSourceSmoke.zero_terminal_truth,NativeGoldLookup.zero_value]
  exact false_or_bad.resolve_left (fun falseFinal => falseFinal truthful)

end
end FormalProof4FHE.HasteBoots.ScalarSourceCausalSmoke
