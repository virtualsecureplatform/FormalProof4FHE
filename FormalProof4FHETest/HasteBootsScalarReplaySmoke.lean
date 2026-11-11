module
import all FormalProof4FHE.HasteBoots.ScalarReplayChallengeLaw
import all FormalProof4FHETest.HasteBootsScalarInputSmoke

namespace FormalProof4FHE.HasteBoots.ScalarReplaySmoke
open HasteBootsScalarFinishAncestrySmoke (usize zero message)
open HasteBootsSamplerAncestrySmoke (child worldZero worldReject)
open NativeScalarBatchVerifier (initial)
open NativeScalarBatchWire (Statement)
open NativeScalarBatchPreflight (Proof)
open InputIndexedOracle (World)
open OracleProgram (run)
open MeasureTheory ProbabilityTheory
noncomputable section

def info : NativeScalarBatchWire.Info := ⟨usize 1,usize 2⟩
def statement : Statement := ⟨⟨[info],by decide⟩,⟨[zero],by decide⟩⟩
def proof : Proof := ⟨[⟨[message,message],by decide⟩],by decide⟩
def machine := initial child statement proof
def afterFirst := (NativeScalarBatchVerifier.execute statement proof 4 machine worldZero).1
def secondPacket : NativeScalarBatchWire.RoundPacket := ⟨usize 1,⟨[message],by decide⟩⟩
def phase := ScalarRoundChallengeMeaning.phase afterFirst.state.transcript secondPacket
def target := phase.pending.input
def before := (TranscriptFrame.decodeAll afterFirst.state.transcript.input).get (by decide +kernel)
def view : ScalarChallengeInputView.View := ⟨before,secondPacket⟩
theorem parsed : ScalarChallengeInputView.parse target = some view :=
  ScalarChallengeInputView.actual_parse afterFirst.state.transcript before secondPacket (Option.some_get _).symm (by decide +kernel)
def replay (budget : ℕ) (world : World) := ScalarStoppedReplay.execute target statement proof budget machine world

/-- One round actually completed, including its three canonical coefficients. -/
example : afterFirst.completed.length = 1 ∧ afterFirst.state.point = [zero] ∧ afterFirst.state.expected = [zero] := by decide +kernel

/-- The second round is stopped at its start, before any candidate bytes. -/
example : (replay 20 worldZero).1.1 = true ∧ (replay 20 worldZero).1.2.completed.length = 1 := by decide +kernel
example : (match (replay 20 worldZero).1.2.control with
    | .sampling packet field => packet.round.val == 1 && field.phase.consumed.isEmpty && field.remaining == 3
    | _ => false) = true := by decide +kernel

/-- Exact logs retain three earlier candidate reads, both receipt observations,
and both round starts. None of those seven observations is discarded. -/
example : (replay 20 worldZero).2.length = 7 := by decide +kernel
example : (replay 20 worldZero).2.filterMap (fun observation =>
    match observation with | .output _ _ bytes => some bytes.length | _ => none) = [8,8,8,64] := by decide +kernel
example : CausalStreamExposure.seen (replay 20 worldZero).2 target = false :=
  ScalarStoppedReplay.unseen target view parsed statement proof 20 machine worldZero

/-- Rejection keeps sampling the earlier stream; it is not silently completed
or removed from the replay experiment. -/
example : (replay 6 worldReject).1.1 = false ∧ (replay 6 worldReject).1.2.completed = [] := by decide +kernel
example : (match (replay 6 worldReject).1.2.control with
    | .sampling packet field => packet.round.val == 0 && field.phase.consumed.length == 40 && field.remaining == 3
    | _ => false) = true := by decide +kernel

example : (replay 0 worldZero).1.1 = false ∧ (replay 0 worldZero).2 = [] := by decide +kernel

/-- Replaying an already stopped machine is idempotent and emits no read. -/
example : ScalarStoppedReplay.execute target statement proof 10 (replay 20 worldZero).1.2 worldZero =
    ((true,(replay 20 worldZero).1.2),[]) :=
  ScalarStoppedReplay.stopped _ _ _ _ _ _ (by decide +kernel)

/-- State and ordered log are literally an original five-tick native prefix. -/
example : ((replay 5 worldZero).1.2,(replay 5 worldZero).2) =
    NativeScalarBatchVerifier.execute statement proof 5 machine worldZero := by
  have same := ScalarStoppedReplay.before_first target statement proof 5 machine worldZero
    (by intro index bound; interval_cases index <;> decide +kernel)
  have pair := congrArg (fun result => (result.1.2,result.2)) same
  dsimp only at pair
  exact pair

/-- The initialized actual chain invariant survives stopping. -/
example (budget : ℕ) (world : World) : NativeScalarBatchHistory.Linked statement proof (replay budget world).1.2 :=
  ScalarStoppedReplay.initialized_linked target child (NativeScalarBatchWire.bindStatement child statement)
    statement proof rfl budget world

/-- Earlier receipt bytes cannot expose even an arbitrary parsed scalar input. -/
example (world : World) : CausalStreamExposure.seen
    (NativeFieldVector.finishExecute world (NativeFieldVector.initial phase 0)).2 target = false :=
  ScalarAncestorExposure.finalize_unseen _ world target view parsed

def step (_ : Unit) : OracleMachine.Command Unit Unit := .read target 99 1 (fun _ => ())

/-- The cubic root bound permits polynomial selection from the replayed point.
This varies the common constant term with the actual native machine state. -/
example : (InputIndexedOracle.law[|{other | (ScalarHealingSmoke.past other).run = (ScalarHealingSmoke.past worldZero).run}])
    {other | ∃ fuel, ScalarReplayChallengeLaw.event target statement proof 20 machine fuel phase
      (fun state value =>
        (Polynomial.C (state.state.point.length : NativeExtensionFields.Goldilocks3)).eval value =
        (Polynomial.X + Polynomial.C (state.state.point.length : NativeExtensionFields.Goldilocks3)).eval value) other} ≤
      (1 : ENNReal) / (NativeFields.goldilocksModulus^3 : ℕ) := by
  have bound := ScalarReplayChallengeLaw.eventual_agreement_bound ScalarHealingSmoke.replay step worldZero (fun _ => 0)
    target view parsed rfl statement proof 20 machine phase rfl
    (fun state => Polynomial.C (state.state.point.length : NativeExtensionFields.Goldilocks3))
    (fun state => Polynomial.X + Polynomial.C (state.state.point.length : NativeExtensionFields.Goldilocks3)) 1
  apply (by simpa only [Nat.cast_one] using bound)
  · intro state same
    have linear := congrArg (fun poly : Polynomial NativeExtensionFields.Goldilocks3 => poly.coeff 1) same
    simp at linear
  · intro state
    simp
  · intro state
    exact (Polynomial.natDegree_add_le _ _).trans (by simp)

end
end FormalProof4FHE.HasteBoots.ScalarReplaySmoke
