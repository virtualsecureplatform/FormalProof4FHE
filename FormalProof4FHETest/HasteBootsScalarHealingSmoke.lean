module
import all FormalProof4FHE.HasteBoots.ScalarRoundHealingBound
import all FormalProof4FHETest.HasteBootsScalarFinishAncestrySmoke

namespace FormalProof4FHE.HasteBoots.ScalarHealingSmoke
open HasteBootsScalarFinishAncestrySmoke (statement info message zero firstPacket)
open HasteBootsSamplerAncestrySmoke (child worldZero worldReject)
open NativeFields (goldilocksModulus)
open NativeExtensionFields (Goldilocks3)
open InputIndexedOracle (World)
open OracleProgram (run)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
open scoped Classical
noncomputable section

def packet := firstPacket message
def phase := ScalarRoundChallengeMeaning.phase child packet
def output (fuel : ℕ) (world : World) := (run (ScalarRoundChallengeMeaning.request fuel child packet) world).run.1

def next : NativeFieldVector.Status → NativeTranscript.Transcript
  | .finished _ transcript => transcript
  | .suspended _ => child

/-- Two accepted coordinates still suspend the real three-coordinate scalar. -/
example : (NativeFieldVector.stateOf (output 2 worldZero)).values = [0,0] ∧
    (NativeFieldVector.stateOf (output 2 worldZero)).remaining = 1 := by decide +kernel

/-- Rejected candidates consume the shared budget and bytes but no coordinate. -/
example : (NativeFieldVector.stateOf (output 3 worldReject)).values = [] ∧
    (NativeFieldVector.stateOf (output 3 worldReject)).remaining = 3 ∧
    (NativeFieldVector.stateOf (output 3 worldReject)).phase.consumed.length = 24 := by decide +kernel

example : (GoldScalarChallengeLaw.values 2 phase worldZero).isNone = true ∧
    (GoldScalarChallengeLaw.values 3 phase worldZero).isSome = true := by decide +kernel

/-- A concrete native healing event exists: the false running sum is zero,
the honest polynomial is X, and the collected zero challenge is a root. -/
example : ScalarRoundHealingBound.Event child packet message Polynomial.X worldZero := by
  refine ⟨3,NativeFieldVector.stateOf (output 3 worldZero),next (output 3 worldZero),zero,zero,?_,?_,?_,?_⟩
  · rfl
  · change NativeGoldLookupProducer.decode [0,0,0] = some zero
    rw [NativeGoldLookupProducer.decode_complete _ rfl (by simp [NativeFields.goldilocksModulus])]
    apply congrArg some
    funext i
    fin_cases i <;> rfl
  · rfl
  · have same : zero = NativeGoldLookup.zero := by funext i; fin_cases i <;> rfl
    simp [same,NativeGoldLookup.zero_value]

def past (_ : World) : NativeTranscript.Execution (Unit ⊕ Unit) := pure (.inl ())
def step (_ : Unit) : OracleMachine.Command Unit Unit := .read phase.pending.input 99 1 (fun _ => ())
theorem replay : ObservationReplay.Replayable past := ObservationReplay.pure_replay ((.inl ()) : Unit ⊕ Unit)
theorem first_read (world : World) : CausalStreamExposure.firstRead step (past world).run = some phase.pending.input := rfl

/-- Reading even one field byte prevents a second first-exposure claim. -/
example : CausalStreamExposure.firstRead step (.inl (),[.output phase.pending.input 99 [0]]) = none := by
  simp [CausalStreamExposure.firstRead,CausalSeedExposure.request,step,CausalStreamExposure.seen,CausalStreamExposure.touches]

/-- The bound applies to the actual raw native healing event at all candidate
prefixes. Its denominator is the cubic extension cardinality. -/
example : (InputIndexedOracle.law[|{other | (past other).run = (past worldZero).run}])
    {other | ScalarRoundHealingBound.Event child packet message Polynomial.X other} ≤
      (1 : ENNReal) / (goldilocksModulus^3 : ℕ) := by
  have falsePrior : (Polynomial.X : Polynomial Goldilocks3).eval 0 + Polynomial.X.eval 1 ≠ NativeFieldWire.goldExtensionValue zero := by
    have same : zero = NativeGoldLookup.zero := by funext i; fin_cases i <;> rfl
    simp [same,NativeGoldLookup.zero_value]
  have bound := ScalarRoundHealingBound.event_bound step replay worldZero (fun _ => 0) child (NativeScalarBatchWire.bindRound child packet)
    packet [zero] rfl (first_read worldZero) statement (by decide +kernel) info (by simp [statement]) 0 message zero rfl rfl rfl
    Polynomial.X (by change (Polynomial.X : Polynomial Goldilocks3).natDegree ≤ 1; simp) falsePrior
  simpa only [show info.maxMultiplicands.val = 1 from rfl,Nat.cast_one] using bound

/-- Decode and extension assembly are conclusions of native completion. -/
example (fuel : ℕ) (world : World) (state : NativeFieldVector.State) (transcript : NativeTranscript.Transcript)
    (finished : (output fuel world) = .finished state transcript) :
    ∃ challenge, NativeGoldLookupProducer.decode state.values = some challenge ∧
      GoldScalarChallengeLaw.values fuel phase world = some (NativeFieldWire.goldExtensionValue challenge) :=
  ScalarRoundChallengeMeaning.finished_decodes fuel child packet world state transcript finished

end
end FormalProof4FHE.HasteBoots.ScalarHealingSmoke
