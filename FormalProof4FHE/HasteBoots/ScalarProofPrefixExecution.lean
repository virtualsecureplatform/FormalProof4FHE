module
public import FormalProof4FHE.HasteBoots.ScalarRecoveredReplay
@[expose] public section

/-! Native execution before an unexposed certificate suffix is independent
of that suffix. Equality covers actual machine state and the whole ordered
primitive log, not only accepted subclaims. -/
namespace FormalProof4FHE.HasteBoots.ScalarProofPrefixExecution
open NativeScalarBatchWire (Statement)
open NativeScalarBatchPreflight (Proof)
open NativeScalarBatchVerifier (Machine)
open NativeUsizeMessage (Usize)
open InputIndexedOracle (World)

def AgreeAt (original reconstructed : Proof) (round : ℕ) : Prop :=
  ∀ index : Usize, index.val = round →
    NativeScalarBatchRoundPacket.packet index original = NativeScalarBatchRoundPacket.packet index reconstructed

/-- Native preparation reads only the packet at the machine's current round. -/
theorem prepare_eq (statement : Statement) (original reconstructed : Proof) (machine : Machine)
    (agree : AgreeAt original reconstructed machine.state.round) :
    NativeScalarBatchVerifier.prepare statement original machine = NativeScalarBatchVerifier.prepare statement reconstructed machine := by
  unfold NativeScalarBatchVerifier.prepare
  split
  · rfl
  · split
    · split
      next fits => rw [agree ⟨machine.state.round,fits⟩ rfl]
      next => rfl
    · rfl

/-- Sampling, rejection and finalization do not consult any later packet. -/
theorem tick_eq (statement : Statement) (original reconstructed : Proof) (machine : Machine) (world : World)
    (agree : machine.control = .ready → AgreeAt original reconstructed machine.state.round) :
    NativeScalarBatchVerifier.tickExecute statement original machine world =
      NativeScalarBatchVerifier.tickExecute statement reconstructed machine world := by
  cases control : machine.control with
  | ready => simp only [NativeScalarBatchVerifier.tickExecute,control,prepare_eq statement original reconstructed machine (agree control)]
  | sampling packet field => simp only [NativeScalarBatchVerifier.tickExecute,control]
  | finished claims => simp only [NativeScalarBatchVerifier.tickExecute,control]
  | failed error => simp only [NativeScalarBatchVerifier.tickExecute,control]

/-- Original and reconstructed certificates with identical reached packets
have identical finite native trajectories and all primitive observations. No
assumption about unvisited packet contents or their recurrences is required. -/
theorem execute_eq (statement : Statement) (original reconstructed : Proof) (fuel : ℕ) (machine : Machine) (world : World)
    (agree : ∀ index < fuel,
      (NativeScalarBatchVerifier.execute statement original index machine world).1.control = .ready →
        AgreeAt original reconstructed (NativeScalarBatchVerifier.execute statement original index machine world).1.state.round) :
    NativeScalarBatchVerifier.execute statement original fuel machine world =
      NativeScalarBatchVerifier.execute statement reconstructed fuel machine world := by
  induction fuel generalizing machine with
  | zero => rfl
  | succ fuel ih =>
    have now : machine.control = .ready → AgreeAt original reconstructed machine.state.round := agree 0 (Nat.zero_lt_succ fuel)
    have first := tick_eq statement original reconstructed machine world now
    have later : ∀ index < fuel,
        (NativeScalarBatchVerifier.execute statement original index
          (NativeScalarBatchVerifier.tickExecute statement original machine world).1 world).1.control = .ready →
        AgreeAt original reconstructed (NativeScalarBatchVerifier.execute statement original index
          (NativeScalarBatchVerifier.tickExecute statement original machine world).1 world).1.state.round := by
      intro index bound
      simpa only [NativeScalarBatchVerifier.execute] using agree (index + 1) (by omega)
    have tail := ih (NativeScalarBatchVerifier.tickExecute statement original machine world).1 later
    simp only [NativeScalarBatchVerifier.execute]
    rw [← first,tail]

/-- Passing native preflight fixes the initial state independently of the
unused future messages. The full statement and parent are the same. -/
theorem initial_eq (transcript result : NativeTranscript.Transcript) (statement : Statement) (original reconstructed : Proof)
    (originalOk : NativeScalarBatchPreflight.beginVerify transcript statement original = .ok result)
    (reconstructedOk : NativeScalarBatchPreflight.beginVerify transcript statement reconstructed = .ok result) :
    NativeScalarBatchVerifier.initial transcript statement original = NativeScalarBatchVerifier.initial transcript statement reconstructed := by
  simp only [NativeScalarBatchVerifier.initial,originalOk,reconstructedOk]

end FormalProof4FHE.HasteBoots.ScalarProofPrefixExecution
