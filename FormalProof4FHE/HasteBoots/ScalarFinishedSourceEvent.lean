module
public import FormalProof4FHE.HasteBoots.ScalarSourceChallengeBound
@[expose] public section

/-! A truthful returned native subclaim at an originally false source equation
supplies an actual causal healing event. Point equality, terminal getters and
dimension transport follow from the completed native execution. -/
namespace FormalProof4FHE.HasteBoots.ScalarFinishedSourceEvent
open MatrixFold (Cube)
open NativeExtensionFields (Goldilocks3)
open NativeFieldWire (goldExtensionValue)
open NativeScalarBatchWire (Statement Info)
open NativeScalarBatchPreflight (Proof)
open NativeTranscript (Transcript)
open InputIndexedOracle (World)
noncomputable section
variable {Factor Term : Type} [Fintype Term]

def Event (transcript : Transcript) (statement : Statement) (proof : Proof) (fuel : ℕ) (world : World)
    (arity : Term → ℕ) (coefficient : Term → Goldilocks3) (indices : (term : Term) → Fin (arity term) → Factor)
    (n : ℕ) (tables : Factor → Cube n → Goldilocks3) (slot : ℕ) (info : Info) : Prop :=
  ∃ entry ∈ (NativeScalarBatchVerifier.execute statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.completed,
    ∃ message, entry.packet.messages.val[slot]? = some message ∧
      ∃ configuration : ScalarRecoveredReplay.Configuration,
        ScalarRecoveredReplay.recover entry.coefficients.phase.pending.input = some configuration ∧
        ScalarRecoveredUnboundedLaw.event entry.coefficients.phase.pending.input configuration transcript.profile
          (ScalarSourceChallengeBound.test info message arity coefficient indices n tables) world

theorem of_claim (transcript result : Transcript) (frames : List TranscriptFrame.Frame) (statement : Statement) (proof : Proof)
    (decoded : TranscriptFrame.decodeAll transcript.input = some frames)
    (accepted : NativeScalarBatchPreflight.beginVerify transcript statement proof = .ok result)
    (first : Info) (head : statement.infos.val.head? = some first)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof) (fuel : ℕ) (world : World)
    (claims : List NativeScalarBatchVerifier.SubClaim)
    (finished : (NativeScalarBatchVerifier.execute statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.control = .finished claims)
    (arity : Term → ℕ) (coefficient : Term → Goldilocks3) (indices : (term : Term) → Fin (arity term) → Factor)
    (n : ℕ) (dimension : first.numVariables.val = n) (tables : Factor → Cube n → Goldilocks3)
    (slot : ℕ) (info : Info) (infoAt : statement.infos.val[slot]? = some info)
    (bounded : ∀ term, arity term ≤ info.maxMultiplicands.val)
    (initial : ScalarChainHealing.value slot statement.claims.val ≠ some (ScalarNativeSourceHealing.truth arity coefficient indices n tables []))
    (claim : NativeScalarBatchVerifier.SubClaim) (claimAt : claims[slot]? = some claim)
    (truthful : goldExtensionValue claim.expected = ScalarNativeSourceHealing.truth arity coefficient indices n tables claim.point) :
    Event transcript statement proof fuel world arity coefficient indices n tables slot info := by
  subst n
  have contract := NativeScalarBatchContract.finished_contract transcript result statement proof first accepted head fuel world claims finished
  have output := NativeScalarBatchContract.contract_output statement proof first _ claims contract
  have point := (output.2.2 claim (List.mem_of_getElem? claimAt)).1
  have expectedEq : claims.map NativeScalarBatchVerifier.SubClaim.expected =
      (NativeScalarBatchVerifier.execute statement proof fuel
        (NativeScalarBatchVerifier.initial transcript statement proof) world).1.state.expected := by
    rw [contract.2.2.2.2.1,List.map_map]
    change (NativeScalarBatchVerifier.execute statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.state.expected.map id = _
    exact List.map_id _
  have terminalTruth : ScalarChainHealing.value slot (NativeScalarBatchVerifier.execute statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.state.expected =
    some (ScalarNativeSourceHealing.truth arity coefficient indices _ tables
      ((NativeScalarBatchVerifier.execute statement proof fuel
        (NativeScalarBatchVerifier.initial transcript statement proof) world).1.completed.map (fun entry => entry.challenge))) := by
    rw [← expectedEq,ScalarChainHealing.value,List.getElem?_map,Option.map_map,claimAt,Option.map_some]
    exact congrArg some (truthful.trans (congrArg (ScalarNativeSourceHealing.truth arity coefficient indices _ tables) point))
  exact (ScalarSourceChallengeBound.false_or_event transcript result frames statement proof decoded accepted statementFits domain first head
    fuel world arity coefficient indices tables slot info infoAt bounded initial).resolve_left (fun falseFinal => falseFinal terminalTruth)

end
end FormalProof4FHE.HasteBoots.ScalarFinishedSourceEvent
