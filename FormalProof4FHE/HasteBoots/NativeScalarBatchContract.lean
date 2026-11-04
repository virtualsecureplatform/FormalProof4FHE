module

public import FormalProof4FHE.HasteBoots.NativeScalarBatchRoundMeaning

@[expose] public section

/-!
# Terminal algebraic contract of the actual scalar verifier

The actual initialized run supplies its chained proof messages, consecutive
rounds, one common point and the polynomial meaning of every matched slot.
These terminal subclaims still require authentication in the lookup caller;
no Fiat--Shamir probability or authentication assumption is hidden here.
-/

namespace FormalProof4FHE.HasteBoots.NativeScalarBatchContract

open NativeFields NativeExtensionFields NativeFieldWire NativeScalarBatchWire NativeScalarBatchPreflight
open NativeScalarBatchVerifier NativeScalarBatchVerifierInvariant NativeScalarBatchHistory NativeScalarBatchRoundMeaning
open NativeTranscript (Transcript)
open InputIndexedOracle (World)

noncomputable section

def Contract (statement : Statement) (proof : Proof) (first : Info) (machine : Machine) (claims : List SubClaim) : Prop :=
  Chain statement proof machine.completed machine.state.expected ∧
  machine.completed.length = first.numVariables.val ∧
  machine.completed.map (fun entry => entry.packet.round.val) = List.range first.numVariables.val ∧
  machine.state.expected.length = statement.claims.val.length ∧
  claims = machine.state.expected.map (fun expected =>
    ⟨machine.completed.map (fun entry => entry.challenge), expected⟩) ∧
  ∀ entry ∈ machine.completed, RoundMeaning statement entry ∧
    NativeScalarBatchRoundPacket.packet entry.packet.round proof = some entry.packet ∧
    goldExtensionValue entry.challenge = TypedFieldRequest.scalarValue goldilocksBasis entry.coefficients.values

/-- Successful actual execution supplies the entire algebraic contract.
The caller provides neither a polynomial trace nor a completed-draw certificate. -/
theorem finished_contract (transcript result : Transcript) (statement : Statement) (proof : Proof)
    (first : Info) (accepted : beginVerify transcript statement proof = .ok result)
    (head : statement.infos.val.head? = some first) (fuel : ℕ) (world : World) (claims : List SubClaim)
    (finished : (execute statement proof fuel (initial transcript statement proof) world).1.control = .finished claims) :
    Contract statement proof first (execute statement proof fuel (initial transcript statement proof) world).1 claims := by
  have preflight := (beginVerify_ok_iff transcript result statement proof).mp accepted
  have valid := execute_valid statement proof first preflight.1 preflight.2.1 head fuel
    (initial transcript statement proof) world (initial_valid transcript result statement proof first accepted)
  have linked := initialized_linked transcript result statement proof accepted fuel world
  have phase := valid.2.2.2.2
  rw [finished] at phase
  have count : (execute statement proof fuel (initial transcript statement proof) world).1.completed.length =
      first.numVariables.val := valid.2.2.2.1.trans phase.1
  refine ⟨linked.1, count, ?_, valid.1, ?_, initialized_rounds transcript result statement proof accepted fuel world⟩
  · rw [chain_ordinals linked.1, count]
  · rw [phase.2, valid.2.2.1]

/-- The returned terminal values are indexed by the same chain that starts
at the original statement sums, and every original equation is retained. -/
theorem contract_output (statement : Statement) (proof : Proof) (first : Info) (machine : Machine)
    (claims : List SubClaim) (contract : Contract statement proof first machine claims) :
    Chain statement proof machine.completed (claims.map SubClaim.expected) ∧
      claims.length = statement.claims.val.length ∧
      ∀ claim ∈ claims, claim.point = machine.completed.map (fun entry => entry.challenge) ∧
        claim.point.length = first.numVariables.val := by
  obtain ⟨chain, rounds, _, count, output, _⟩ := contract
  have expected : claims.map SubClaim.expected = machine.state.expected := by
    rw [output, List.map_map]
    change machine.state.expected.map id = machine.state.expected
    simp only [List.map_id]
  refine ⟨?_, ?_, ?_⟩
  · rw [expected]
    exact chain
  · rw [output, List.length_map, count]
  · intro claim member
    rw [output] at member
    rcases List.mem_map.mp member with ⟨value, _, rfl⟩
    exact ⟨rfl, by simpa only [List.length_map] using rounds⟩

end

end FormalProof4FHE.HasteBoots.NativeScalarBatchContract
