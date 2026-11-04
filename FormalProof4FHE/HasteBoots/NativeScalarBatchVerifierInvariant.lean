module

public import FormalProof4FHE.HasteBoots.NativeScalarBatchVerifier

@[expose] public section

/-!
# Count, common-point and sampler invariants of actual scalar verification

Accepted native preflight supplies every packet width and count. These
invariants exclude internal checked-model failures and preserve ordered
claims and the shared point across arbitrary resumed analysis prefixes.
-/

namespace FormalProof4FHE.HasteBoots.NativeScalarBatchVerifierInvariant

open NativeFields NativeScalarBatchWire NativeScalarBatchPreflight NativeScalarBatchVerifier
open NativeTranscript (Transcript Observation)
open InputIndexedOracle (World)

/-- Structural invariants of every control phase, including active requests. -/
def Valid (statement : Statement) (first : Info) (machine : Machine) : Prop :=
  machine.state.expected.length = statement.claims.val.length ∧
  machine.state.round ≤ first.numVariables.val ∧
  machine.state.point = machine.completed.map (fun round => round.challenge) ∧
  machine.completed.length = machine.state.round ∧
  match machine.control with
  | .ready => True
  | .sampling packet field =>
      machine.state.round < first.numVariables.val ∧ packet.round.val = machine.state.round ∧
      List.Forall₂ (fun info message => message.evaluations.val.length = info.maxMultiplicands.val + 1)
        statement.infos.val packet.messages.val ∧
      packet.messages.val.length = statement.claims.val.length ∧
      check packet.messages.val machine.state.expected = true ∧
      TypedFieldRequest.FieldValid goldilocksModulus 3 field
  | .finished claims => machine.state.round = first.numVariables.val ∧
      claims = machine.state.expected.map (fun value => ⟨machine.state.point, value⟩)
  | .failed (.reject reason) => reason = .recurrence
  | .failed _ => False

theorem initial_valid (transcript result : Transcript) (statement : Statement) (proof : Proof)
    (first : Info) (accepted : beginVerify transcript statement proof = .ok result) :
    Valid statement first (initial transcript statement proof) := by
  rw [initial_success transcript result statement proof accepted]
  exact ⟨rfl, Nat.zero_le _, rfl, rfl, True.intro⟩

/-- A completed field request decodes and updates all actual matched claims. -/
theorem afterField_valid (statement : Statement) (first : Info) (machine : Machine)
    (packet : RoundPacket) (field completed : NativeFieldVector.State) (transcript : Transcript) (world : World)
    (accepted : dimensions statement = true) (valid : Valid statement first machine)
    (sampling : machine.control = .sampling packet field)
    (finished : (NativeFieldVector.driveExecute goldilocksModulus 1 field world).1 = .finished completed transcript) :
    Valid statement first (afterField machine packet (.finished completed transcript)) := by
  obtain ⟨expectedCount, roundBound, pointSource, completedCount, phase⟩ := valid
  rw [sampling] at phase
  obtain ⟨pending, _, widths, messageCount, _, fieldValid⟩ := phase
  obtain ⟨length, bounded⟩ := TypedFieldRequest.drive_finished_length goldilocksModulus 3 1 world
    field completed transcript fieldValid finished
  have decoded := NativeGoldLookupProducer.decode_complete completed.values length bounded
  let challenge := NativeGoldLookupCompleted.fromCoefficients completed.values length bounded
  have safe := NativeGoldInterpolationSafety.messages_safe statement accepted packet.messages.val widths challenge
  obtain ⟨expected, updated⟩ := NativeScalarBatchUpdate.update_success machine.state.expected packet.messages.val challenge safe
  have count := NativeScalarBatchUpdate.update_length machine.state.expected packet.messages.val challenge expected updated
  rw [afterField, decoded]
  change Valid statement first (match NativeScalarBatchUpdate.update machine.state.expected packet.messages.val challenge with
    | none => _ | some expected => _)
  rw [updated]
  dsimp only [Valid]
  refine ⟨count.trans expectedCount, by omega, ?_, ?_, True.intro⟩
  · simp only [List.map_append, List.map_cons, List.map_nil]
    exact congrArg (fun prior => prior ++ [challenge]) pointSource
  · simp only [List.length_append, List.length_singleton]
    omega

theorem tick_valid (statement : Statement) (proof : Proof) (first : Info)
    (shape : proofShape statement proof = true) (accepted : dimensions statement = true)
    (head : statement.infos.val.head? = some first) (machine : Machine) (world : World)
    (valid : Valid statement first machine) :
    Valid statement first (tickExecute statement proof machine world).1 := by
  have original := valid
  obtain ⟨expectedCount, roundBound, pointSource, completedCount, phase⟩ := valid
  cases control : machine.control with
  | finished claims => simpa only [tickExecute, control] using original
  | failed error => simpa only [tickExecute, control] using original
  | ready =>
    by_cases pending : machine.state.round < first.numVariables.val
    · have fits : machine.state.round < 2 ^ 64 := pending.trans first.numVariables.isLt
      obtain ⟨packet, found, packetRound, widths, messageCount⟩ := NativeScalarBatchRoundPacket.packet_success
        statement proof ⟨machine.state.round, fits⟩ first shape accepted head pending
      have packetIndex : packet.round.val = machine.state.round := congrArg Fin.val packetRound
      cases checked : check packet.messages.val machine.state.expected with
      | false =>
        simp only [tickExecute, control, prepare, head, pending, ite_true, dite_eq_left fits, found,
          bindCheckedRound, checked, Bool.false_eq_true, ite_false]
        exact ⟨expectedCount, roundBound, pointSource, completedCount, rfl⟩
      | true =>
        simp only [tickExecute, control, prepare, head, pending, ite_true, dite_eq_left fits, found,
          bindCheckedRound, checked]
        refine ⟨expectedCount, roundBound, pointSource, completedCount,
          pending, packetIndex, widths, messageCount, checked, ?_⟩
        exact TypedFieldRequest.begin_valid goldilocksModulus 3 7 _ challengeLabel
    · simp only [tickExecute, control, prepare, head, pending, ite_false]
      exact ⟨expectedCount, roundBound, pointSource, completedCount, by change machine.state.round = first.numVariables.val; omega, rfl⟩
  | sampling packet field =>
    rw [control] at phase
    have active : TypedFieldRequest.FieldValid goldilocksModulus 3 field := phase.2.2.2.2.2
    cases result : (NativeFieldVector.driveExecute goldilocksModulus 1 field world).1 with
    | suspended next =>
      have nextValid := TypedFieldRequest.drive_valid goldilocksModulus 3 1 world field active
      rw [result] at nextValid
      simp only [tickExecute, control, result, afterField]
      exact ⟨expectedCount, roundBound, pointSource, completedCount,
        phase.1, phase.2.1, phase.2.2.1, phase.2.2.2.1, phase.2.2.2.2.1, nextValid⟩
    | finished completed transcript =>
      simp only [tickExecute, control, result]
      exact afterField_valid statement first machine packet field completed transcript world accepted original control result

theorem execute_valid (statement : Statement) (proof : Proof) (first : Info)
    (shape : proofShape statement proof = true) (accepted : dimensions statement = true)
    (head : statement.infos.val.head? = some first) (fuel : ℕ) (machine : Machine) (world : World)
    (valid : Valid statement first machine) :
    Valid statement first (execute statement proof fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact valid
  | succ fuel ih => exact ih _ (tick_valid statement proof first shape accepted head machine world valid)

/-- Every completed initialized execution has the original claim count and
one common point of the trusted number of variables. The subclaims remain
unauthenticated; this is the native verifier's return contract. -/
theorem finished_shape (transcript result : Transcript) (statement : Statement) (proof : Proof)
    (first : Info) (accepted : beginVerify transcript statement proof = .ok result)
    (head : statement.infos.val.head? = some first) (fuel : ℕ) (world : World) (claims : List SubClaim)
    (finished : (execute statement proof fuel (initial transcript statement proof) world).1.control = .finished claims) :
    claims.length = statement.claims.val.length ∧
      ∀ claim ∈ claims, claim.point = (execute statement proof fuel (initial transcript statement proof) world).1.state.point ∧
        claim.point.length = first.numVariables.val := by
  have preflight := (beginVerify_ok_iff transcript result statement proof).mp accepted
  have valid := execute_valid statement proof first preflight.1 preflight.2.1 head fuel
    (initial transcript statement proof) world (initial_valid transcript result statement proof first accepted)
  obtain ⟨count, _, source, rounds, phase⟩ := valid
  rw [finished] at phase
  rw [phase.2]
  refine ⟨by simpa only [List.length_map] using count, ?_⟩
  intro claim member
  rcases List.mem_map.mp member with ⟨value, _, rfl⟩
  refine ⟨rfl, ?_⟩
  change (execute statement proof fuel (initial transcript statement proof) world).1.state.point.length = _
  rw [source, List.length_map, rounds, phase.1]

/-- All internal checked-model failures are unreachable after actual preflight.
Only a native recurrence rejection may stop the round execution. -/
theorem no_internal_failure (transcript result : Transcript) (statement : Statement) (proof : Proof)
    (accepted : beginVerify transcript statement proof = .ok result) (fuel : ℕ) (world : World) (error : NativeScalarBatchVerifier.Error)
    (failed : (execute statement proof fuel (initial transcript statement proof) world).1.control = .failed error) :
    error = .reject .recurrence := by
  have preflight := (beginVerify_ok_iff transcript result statement proof).mp accepted
  obtain ⟨first, head, _, _, _⟩ := dimensions_success statement preflight.2.1
  have valid := execute_valid statement proof first preflight.1 preflight.2.1 head fuel
    (initial transcript statement proof) world (initial_valid transcript result statement proof first accepted)
  have phase := valid.2.2.2.2
  rw [failed] at phase
  cases error with
  | reject reason => exact congrArg NativeScalarBatchVerifier.Error.reject phase
  | invalidRound => exact False.elim phase
  | invalidPacket => exact False.elim phase
  | invalidCoefficients => exact False.elim phase
  | invalidInterpolation => exact False.elim phase

end FormalProof4FHE.HasteBoots.NativeScalarBatchVerifierInvariant
