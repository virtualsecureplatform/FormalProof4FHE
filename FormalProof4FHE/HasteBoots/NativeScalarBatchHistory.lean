module

public import FormalProof4FHE.HasteBoots.NativeScalarBatchVerifierInvariant

@[expose] public section

/-!
# Chained history of actual scalar verifier executions

Completed records come from the actual proof packet at their recorded round.
Every record retains its passed recurrence, actual interpolation update and
completed canonical scalar request. The chain starts at the real statement
claims and ends at the machine's current expected vector.
-/

namespace FormalProof4FHE.HasteBoots.NativeScalarBatchHistory

open NativeFields NativeGoldExtensionArithmetic NativeScalarBatchWire NativeScalarBatchPreflight
open NativeScalarBatchVerifier NativeScalarBatchVerifierInvariant
open NativeTranscript (Transcript)
open InputIndexedOracle (World)

/-- Raw operational facts about one completed native round. -/
def RoundValid (statement : Statement) (entry : CompletedRound) : Prop :=
  List.Forall₂ (fun info message => message.evaluations.val.length = info.maxMultiplicands.val + 1)
    statement.infos.val entry.packet.messages.val ∧
  entry.priorExpected.length = statement.claims.val.length ∧
  entry.packet.messages.val.length = statement.claims.val.length ∧
  check entry.packet.messages.val entry.priorExpected = true ∧
  NativeScalarBatchUpdate.update entry.priorExpected entry.packet.messages.val entry.challenge = some entry.expected ∧
  entry.coefficients.remaining = 0 ∧
  TypedFieldRequest.FieldValid goldilocksModulus 3 entry.coefficients ∧
  NativeGoldLookupProducer.decode entry.coefficients.values = some entry.challenge

/-- No supplied claim chain: each link is the actual native packet, prior
expected vector and completed update, in consecutive round order. -/
inductive Chain (statement : Statement) (proof : Proof) : List CompletedRound → List Word → Prop
  | nil : Chain statement proof [] statement.claims.val
  | snoc {prior : List CompletedRound} {expected : List Word} (entry : CompletedRound)
      (earlier : Chain statement proof prior expected)
      (input : entry.priorExpected = expected)
      (ordinal : entry.packet.round.val = prior.length)
      (source : NativeScalarBatchRoundPacket.packet entry.packet.round proof = some entry.packet)
      (valid : RoundValid statement entry) :
      Chain statement proof (prior ++ [entry]) entry.expected

def Linked (statement : Statement) (proof : Proof) (machine : Machine) : Prop :=
  Chain statement proof machine.completed machine.state.expected ∧
  match machine.control with
  | .sampling packet _ => NativeScalarBatchRoundPacket.packet packet.round proof = some packet
  | _ => True

theorem initial_linked (transcript result : Transcript) (statement : Statement) (proof : Proof)
    (accepted : beginVerify transcript statement proof = .ok result) :
    Linked statement proof (initial transcript statement proof) := by
  rw [initial_success transcript result statement proof accepted]
  exact ⟨.nil, True.intro⟩

theorem afterField_linked (statement : Statement) (proof : Proof) (first : Info) (machine : Machine)
    (packet : RoundPacket) (field completed : NativeFieldVector.State) (transcript : Transcript) (world : World)
    (accepted : dimensions statement = true) (valid : Valid statement first machine)
    (linked : Linked statement proof machine) (sampling : machine.control = .sampling packet field)
    (finished : (NativeFieldVector.driveExecute goldilocksModulus 1 field world).1 = .finished completed transcript) :
    Linked statement proof (afterField machine packet (.finished completed transcript)) := by
  obtain ⟨expectedCount, _, _, completedCount, phase⟩ := valid
  rw [sampling] at phase
  obtain ⟨_, packetRound, widths, messageCount, checked, fieldValid⟩ := phase
  obtain ⟨earlier, source⟩ := linked
  rw [sampling] at source
  obtain ⟨length, bounded⟩ := TypedFieldRequest.drive_finished_length goldilocksModulus 3 1 world
    field completed transcript fieldValid finished
  have done := NativeFieldVector.finish_status world (NativeFieldVector.execute goldilocksModulus 1 field world).1
  change NativeFieldVector.StatusValid (NativeFieldVector.driveExecute goldilocksModulus 1 field world).1 at done
  rw [finished] at done
  change completed.remaining = 0 at done
  have completedValid : TypedFieldRequest.FieldValid goldilocksModulus 3 completed := by
    exact ⟨by rw [done, zero_add, length], bounded⟩
  have decoded := NativeGoldLookupProducer.decode_complete completed.values length bounded
  let challenge := NativeGoldLookupCompleted.fromCoefficients completed.values length bounded
  have safe := NativeGoldInterpolationSafety.messages_safe statement accepted packet.messages.val widths challenge
  obtain ⟨expected, updated⟩ := NativeScalarBatchUpdate.update_success machine.state.expected packet.messages.val challenge safe
  let entry : CompletedRound := ⟨packet, challenge, completed, machine.state.expected, expected⟩
  have entryValid : RoundValid statement entry :=
    ⟨widths, expectedCount, messageCount, checked, updated, done, completedValid, decoded⟩
  have chain := Chain.snoc entry earlier rfl (packetRound.trans completedCount.symm) source entryValid
  rw [afterField, decoded]
  change Linked statement proof (match NativeScalarBatchUpdate.update machine.state.expected packet.messages.val challenge with
    | none => _ | some expected => _)
  rw [updated]
  exact ⟨chain, True.intro⟩

theorem tick_linked (statement : Statement) (proof : Proof) (first : Info)
    (shape : proofShape statement proof = true) (accepted : dimensions statement = true)
    (head : statement.infos.val.head? = some first) (machine : Machine) (world : World)
    (valid : Valid statement first machine) (linked : Linked statement proof machine) :
    Linked statement proof (tickExecute statement proof machine world).1 := by
  cases control : machine.control with
  | finished claims => simpa only [tickExecute, control] using linked
  | failed error => simpa only [tickExecute, control] using linked
  | ready =>
    by_cases pending : machine.state.round < first.numVariables.val
    · have fits : machine.state.round < 2 ^ 64 := pending.trans first.numVariables.isLt
      obtain ⟨packet, found, packetRound, _, _⟩ := NativeScalarBatchRoundPacket.packet_success
        statement proof ⟨machine.state.round, fits⟩ first shape accepted head pending
      cases checked : check packet.messages.val machine.state.expected with
      | false =>
        simp only [tickExecute, control, prepare, head, pending, ite_true, dite_eq_left fits, found,
          bindCheckedRound, checked, Bool.false_eq_true, ite_false]
        exact ⟨linked.1, True.intro⟩
      | true =>
        simp only [tickExecute, control, prepare, head, pending, ite_true, dite_eq_left fits, found,
          bindCheckedRound, checked]
        refine ⟨linked.1, ?_⟩
        change NativeScalarBatchRoundPacket.packet packet.round proof = some packet
        rw [packetRound]
        exact found
    · simp only [tickExecute, control, prepare, head, pending, ite_false]
      exact ⟨linked.1, True.intro⟩
  | sampling packet field =>
    cases result : (NativeFieldVector.driveExecute goldilocksModulus 1 field world).1 with
    | suspended next =>
      simp only [tickExecute, control, result, afterField]
      refine ⟨linked.1, ?_⟩
      have source := linked.2
      rwa [control] at source
    | finished completed transcript =>
      simp only [tickExecute, control, result]
      exact afterField_linked statement proof first machine packet field completed transcript world
        accepted valid linked control result

theorem execute_linked (statement : Statement) (proof : Proof) (first : Info)
    (shape : proofShape statement proof = true) (accepted : dimensions statement = true)
    (head : statement.infos.val.head? = some first) (fuel : ℕ) (machine : Machine) (world : World)
    (valid : Valid statement first machine) (linked : Linked statement proof machine) :
    Linked statement proof (execute statement proof fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact linked
  | succ fuel ih =>
    exact ih _ (tick_valid statement proof first shape accepted head machine world valid)
      (tick_linked statement proof first shape accepted head machine world valid linked)

theorem chain_all {statement : Statement} {proof : Proof} {entries : List CompletedRound} {expected : List Word}
    (chain : Chain statement proof entries expected) :
    ∀ entry ∈ entries, RoundValid statement entry ∧
      NativeScalarBatchRoundPacket.packet entry.packet.round proof = some entry.packet := by
  induction chain with
  | nil => simp
  | @snoc prior expected entry earlier input ordinal source valid ih =>
    intro current member
    rcases List.mem_append.mp member with old | new
    · exact ih current old
    · have same := List.mem_singleton.mp new
      subst current
      exact ⟨valid, source⟩

theorem chain_ordinals {statement : Statement} {proof : Proof} {entries : List CompletedRound} {expected : List Word}
    (chain : Chain statement proof entries expected) :
    entries.map (fun entry => entry.packet.round.val) = List.range entries.length := by
  induction chain with
  | nil => rfl
  | @snoc prior expected entry earlier input ordinal source valid ih =>
    simp only [List.map_append, List.map_cons, List.map_nil, List.length_append, List.length_singleton, List.range_succ]
    rw [ih, ordinal]

/-- Every initialized prefix retains the actual chain from the statement's
initial claims, with no caller-supplied chain or polynomial witnesses. -/
theorem initialized_linked (transcript result : Transcript) (statement : Statement) (proof : Proof)
    (accepted : beginVerify transcript statement proof = .ok result) (fuel : ℕ) (world : World) :
    Linked statement proof (execute statement proof fuel (initial transcript statement proof) world).1 := by
  have preflight := (beginVerify_ok_iff transcript result statement proof).mp accepted
  obtain ⟨first, head, _, _, _⟩ := dimensions_success statement preflight.2.1
  exact execute_linked statement proof first preflight.1 preflight.2.1 head fuel
    (initial transcript statement proof) world (initial_valid transcript result statement proof first accepted)
    (initial_linked transcript result statement proof accepted)

end FormalProof4FHE.HasteBoots.NativeScalarBatchHistory
