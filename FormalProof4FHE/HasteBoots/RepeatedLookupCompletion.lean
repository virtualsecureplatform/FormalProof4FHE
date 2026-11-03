module

public import FormalProof4FHE.HasteBoots.RepeatedLookupSelector

@[expose] public section

/-!
# Selected-pair arithmetic and final accepted wrong openings

A selected index is fixed before repeated algebra. Successful provenance ties
the packet sent to later PCS to its actual earlier raw result. Other pairs,
rejection and the actual later verifier all stay on the same shared execution.
No security property is assumed for the later opening callback.
-/

open OracleSpec OracleComp BinaryTree
open scoped Classical
open FormalProof4FHE.HasteBoots.RepeatedLookupSelector

namespace FormalProof4FHE.HasteBoots.RepeatedLookupCompletion

noncomputable section

variable {F K Memory Cfg Input Digest Payload : Type} {width count n repetitions : ℕ}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- The selected successful packet inherits its native algebra-or-wrong
opening consequence, rather than an unrelated supplied packet certificate. -/
theorem accepted_selected_or_wrong (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (run : Fin repetitions → Memory → OracleComp (SharedSequence.Shared Cfg Input Digest)
      (Raw (F := F) (K := K) (Memory := Memory) (width := width) (count := count) (n := n)))
    (selected : Fin repetitions)
    (arithmetic : Raw (F := F) (K := K) (Memory := Memory) (width := width) (count := count) (n := n) → Prop)
    (wrong : Packet (F := F) (K := K) (width := width) (count := count) (n := n) → Prop)
    (localLaw : ∀ memory initial native,
      native ∈ support ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (run selected memory)).run initial) → ∀ packet retainedMemory,
      native.1.2 = some (packet, retainedMemory) → arithmetic native.1 ∨ wrong packet)
    (memory : Memory) (fallback : Packet (F := F) (K := K) (width := width) (count := count) (n := n))
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : Outcome (F := F) (K := K) (Memory := Memory) (width := width) (count := count) (n := n) (repetitions := repetitions) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) (program run memory)).run initial))
    (accepted : outcome.1.accepted = true) :
    SharedSequence.AnyBad (fun index earlier => index = selected ∧ arithmetic earlier) outcome.1.results ∨
      wrong (packets fallback outcome.1 selected) := by
  have checked := ShortCircuitSequence.accepted_results enc dummy shape (step run) (List.finRange repetitions)
    (fun index raw => index = selected → ∀ packet retainedMemory,
      raw.2 = some (packet, retainedMemory) → arithmetic raw ∨ wrong packet)
    (by
      intro index _ previous state result present _ same packet retainedMemory returned
      subst index
      obtain ⟨native, nativeSupported, equal⟩ := support_step enc dummy shape run selected previous state result present
      subst result
      exact localLaw previous.memory state native nativeSupported packet retainedMemory returned)
    ⟨memory, fun _ => none⟩ initial outcome supported accepted
  obtain ⟨earlier, member, retainedMemory, returned⟩ := accepted_packet enc dummy shape run memory fallback initial outcome supported accepted selected
  obtain arithmeticBad | wrongPacket := checked (selected, earlier) member rfl (packets fallback outcome.1 selected) retainedMemory returned
  · exact Or.inl ⟨(selected, earlier), member, rfl, arithmeticBad⟩
  · exact Or.inr wrongPacket

/-- Later PCS work runs only after the whole computed algebra selector accepts. -/
def finish (fallback : Packet (F := F) (K := K) (width := width) (count := count) (n := n))
    (next : (Fin repetitions → Packet (F := F) (K := K) (width := width) (count := count) (n := n)) → Memory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Bool)
    (earlier : Outcome (F := F) (K := K) (Memory := Memory) (width := width) (count := count) (n := n) (repetitions := repetitions)) :=
  if earlier.accepted then next (packets fallback earlier) earlier.memory.memory else pure false

def program (run : Fin repetitions → Memory → OracleComp (SharedSequence.Shared Cfg Input Digest)
    (Raw (F := F) (K := K) (Memory := Memory) (width := width) (count := count) (n := n)))
    (memory : Memory) (fallback : Packet (F := F) (K := K) (width := width) (count := count) (n := n))
    (next : (Fin repetitions → Packet (F := F) (K := K) (width := width) (count := count) (n := n)) → Memory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Bool) :=
  SharedContinuation.program (RepeatedLookupSelector.program run memory) (finish fallback next)

theorem support_accepts (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (run : Fin repetitions → Memory → OracleComp (SharedSequence.Shared Cfg Input Digest)
      (Raw (F := F) (K := K) (Memory := Memory) (width := width) (count := count) (n := n)))
    (memory : Memory) (fallback : Packet (F := F) (K := K) (width := width) (count := count) (n := n))
    (next : (Fin repetitions → Packet (F := F) (K := K) (width := width) (count := count) (n := n)) → Memory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Bool)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : (Outcome (F := F) (K := K) (Memory := Memory) (width := width) (count := count) (n := n) (repetitions := repetitions) × Bool) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) (program run memory fallback next)).run initial))
    (accepted : outcome.1.2 = true) :
    ∃ earlier ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) (RepeatedLookupSelector.program run memory)).run initial),
      outcome.1.1 = earlier.1 ∧ earlier.1.accepted = true := by
  rw [program, SharedContinuation.support_program] at supported
  obtain ⟨earlier, earlierSupported, later, laterSupported, equal⟩ := supported
  subst outcome
  cases flag : earlier.1.accepted with
  | false =>
    simp only [finish, flag, Bool.false_eq_true, reduceIte, simulateQ_pure, StateT.run_pure] at laterSupported
    have equal := eq_of_mem_support_pure _ laterSupported
    subst later
    cases accepted
  | true => exact ⟨earlier, earlierSupported, rfl, flag⟩

/-- One selected-pair arithmetic loss survives the real repeated selector and
later PCS work. Wrong original openings are gated by this same final acceptance. -/
theorem probability_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (run : Fin repetitions → Memory → OracleComp (SharedSequence.Shared Cfg Input Digest)
      (Raw (F := F) (K := K) (Memory := Memory) (width := width) (count := count) (n := n)))
    (selected : Fin repetitions)
    (arithmetic : Raw (F := F) (K := K) (Memory := Memory) (width := width) (count := count) (n := n) → Prop)
    (wrong : Packet (F := F) (K := K) (width := width) (count := count) (n := n) → Prop) (epsilon : ENNReal)
    (localLaw : ∀ memory initial native,
      native ∈ support ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (run selected memory)).run initial) → ∀ packet retainedMemory,
      native.1.2 = some (packet, retainedMemory) → arithmetic native.1 ∨ wrong packet)
    (localBound : ∀ memory initial,
      Pr{let result ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (run selected memory)).run initial}[arithmetic result.1] ≤ epsilon)
    (memory : Memory) (fallback : Packet (F := F) (K := K) (width := width) (count := count) (n := n))
    (next : (Fin repetitions → Packet (F := F) (K := K) (width := width) (count := count) (n := n)) → Memory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Bool)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program run memory fallback next)).run initial}[outcome.1.2 = true] ≤ epsilon +
      Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (program run memory fallback next)).run initial}[
          outcome.1.2 = true ∧ wrong (packets fallback outcome.1.1 selected)] := by
  let bad := fun (earlier : Outcome (F := F) (K := K) (Memory := Memory) (width := width) (count := count) (n := n) (repetitions := repetitions)) => SharedSequence.AnyBad (fun index raw => index = selected ∧ arithmetic raw) earlier.results
  have pointwise : ∀ outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) (program run memory fallback next)).run initial),
      outcome.1.2 = true → bad outcome.1.1 ∨ (outcome.1.2 = true ∧ wrong (packets fallback outcome.1.1 selected)) := by
    intro outcome supported accepted
    obtain ⟨earlier, earlierSupported, equal, passed⟩ := support_accepts enc dummy shape run memory fallback next initial outcome supported accepted
    have alternatives := accepted_selected_or_wrong enc dummy shape run selected arithmetic wrong localLaw memory fallback initial earlier earlierSupported passed
    rw [← equal] at alternatives
    exact alternatives.imp_right (fun incorrect => ⟨accepted, incorrect⟩)
  have union := prEvent_or_le
    ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) (program run memory fallback next)).run initial)
    (fun outcome => bad outcome.1.1) (fun outcome => outcome.1.2 = true ∧ wrong (packets fallback outcome.1.1 selected))
  have retained := SharedContinuation.earlier_event_le enc dummy shape (RepeatedLookupSelector.program run memory) (finish fallback next) initial bad
  have bounded := selected_arithmetic_bound enc dummy shape run selected arithmetic epsilon localBound memory initial
  exact (prEvent_mono_of_support _ _ _ pointwise).trans (union.trans (add_le_add (retained.trans bounded) le_rfl))

end

end FormalProof4FHE.HasteBoots.RepeatedLookupCompletion
