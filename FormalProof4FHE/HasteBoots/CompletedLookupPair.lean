module

public import FormalProof4FHE.HasteBoots.PreparedLookupSoundness

@[expose] public section

/-!
# Lookup success after actual later opening work

A disabled preparation skips the completion callback. Otherwise the callback
runs on the actual returned shared state. Final acceptance implies the
arithmetic event or an original opening failure, gated by this same final
acceptance. Rejected proposals and failed openings are not counted as accepted
attacks. The callback is not assumed secure: concrete grouped PCS must still
bound the explicit final accepted-wrong-opening event.
-/

open OracleSpec OracleComp BinaryTree
open scoped Classical

namespace FormalProof4FHE.HasteBoots.CompletedLookupPair

noncomputable section

variable {F K Memory Cfg Input Digest Payload : Type} {width count n : ℕ}

abbrev Output := PreparedLookupSoundness.Output F K Memory width count n

def finish (next : PreparedLookupPair.Packet F K width count n → Memory →
    OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Bool) (preparation : Output (F := F) (K := K) (Memory := Memory) (width := width) (count := count) (n := n)) :
    OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Bool :=
  match preparation.2 with
  | none => pure false
  | some entry => next entry.1 entry.2

def program (preparation : OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Output (F := F) (K := K) (Memory := Memory) (width := width) (count := count) (n := n)))
    (next : PreparedLookupPair.Packet F K width count n → Memory → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Bool) :=
  SharedContinuation.program preparation (finish next)

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- Final acceptance entails a real successful preparation; missing packets
cannot invoke the later verifier or supply a forged success flag. -/
theorem support_accepts (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (workerShape : Cfg → Skeleton)
    (preparation : OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Output (F := F) (K := K) (Memory := Memory) (width := width) (count := count) (n := n)))
    (next : PreparedLookupPair.Packet F K width count n → Memory → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Bool)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) workerShape)
    (outcome : (Output (F := F) (K := K) (Memory := Memory) (width := width) (count := count) (n := n) × Bool) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) workerShape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape) (program preparation next)).run before))
    (accepted : outcome.1.2 = true) :
    ∃ earlier ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape) preparation).run before),
      outcome.1.1 = earlier.1 ∧ earlier.1.2.isSome = true := by
  rw [program, SharedContinuation.support_program] at supported
  obtain ⟨earlier, earlierSupported, later, laterSupported, equal⟩ := supported
  subst outcome
  cases returned : earlier.1.2 with
  | none =>
    simp only [finish, returned, simulateQ_pure, StateT.run_pure] at laterSupported
    have equal := eq_of_mem_support_pure _ laterSupported
    subst later
    cases accepted
  | some entry => exact ⟨earlier, earlierSupported, rfl, by simp only [returned, Option.isSome_some]⟩

/-- General same-run composition. Only the arithmetic event is charged
unconditionally; wrong openings are counted only with final acceptance. -/
theorem probability_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (workerShape : Cfg → Skeleton)
    (preparation : OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Output (F := F) (K := K) (Memory := Memory) (width := width) (count := count) (n := n)))
    (next : PreparedLookupPair.Packet F K width count n → Memory → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Bool)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) workerShape)
    (arithmetic : Output (F := F) (K := K) (Memory := Memory) (width := width) (count := count) (n := n) → Prop)
    (wrong : PreparedLookupSoundness.Prepared F K Memory width count n → Prop) (epsilon : ENNReal)
    (localCheck : ∀ earlier ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape) preparation).run before),
      earlier.1.2.isSome = true → arithmetic earlier.1 ∨ wrong earlier.1.2)
    (bound : Pr{let earlier ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape) preparation).run before}[
        arithmetic earlier.1] ≤ epsilon) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape) (program preparation next)).run before}[
        outcome.1.2 = true] ≤ epsilon +
      Pr{let outcome ← (simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape) (program preparation next)).run before}[
          outcome.1.2 = true ∧ wrong outcome.1.1.2] := by
  have pointwise : ∀ outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape) (program preparation next)).run before),
      outcome.1.2 = true → arithmetic outcome.1.1 ∨ (outcome.1.2 = true ∧ wrong outcome.1.1.2) := by
    intro outcome supported accepted
    obtain ⟨earlier, earlierSupported, equal, prepared⟩ := support_accepts enc dummy workerShape preparation next before outcome supported accepted
    have alternatives := localCheck earlier earlierSupported prepared
    rw [← equal] at alternatives
    exact alternatives.imp_right (fun incorrect => ⟨accepted, incorrect⟩)
  have union := prEvent_or_le
    ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape) (program preparation next)).run before)
    (fun outcome => arithmetic outcome.1.1) (fun outcome => outcome.1.2 = true ∧ wrong outcome.1.1.2)
  have retained := SharedContinuation.earlier_event_le enc dummy workerShape preparation (finish next) before arithmetic
  exact (prEvent_mono_of_support _ _ _ pointwise).trans (union.trans (add_le_add (retained.trans bound) le_rfl))

end

end FormalProof4FHE.HasteBoots.CompletedLookupPair
