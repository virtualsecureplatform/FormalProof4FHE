module

public import FormalProof4FHE.HasteBoots.ShortCircuitAccumulator
public import FormalProof4FHE.HasteBoots.PreparedLookupSoundness
public import Mathlib.Data.List.FinRange
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Actual repeated lookup selection and packet provenance

Pairs run in native index order on one shared state. A returned packet sets
that pair's slot and carries its actual successful private memory forward.
Rejection retains the raw result/shared work and skips all later pairs.
Defaults exist only for a total PCS projection; no accepted slot uses them.
-/

open OracleSpec OracleComp BinaryTree
open scoped Classical

namespace FormalProof4FHE.HasteBoots.RepeatedLookupSelector

noncomputable section

variable {F K Memory Cfg Input Digest Payload : Type} {width count n repetitions : ℕ}

abbrev Packet := PreparedLookupPair.Packet F K width count n
abbrev Raw := PreparedLookupSoundness.Output F K Memory width count n

structure State (F K Memory : Type) (width count n repetitions : ℕ) where
  memory : Memory
  packets : Fin repetitions → Option (PreparedLookupPair.Packet F K width count n)

abbrev Outcome := ShortCircuitSequence.Outcome (Fin repetitions)
  (Raw (F := F) (K := K) (Memory := Memory) (width := width) (count := count) (n := n))
  (State F K Memory width count n repetitions)

def advance (index : Fin repetitions) (before : State F K Memory width count n repetitions)
    (earlier : Raw (F := F) (K := K) (Memory := Memory) (width := width) (count := count) (n := n)) :
    ShortCircuitSequence.StepResult (Raw (F := F) (K := K) (Memory := Memory) (width := width) (count := count) (n := n))
      (State F K Memory width count n repetitions) where
  result := earlier
  memory := match earlier.2 with
    | none => before
    | some entry => ⟨entry.2, Function.update before.packets index (some entry.1)⟩
  accepted := earlier.2.isSome

def step (run : Fin repetitions → Memory → OracleComp (SharedSequence.Shared Cfg Input Digest)
    (Raw (F := F) (K := K) (Memory := Memory) (width := width) (count := count) (n := n)))
    (index : Fin repetitions) (before : State F K Memory width count n repetitions) :=
  advance index before <$> run index before.memory

def program (run : Fin repetitions → Memory → OracleComp (SharedSequence.Shared Cfg Input Digest)
    (Raw (F := F) (K := K) (Memory := Memory) (width := width) (count := count) (n := n))) (memory : Memory) :=
  ShortCircuitSequence.program (step run) (List.finRange repetitions) ⟨memory, fun _ => none⟩

/-- Total projection for the later PCS family. Successful provenance proves
that the fallback is never used on any index of an accepted execution. -/
def packets (fallback : Packet (F := F) (K := K) (width := width) (count := count) (n := n))
    (outcome : Outcome (F := F) (K := K) (Memory := Memory) (width := width) (count := count) (n := n) (repetitions := repetitions))
    (index : Fin repetitions) := (outcome.memory.packets index).getD fallback

def Provenance
    (history : List (Fin repetitions × Raw (F := F) (K := K) (Memory := Memory) (width := width) (count := count) (n := n)))
    (state : State F K Memory width count n repetitions) : Prop :=
  (∀ index packet, state.packets index = some packet →
    ∃ earlier, (index, earlier) ∈ history ∧ ∃ memory, earlier.2 = some (packet, memory)) ∧
  (∀ entry ∈ history, (state.packets entry.1).isSome = true)

/-- Every accepted transition fills the trusted scheduled slot with the
packet actually returned by that pair; all previously filled slots remain filled. -/
theorem advance_provenance
    (history : List (Fin repetitions × Raw (F := F) (K := K) (Memory := Memory) (width := width) (count := count) (n := n)))
    (before : State F K Memory width count n repetitions) (valid : Provenance history before) (index : Fin repetitions)
    (earlier : Raw (F := F) (K := K) (Memory := Memory) (width := width) (count := count) (n := n))
    (accepted : earlier.2.isSome = true) :
    Provenance (history ++ [(index, earlier)]) (advance index before earlier).memory := by
  cases returned : earlier.2 with
  | none => simp only [returned, Option.isSome_none, Bool.false_eq_true] at accepted
  | some entry =>
    change Provenance (history ++ [(index, earlier)])
      (match earlier.2 with | none => before | some entry => ⟨entry.2, Function.update before.packets index (some entry.1)⟩)
    rw [returned]
    constructor
    · intro target packet known
      by_cases same : target = index
      · subst target
        simp only [Function.update_self] at known
        have equal := Option.some.inj known
        subst packet
        exact ⟨earlier, List.mem_append_right _ (List.mem_singleton_self _), entry.2, returned⟩
      · have old : before.packets target = some packet := by simpa only [Function.update_of_ne same] using known
        obtain ⟨previous, member, memory, prepared⟩ := valid.1 target packet old
        exact ⟨previous, List.mem_append_left _ member, memory, prepared⟩
    · intro previous member
      obtain member | member := List.mem_append.mp member
      · by_cases same : previous.1 = index
        · simp only [same, Function.update_self, Option.isSome_some]
        · simpa only [Function.update_of_ne same] using valid.2 previous member
      · have equal := List.mem_singleton.mp member
        subst previous
        simp only [Function.update_self, Option.isSome_some]

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

theorem support_step (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (run : Fin repetitions → Memory → OracleComp (SharedSequence.Shared Cfg Input Digest)
      (Raw (F := F) (K := K) (Memory := Memory) (width := width) (count := count) (n := n)))
    (index : Fin repetitions) (before : State F K Memory width count n repetitions)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : ShortCircuitSequence.StepResult
      (Raw (F := F) (K := K) (Memory := Memory) (width := width) (count := count) (n := n))
      (State F K Memory width count n repetitions) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) (step run index before)).run initial)) :
    ∃ native ∈ support ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (run index before.memory)).run initial), outcome = (advance index before native.1, native.2) := by
  rw [step, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨native, present, equal⟩ := supported
  exact ⟨native, present, equal.symm⟩

/-- Every accepted projected packet is a successful result in the actual
ordered pair trace. This is independent of the chosen total-projection fallback. -/
theorem accepted_packet (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (run : Fin repetitions → Memory → OracleComp (SharedSequence.Shared Cfg Input Digest)
      (Raw (F := F) (K := K) (Memory := Memory) (width := width) (count := count) (n := n)))
    (memory : Memory) (fallback : Packet (F := F) (K := K) (width := width) (count := count) (n := n))
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : Outcome (F := F) (K := K) (Memory := Memory) (width := width) (count := count) (n := n) (repetitions := repetitions) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) (program run memory)).run initial))
    (accepted : outcome.1.accepted = true) (index : Fin repetitions) :
    ∃ earlier, (index, earlier) ∈ outcome.1.results ∧ ∃ retainedMemory,
      earlier.2 = some (packets fallback outcome.1 index, retainedMemory) := by
  have valid := ShortCircuitAccumulator.accepted_invariant enc dummy shape (step run) Provenance
    (by
      intro history previous valid index state result present passed
      obtain ⟨native, _, equal⟩ := support_step enc dummy shape run index previous state result present
      subst result
      exact advance_provenance history previous valid index native.1 passed)
    (List.finRange repetitions) [] ⟨memory, fun _ => none⟩
    (by simp [Provenance]) initial outcome supported accepted
  simp only [List.nil_append] at valid
  have coverage := ShortCircuitSequence.accepted_indices enc dummy shape (step run) (List.finRange repetitions)
    ⟨memory, fun _ => none⟩ initial outcome supported accepted
  have occurs : index ∈ outcome.1.results.map Prod.fst := by rw [coverage]; exact List.mem_finRange index
  obtain ⟨entry, member, same⟩ := List.mem_map.mp occurs
  have filled := valid.2 entry member
  rw [same] at filled
  cases found : outcome.1.memory.packets index with
  | none => simp only [found, Option.isSome_none, Bool.false_eq_true] at filled
  | some packet =>
    obtain ⟨earlier, member, retainedMemory, returned⟩ := valid.1 index packet found
    exact ⟨earlier, member, retainedMemory, by simpa only [packets, found, Option.getD_some] using returned⟩

/-- A pair index fixed before the algebra coins costs one local arithmetic
loss. Native canonical coverage contains that index once, so there is no
repetition multiplier, and rejected earlier attempts remain in the real run. -/
theorem selected_arithmetic_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (run : Fin repetitions → Memory → OracleComp (SharedSequence.Shared Cfg Input Digest)
      (Raw (F := F) (K := K) (Memory := Memory) (width := width) (count := count) (n := n)))
    (selected : Fin repetitions)
    (arithmetic : Raw (F := F) (K := K) (Memory := Memory) (width := width) (count := count) (n := n) → Prop)
    (epsilon : ENNReal)
    (localBound : ∀ memory initial,
      Pr{let result ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (run selected memory)).run initial}[arithmetic result.1] ≤ epsilon)
    (memory : Memory) (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program run memory)).run initial}[
        SharedSequence.AnyBad (fun index earlier => index = selected ∧ arithmetic earlier) outcome.1.results] ≤ epsilon := by
  have summed := ShortCircuitSequence.arithmetic_union_bound enc dummy shape (step run)
    (fun index earlier => index = selected ∧ arithmetic earlier) (fun index => if index = selected then epsilon else 0)
    (List.finRange repetitions) (by
      intro index _ previous state
      by_cases same : index = selected
      · subst index
        simpa only [step, simulateQ_map, StateT.run_map, prEvent_map, advance, and_self, true_and, ite_true]
          using localBound previous.memory state
      · simp [same, step, advance, simulateQ_map, StateT.run_map, prEvent_norm])
    ⟨memory, fun _ => none⟩ initial
  simpa only [program, ← List.ofFn_eq_map, List.sum_ofFn, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using summed

end

end FormalProof4FHE.HasteBoots.RepeatedLookupSelector
