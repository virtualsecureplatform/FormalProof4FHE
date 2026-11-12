module
public import FormalProof4FHE.HasteBoots.PaddedNTTSequenceSoundness
public import FormalProof4FHE.HasteBoots.PackedPBSOriginalReferences
@[expose] public section

/-! Final key-switch NTT order: the d digit coefficient/evaluation pairs and
then the result pair. Each pair keeps its own physical PCS geometry and uses
the same caller-owned family roots; native butterflies act on two logical
polynomial rows. The native row-repetition count is the packing width b. -/
namespace FormalProof4FHE.HasteBoots.KeySwitchPaddedNTT
open OracleSpec OracleComp BinaryTree
open NativeRootMessage (Digest)
noncomputable section
variable {q log d b c : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory : Type}
  [DecidableEq Input] [DecidableEq Digest] {heights : Cfg → ℕ}

/-- Coefficients precede evaluations within each scheduled native NTT. -/
def roots (family : PackedPBSOriginalReferences.Family d) (index : Fin (d+1)) : Bool → Digest
  | false => family.coefficients index
  | true => family.evaluations index

variable (base : Fin (d+1) → Memory → PaddedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory heights b c 1 b)
  (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (family : PackedPBSOriginalReferences.Family d)
  (nodesEnough : 2*b ≤ q) (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))

/-- Source identities, native nodes and butterfly maps are caller-selected. -/
abbrev factory (index : Fin (d+1)) (memory : Memory) :=
  PaddedNTT.nativeScheme (base index memory) enc (roots family index) q nodesEnough length psi primitive

variable [SampleableType (Fin b → Fin 1 → ZMod q)] [SampleableType (Fin b → ZMod q)] [SampleableType Digest]
  [∀ index memory side, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((base index memory).code side).front) b)]
  [∀ index memory side, SampleableType (Fin ((base index memory).code side).queries → Fin (2^heights ((base index memory).tag side)))]

abbrev program (memory : Memory) :=
  PaddedNTTSequence.program (factory base enc family nodesEnough length psi primitive) enc (List.finRange (d+1)) memory
abbrev witness (dummy : Digest) (memory : Memory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :=
  PaddedNTTSequence.witness (factory base enc family nodesEnough length psi primitive) enc dummy (List.finRange (d+1)) memory initial

/-- The actual loop and its retained witness have identical observable results
and shared final state. -/
theorem project_witness (dummy : Digest) (memory : Memory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :
    (fun outcome => (PaddedNTTSequence.erase (factory base enc family nodesEnough length psi primitive) outcome.1,outcome.2)) <$>
      witness base enc family nodesEnough length psi primitive dummy memory initial =
      (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy
        (AmbientMatrixSource.Shape heights)) (program base enc family nodesEnough length psi primitive memory)).run initial :=
  PaddedNTTSequence.project_witness _ enc dummy _ memory initial

variable (dummy : Digest) (memory : Memory)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
  (outcome : PaddedNTTSequence.Trace (factory base enc family nodesEnough length psi primitive) ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
  (supported : outcome ∈ support (witness base enc family nodesEnough length psi primitive dummy memory initial))

include supported in
/-- Acceptance attempts exactly all d+1 original coefficient/evaluation pairs. -/
theorem accepted_indices (passes : outcome.1.accepted = true) :
    outcome.1.results.map Prod.fst = List.finRange (d+1) :=
  PaddedNTTSequence.accepted_indices _ enc dummy _ memory initial outcome supported passes

include supported in
/-- The actual accepted call count is d+1, independently of private factories. -/
theorem accepted_count (passes : outcome.1.accepted = true) : outcome.1.results.length = d+1 := by
  have order := accepted_indices base enc family nodesEnough length psi primitive dummy memory initial outcome supported passes
  have count := congrArg List.length order
  simpa only [List.length_map,List.length_finRange] using count

include supported in
/-- A retained child uses the scheduled family coefficient/evaluation roots,
even if that call rejects. Neither its factory nor proof bytes choose the pair. -/
theorem retained_roots
    (entry : Fin (d+1) × PaddedNTTSequence.Child (factory base enc family nodesEnough length psi primitive))
    (member : entry ∈ outcome.1.results) : entry.2.2.1.1.1 = roots family entry.1 := by
  obtain ⟨before,present⟩ := PaddedNTTSequence.retained_child_support _ enc dummy _ memory initial outcome supported entry member
  have bound := PaddedNTT.native_witness_roots (base entry.2.1.1 entry.2.1.2) enc (roots family entry.2.1.1)
    q nodesEnough length psi primitive dummy before entry.2.2 present
  exact bound.trans (congrArg (roots family)
    (PaddedNTTSequence.retained_index _ enc dummy _ memory initial outcome supported entry member))

variable {K : Type} [Field K] [Algebra (ZMod q) K] [Fintype K] [DecidableEq K]
  [SampleableType (ZMod q)] [SampleableType (Fin 1 → ZMod q)]
  [∀ index memory side, SampleableType ((Fin (2^((base index memory).code side).front) × Fin b) → K)]

/-- All d+1 NTT rates are derived on the actual ordered dependent loop, with
one enclosing final exclusion and no separately supplied child security bound. -/
theorem original_safe_bound [NeZero b]
    [∀ index memory side, NeZero ((base index memory).code side).m]
    (basis : Module.Basis (Fin b) (ZMod q) K)
    (enough : ∀ index memory side, ((base index memory).code side).m ≤
      Fintype.card (Fin (2^heights ((base index memory).tag side))))
    (capacity : ∀ index memory side, 2^((base index memory).code side).suffix ≤ ((base index memory).code side).m*b)
    (radius : Fin (d+1) → Memory → Bool → ℕ) (epsilon : Fin (d+1) → ENNReal)
    (small : ∀ index memory side, (radius index memory side : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) ((base index memory).domain side))
        ((base index memory).code side).m : Set (Fin (2^heights ((base index memory).tag side)) → K)) : ℚ≥0)/3)
    (calibrated : ∀ index memory,
      ((((1 : ENNReal)/Fintype.card (ZMod q))^b) + (c : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^b))) +
      (JointMatrixOpening.error (K := K) (m := ((base index memory).code false).m) (b := b)
          (queries := ((base index memory).code false).queries) ((base index memory).domain false) (radius index memory false) +
        JointMatrixOpening.error (K := K) (m := ((base index memory).code true).m) (b := b)
          (queries := ((base index memory).code true).queries) ((base index memory).domain true) (radius index memory true)) ≤ epsilon index)
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let actual ← (witness base enc family nodesEnough length psi primitive dummy memory initial)}[
      PaddedNTTSequenceSoundness.AnyOriginalRisk (factory base enc family nodesEnough length psi primitive) enc dummy capacity radius actual.1 ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) actual.2] ≤ ((List.finRange (d+1)).map epsilon).sum :=
  PaddedNTTSequenceSoundness.derived_original_safe_union_bound
    (factory base enc family nodesEnough length psi primitive) enc dummy basis _ enough capacity radius epsilon small
    (fun index before => by simpa only [Nat.cast_one] using calibrated index before) memory initial audited

/-- Accepted false logical NTT relations have the same derived d+1-call rate.
The source owners and child acceptance facts are obtained from execution. -/
theorem accepted_false_bound [NeZero b]
    [∀ index memory side, NeZero ((base index memory).code side).m]
    (basis : Module.Basis (Fin b) (ZMod q) K)
    (enough : ∀ index memory side, ((base index memory).code side).m ≤
      Fintype.card (Fin (2^heights ((base index memory).tag side))))
    (capacity : ∀ index memory side, 2^((base index memory).code side).suffix ≤ ((base index memory).code side).m*b)
    (radius : Fin (d+1) → Memory → Bool → ℕ) (epsilon : Fin (d+1) → ENNReal)
    (small : ∀ index memory side, (radius index memory side : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) ((base index memory).domain side))
        ((base index memory).code side).m : Set (Fin (2^heights ((base index memory).tag side)) → K)) : ℚ≥0)/3)
    (calibrated : ∀ index memory,
      ((((1 : ENNReal)/Fintype.card (ZMod q))^b) + (c : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^b))) +
      (JointMatrixOpening.error (K := K) (m := ((base index memory).code false).m) (b := b)
          (queries := ((base index memory).code false).queries) ((base index memory).domain false) (radius index memory false) +
        JointMatrixOpening.error (K := K) (m := ((base index memory).code true).m) (b := b)
          (queries := ((base index memory).code true).queries) ((base index memory).domain true) (radius index memory true)) ≤ epsilon index)
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let actual ← (witness base enc family nodesEnough length psi primitive dummy memory initial)}[
      actual.1.accepted = true ∧ PaddedNTTSequenceSoundness.AnyFalseRelation (factory base enc family nodesEnough length psi primitive) enc dummy capacity radius actual.1 ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) actual.2] ≤ ((List.finRange (d+1)).map epsilon).sum :=
  (PaddedNTTSequenceSoundness.accepted_false_le_original
    (factory base enc family nodesEnough length psi primitive) enc dummy _ capacity radius memory initial).trans
      (original_safe_bound base enc family nodesEnough length psi primitive dummy memory initial basis enough capacity radius epsilon small calibrated audited)

end
end FormalProof4FHE.HasteBoots.KeySwitchPaddedNTT
