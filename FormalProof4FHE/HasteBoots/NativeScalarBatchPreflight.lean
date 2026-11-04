module

public import FormalProof4FHE.HasteBoots.NativeScalarBatchWire
public import FormalProof4FHE.HasteBoots.NativeGoldLookup
public import Mathlib.Algebra.CharP.Algebra

@[expose] public section

/-!
# Native scalar-batch shape, dimensions and independent recurrences

The proof shape is checked before binding the statement. The native node
loop retains every raw addition until a zero is reached. Every recurrence
is checked separately; no aggregate or random linear combination is used.
Full round execution, interpolation and Rust/work refinement remain open.
-/

namespace FormalProof4FHE.HasteBoots.NativeScalarBatchPreflight

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeGoldExtensionArithmetic (Word)
open NativeScalarBatchWire
open NativePrefixCodec (Vector)

abbrev Instance := NativePrefixCodec.Vector Message
abbrev Proof := NativePrefixCodec.Vector Instance

def nodesFrom : ℕ → Word → Bool
  | 0, _ => true
  | count + 1, node =>
      let next := NativeGoldExtensionArithmetic.add node NativeGoldLookup.one
      !NativeGoldLookup.isZero next && nodesFrom count next

def proofShape (statement : Statement) (proof : Proof) : Bool :=
  decide (proof.val.length = statement.infos.val.length) &&
    (statement.infos.val.zip proof.val).all (fun pair =>
      decide (pair.2.val.length = pair.1.numVariables.val) &&
      decide (pair.1.maxMultiplicands.val + 1 < 2 ^ 64) &&
      pair.2.val.all (fun message =>
        decide (message.evaluations.val.length = pair.1.maxMultiplicands.val + 1)))

def metadataDimensions (statement : Statement) : Bool :=
  match statement.infos.val with
  | [] => false
  | first :: _ =>
      decide (statement.infos.val.length = statement.claims.val.length) &&
      decide (first.numVariables.val ≠ 0) &&
      statement.infos.val.all (fun info =>
        decide (info.numVariables = first.numVariables) &&
        decide (info.maxMultiplicands.val ≠ 0) &&
        decide (info.maxMultiplicands.val + 1 < 2 ^ 64))

def interpolationNodes (statement : Statement) : Bool :=
  statement.infos.val.all (fun info => nodesFrom info.maxMultiplicands.val NativeGoldLookup.zero)

def dimensions (statement : Statement) : Bool := metadataDimensions statement && interpolationNodes statement

inductive Error where
  | proofShape | emptyBatch | dimensions | nodes | recurrence
  deriving DecidableEq

/-- No statement bytes are absorbed when either native preflight fails. -/
def beginVerify (transcript : NativeTranscript.Transcript) (statement : Statement) (proof : Proof) :
    Except Error NativeTranscript.Transcript :=
  if proofShape statement proof then
    if statement.infos.val = [] then .error .emptyBatch else
    if metadataDimensions statement then
      if interpolationNodes statement then .ok (bindStatement transcript statement) else .error .nodes
    else .error .dimensions
  else .error .proofShape

/-- Checked native first-two-entry access. Shape validation will discharge
these index preconditions before the actual round checker uses them. -/
def recurrence (message : Message) (expected : Word) : Bool :=
  match message.evaluations.val with
  | first :: second :: _ =>
      decide (∀ coordinate, NativeFieldRepresentation.goldCanonical
        (NativeGoldExtensionArithmetic.add first second coordinate) =
        NativeFieldRepresentation.goldCanonical (expected coordinate))
  | _ => false

def check (messages : List Message) (expected : List Word) : Bool :=
  (messages.zip expected).all (fun pair => recurrence pair.1 pair.2)

/-- Separate guard from the challenge request: rejection has no binding. -/
def bindCheckedRound (transcript : NativeTranscript.Transcript) (packet : RoundPacket) (expected : List Word) :
    Except Error NativeTranscript.Transcript :=
  if check packet.messages.val expected then .ok (bindRound transcript packet) else .error .recurrence

def FitsInfo (info : Info) (certificate : Instance) : Prop :=
  certificate.val.length = info.numVariables.val ∧
    info.maxMultiplicands.val + 1 < 2 ^ 64 ∧
    ∀ message ∈ certificate.val, message.evaluations.val.length = info.maxMultiplicands.val + 1

private theorem not_true_iff (value : Bool) : (!value) = true ↔ value = false := by cases value <;> decide

noncomputable section

private theorem isZero_false_iff (value : Word) : NativeGoldLookup.isZero value = false ↔ goldExtensionValue value ≠ 0 := by
  change NativeGoldLookup.isZero value = false ↔ ¬(goldExtensionValue value = 0)
  rw [← NativeGoldLookup.isZero_iff]
  cases NativeGoldLookup.isZero value <;> decide

/-- All checked consecutive nodes, not merely the final accumulator. -/
theorem nodesFrom_iff (count : ℕ) (node : Word) :
    nodesFrom count node = true ↔
      ∀ i : ℕ, 0 < i → i ≤ count → goldExtensionValue node + (i : Goldilocks3) ≠ 0 := by
  induction count generalizing node with
  | zero =>
    constructor
    · intro _ i positive small
      omega
    · intro _
      rfl
  | succ count ih =>
    rw [nodesFrom, Bool.and_eq_true, not_true_iff, isZero_false_iff, ih,
      NativeGoldExtensionArithmetic.add_value, NativeGoldLookup.one_value]
    constructor
    · rintro ⟨first, rest⟩ i positive small
      by_cases firstIndex : i = 1
      · simpa only [firstIndex, Nat.cast_one] using first
      · have next := rest (i - 1) (by omega) (by omega)
        have shift : goldExtensionValue node + 1 + ((i - 1 : ℕ) : Goldilocks3) =
            goldExtensionValue node + (i : Goldilocks3) := by
          rw [add_assoc, ← Nat.cast_one, ← Nat.cast_add, show 1 + (i - 1) = i by omega]
        rwa [shift] at next
    · intro all
      refine ⟨?_, ?_⟩
      · simpa only [Nat.cast_one] using all 1 (by omega) (by omega)
      · intro i positive small
        have next := all (i + 1) (by omega) (by omega)
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using next

local instance goldCharacteristic : CharP Goldilocks3 goldilocksModulus :=
  charP_of_injective_algebraMap (algebraMap Goldilocks Goldilocks3).injective goldilocksModulus

/-- The literal loop enforces the native noncolliding-node degree range. -/
theorem nodesFrom_zero_iff (count : ℕ) : nodesFrom count NativeGoldLookup.zero = true ↔ count < goldilocksModulus := by
  rw [nodesFrom_iff]
  simp only [NativeGoldLookup.zero_value, zero_add]
  constructor
  · intro valid
    by_contra large
    have positive : 0 < goldilocksModulus := by decide
    have failure := valid goldilocksModulus positive (by omega)
    exact failure (CharP.cast_eq_zero Goldilocks3 goldilocksModulus)
  · intro small i positive bound zero
    have divides := (CharP.cast_eq_zero_iff Goldilocks3 goldilocksModulus i).mp zero
    exact (Nat.not_dvd_of_pos_of_lt positive (bound.trans_lt small)) divides

theorem beginVerify_proof_failure (transcript : NativeTranscript.Transcript) (statement : Statement) (proof : Proof)
    (failed : proofShape statement proof = false) : beginVerify transcript statement proof = .error .proofShape := by
  simp only [beginVerify, failed, Bool.false_eq_true, ite_false]

theorem beginVerify_empty_failure (transcript : NativeTranscript.Transcript) (statement : Statement) (proof : Proof)
    (shape : proofShape statement proof = true) (empty : statement.infos.val = []) :
    beginVerify transcript statement proof = .error .emptyBatch := by
  simp only [beginVerify, shape, ite_true, empty]

theorem beginVerify_dimension_failure (transcript : NativeTranscript.Transcript) (statement : Statement) (proof : Proof)
    (shape : proofShape statement proof = true) (nonempty : statement.infos.val ≠ [])
    (failed : metadataDimensions statement = false) :
    beginVerify transcript statement proof = .error .dimensions := by
  simp only [beginVerify, shape, ite_true, nonempty, ite_false, failed, Bool.false_eq_true]

theorem beginVerify_node_failure (transcript : NativeTranscript.Transcript) (statement : Statement) (proof : Proof)
    (shape : proofShape statement proof = true) (metadata : metadataDimensions statement = true)
    (failed : interpolationNodes statement = false) :
    beginVerify transcript statement proof = .error .nodes := by
  have nonempty : statement.infos.val ≠ [] := by
    intro empty
    simp only [metadataDimensions, empty, Bool.false_eq_true] at metadata
  simp only [beginVerify, shape, ite_true, nonempty, ite_false, metadata, failed, Bool.false_eq_true]

theorem recurrence_iff (first second : Word) (tail : List Word) (fits : (first :: second :: tail).length < 2 ^ 64)
    (expected : Word) : recurrence ⟨⟨first :: second :: tail, fits⟩⟩ expected = true ↔
      goldExtensionValue first + goldExtensionValue second = goldExtensionValue expected := by
  rw [recurrence, decide_eq_true_eq]
  exact NativeGoldExtensionArithmetic.recurrence_iff first second expected

theorem check_cons (message : Message) (messages : List Message) (claim : Word) (claims : List Word) :
    check (message :: messages) (claim :: claims) = true ↔ recurrence message claim = true ∧ check messages claims = true := by
  simp only [check, List.zip_cons_cons, List.all_cons, Bool.and_eq_true]

theorem bindCheckedRound_failure (transcript : NativeTranscript.Transcript) (packet : RoundPacket) (expected : List Word)
    (failed : check packet.messages.val expected = false) :
    bindCheckedRound transcript packet expected = .error .recurrence := by
  simp only [bindCheckedRound, failed, Bool.false_eq_true, ite_false]

theorem proofShape_iff (statement : Statement) (proof : Proof) :
    proofShape statement proof = true ↔ List.Forall₂ FitsInfo statement.infos.val proof.val := by
  rw [List.forall₂_iff_zip]
  simp only [proofShape, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, and_assoc]
  constructor
  · rintro ⟨length, all⟩
    exact ⟨length.symm, fun {info} {certificate} member => all (info, certificate) member⟩
  · rintro ⟨length, all⟩
    exact ⟨length.symm, fun pair member => all member⟩

/-- Successful dimensions supply a nonempty common variable count and every
trusted independent equation's positive, noncolliding degree. -/
theorem dimensions_success (statement : Statement) (accepted : dimensions statement = true) :
    ∃ first, statement.infos.val.head? = some first ∧
      statement.infos.val.length = statement.claims.val.length ∧ first.numVariables.val ≠ 0 ∧
      ∀ info ∈ statement.infos.val, info.numVariables = first.numVariables ∧
        info.maxMultiplicands.val ≠ 0 ∧ info.maxMultiplicands.val < goldilocksModulus := by
  cases source : statement.infos.val with
  | nil => simp only [dimensions, metadataDimensions, source, Bool.false_and, Bool.false_eq_true] at accepted
  | cons first rest =>
    rw [dimensions, metadataDimensions, interpolationNodes, source] at accepted
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, nodesFrom_zero_iff, and_assoc] at accepted
    refine ⟨first, rfl, accepted.1, accepted.2.1, ?_⟩
    intro info member
    have present : info ∈ first :: rest := member
    exact ⟨(accepted.2.2.1 info present).1, (accepted.2.2.1 info present).2.1,
      accepted.2.2.2 info present⟩

theorem beginVerify_ok_iff (transcript result : NativeTranscript.Transcript) (statement : Statement) (proof : Proof) :
    beginVerify transcript statement proof = .ok result ↔
      proofShape statement proof = true ∧ dimensions statement = true ∧ result = bindStatement transcript statement := by
  by_cases empty : statement.infos.val = []
  · cases hs : proofShape statement proof <;> simp [beginVerify, dimensions, metadataDimensions, empty, hs]
  · cases hs : proofShape statement proof <;> cases hm : metadataDimensions statement <;>
      cases hn : interpolationNodes statement <;> simp [beginVerify, dimensions, empty, hs, hm, hn, eq_comm]

/-- With the preflight's length invariant, the native zip checks every
independent equation; it cannot silently drop unmatched claims. -/
theorem check_iff (messages : List Message) (expected : List Word) (length : messages.length = expected.length) :
    check messages expected = true ↔ List.Forall₂ (fun message claim => recurrence message claim = true) messages expected := by
  rw [List.forall₂_iff_zip]
  simp only [check, List.all_eq_true]
  exact ⟨fun all => ⟨length, fun {message} {claim} member => all (message, claim) member⟩,
    fun all pair member => all.2 member⟩

end

end FormalProof4FHE.HasteBoots.NativeScalarBatchPreflight
