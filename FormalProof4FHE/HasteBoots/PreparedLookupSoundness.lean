module

public import FormalProof4FHE.HasteBoots.PreparedLookupPair

@[expose] public section

/-!
# Prepared lookup success and arithmetic-or-original-opening failure

Supported returned packets inherit the actual earlier sum/EQ/identity results.
Success therefore entails their joint arithmetic event or a wrong original
opening. Concrete partial/full arithmetic bounds survive real reception and
binding work. No supplied PCS flag or query-form certificate is assumed.
-/

open OracleSpec OracleComp BinaryTree
open scoped BigOperators Classical
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim

namespace FormalProof4FHE.HasteBoots.PreparedLookupSoundness

noncomputable section

structure Interface (F K Memory Cfg Input Digest : Type) (width count n : ℕ) where
  receive : Subclaim K 1 n → (Fin n → K) → Subclaim K 1 n → Memory →
    OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (PreparedLookupPair.Values F K width count × Memory)
  bindValues : Subclaim K 1 n → (Fin n → K) → Subclaim K 1 n → PreparedLookupPair.Values F K width count → Memory →
    OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory

abbrev Prepared (F K Memory : Type) (width count n : ℕ) := Option (PreparedLookupPair.Packet F K width count n × Memory)
abbrev Output (F K Memory : Type) (width count n : ℕ) := LookupPairSequence.Result K Memory n × Prepared F K Memory width count n

variable {F K Memory Cfg Input Digest : Type} [Field F] [Field K] [Algebra F K] {d padding c row count : ℕ}

def Wrong (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + padding) → F) : Prepared F K Memory (d + padding) count (c + row) → Prop
  | none => False
  | some entry => LookupPairTerminal.WrongOpenings basis shape sources helpers entry.1.sumClaim entry.1.zeroClaim
      entry.1.values.sources entry.1.values.helper

def PartialEvent (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c) (r y : K) (active : ℕ)
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + padding) → F) : LookupPairSequence.Result K Memory (c + row) → Prop :=
  LookupPairSequence.JointTruthful ExtensionLookupIdentity.partialArity (ExtensionLookupIdentity.partialCoefficient r)
    ExtensionLookupIdentity.partialIndices
    (fun eqPoint => ExtensionLookupIdentity.factors eqPoint y (fun i => LookupSourceFlattening.flatten shape (sources i))
      (fun cell => PaddedExtension.decode basis (helpers cell)) active) (fun cell => PaddedExtension.decode basis (helpers cell))

def FullEvent (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c) (r y : K)
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + padding) → F) : LookupPairSequence.Result K Memory (c + row) → Prop :=
  LookupPairSequence.JointTruthful ExtensionLookupIdentity.fullArity ExtensionLookupIdentity.fullCoefficient
    ExtensionLookupIdentity.fullIndices
    (fun eqPoint => LookupPairArithmetic.fullTables eqPoint r y (fun i => LookupSourceFlattening.flatten shape (sources i))
      (fun cell => PaddedExtension.decode basis (helpers cell))) (fun cell => PaddedExtension.decode basis (helpers cell))

variable [SampleableType (Fin 1 → K)] [SampleableType (Fin (c + row) → K)]

def program (p : ℕ) [CharP K p] {degree : ℕ} (small : degree + 1 ≤ p) (positive : 1 ≤ degree)
    (schedule : LookupPairSequence.Schedule K Memory Cfg Input Digest (c + row) degree)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c) (r y : K)
    (active : ℕ) (enough : active ≤ 2 ^ (c + row)) (publicTotal claimed : K) (memory : Memory)
    (io : Interface F K Memory Cfg Input Digest (d + padding) count (c + row)) :=
  PreparedLookupPair.program p small positive schedule basis shape r y active enough publicTotal claimed memory io.receive io.bindValues

variable {Payload : Type} [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- Original subclaims and computed checking force the arithmetic-or-wrong
opening alternatives on every supported successful partial packet. -/
theorem partial_supported (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (workerShape : Cfg → Skeleton)
    (p : ℕ) [CharP K p] (small : 4 + 1 ≤ p)
    (schedule : LookupPairSequence.Schedule K Memory Cfg Input Digest (c + row) 4)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c) (r y : K)
    (active : ℕ) (enough : active ≤ 2 ^ (c + row)) (publicTotal claimed : K) (memory : Memory)
    (io : Interface F K Memory Cfg Input Digest (d + padding) count (c + row))
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + padding) → F)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) workerShape)
    (outcome : Output F K Memory (d + padding) count (c + row) × CheckpointExecution.State (Input := Input) (Digest := Digest) workerShape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape)
      (program p small (by decide) schedule basis shape r y active enough publicTotal claimed memory io)).run before))
    (accepted : outcome.1.2.isSome = true) :
    PartialEvent basis shape r y active sources helpers outcome.1.1 ∨ Wrong basis shape sources helpers outcome.1.2 := by
  rw [program, PreparedLookupPair.program, SharedContinuation.support_program] at supported
  obtain ⟨earlier, _, later, laterSupported, equal⟩ := supported
  subst outcome
  cases returned : later.1 with
  | none => simp only [returned, Option.isSome_none, Bool.false_eq_true] at accepted
  | some entry =>
    obtain ⟨sumMemory, zeroMemory, earlierEq, checked⟩ := PreparedLookupPair.prepare_sound enc dummy workerShape
      basis shape r y active enough io.receive io.bindValues earlier.1 earlier.2 later laterSupported entry.1 entry.2 returned
    rw [earlierEq]
    have alternatives := LookupPairTerminal.partial_joint_or_wrong basis shape entry.1.eqPoint r y active enough
      sources helpers entry.1.sumClaim entry.1.zeroClaim entry.1.values.sources entry.1.values.helper checked
    simpa only [PartialEvent, Wrong, LookupPairSequence.JointTruthful, LookupPairSequence.SumTruthful,
      LookupPairSequence.IdentityTruthful, ScalarSumcheckOracle.MLETruthful] using alternatives

/-- Full-table packets retain the native degree-three arithmetic event. -/
theorem full_supported (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (workerShape : Cfg → Skeleton)
    (p : ℕ) [CharP K p] (small : 3 + 1 ≤ p)
    (schedule : LookupPairSequence.Schedule K Memory Cfg Input Digest (c + row) 3)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c) (r y : K)
    (publicTotal claimed : K) (memory : Memory)
    (io : Interface F K Memory Cfg Input Digest (d + padding) count (c + row))
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + padding) → F)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) workerShape)
    (outcome : Output F K Memory (d + padding) count (c + row) × CheckpointExecution.State (Input := Input) (Digest := Digest) workerShape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape)
      (program p small (by decide) schedule basis shape r y (2 ^ (c + row)) le_rfl publicTotal claimed memory io)).run before))
    (accepted : outcome.1.2.isSome = true) :
    FullEvent basis shape r y sources helpers outcome.1.1 ∨ Wrong basis shape sources helpers outcome.1.2 := by
  rw [program, PreparedLookupPair.program, SharedContinuation.support_program] at supported
  obtain ⟨earlier, _, later, laterSupported, equal⟩ := supported
  subst outcome
  cases returned : later.1 with
  | none => simp only [returned, Option.isSome_none, Bool.false_eq_true] at accepted
  | some entry =>
    obtain ⟨sumMemory, zeroMemory, earlierEq, checked⟩ := PreparedLookupPair.prepare_sound enc dummy workerShape
      basis shape r y (2 ^ (c + row)) le_rfl io.receive io.bindValues earlier.1 earlier.2 later laterSupported entry.1 entry.2 returned
    rw [earlierEq]
    have alternatives := LookupPairTerminal.full_joint_or_wrong basis shape entry.1.eqPoint r y
      sources helpers entry.1.sumClaim entry.1.zeroClaim entry.1.values.sources entry.1.values.helper checked
    simpa only [FullEvent, Wrong, LookupPairSequence.JointTruthful, LookupPairSequence.SumTruthful,
      LookupPairSequence.IdentityTruthful, ScalarSumcheckOracle.MLETruthful] using alternatives

variable [Fintype K] [DecidableEq K] [SampleableType K]

/-- Actual reception and binding retain the partial arithmetic event and all
issued calls; the helper/source interpretation is the original packed one. -/
theorem partial_retained_bound {active inactive size : ℕ}
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (workerShape : Cfg → Skeleton)
    (p : ℕ) [CharP K p] (small : 4 + 1 ≤ p)
    (schedule : LookupPairSequence.Schedule K Memory Cfg Input Digest (c + row) 4)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c) (logicalShape : active + inactive = 2 ^ (c + row))
    (r y : K) (table : Fin size → Fin count → F) (multiplicities : Fin size → F)
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + padding) → F) (rNonzero : r ≠ 0)
    (notPasses : ¬TupleLookupPair.Passes
      (LookupPairArithmetic.activeTuples logicalShape (fun i => LookupSourceFlattening.flatten shape (sources i))) table
      (fun i => algebraMap F K (multiplicities i)) (y, r))
    (claimed : K) (memory : Memory) (io : Interface F K Memory Cfg Input Digest (d + padding) count (c + row))
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) workerShape) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape)
      (program p small (by decide) schedule basis shape r y active (by omega)
        (LookupPairArithmetic.tableSum r y table multiplicities) claimed memory io)).run before}[
        PartialEvent basis shape r y active sources helpers outcome.1.1] ≤
      ((c + row : ℕ) : ENNReal) / Fintype.card K + ((c + row : ℕ) : ENNReal) * (4 / Fintype.card K) := by
  have retained := SharedContinuation.earlier_event_le enc dummy workerShape
    (LookupPairSequence.program p small (by decide) schedule (LookupPairArithmetic.tableSum r y table multiplicities) claimed memory)
    (PreparedLookupPair.prepare basis shape r y active (by omega) io.receive io.bindValues) before
    (PartialEvent basis shape r y active sources helpers)
  exact retained.trans (LookupPairArithmetic.partial_bound enc dummy workerShape p small schedule logicalShape r y table multiplicities
    (fun i => LookupSourceFlattening.flatten shape (sources i)) (fun cell => PaddedExtension.decode basis (helpers cell))
    rNonzero notPasses claimed memory before)

theorem full_retained_bound {size : ℕ}
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (workerShape : Cfg → Skeleton)
    (p : ℕ) [CharP K p] (small : 3 + 1 ≤ p)
    (schedule : LookupPairSequence.Schedule K Memory Cfg Input Digest (c + row) 3)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (r y : K) (table : Fin size → Fin count → F) (multiplicities : Fin size → F)
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + padding) → F) (rNonzero : r ≠ 0)
    (notPasses : ¬TupleLookupPair.Passes
      (LookupPairArithmetic.activeTuples (active := 2 ^ (c + row)) (inactive := 0) (by omega)
        (fun i => LookupSourceFlattening.flatten shape (sources i))) table
      (fun i => algebraMap F K (multiplicities i)) (y, r))
    (claimed : K) (memory : Memory) (io : Interface F K Memory Cfg Input Digest (d + padding) count (c + row))
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) workerShape) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape)
      (program p small (by decide) schedule basis shape r y (2 ^ (c + row)) le_rfl
        (LookupPairArithmetic.tableSum r y table multiplicities) claimed memory io)).run before}[
        FullEvent basis shape r y sources helpers outcome.1.1] ≤
      ((c + row : ℕ) : ENNReal) / Fintype.card K + ((c + row : ℕ) : ENNReal) * (3 / Fintype.card K) := by
  have retained := SharedContinuation.earlier_event_le enc dummy workerShape
    (LookupPairSequence.program p small (by decide) schedule (LookupPairArithmetic.tableSum r y table multiplicities) claimed memory)
    (PreparedLookupPair.prepare basis shape r y (2 ^ (c + row)) le_rfl io.receive io.bindValues) before
    (FullEvent basis shape r y sources helpers)
  exact retained.trans (LookupPairArithmetic.full_bound enc dummy workerShape p small schedule r y table multiplicities
    (fun i => LookupSourceFlattening.flatten shape (sources i)) (fun cell => PaddedExtension.decode basis (helpers cell))
    rNonzero notPasses claimed memory before)

end

end FormalProof4FHE.HasteBoots.PreparedLookupSoundness
