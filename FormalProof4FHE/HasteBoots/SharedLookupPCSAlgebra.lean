module
public import FormalProof4FHE.HasteBoots.SharedLookupPCS
public import FormalProof4FHE.HasteBoots.RepeatedLookupPCSAlgebra
@[expose] public section

/-! Concrete local facts for the shared terminal/PCS composition. Public totals
are computed per job from literal tables and fixed multiplicities. Packet
provenance, computed acceptance reduction, and the retained arithmetic bound
are derived from the actual common-challenge execution, not supplied as laws. -/
open OracleSpec OracleComp BinaryTree
open scoped Classical
namespace FormalProof4FHE.HasteBoots.SharedLookupPCSAlgebra
noncomputable section
abbrev Mode := RepeatedLookupPCSAlgebra.Mode
abbrev degree := RepeatedLookupPCSAlgebra.degree
abbrev error := RepeatedLookupPCSAlgebra.error

structure Driver (F K Message Memory Cfg Input Digest : Type) (width count jobs n : ℕ) [Field K] where
  schedule : SharedLookupBatchSequence.Schedule K Message Memory Cfg Input Digest jobs n
  receiver : SharedLookupTerminal.Receiver F K Memory Cfg Input Digest width count jobs n
  memory : Memory

variable {F K Message Memory Cfg Input Digest : Type} [Field F] [Field K] [Algebra F K]
  {d padding c row count jobs : ℕ} {columns sizes : Fin jobs → ℕ}
  [SampleableType (Fin 1 → K)] [SampleableType (Fin (c + row) → K)]

def run (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c) (jobsPositive : 0 < jobs)
    (slots : (job : Fin jobs) → Fin (columns job) → Fin count) (pairs : Fin jobs → K × K)
    (active : Fin jobs → ℕ) (enough : ∀ job, active job ≤ 2 ^ (c + row))
    (tables : (job : Fin jobs) → Fin (sizes job) → Fin (columns job) → F)
    (multiplicities : (job : Fin jobs) → Fin (sizes job) → F)
    (algebra : Driver F K Message Memory Cfg Input Digest (d + padding) count jobs (c + row)) :=
  SharedLookupTerminal.program p small algebra.schedule basis shape jobsPositive slots pairs active enough
    (SharedLookupBatchArithmetic.totals pairs tables multiplicities) algebra.memory algebra.receiver

def Arithmetic (mode : Mode) (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (slots : (job : Fin jobs) → Fin (columns job) → Fin count) (active : Fin jobs → ℕ) (pairs : Fin jobs → K × K)
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : Fin jobs → MatrixFold.Cube (c + row) → Fin (d + padding) → F) (selected : Fin jobs)
    (native : SharedLookupPCS.Selection F K Memory (d + padding) count jobs (c + row)) : Prop :=
  match mode with
  | .partialTable => SharedLookupBatchSequence.JointTruthful selected ExtensionLookupIdentity.partialArity
      (ExtensionLookupIdentity.partialCoefficient (pairs selected).2) ExtensionLookupIdentity.partialIndices
      (fun eqPoint => ExtensionLookupIdentity.factors eqPoint (pairs selected).1
        (fun column => LookupSourceFlattening.flatten shape (sources (slots selected column)))
        (fun cell => PaddedExtension.decode basis (helpers selected cell)) (active selected))
      (fun cell => PaddedExtension.decode basis (helpers selected cell)) native.1
  | .full => SharedLookupBatchSequence.JointTruthful selected ExtensionLookupIdentity.fullArity
      (ExtensionLookupIdentity.fullCoefficient (K := K)) ExtensionLookupIdentity.fullIndices
      (fun eqPoint => LookupPairArithmetic.fullTables eqPoint (pairs selected).2 (pairs selected).1
        (fun column => LookupSourceFlattening.flatten shape (sources (slots selected column)))
        (fun cell => PaddedExtension.decode basis (helpers selected cell)))
      (fun cell => PaddedExtension.decode basis (helpers selected cell)) native.1

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [Fintype K] [DecidableEq K] [SampleableType K]

/-- A fixed selected nonpassing job supplies both facts used by the grouped
PCS reduction. Distinct jobs keep their own tables and original source slots. -/
theorem facts {inactive : ℕ}
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (workerShape : Cfg → Skeleton)
    (mode : Mode) (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c) (jobsPositive : 0 < jobs)
    (slots : (job : Fin jobs) → Fin (columns job) → Fin count) (pairs : Fin jobs → K × K)
    (active : Fin jobs → ℕ) (enough : ∀ job, active job ≤ 2 ^ (c + row))
    (tables : (job : Fin jobs) → Fin (sizes job) → Fin (columns job) → F)
    (multiplicities : (job : Fin jobs) → Fin (sizes job) → F)
    (algebra : Driver F K Message Memory Cfg Input Digest (d + padding) count jobs (c + row))
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : Fin jobs → MatrixFold.Cube (c + row) → Fin (d + padding) → F)
    (selected : Fin jobs) (logicalShape : active selected + inactive = 2 ^ (c + row))
    (fullShape : mode = .full → active selected = 2 ^ (c + row))
    (rNonzero : (pairs selected).2 ≠ 0)
    (notPasses : ¬TupleLookupPair.Passes
      (LookupPairArithmetic.activeTuples logicalShape
        (fun column => LookupSourceFlattening.flatten shape (sources (slots selected column)))) (tables selected)
      (fun i => algebraMap F K (multiplicities selected i)) (pairs selected))
    (sumDegree : ∀ points message, (algebra.schedule.interpret points message (selected,false)).natDegree ≤ 1)
    (identityDegree : ∀ points message, (algebra.schedule.interpret points message (selected,true)).natDegree ≤ degree mode) :
    (∀ state native,
      native ∈ support ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape)
        (run p small basis shape jobsPositive slots pairs active enough tables multiplicities algebra)).run state) →
      ∀ packet retainedMemory, native.1.2 = some (packet,retainedMemory) →
        Arithmetic mode basis shape slots active pairs sources helpers selected native.1 ∨
        SharedLookupTerminalReduction.Wrong basis shape slots sources helpers packet) ∧
    (∀ state,
      Pr{let native ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape)
        (run p small basis shape jobsPositive slots pairs active enough tables multiplicities algebra)).run state}[
          Arithmetic mode basis shape slots active pairs sources helpers selected native.1] ≤ error K mode (c + row)) := by
  cases mode with
  | partialTable =>
    constructor
    · intro state native supported packet retainedMemory returned
      exact SharedLookupTerminalReduction.partial_acceptance_or_wrong enc dummy workerShape p small algebra.schedule basis shape
        jobsPositive slots pairs active enough (SharedLookupBatchArithmetic.totals pairs tables multiplicities) algebra.memory algebra.receiver
        state native supported packet retainedMemory returned sources helpers selected
    · intro state
      have arithmetic := SharedLookupBatchArithmetic.partial_bound enc dummy workerShape p small algebra.schedule selected pairs tables multiplicities
        logicalShape (fun column => LookupSourceFlattening.flatten shape (sources (slots selected column)))
        (fun cell => PaddedExtension.decode basis (helpers selected cell)) rNonzero notPasses sumDegree identityDegree algebra.memory state
      have retained := SharedContinuation.earlier_event_le enc dummy workerShape
        (SharedLookupBatchSequence.program p small algebra.schedule (SharedLookupBatchArithmetic.totals pairs tables multiplicities) algebra.memory)
        (SharedLookupTerminal.prepare basis shape jobsPositive slots pairs active enough algebra.receiver) state
        (fun native => Arithmetic .partialTable basis shape slots active pairs sources helpers selected (native,none))
      exact retained.trans arithmetic
  | full =>
    have full := fullShape rfl
    constructor
    · intro state native supported packet retainedMemory returned
      exact SharedLookupTerminalReduction.full_acceptance_or_wrong enc dummy workerShape p small algebra.schedule basis shape
        jobsPositive slots pairs active enough (SharedLookupBatchArithmetic.totals pairs tables multiplicities) algebra.memory algebra.receiver
        state native supported packet retainedMemory returned sources helpers selected full
    · intro state
      have notPassesFull : ¬TupleLookupPair.Passes
          (LookupPairArithmetic.activeTuples (active := 2 ^ (c + row)) (inactive := 0) (by omega)
            (fun column => LookupSourceFlattening.flatten shape (sources (slots selected column)))) (tables selected)
          (fun i => algebraMap F K (multiplicities selected i)) (pairs selected) := by
        have transport (length extra : ℕ) (logical : length + extra = 2 ^ (c + row))
            (isFull : length = 2 ^ (c + row))
            (bad : ¬TupleLookupPair.Passes (LookupPairArithmetic.activeTuples logical
              (fun column => LookupSourceFlattening.flatten shape (sources (slots selected column)))) (tables selected)
              (fun i => algebraMap F K (multiplicities selected i)) (pairs selected)) :
            ¬TupleLookupPair.Passes (LookupPairArithmetic.activeTuples (active := 2 ^ (c + row)) (inactive := 0) (by omega)
              (fun column => LookupSourceFlattening.flatten shape (sources (slots selected column)))) (tables selected)
              (fun i => algebraMap F K (multiplicities selected i)) (pairs selected) := by
          subst length
          have zero : extra = 0 := by omega
          subst extra
          exact bad
        exact transport (active selected) inactive logicalShape full notPasses
      have arithmetic := SharedLookupBatchArithmetic.full_bound enc dummy workerShape p small algebra.schedule selected pairs tables multiplicities
        (fun column => LookupSourceFlattening.flatten shape (sources (slots selected column)))
        (fun cell => PaddedExtension.decode basis (helpers selected cell)) rNonzero notPassesFull sumDegree identityDegree algebra.memory state
      have retained := SharedContinuation.earlier_event_le enc dummy workerShape
        (SharedLookupBatchSequence.program p small algebra.schedule (SharedLookupBatchArithmetic.totals pairs tables multiplicities) algebra.memory)
        (SharedLookupTerminal.prepare basis shape jobsPositive slots pairs active enough algebra.receiver) state
        (fun native => Arithmetic .full basis shape slots active pairs sources helpers selected (native,none))
      exact retained.trans arithmetic
end
end FormalProof4FHE.HasteBoots.SharedLookupPCSAlgebra
