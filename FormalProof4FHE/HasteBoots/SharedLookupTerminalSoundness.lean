module
public import FormalProof4FHE.HasteBoots.SharedLookupTerminalReduction
@[expose] public section

/-! Computed terminal acceptance without a wrong original opening is bounded
by the actual ordered-EQ/common-batch arithmetic error. This event restriction
is analysis, not a caller-supplied authentication certificate. Grouped PCS
will control its complement on the same continued execution. -/
open OracleSpec OracleComp BinaryTree
open scoped BigOperators Classical
namespace FormalProof4FHE.HasteBoots.SharedLookupTerminalSoundness
noncomputable section
variable {F K Memory : Type} [Field F] [Field K] [Algebra F K]
  {d padding c row count jobs : ℕ} {columns sizes : Fin jobs → ℕ}

abbrev Result (F K Memory : Type) (width count jobs n : ℕ) :=
  SharedLookupBatchSequence.Result K Memory jobs n ×
    Option (SharedLookupOpeningFamily.Packet F K width count n jobs × Memory)

def AcceptedWithoutWrong (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (slots : (job : Fin jobs) → Fin (columns job) → Fin count)
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : Fin jobs → MatrixFold.Cube (c + row) → Fin (d + padding) → F)
    (result : Result F K Memory (d + padding) count jobs (c + row)) : Prop :=
  ∃ packet memory, result.2 = some (packet,memory) ∧
    ¬SharedLookupTerminalReduction.Wrong basis shape slots sources helpers packet

variable {Message Cfg Input Digest Payload : Type} [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [Fintype K] [DecidableEq K] [SampleableType K]
  [SampleableType (Fin 1 → K)] [SampleableType (Fin (c + row) → K)]

/-- For a fixed nonpassing job, the actual computed terminal program can
accept without a wrong opening only within the degree-four arithmetic loss.
Its received values and binding work remain in the same shared execution. -/
theorem partial_bound {inactive : ℕ}
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (workerShape : Cfg → Skeleton)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (schedule : SharedLookupBatchSequence.Schedule K Message Memory Cfg Input Digest jobs (c + row))
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (jobsPositive : 0 < jobs) (slots : (job : Fin jobs) → Fin (columns job) → Fin count)
    (pairs : Fin jobs → K × K) (active : Fin jobs → ℕ) (enough : ∀ job, active job ≤ 2 ^ (c + row))
    (tables : (job : Fin jobs) → Fin (sizes job) → Fin (columns job) → F)
    (multiplicities : (job : Fin jobs) → Fin (sizes job) → F)
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : Fin jobs → MatrixFold.Cube (c + row) → Fin (d + padding) → F)
    (selected : Fin jobs) (logicalShape : active selected + inactive = 2 ^ (c + row))
    (rNonzero : (pairs selected).2 ≠ 0)
    (notPasses : ¬TupleLookupPair.Passes
      (LookupPairArithmetic.activeTuples logicalShape
        (fun column => LookupSourceFlattening.flatten shape (sources (slots selected column)))) (tables selected)
      (fun i => algebraMap F K (multiplicities selected i)) (pairs selected))
    (sumDegree : ∀ points message, (schedule.interpret points message (selected,false)).natDegree ≤ 1)
    (identityDegree : ∀ points message, (schedule.interpret points message (selected,true)).natDegree ≤ 4)
    (memory : Memory) (receiver : SharedLookupTerminal.Receiver F K Memory Cfg Input Digest (d + padding) count jobs (c + row))
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) workerShape) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape)
      (SharedLookupTerminal.program p small schedule basis shape jobsPositive slots pairs active enough
        (SharedLookupBatchArithmetic.totals pairs tables multiplicities) memory receiver)).run before}[
        AcceptedWithoutWrong basis shape slots sources helpers outcome.1] ≤
      ((c + row : ℕ) : ENNReal) / Fintype.card K + ((c + row : ℕ) : ENNReal) * (4 / Fintype.card K) := by
  let event : SharedLookupBatchSequence.Result K Memory jobs (c + row) → Prop := SharedLookupBatchSequence.JointTruthful selected ExtensionLookupIdentity.partialArity
    (ExtensionLookupIdentity.partialCoefficient (pairs selected).2) ExtensionLookupIdentity.partialIndices
    (fun eqPoint => ExtensionLookupIdentity.factors eqPoint (pairs selected).1
      (fun column => LookupSourceFlattening.flatten shape (sources (slots selected column)))
      (fun cell => PaddedExtension.decode basis (helpers selected cell)) (active selected))
    (fun cell => PaddedExtension.decode basis (helpers selected cell))
  have arithmetic := SharedLookupBatchArithmetic.partial_bound enc dummy workerShape p small schedule selected pairs tables multiplicities
    logicalShape (fun column => LookupSourceFlattening.flatten shape (sources (slots selected column)))
    (fun cell => PaddedExtension.decode basis (helpers selected cell)) rNonzero notPasses sumDegree identityDegree memory before
  have retained := SharedContinuation.earlier_event_le enc dummy workerShape
    (SharedLookupBatchSequence.program p small schedule (SharedLookupBatchArithmetic.totals pairs tables multiplicities) memory)
    (SharedLookupTerminal.prepare basis shape jobsPositive slots pairs active enough receiver) before event
  have included := prEvent_mono_of_support
    ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape)
      (SharedLookupTerminal.program p small schedule basis shape jobsPositive slots pairs active enough
        (SharedLookupBatchArithmetic.totals pairs tables multiplicities) memory receiver)).run before)
    (fun outcome => AcceptedWithoutWrong basis shape slots sources helpers outcome.1)
    (fun outcome => event outcome.1.1) (by
      intro outcome supported clean
      obtain ⟨packet,finalMemory,returned,noWrong⟩ := clean
      have reduction := SharedLookupTerminalReduction.partial_acceptance_or_wrong enc dummy workerShape p small schedule basis shape
        jobsPositive slots pairs active enough (SharedLookupBatchArithmetic.totals pairs tables multiplicities) memory receiver
        before outcome supported packet finalMemory returned sources helpers selected
      exact reduction.resolve_right noWrong)
  exact included.trans (retained.trans arithmetic)
/-- For a fixed nonpassing job, the actual computed terminal program can
accept without a wrong opening only within the degree-three arithmetic loss.
Its received values and binding work remain in the same shared execution. -/
theorem full_bound
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (workerShape : Cfg → Skeleton)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (schedule : SharedLookupBatchSequence.Schedule K Message Memory Cfg Input Digest jobs (c + row))
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (jobsPositive : 0 < jobs) (slots : (job : Fin jobs) → Fin (columns job) → Fin count)
    (pairs : Fin jobs → K × K) (active : Fin jobs → ℕ) (enough : ∀ job, active job ≤ 2 ^ (c + row))
    (tables : (job : Fin jobs) → Fin (sizes job) → Fin (columns job) → F)
    (multiplicities : (job : Fin jobs) → Fin (sizes job) → F)
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : Fin jobs → MatrixFold.Cube (c + row) → Fin (d + padding) → F)
    (selected : Fin jobs) (selectedFull : active selected = 2 ^ (c + row))
    (rNonzero : (pairs selected).2 ≠ 0)
    (notPasses : ¬TupleLookupPair.Passes
      (LookupPairArithmetic.activeTuples (active := 2 ^ (c + row)) (inactive := 0) (by omega)
        (fun column => LookupSourceFlattening.flatten shape (sources (slots selected column)))) (tables selected)
      (fun i => algebraMap F K (multiplicities selected i)) (pairs selected))
    (sumDegree : ∀ points message, (schedule.interpret points message (selected,false)).natDegree ≤ 1)
    (identityDegree : ∀ points message, (schedule.interpret points message (selected,true)).natDegree ≤ 3)
    (memory : Memory) (receiver : SharedLookupTerminal.Receiver F K Memory Cfg Input Digest (d + padding) count jobs (c + row))
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) workerShape) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape)
      (SharedLookupTerminal.program p small schedule basis shape jobsPositive slots pairs active enough
        (SharedLookupBatchArithmetic.totals pairs tables multiplicities) memory receiver)).run before}[
        AcceptedWithoutWrong basis shape slots sources helpers outcome.1] ≤
      ((c + row : ℕ) : ENNReal) / Fintype.card K + ((c + row : ℕ) : ENNReal) * (3 / Fintype.card K) := by
  let event : SharedLookupBatchSequence.Result K Memory jobs (c + row) → Prop := SharedLookupBatchSequence.JointTruthful selected ExtensionLookupIdentity.fullArity
    (ExtensionLookupIdentity.fullCoefficient (K := K)) ExtensionLookupIdentity.fullIndices
    (fun eqPoint => LookupPairArithmetic.fullTables eqPoint (pairs selected).2 (pairs selected).1
      (fun column => LookupSourceFlattening.flatten shape (sources (slots selected column)))
      (fun cell => PaddedExtension.decode basis (helpers selected cell)))
    (fun cell => PaddedExtension.decode basis (helpers selected cell))
  have arithmetic := SharedLookupBatchArithmetic.full_bound enc dummy workerShape p small schedule selected pairs tables multiplicities
    (fun column => LookupSourceFlattening.flatten shape (sources (slots selected column)))
    (fun cell => PaddedExtension.decode basis (helpers selected cell)) rNonzero notPasses sumDegree identityDegree memory before
  have retained := SharedContinuation.earlier_event_le enc dummy workerShape
    (SharedLookupBatchSequence.program p small schedule (SharedLookupBatchArithmetic.totals pairs tables multiplicities) memory)
    (SharedLookupTerminal.prepare basis shape jobsPositive slots pairs active enough receiver) before event
  have included := prEvent_mono_of_support
    ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape)
      (SharedLookupTerminal.program p small schedule basis shape jobsPositive slots pairs active enough
        (SharedLookupBatchArithmetic.totals pairs tables multiplicities) memory receiver)).run before)
    (fun outcome => AcceptedWithoutWrong basis shape slots sources helpers outcome.1)
    (fun outcome => event outcome.1.1) (by
      intro outcome supported clean
      obtain ⟨packet,finalMemory,returned,noWrong⟩ := clean
      have reduction := SharedLookupTerminalReduction.full_acceptance_or_wrong enc dummy workerShape p small schedule basis shape
        jobsPositive slots pairs active enough (SharedLookupBatchArithmetic.totals pairs tables multiplicities) memory receiver
        before outcome supported packet finalMemory returned sources helpers selected selectedFull
      exact reduction.resolve_right noWrong)
  exact included.trans (retained.trans arithmetic)
end
end FormalProof4FHE.HasteBoots.SharedLookupTerminalSoundness
