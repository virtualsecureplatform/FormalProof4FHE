module

public import FormalProof4FHE.HasteBoots.RepeatedLookupPCS

@[expose] public section

/-!
# Concrete algebra facts for both branches of the combined native verifier

The partial/full branch fixes the native degree. Public totals are computed
from the table/multiplicities and already-selected pair vector. Local support,
packet provenance and scalar probability facts are derived here, rather than
assumed as certificates at the staged PCS boundary.
-/

open OracleSpec OracleComp BinaryTree
open scoped Classical

namespace FormalProof4FHE.HasteBoots.RepeatedLookupPCSAlgebra

noncomputable section

inductive Mode | partialTable | full

def degree : Mode → ℕ | .partialTable => 4 | .full => 3

structure ScheduleData (F K Memory Cfg Input Digest : Type) (width count n repetitions : ℕ) (mode : Mode) where
  schedule : Fin repetitions → LookupPairSequence.Schedule K Memory Cfg Input Digest n (degree mode)
  claimed : Fin repetitions → K
  io : Fin repetitions → PreparedLookupSoundness.Interface F K Memory Cfg Input Digest width count n
  memory : Memory

variable {F K Memory Cfg Input Digest : Type} [Field F] [Field K] [Algebra F K]
  {d padding c row count repetitions size : ℕ}
  [SampleableType (Fin 1 → K)] [SampleableType (Fin (c + row) → K)]

def run (mode : Mode) (p : ℕ) [CharP K p] (small : degree mode + 1 ≤ p)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (active : ℕ) (enough : active ≤ 2 ^ (c + row))
    (table : Fin size → Fin count → F) (multiplicities : Fin size → F) (pairs : Fin repetitions → K × K)
    (algebra : ScheduleData F K Memory Cfg Input Digest (d + padding) count (c + row) repetitions mode) :=
  RepeatedLookupAlgebra.run p small (by cases mode <;> decide) algebra.schedule basis shape pairs active enough
    table multiplicities algebra.claimed algebra.io

def Arithmetic (mode : Mode) (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (active : ℕ) (r y : K) (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + padding) → F)
    (native : PreparedLookupSoundness.Output F K Memory (d + padding) count (c + row)) : Prop :=
  match mode with
  | .partialTable => PreparedLookupSoundness.PartialEvent basis shape r y active sources helpers native.1
  | .full => PreparedLookupSoundness.FullEvent basis shape r y sources helpers native.1

def error (K : Type) [Fintype K] (mode : Mode) (n : ℕ) : ENNReal :=
  (n : ENNReal) / Fintype.card K + (n : ENNReal) * ((degree mode : ENNReal) / Fintype.card K)

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [Fintype K] [DecidableEq K] [SampleableType K]

/-- Both native local interfaces are proved for a selected nonpassing pair.
The full branch explicitly requires its public logical length to be full. -/
theorem facts {active inactive : ℕ}
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (workerShape : Cfg → Skeleton)
    (mode : Mode) (p : ℕ) [CharP K p] (small : degree mode + 1 ≤ p)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (logicalShape : active + inactive = 2 ^ (c + row)) (fullShape : mode = .full → active = 2 ^ (c + row))
    (table : Fin size → Fin count → F) (multiplicities : Fin size → F) (pairs : Fin repetitions → K × K)
    (algebra : ScheduleData F K Memory Cfg Input Digest (d + padding) count (c + row) repetitions mode)
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + padding) → F)
    (selected : Fin repetitions) (rNonzero : (pairs selected).2 ≠ 0)
    (notPasses : ¬TupleLookupPair.Passes
      (LookupPairArithmetic.activeTuples logicalShape (fun i => LookupSourceFlattening.flatten shape (sources i))) table
      (fun i => algebraMap F K (multiplicities i)) (pairs selected)) :
    (∀ incoming state native,
      native ∈ support ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape)
        (run mode p small basis shape active (by omega) table multiplicities pairs algebra selected incoming)).run state) →
      ∀ packet retainedMemory, native.1.2 = some (packet, retainedMemory) →
        Arithmetic mode basis shape active (pairs selected).2 (pairs selected).1 sources helpers native.1 ∨
        LookupPairTerminal.WrongOpenings basis shape sources helpers packet.sumClaim packet.zeroClaim packet.values.sources packet.values.helper) ∧
    (∀ incoming state,
      Pr{let native ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape)
        (run mode p small basis shape active (by omega) table multiplicities pairs algebra selected incoming)).run state}[
          Arithmetic mode basis shape active (pairs selected).2 (pairs selected).1 sources helpers native.1] ≤ error K mode (c + row)) := by
  cases mode with
  | partialTable =>
    constructor
    · intro incoming state native supported packet retainedMemory returned
      have alternatives := PreparedLookupSoundness.partial_supported enc dummy workerShape p small (algebra.schedule selected) basis shape
        (pairs selected).2 (pairs selected).1 active (by omega)
        (LookupPairArithmetic.tableSum (pairs selected).2 (pairs selected).1 table multiplicities) (algebra.claimed selected)
        incoming (algebra.io selected) sources helpers state native supported (by simp only [returned, Option.isSome_some])
      simpa only [Arithmetic, PreparedLookupSoundness.Wrong, returned] using alternatives
    · intro incoming state
      exact PreparedLookupSoundness.partial_retained_bound enc dummy workerShape p small (algebra.schedule selected) basis shape logicalShape
        (pairs selected).2 (pairs selected).1 table multiplicities sources helpers rNonzero notPasses (algebra.claimed selected)
        incoming (algebra.io selected) state
  | full =>
    have equal := fullShape rfl
    subst active
    constructor
    · intro incoming state native supported packet retainedMemory returned
      have alternatives := PreparedLookupSoundness.full_supported enc dummy workerShape p small (algebra.schedule selected) basis shape
        (pairs selected).2 (pairs selected).1
        (LookupPairArithmetic.tableSum (pairs selected).2 (pairs selected).1 table multiplicities) (algebra.claimed selected)
        incoming (algebra.io selected) sources helpers state native supported (by simp only [returned, Option.isSome_some])
      simpa only [Arithmetic, PreparedLookupSoundness.Wrong, returned] using alternatives
    · intro incoming state
      exact PreparedLookupSoundness.full_retained_bound enc dummy workerShape p small (algebra.schedule selected) basis shape
        (pairs selected).2 (pairs selected).1 table multiplicities sources helpers rNonzero notPasses (algebra.claimed selected)
        incoming (algebra.io selected) state

end

end FormalProof4FHE.HasteBoots.RepeatedLookupPCSAlgebra
