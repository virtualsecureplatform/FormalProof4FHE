module

public import FormalProof4FHE.HasteBoots.CompletedLookupPair

@[expose] public section

/-!
# Concrete lookup completion bounds with accepted opening failures retained

Reception, checked binding and later verification all run on one actual shared
execution. The final accepted-wrong-opening event remains explicit and includes
final acceptance, so rejecting proposals/openings are not counted as attacks.
The later verifier is not postulated secure: grouped original-root PCS must
still discharge this event, including its complete-run availability charge.
-/

open OracleSpec OracleComp BinaryTree
open scoped BigOperators Classical

namespace FormalProof4FHE.HasteBoots.LookupCompletionSoundness

noncomputable section

variable {F K Memory Cfg Input Digest Payload : Type} [Field F] [Field K] [Algebra F K]
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest] [Fintype K] [DecidableEq K] [SampleableType K]
  {d padding c row count : ℕ} [SampleableType (Fin 1 → K)] [SampleableType (Fin (c + row) → K)]

/-- Partial-table completion: no PCS acceptance/security certificate is an
input. The only remaining probabilistic obligation is final accepted wrong
original openings on this exact complete execution. -/
theorem partial_bound {active inactive size : ℕ}
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
    (claimed : K) (memory : Memory)
    (io : PreparedLookupSoundness.Interface F K Memory Cfg Input Digest (d + padding) count (c + row))
    (next : PreparedLookupPair.Packet F K (d + padding) count (c + row) → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Bool)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) workerShape) :
    let preparation := PreparedLookupSoundness.program p small (by decide) schedule basis shape r y active (by omega)
      (LookupPairArithmetic.tableSum r y table multiplicities) claimed memory io
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape)
      (CompletedLookupPair.program preparation next)).run before}[outcome.1.2 = true] ≤
      (((c + row : ℕ) : ENNReal) / Fintype.card K + ((c + row : ℕ) : ENNReal) * (4 / Fintype.card K)) +
      Pr{let outcome ← (simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape)
        (CompletedLookupPair.program preparation next)).run before}[
          outcome.1.2 = true ∧ PreparedLookupSoundness.Wrong basis shape sources helpers outcome.1.1.2] := by
  dsimp only
  apply CompletedLookupPair.probability_bound enc dummy workerShape _ next before
    (fun earlier => PreparedLookupSoundness.PartialEvent basis shape r y active sources helpers earlier.1)
    (PreparedLookupSoundness.Wrong basis shape sources helpers) _
  · intro earlier supported accepted
    exact PreparedLookupSoundness.partial_supported enc dummy workerShape p small schedule basis shape r y active (by omega)
      (LookupPairArithmetic.tableSum r y table multiplicities) claimed memory io sources helpers before earlier supported accepted
  · exact PreparedLookupSoundness.partial_retained_bound enc dummy workerShape p small schedule basis shape logicalShape
      r y table multiplicities sources helpers rNonzero notPasses claimed memory io before

/-- Full-table completion keeps the native smaller degree-three loss. -/
theorem full_bound {size : ℕ}
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
    (claimed : K) (memory : Memory)
    (io : PreparedLookupSoundness.Interface F K Memory Cfg Input Digest (d + padding) count (c + row))
    (next : PreparedLookupPair.Packet F K (d + padding) count (c + row) → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Bool)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) workerShape) :
    let preparation := PreparedLookupSoundness.program p small (by decide) schedule basis shape r y (2 ^ (c + row)) le_rfl
      (LookupPairArithmetic.tableSum r y table multiplicities) claimed memory io
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape)
      (CompletedLookupPair.program preparation next)).run before}[outcome.1.2 = true] ≤
      (((c + row : ℕ) : ENNReal) / Fintype.card K + ((c + row : ℕ) : ENNReal) * (3 / Fintype.card K)) +
      Pr{let outcome ← (simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape)
        (CompletedLookupPair.program preparation next)).run before}[
          outcome.1.2 = true ∧ PreparedLookupSoundness.Wrong basis shape sources helpers outcome.1.1.2] := by
  dsimp only
  apply CompletedLookupPair.probability_bound enc dummy workerShape _ next before
    (fun earlier => PreparedLookupSoundness.FullEvent basis shape r y sources helpers earlier.1)
    (PreparedLookupSoundness.Wrong basis shape sources helpers) _
  · intro earlier supported accepted
    exact PreparedLookupSoundness.full_supported enc dummy workerShape p small schedule basis shape r y
      (LookupPairArithmetic.tableSum r y table multiplicities) claimed memory io sources helpers before earlier supported accepted
  · exact PreparedLookupSoundness.full_retained_bound enc dummy workerShape p small schedule basis shape
      r y table multiplicities sources helpers rNonzero notPasses claimed memory io before

end

end FormalProof4FHE.HasteBoots.LookupCompletionSoundness
