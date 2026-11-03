module

public import FormalProof4FHE.HasteBoots.RepeatedLookupCompletion

@[expose] public section

/-!
# Concrete repeated native lookup algebra bounds for a selected nonpassing pair

All pair parameters and helper words precede the algebra coins. Pairs execute
in canonical order, use the actual prepared verifier, and pass only successful
packets to later shared opening work. A fixed nonpassing index costs one native
scalar loss, not the repetition count times that loss. No local EQ, sumcheck,
packet-provenance or PCS security certificate is supplied to these theorems.
-/

open OracleSpec OracleComp BinaryTree
open scoped Classical

namespace FormalProof4FHE.HasteBoots.RepeatedLookupAlgebra

noncomputable section

variable {F K Memory Cfg Input Digest Payload : Type} [Field F] [Field K] [Algebra F K]
  {d padding c row count repetitions size degree : ℕ}
  [SampleableType (Fin 1 → K)] [SampleableType (Fin (c + row) → K)]

def run (p : ℕ) [CharP K p] (small : degree + 1 ≤ p) (positive : 1 ≤ degree)
    (schedule : Fin repetitions → LookupPairSequence.Schedule K Memory Cfg Input Digest (c + row) degree)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (pairs : Fin repetitions → K × K) (active : ℕ) (enough : active ≤ 2 ^ (c + row))
    (table : Fin size → Fin count → F) (multiplicities : Fin size → F) (claimed : Fin repetitions → K)
    (io : Fin repetitions → PreparedLookupSoundness.Interface F K Memory Cfg Input Digest (d + padding) count (c + row))
    (index : Fin repetitions) (memory : Memory) :=
  PreparedLookupSoundness.program p small positive (schedule index) basis shape (pairs index).2 (pairs index).1 active enough
    (LookupPairArithmetic.tableSum (pairs index).2 (pairs index).1 table multiplicities) (claimed index) memory (io index)

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [Fintype K] [DecidableEq K] [SampleableType K]

/-- Concrete partial-table repeated completion, with native degree four.
The selected pair is fixed before the actual repeated algebra runs. -/
theorem partial_bound {active inactive : ℕ}
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (workerShape : Cfg → Skeleton)
    (p : ℕ) [CharP K p] (small : 4 + 1 ≤ p)
    (schedule : Fin repetitions → LookupPairSequence.Schedule K Memory Cfg Input Digest (c + row) 4)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c) (logicalShape : active + inactive = 2 ^ (c + row))
    (pairs : Fin repetitions → K × K) (selected : Fin repetitions)
    (table : Fin size → Fin count → F) (multiplicities : Fin size → F)
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + padding) → F) (rNonzero : (pairs selected).2 ≠ 0)
    (notPasses : ¬TupleLookupPair.Passes
      (LookupPairArithmetic.activeTuples logicalShape (fun i => LookupSourceFlattening.flatten shape (sources i))) table
      (fun i => algebraMap F K (multiplicities i)) (pairs selected))
    (claimed : Fin repetitions → K)
    (io : Fin repetitions → PreparedLookupSoundness.Interface F K Memory Cfg Input Digest (d + padding) count (c + row))
    (memory : Memory) (fallback : PreparedLookupPair.Packet F K (d + padding) count (c + row))
    (next : (Fin repetitions → PreparedLookupPair.Packet F K (d + padding) count (c + row)) → Memory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Bool)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) workerShape) :
    let verifier := run p small (by decide) schedule basis shape pairs active (by omega) table multiplicities claimed io
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape)
      (RepeatedLookupCompletion.program verifier memory fallback next)).run initial}[outcome.1.2 = true] ≤
      (((c + row : ℕ) : ENNReal) / Fintype.card K + ((c + row : ℕ) : ENNReal) * (4 / Fintype.card K)) +
      Pr{let outcome ← (simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape)
        (RepeatedLookupCompletion.program verifier memory fallback next)).run initial}[
          outcome.1.2 = true ∧
          let packet := RepeatedLookupSelector.packets fallback outcome.1.1 selected
          LookupPairTerminal.WrongOpenings basis shape sources helpers packet.sumClaim packet.zeroClaim packet.values.sources packet.values.helper] := by
  dsimp only
  apply RepeatedLookupCompletion.probability_bound enc dummy workerShape _ selected
    (fun earlier => PreparedLookupSoundness.PartialEvent basis shape (pairs selected).2 (pairs selected).1 active sources helpers earlier.1)
    (fun packet => LookupPairTerminal.WrongOpenings basis shape sources helpers packet.sumClaim packet.zeroClaim packet.values.sources packet.values.helper) _ _ _
    memory fallback next initial
  · intro incoming state native supported packet retainedMemory returned
    have alternatives := PreparedLookupSoundness.partial_supported enc dummy workerShape p small (schedule selected) basis shape
      (pairs selected).2 (pairs selected).1 active (by omega)
      (LookupPairArithmetic.tableSum (pairs selected).2 (pairs selected).1 table multiplicities) (claimed selected) incoming (io selected)
      sources helpers state native supported (by simp only [returned, Option.isSome_some])
    simpa only [PreparedLookupSoundness.Wrong, returned] using alternatives
  · intro incoming state
    exact PreparedLookupSoundness.partial_retained_bound enc dummy workerShape p small (schedule selected) basis shape logicalShape
      (pairs selected).2 (pairs selected).1 table multiplicities sources helpers rNonzero notPasses (claimed selected) incoming (io selected) state

/-- Full-table repetition preserves the smaller native degree-three loss. -/
theorem full_bound
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (workerShape : Cfg → Skeleton)
    (p : ℕ) [CharP K p] (small : 3 + 1 ≤ p)
    (schedule : Fin repetitions → LookupPairSequence.Schedule K Memory Cfg Input Digest (c + row) 3)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (pairs : Fin repetitions → K × K) (selected : Fin repetitions)
    (table : Fin size → Fin count → F) (multiplicities : Fin size → F)
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + padding) → F) (rNonzero : (pairs selected).2 ≠ 0)
    (notPasses : ¬TupleLookupPair.Passes
      (LookupPairArithmetic.activeTuples (active := 2 ^ (c + row)) (inactive := 0) (by omega)
        (fun i => LookupSourceFlattening.flatten shape (sources i))) table
      (fun i => algebraMap F K (multiplicities i)) (pairs selected))
    (claimed : Fin repetitions → K)
    (io : Fin repetitions → PreparedLookupSoundness.Interface F K Memory Cfg Input Digest (d + padding) count (c + row))
    (memory : Memory) (fallback : PreparedLookupPair.Packet F K (d + padding) count (c + row))
    (next : (Fin repetitions → PreparedLookupPair.Packet F K (d + padding) count (c + row)) → Memory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Bool)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) workerShape) :
    let verifier := run p small (by decide) schedule basis shape pairs (2 ^ (c + row)) le_rfl table multiplicities claimed io
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape)
      (RepeatedLookupCompletion.program verifier memory fallback next)).run initial}[outcome.1.2 = true] ≤
      (((c + row : ℕ) : ENNReal) / Fintype.card K + ((c + row : ℕ) : ENNReal) * (3 / Fintype.card K)) +
      Pr{let outcome ← (simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape)
        (RepeatedLookupCompletion.program verifier memory fallback next)).run initial}[
          outcome.1.2 = true ∧
          let packet := RepeatedLookupSelector.packets fallback outcome.1.1 selected
          LookupPairTerminal.WrongOpenings basis shape sources helpers packet.sumClaim packet.zeroClaim packet.values.sources packet.values.helper] := by
  dsimp only
  apply RepeatedLookupCompletion.probability_bound enc dummy workerShape _ selected
    (fun earlier => PreparedLookupSoundness.FullEvent basis shape (pairs selected).2 (pairs selected).1 sources helpers earlier.1)
    (fun packet => LookupPairTerminal.WrongOpenings basis shape sources helpers packet.sumClaim packet.zeroClaim packet.values.sources packet.values.helper) _ _ _
    memory fallback next initial
  · intro incoming state native supported packet retainedMemory returned
    have alternatives := PreparedLookupSoundness.full_supported enc dummy workerShape p small (schedule selected) basis shape
      (pairs selected).2 (pairs selected).1
      (LookupPairArithmetic.tableSum (pairs selected).2 (pairs selected).1 table multiplicities) (claimed selected) incoming (io selected)
      sources helpers state native supported (by simp only [returned, Option.isSome_some])
    simpa only [PreparedLookupSoundness.Wrong, returned] using alternatives
  · intro incoming state
    exact PreparedLookupSoundness.full_retained_bound enc dummy workerShape p small (schedule selected) basis shape
      (pairs selected).2 (pairs selected).1 table multiplicities sources helpers rNonzero notPasses (claimed selected) incoming (io selected) state

end

end FormalProof4FHE.HasteBoots.RepeatedLookupAlgebra
