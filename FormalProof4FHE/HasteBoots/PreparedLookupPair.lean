module

public import FormalProof4FHE.HasteBoots.LookupPairTerminal

@[expose] public section

/-!
# Operational lookup terminal reception and checked binding

Successful scalar stages receive original source claim vectors and one helper
value. The verifier computes decoding and the terminal equality itself, then
binds these values only after success. Rejection preserves received work and
skips binding. No ghost source table is an operational argument. The retained
stage result supports arithmetic/PCS composition on the same shared state.
-/

open OracleSpec OracleComp BinaryTree
open scoped Classical
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim

namespace FormalProof4FHE.HasteBoots.PreparedLookupPair

noncomputable section

structure Values (F K : Type) (width count : ℕ) where
  sources : Fin count → Fin width → F
  helper : K

structure Packet (F K : Type) (width count n : ℕ) where
  sumClaim : Subclaim K 1 n
  eqPoint : Fin n → K
  zeroClaim : Subclaim K 1 n
  values : Values F K width count

variable {F K Memory Cfg Input Digest : Type} [Field F] [Field K] [Algebra F K]
  {d padding c row count : ℕ}

def prepare (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c) (r y : K)
    (active : ℕ) (enough : active ≤ 2 ^ (c + row))
    (receive : Subclaim K 1 (c + row) → (Fin (c + row) → K) → Subclaim K 1 (c + row) → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Values F K (d + padding) count × Memory))
    (bindValues : Subclaim K 1 (c + row) → (Fin (c + row) → K) → Subclaim K 1 (c + row) →
      Values F K (d + padding) count → Memory → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (earlier : LookupPairSequence.Result K Memory (c + row)) :
    OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Option (Packet F K (d + padding) count (c + row) × Memory)) :=
  match earlier.1, earlier.2 with
  | some sumEntry, some (eqPoint, some zeroEntry) => do
    let proposal ← receive sumEntry.1 eqPoint zeroEntry.1 zeroEntry.2
    if LookupPairTerminal.check basis shape eqPoint (ScalarSumcheckQuery.point zeroEntry.1.query) r y active enough
        proposal.1.sources proposal.1.helper (zeroEntry.1.expected 0) = true then
      let memory ← bindValues sumEntry.1 eqPoint zeroEntry.1 proposal.1 proposal.2
      pure (some (⟨sumEntry.1, eqPoint, zeroEntry.1, proposal.1⟩, memory))
    else pure none
  | _, _ => pure none

variable {Payload : Type} [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- Every returned packet is tied to the actual successful earlier subclaims
and the literal computed check; its flag is never supplied by the prover. -/
theorem prepare_sound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (workerShape : Cfg → Skeleton)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c) (r y : K)
    (active : ℕ) (enough : active ≤ 2 ^ (c + row))
    (receive : Subclaim K 1 (c + row) → (Fin (c + row) → K) → Subclaim K 1 (c + row) → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Values F K (d + padding) count × Memory))
    (bindValues : Subclaim K 1 (c + row) → (Fin (c + row) → K) → Subclaim K 1 (c + row) →
      Values F K (d + padding) count → Memory → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (earlier : LookupPairSequence.Result K Memory (c + row))
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) workerShape)
    (outcome : Option (Packet F K (d + padding) count (c + row) × Memory) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) workerShape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape)
      (prepare basis shape r y active enough receive bindValues earlier)).run before))
    (packet : Packet F K (d + padding) count (c + row)) (memory : Memory) (returned : outcome.1 = some (packet, memory)) :
    ∃ sumMemory zeroMemory,
      earlier = (some (packet.sumClaim, sumMemory), some (packet.eqPoint, some (packet.zeroClaim, zeroMemory))) ∧
      LookupPairTerminal.check basis shape packet.eqPoint (ScalarSumcheckQuery.point packet.zeroClaim.query) r y active enough
        packet.values.sources packet.values.helper (packet.zeroClaim.expected 0) = true := by
  rcases earlier with ⟨sumResult, identityResult⟩
  cases sumResult with
  | none =>
    have equal := eq_of_mem_support_pure _ supported
    subst outcome
    cases returned
  | some sumEntry =>
    cases identityResult with
    | none =>
      have equal := eq_of_mem_support_pure _ supported
      subst outcome
      cases returned
    | some identityEntry =>
      rcases identityEntry with ⟨eqPoint, zeroResult⟩
      cases zeroResult with
      | none =>
        have equal := eq_of_mem_support_pure _ supported
        subst outcome
        cases returned
      | some zeroEntry =>
        rw [prepare, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
        obtain ⟨proposal, _, rest⟩ := supported
        by_cases checked : LookupPairTerminal.check basis shape eqPoint (ScalarSumcheckQuery.point zeroEntry.1.query) r y active enough
            proposal.1.1.sources proposal.1.1.helper (zeroEntry.1.expected 0) = true
        · simp only [checked, reduceIte, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at rest
          obtain ⟨newMemory, _, done⟩ := rest
          have equal := eq_of_mem_support_pure _ done
          subst outcome
          have samePacket := congrArg Prod.fst (Option.some.inj returned)
          dsimp only at samePacket
          subst packet
          exact ⟨sumEntry.2, zeroEntry.2, rfl, checked⟩
        · simp only [checked] at rest
          have equal := eq_of_mem_support_pure _ rest
          subst outcome
          cases returned

variable [SampleableType (Fin 1 → K)] [SampleableType (Fin (c + row) → K)]

/-- Same shared execution through scalar stages, claim reception, computed
terminal gating and successful binding; no source table is an input. -/
def program (p : ℕ) [CharP K p] {degree : ℕ} (small : degree + 1 ≤ p) (positive : 1 ≤ degree)
    (schedule : LookupPairSequence.Schedule K Memory Cfg Input Digest (c + row) degree)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c) (r y : K)
    (active : ℕ) (enough : active ≤ 2 ^ (c + row)) (publicTotal claimed : K) (memory : Memory)
    (receive : Subclaim K 1 (c + row) → (Fin (c + row) → K) → Subclaim K 1 (c + row) → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Values F K (d + padding) count × Memory))
    (bindValues : Subclaim K 1 (c + row) → (Fin (c + row) → K) → Subclaim K 1 (c + row) →
      Values F K (d + padding) count → Memory → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory) :=
  SharedContinuation.program (LookupPairSequence.program p small positive schedule publicTotal claimed memory)
    (prepare basis shape r y active enough receive bindValues)

end

end FormalProof4FHE.HasteBoots.PreparedLookupPair
