module

public import FormalProof4FHE.HasteBoots.NativeMatrixVerifier
public import FormalProof4FHE.HasteBoots.CommittedStoppingMatrixOpening

@[expose] public section

/-!
# Concrete native-worker opening soundness from empty initialization

Trusted public code parameters and the selected matrix query override the
prover/scheduler inputs. Root snapshots are fixed before query selection.
Only a successful actual native factor loop can contribute a wrong supplied
value. Its probability is bounded by the PCS arithmetic sum plus one hash
charge for exactly the executed commitment, query and interleaved worker calls.
There is no external worker-flag, replay or PCS-security certificate.
This uses private verifier coins. Full ZeroCheck/terminal orchestration,
Fiat--Shamir, native scheduling completion and Rust/physical-cost refinement
remain separate obligations.
-/

open OracleSpec OracleComp BinaryTree Matrix
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.CommittedJointMatrixOpening

namespace FormalProof4FHE.HasteBoots.NativeCommittedOpening

noncomputable section

variable {F K Factor Input Digest Cfg Response Memory CommitMemory QueryData : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {leftCount b m size queries height : ℕ}

/-- The prover supplies behavior and claimed values; trusted public context
supplies the encoding, domain, roots and matrix query. -/
def protocol (enc : MerkleOracle.Encoding Input Digest (List F)) (domain : Fin (2 ^ height) ↪ F)
    (left : QueryData → Factor → Fin leftCount → Matrix (Fin b) (Fin b) F)
    (right : QueryData → Factor → Fin size → Matrix (Fin b) (Fin b) F)
    (build : ((Factor → Digest) × CommitMemory) → QueryData →
      NativeMatrixVerifier.Protocol F Factor Input Digest Cfg Response Memory leftCount b m size queries height)
    (emission : (Factor → Digest) × CommitMemory) (query : QueryData) :
    NativeMatrixVerifier.Protocol F Factor Input Digest Cfg Response Memory leftCount b m size queries height :=
  { build emission query with
    encoding := enc
    domain := domain
    root := emission.1
    left := left query
    right := right query }

section Sampling

variable [SampleableType (TestMatrix F leftCount b)] [SampleableType (Fin queries → Fin (2 ^ height))]

def continuation (enc : MerkleOracle.Encoding Input Digest (List F)) (domain : Fin (2 ^ height) ↪ F)
    (left : QueryData → Factor → Fin leftCount → Matrix (Fin b) (Fin b) F)
    (right : QueryData → Factor → Fin size → Matrix (Fin b) (Fin b) F)
    (build : ((Factor → Digest) × CommitMemory) → QueryData →
      NativeMatrixVerifier.Protocol F Factor Input Digest Cfg Response Memory leftCount b m size queries height)
    (selectQuery : ((Factor → Digest) × CommitMemory) → OracleComp (SharedSequence.Shared Cfg Input Digest) QueryData)
    (enabled : ((Factor → Digest) × CommitMemory) → QueryData → Bool)
    (start : ((Factor → Digest) × CommitMemory) → QueryData → Memory)
    (factors : List Factor) (emission : (Factor → Digest) × CommitMemory) :=
  SharedContinuation.program (selectQuery emission) (fun query =>
    if enabled emission query then
      ShortCircuitSequence.program (NativeMatrixVerifier.step (protocol enc domain left right build emission query))
        factors (start emission query)
    else pure ⟨[], start emission query, false⟩)

variable [SampleableType Digest] [Fintype Digest]
  [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq K]
  [SampleableType ((Fin leftCount × Fin b) → K)]

/-- The supplied value, rather than an assumed authenticated response, is
bounded on the concrete stopped program with actual interleaved native workers. -/
theorem soundness_from_empty [NeZero m] [NeZero b]
    (basis : Module.Basis (Fin b) F K)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (tag : Factor → Cfg) (factors : List Factor) (complete : ∀ factor, factor ∈ factors)
    (domain : Fin (2 ^ height) ↪ F) (enough : m ≤ Fintype.card (Fin (2 ^ height)))
    (capacity : size ≤ m * b) (radius : ℕ)
    (left : QueryData → Factor → Fin leftCount → Matrix (Fin b) (Fin b) F)
    (right : QueryData → Factor → Fin size → Matrix (Fin b) (Fin b) F)
    (build : ((Factor → Digest) × CommitMemory) → QueryData →
      NativeMatrixVerifier.Protocol F Factor Input Digest Cfg Response Memory leftCount b m size queries height)
    (commit : OracleComp (SharedSequence.Shared Cfg Input Digest) ((Factor → Digest) × CommitMemory))
    (selectQuery : ((Factor → Digest) × CommitMemory) → OracleComp (SharedSequence.Shared Cfg Input Digest) QueryData)
    (enabled : ((Factor → Digest) × CommitMemory) → QueryData → Bool)
    (start : ((Factor → Digest) × CommitMemory) → QueryData → Memory)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← (MultiCommitmentPrefix.witness enc dummy (fun _ : Cfg => Skeleton.perfect height)
      (requests tag factors) commit (continuation enc domain left right build selectQuery enabled start factors)
      (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)))}[
        outcome.2.1.2.accepted = true ∧
        ∃ factor, (protocol enc domain left right build outcome.1.1 outcome.2.1.1).value factor ≠
          matrixEvaluation (left outcome.2.1.1 factor) (right outcome.2.1.1 factor)
            (MatrixOpeningSecurity.extract domain capacity radius
              (JointMatrixOpening.frozen enc dummy tag (snapshots tag outcome.1) factor))] ≤
      (factors.map (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) domain radius)).sum +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun _ : Cfg => Skeleton.perfect height))
        (CheckpointCollision.loss unifSpec (fun _ : Cfg => Skeleton.perfect height))
        (MultiCommitmentPrefix.program (requests tag factors) commit
          (continuation enc domain left right build selectQuery enabled start factors))
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) := by
  let p := protocol enc domain left right build
  have bound := CommittedStoppingMatrixOpening.soundness_from_empty basis enc dummy tag factors complete domain enough
    capacity radius left right commit selectQuery enabled start
    (fun emission query => (p emission query).respond)
    (fun emission query => StoppingJointMatrixOpening.checkedNext
      (NativeMatrixVerifier.checks (p emission query)) (NativeMatrixVerifier.next (p emission query)))
    (fun emission query => (p emission query).testResponse)
    (fun emission query => (p emission query).structuredResponse) small
  apply le_trans (prEvent_mono_of_support _ _ (fun outcome =>
    JointMatrixOpening.AnyAcceptedWrong enc dummy tag (snapshots tag outcome.1) domain capacity radius
      (left outcome.2.1.1) (right outcome.2.1.1) (p outcome.1.1 outcome.2.1.1).testResponse
      (p outcome.1.1 outcome.2.1.1).structuredResponse
      ((outcome.2.1.2.results, outcome.2.1.2.memory), outcome.2.2)) ?_) bound
  intro outcome supported accepted
  simp only [MultiCommitmentPrefix.witness, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at supported
  obtain ⟨first, _, last, lastSupported, equal⟩ := supported
  subst outcome
  obtain ⟨selected, _, opened, openedSupported, lastEqual⟩ :=
    (SharedContinuation.support_program enc dummy (fun _ : Cfg => Skeleton.perfect height)
      (selectQuery first.1) (fun query => if enabled first.1 query then
        ShortCircuitSequence.program (NativeMatrixVerifier.step (p first.1 query)) factors (start first.1 query)
        else pure ⟨[], start first.1 query, false⟩)
      (RecordRoots.state _ (requests tag factors first.1) first.2) last).mp lastSupported
  subst last
  cases gate : enabled first.1 selected.1 with
  | false =>
    simp only [gate, Bool.false_eq_true, reduceIte, simulateQ_pure, StateT.run_pure] at openedSupported
    have equal := eq_of_mem_support_pure _ openedSupported
    subst opened
    exact (Bool.false_ne_true accepted.1).elim
  | true =>
    simp only [gate, reduceIte] at openedSupported
    exact NativeMatrixVerifier.successful_wrong_evaluation (p first.1 selected.1) dummy tag (snapshots tag first)
      (fun _ => rfl) capacity radius factors complete (start first.1 selected.1) selected.2 opened openedSupported
      accepted.1 accepted.2

end Sampling

end

end FormalProof4FHE.HasteBoots.NativeCommittedOpening
