module
public import FormalProof4FHE.HasteBoots.AmbientSingleChecks
public import FormalProof4FHE.HasteBoots.AmbientCommittedBatchSafeBound
public import FormalProof4FHE.HasteBoots.NativeCommittedOpening
@[expose] public section

/-! Original single-query native openings on the caller's entire ambient state.
Only local source heights are fixed; all previous helpers/checkpoints remain. -/
namespace FormalProof4FHE.HasteBoots.AmbientCommittedOpeningSafeBound
open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open InteractiveAuthenticatedOpening CommittedJointMatrixOpening NativeCommittedOpening
noncomputable section
variable {F K Factor Input Digest Cfg Response Memory CommitMemory QueryData : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {b front suffix m queries height : ℕ}
  [SampleableType Digest] [SampleableType (TestMatrix F (2^front) b)] [SampleableType (Fin queries → Fin (2^height))]
  [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq K]
  [SampleableType ((Fin (2^front) × Fin b) → K)]

/-- Native step arithmetic is uniform over the actual incoming ambient state,
including arbitrary interleaved response/column/worker computations. -/
theorem step_arithmetic_bound [NeZero m] [NeZero b]
    (p : NativeMatrixVerifier.Protocol F Factor Input Digest Cfg Response Memory (2^front) b m (2^suffix) queries height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest) (heights : Cfg → ℕ)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (source : Fin (2^height) → (Fin (2^front) × Fin b) → Fin b → F) (factor : Factor) (memory : Memory)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) p.domain) m : Set (Fin (2^height) → K)) : ℚ≥0)/3) :
    Pr{let outcome ← ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) p.encoding dummy
      (AmbientMatrixSource.Shape heights)) (NativeMatrixVerifier.step p factor memory)).run state)}[
      SharedMatrixSampling.ArithmeticBad p.domain capacity radius source (p.left factor) (p.right factor)
        (p.testResponse factor) (p.structuredResponse factor) outcome.1.result.1] ≤
      JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) p.domain radius := by
  classical
  let : Fintype (Matrix.rowSpan (BaseMatrixProximity.stack basis source)) := Fintype.ofFinite _
  let : SampleableType (Matrix.rowSpan (BaseMatrixProximity.stack basis source)) := SampleableType.ofFintype _
  let : Fintype (RowSpanSampling.toSpan (BaseMatrixProximity.stack basis source)).toAddMonoidHom.ker := Fintype.ofFinite _
  let : SampleableType (RowSpanSampling.toSpan (BaseMatrixProximity.stack basis source)).toAddMonoidHom.ker := SampleableType.ofFintype _
  rw [NativeMatrixVerifier.step,StoppingJointMatrixOpening.step,simulateQ_map,StateT.run_map,prEvent_map]
  exact SharedMatrixSampling.arithmetic_after_bound basis p.domain enough capacity radius source
    (p.left factor) (p.right factor) p.encoding dummy (AmbientMatrixSource.Shape heights) (p.respond factor memory)
    (p.testResponse factor) (p.structuredResponse factor)
    (StoppingJointMatrixOpening.checkedNext (NativeMatrixVerifier.checks p) (NativeMatrixVerifier.next p) factor memory) state small

def Wrong (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (heights : Cfg → ℕ) (tag : Factor → Cfg)
    (domain : Fin (2^height) ↪ F) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (left : QueryData → Factor → Fin (2^front) → Matrix (Fin b) (Fin b) F)
    (right : QueryData → Factor → Fin (2^suffix) → Matrix (Fin b) (Fin b) F)
    (build : ((Factor → Digest) × CommitMemory) → QueryData →
      NativeMatrixVerifier.Protocol F Factor Input Digest Cfg Response Memory (2^front) b m (2^suffix) queries height)
    (first : ((Factor → Digest) × CommitMemory) × CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (last : (QueryData × ShortCircuitSequence.Outcome Factor
      (JointMatrixOpening.Data F Digest Response (2^front) b height queries) Memory) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) : Prop :=
  last.1.2.accepted = true ∧ ∃ factor, (protocol enc domain left right build first.1 last.1.1).value factor ≠
    matrixEvaluation (left last.1.1 factor) (right last.1.1 factor)
      (MatrixOpeningSecurity.extract domain capacity radius (AmbientCommittedBatchSafeBound.frozen enc dummy heights tag first factor))

/-- All accepted incorrect values pay one PCS arithmetic error per listed
source outside the same final exception, with no local authentication charge. -/
theorem soundness [NeZero m] [NeZero b]
    (basis : Module.Basis (Fin b) F K) (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (heights : Cfg → ℕ) (tag : Factor → Cfg) (factors : List Factor) (complete : ∀ factor, factor ∈ factors)
    (geometry : ∀ factor, heights (tag factor) = height)
    (domain : Fin (2^height) ↪ F) (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (left : QueryData → Factor → Fin (2^front) → Matrix (Fin b) (Fin b) F)
    (right : QueryData → Factor → Fin (2^suffix) → Matrix (Fin b) (Fin b) F)
    (build : ((Factor → Digest) × CommitMemory) → QueryData →
      NativeMatrixVerifier.Protocol F Factor Input Digest Cfg Response Memory (2^front) b m (2^suffix) queries height)
    (commit : OracleComp (SharedSequence.Shared Cfg Input Digest) ((Factor → Digest) × CommitMemory))
    (selectQuery : ((Factor → Digest) × CommitMemory) → OracleComp (SharedSequence.Shared Cfg Input Digest) QueryData)
    (enabled : ((Factor → Digest) × CommitMemory) → QueryData → Bool)
    (start : ((Factor → Digest) × CommitMemory) → QueryData → Memory)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m : Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (MultiCommitmentPrefix.witness enc dummy (AmbientMatrixSource.Shape heights) (requests tag factors) commit
      (continuation enc domain left right build selectQuery enabled start factors) initial)}[
      Wrong enc dummy heights tag domain capacity radius left right build outcome.1 outcome.2 ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2] ≤
      (factors.map (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) domain radius)).sum := by
  let p := protocol enc domain left right build
  let arithmetic := fun first query factor (data : JointMatrixOpening.Data F Digest Response (2^front) b height queries) =>
    SharedMatrixSampling.ArithmeticBad domain capacity radius (AmbientCommittedBatchSafeBound.frozen enc dummy heights tag first factor)
      (left query factor) (right query factor) ((p first.1 query).testResponse factor)
      ((p first.1 query).structuredResponse factor) data.1
  apply CommittedPrefixSafeBound.event_bound enc dummy (AmbientMatrixSource.Shape heights) (requests tag factors) commit
    (continuation enc domain left right build selectQuery enabled start factors) initial audited
    (Wrong enc dummy heights tag domain capacity radius left right build)
    (fun first last => SharedSequence.AnyBad (arithmetic first last.1.1) last.1.2.results) _
  · intro first
    apply SharedContinuation.later_event_le enc dummy (AmbientMatrixSource.Shape heights)
      (selectQuery first.1) (fun query => if enabled first.1 query then
        ShortCircuitSequence.program (NativeMatrixVerifier.step (p first.1 query)) factors (start first.1 query)
        else pure ⟨[],start first.1 query,false⟩)
      (RecordRoots.state _ (requests tag factors first.1) first.2)
      (fun query outcome => SharedSequence.AnyBad (arithmetic first query) outcome.1.results)
    intro query initial
    cases gate : enabled first.1 query with
    | false => simp [SharedSequence.AnyBad,prEvent_norm]
    | true =>
      simp only [reduceIte]
      exact ShortCircuitSequence.arithmetic_union_bound enc dummy (AmbientMatrixSource.Shape heights)
        (NativeMatrixVerifier.step (p first.1 query)) (arithmetic first query)
        (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) domain radius) factors
        (fun factor _ memory state => step_arithmetic_bound (p first.1 query) basis dummy heights enough capacity radius
          (AmbientCommittedBatchSafeBound.frozen enc dummy heights tag first factor) factor memory state small)
        (start first.1 query) initial
  · intro first last supported accepted
    obtain ⟨passed,factor,different⟩ := accepted
    have recorded := CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape heights)
      (tag factor) (AmbientCommittedBatchSafeBound.snapshots heights tag first factor)
      (continuation enc domain left right build selectQuery enabled start factors first.1)
      (RecordRoots.state _ (requests tag factors first.1) first.2)
      (RecordRoots.recorded _ _ first.2 (tag factor,first.1.1 factor) (List.mem_map_of_mem (complete factor))) last supported
    obtain ⟨selected,_,opened,openedSupported,equal⟩ :=
      (SharedContinuation.support_program enc dummy (AmbientMatrixSource.Shape heights) (selectQuery first.1)
        (fun query => if enabled first.1 query then
          ShortCircuitSequence.program (NativeMatrixVerifier.step (p first.1 query)) factors (start first.1 query)
          else pure ⟨[],start first.1 query,false⟩)
        (RecordRoots.state _ (requests tag factors first.1) first.2) last).mp supported
    subst last
    cases gate : enabled first.1 selected.1 with
    | false =>
      simp only [gate,Bool.false_eq_true,reduceIte,simulateQ_pure,StateT.run_pure] at openedSupported
      have equal := eq_of_mem_support_pure _ openedSupported
      subst opened
      exact (Bool.false_ne_true passed).elim
    | true =>
      simp only [gate,reduceIte] at openedSupported
      have checked := NativeMatrixVerifier.successful_results (p first.1 selected.1) dummy (AmbientMatrixSource.Shape heights)
        tag factors (start first.1 selected.1) selected.2 opened openedSupported passed
      have coverage := ShortCircuitSequence.accepted_indices enc dummy (AmbientMatrixSource.Shape heights)
        (NativeMatrixVerifier.step (p first.1 selected.1)) factors (start first.1 selected.1) selected.2 opened openedSupported passed
      have occurs : factor ∈ opened.1.results.map Prod.fst := by rw [coverage]; exact complete factor
      obtain ⟨entry,member,same⟩ := List.mem_map.mp occurs
      subst factor
      obtain arithmeticBad | unavailable := AmbientSingleChecks.wrong_implies_arithmetic_or_disagreement enc dummy heights
        (tag entry.1) (geometry entry.1) (AmbientCommittedBatchSafeBound.snapshots heights tag first entry.1) domain
        (left selected.1 entry.1) (right selected.1 entry.1) ((p first.1 selected.1).value entry.1) capacity radius
        ((p first.1 selected.1).testResponse entry.1) ((p first.1 selected.1).structuredResponse entry.1)
        entry.2 opened.2 recorded (checked entry member).2 (checked entry member).1 different
      · exact Or.inl ⟨entry,member,arithmeticBad⟩
      · exact Or.inr unavailable

end
end FormalProof4FHE.HasteBoots.AmbientCommittedOpeningSafeBound
