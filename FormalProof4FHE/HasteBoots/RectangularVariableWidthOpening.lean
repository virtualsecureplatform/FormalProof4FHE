module

public import FormalProof4FHE.HasteBoots.DependentShortCircuitSequence
public import FormalProof4FHE.HasteBoots.VariableWidthBatchOpening
public import FormalProof4FHE.HasteBoots.RectangularVariableHeightVerifier
public import FormalProof4FHE.HasteBoots.MultiCommitmentPrefix

@[expose] public section

/-!
# Original-root batches with different native PCS layouts

Every root retains its own tensor split, claim count, code length, query
count and tree height. Each root retains its own packing width and independent code-symbol width.
No padded root views or new commitments are introduced. Query selection is
after the actual root-recording prefix, steps short-circuit, and one global
availability charge covers the entire actual execution.
-/

open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening

namespace FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening

noncomputable section

abbrev Layout := VariableWidthBatchOpening.Layout

/-- The rectangular kernel rate retains the code-symbol width separately from
its number of independent base-field test rows. -/
def error {F : Type} [Field F] [DecidableEq F] [Fintype F] {height : ℕ}
    (domain : Fin (2^height) ↪ F) (m symbols tests queries radius : ℕ) : ENNReal :=
  ((Code.minDist (BlockCode.code domain m symbols : Set (Fin (2^height) → Fin symbols → F)) : ENNReal) / Fintype.card F)^tests +
  max (ColumnOpening.missBound (Fin (2^height)) queries
    (Code.minDist (BlockCode.code domain m symbols : Set (Fin (2^height) → Fin symbols → F)) - radius))
    (ColumnOpening.missBound (Fin (2^height)) queries (radius+1))

variable {F Factor Input Digest Cfg Response Memory CommitMemory QueryData : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {width symbolWidth : Factor → ℕ}

abbrev Protocol (F Input Digest Cfg Response Memory : Type) (width symbolWidth : Factor → ℕ)
    (heights : Cfg → ℕ) (tag : Factor → Cfg) (layout : Factor → Layout) (factor : Factor) [Field F] [DecidableEq F] :=
  RectangularBatchVerifier.Protocol F Input Digest Cfg Response Memory (width factor) (symbolWidth factor) (layout factor).front (layout factor).suffix
    (layout factor).claims (layout factor).m (layout factor).queries (heights (tag factor))

abbrev Data (F Digest Response : Type) (width symbolWidth : Factor → ℕ)
    (heights : Cfg → ℕ) (tag : Factor → Cfg) (layout : Factor → Layout) (factor : Factor) :=
  RectangularBatchChecks.Data F Digest Response (layout factor).front (width factor) (symbolWidth factor) (heights (tag factor)) (layout factor).queries

def requests (tag : Factor → Cfg) (indices : List Factor)
    (emission : (Factor → Digest) × CommitMemory) : List (Cfg × Digest) :=
  indices.map (fun factor => (tag factor, emission.1 factor))

def snapshots (heights : Cfg → ℕ) (tag : Factor → Cfg)
    (first : ((Factor → Digest) × CommitMemory) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (factor : Factor) : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun cfg => Skeleton.perfect (heights cfg))) (tag factor) :=
  ⟨first.1.1 factor, first.2.hash.log⟩

omit [DecidableEq Input] [DecidableEq Digest] in
theorem snapshots_recorded (heights : Cfg → ℕ) (tag : Factor → Cfg) (indices : List Factor)
    (complete : ∀ factor, factor ∈ indices)
    (first : ((Factor → Digest) × CommitMemory) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg))) (factor : Factor) :
    ⟨tag factor, snapshots heights tag first factor⟩ ∈
      (RecordRoots.state (fun cfg => Skeleton.perfect (heights cfg)) (requests tag indices first.1)
        first.2).checkpoints.checkpoints :=
  RecordRoots.recorded _ _ first.2 (tag factor, first.1.1 factor) (List.mem_map_of_mem (complete factor))

def protocol (enc : MerkleOracle.Encoding Input Digest (List F)) (heights : Cfg → ℕ) (tag : Factor → Cfg)
    (layout : Factor → Layout) (domain : ∀ factor, Fin (2 ^ heights (tag factor)) ↪ F)
    (build : ((Factor → Digest) × CommitMemory) → QueryData → (factor : Factor) →
      Protocol F Input Digest Cfg Response Memory width symbolWidth heights tag layout factor)
    (emission : (Factor → Digest) × CommitMemory) (query : QueryData) (factor : Factor) :
    Protocol F Input Digest Cfg Response Memory width symbolWidth heights tag layout factor :=
  { build emission query factor with encoding := enc, domain := domain factor, root := emission.1 factor }

variable {heights : Cfg → ℕ} {tag : Factor → Cfg} {layout : Factor → Layout}
  [∀ factor, SampleableType (TestMatrix F (2 ^ (layout factor).front) (width factor))]
  [∀ factor, SampleableType (Fin (layout factor).queries → Fin (2 ^ heights (tag factor)))]

def continuation (enc : MerkleOracle.Encoding Input Digest (List F))
    (domain : ∀ factor, Fin (2 ^ heights (tag factor)) ↪ F)
    (build : ((Factor → Digest) × CommitMemory) → QueryData → (factor : Factor) →
      Protocol F Input Digest Cfg Response Memory width symbolWidth heights tag layout factor)
    (selectQuery : ((Factor → Digest) × CommitMemory) → OracleComp (SharedSequence.Shared Cfg Input Digest) QueryData)
    (enabled : ((Factor → Digest) × CommitMemory) → QueryData → Bool)
    (start : ((Factor → Digest) × CommitMemory) → QueryData → Memory)
    (factors : List Factor) (emission : (Factor → Digest) × CommitMemory) :=
  SharedContinuation.program (selectQuery emission) (fun query => if enabled emission query then
    DependentShortCircuitSequence.program
      (fun factor => RectangularBatchVerifier.step (protocol enc heights tag layout domain build emission query factor))
      factors (start emission query)
    else pure ⟨[], start emission query, false⟩)

/-- The proof snapshot erases to the exact real program, including rejected
and disabled branches and every actual hash call. -/
theorem project_witness [SampleableType Digest]
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (domain : ∀ factor, Fin (2 ^ heights (tag factor)) ↪ F)
    (build : ((Factor → Digest) × CommitMemory) → QueryData → (factor : Factor) →
      Protocol F Input Digest Cfg Response Memory width symbolWidth heights tag layout factor)
    (commit : OracleComp (SharedSequence.Shared Cfg Input Digest) ((Factor → Digest) × CommitMemory))
    (selectQuery : ((Factor → Digest) × CommitMemory) → OracleComp (SharedSequence.Shared Cfg Input Digest) QueryData)
    (enabled : ((Factor → Digest) × CommitMemory) → QueryData → Bool)
    (start : ((Factor → Digest) × CommitMemory) → QueryData → Memory) (factors : List Factor) :
    (fun outcome => ((outcome.1.1, outcome.2.1), outcome.2.2)) <$>
      MultiCommitmentPrefix.witness enc dummy (fun cfg => Skeleton.perfect (heights cfg)) (requests tag factors) commit
        (continuation enc domain build selectQuery enabled start factors)
        (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg))) =
      (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy
        (fun cfg => Skeleton.perfect (heights cfg)))
        (MultiCommitmentPrefix.program (requests tag factors) commit
          (continuation enc domain build selectQuery enabled start factors))).run
        (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg))) :=
  MultiCommitmentPrefix.project_witness enc dummy _ _ _ _ _

/-- Every claimed value is interpreted against its own original root's source
frozen before the query phase, with that root's actual layout and code. -/
def Wrong (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (domain : ∀ factor, Fin (2 ^ heights (tag factor)) ↪ F)
    (capacity : ∀ factor, 2 ^ (layout factor).suffix ≤ (layout factor).m * symbolWidth factor) (radius : Factor → ℕ)
    (build : ((Factor → Digest) × CommitMemory) → QueryData → (factor : Factor) →
      Protocol F Input Digest Cfg Response Memory width symbolWidth heights tag layout factor)
    (first : ((Factor → Digest) × CommitMemory) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (last : (QueryData × ShortCircuitSequence.Outcome Factor
      (Sigma (Data F Digest Response width symbolWidth heights tag layout)) Memory) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg))) : Prop :=
  last.1.2.accepted = true ∧ ∃ factor claim,
    (protocol enc heights tag layout domain build first.1 last.1.1 factor).values claim ≠
      matrixEvaluation
        (NativeBatchChecks.left (front := (layout factor).front) (suffix := (layout factor).suffix)
          (protocol enc heights tag layout domain build first.1 last.1.1 factor).query claim)
        (NativeBatchChecks.right (front := (layout factor).front) (suffix := (layout factor).suffix)
          (protocol enc heights tag layout domain build first.1 last.1.1 factor).query claim)
        (RectangularMatrixOpeningKernel.extract (domain factor) (capacity factor) (radius factor)
          (AmbientRectangularSource.word enc dummy heights (tag factor) (snapshots heights tag first factor)))

variable [SampleableType Digest] [Fintype Digest] [Fintype F]
  [∀ factor, SampleableType ((Fin (2 ^ (layout factor).front) × Fin (width factor)) → F)]

/-- Per-root arithmetic losses plus one whole-run expected availability charge.
No initial safety, replay, PCS security certificate or query cap is supplied. -/
theorem soundness_from_empty [∀ factor, NeZero (symbolWidth factor)] [∀ factor, NeZero (layout factor).m]
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (factors : List Factor) (complete : ∀ factor, factor ∈ factors)
    (domain : ∀ factor, Fin (2 ^ heights (tag factor)) ↪ F)
    (enough : ∀ factor, (layout factor).m ≤ Fintype.card (Fin (2 ^ heights (tag factor))))
    (capacity : ∀ factor, 2 ^ (layout factor).suffix ≤ (layout factor).m * symbolWidth factor) (radius : Factor → ℕ)
    (build : ((Factor → Digest) × CommitMemory) → QueryData → (factor : Factor) →
      Protocol F Input Digest Cfg Response Memory width symbolWidth heights tag layout factor)
    (commit : OracleComp (SharedSequence.Shared Cfg Input Digest) ((Factor → Digest) × CommitMemory))
    (selectQuery : ((Factor → Digest) × CommitMemory) → OracleComp (SharedSequence.Shared Cfg Input Digest) QueryData)
    (enabled : ((Factor → Digest) × CommitMemory) → QueryData → Bool)
    (start : ((Factor → Digest) × CommitMemory) → QueryData → Memory)
    (large : ∀ factor, radius factor < Fintype.card F)
    (small : ∀ factor, 3*radius factor < Code.minDist (BlockCode.code (domain factor) (layout factor).m (symbolWidth factor) :
      Set (Fin (2^heights (tag factor)) → Fin (symbolWidth factor) → F))) :
    Pr{let outcome ← (MultiCommitmentPrefix.witness enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (requests tag factors) commit (continuation enc domain build selectQuery enabled start factors)
      (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg))))}[
        Wrong enc dummy domain capacity radius build outcome.1 outcome.2] ≤
      (factors.map (fun factor => error (domain factor) (layout factor).m (symbolWidth factor) (width factor) (layout factor).queries (radius factor))).sum +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg)))
        (CheckpointCollision.loss unifSpec (fun cfg => Skeleton.perfect (heights cfg)))
        (MultiCommitmentPrefix.program (requests tag factors) commit
          (continuation enc domain build selectQuery enabled start factors))
        (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg))) := by
  let p := protocol enc heights tag layout domain build
  let arithmetic := fun first query (entry : Sigma (Data F Digest Response width symbolWidth heights tag layout)) =>
    SharedRectangularBatchSampling.ArithmeticBad (domain entry.1) (capacity entry.1) (radius entry.1)
      (AmbientRectangularSource.word enc dummy heights (tag entry.1) (snapshots heights tag first entry.1))
      (BatchQueryLayout.groupOf (front := (layout entry.1).front) (suffix := (layout entry.1).suffix) (p first.1 query entry.1).query)
      (NativeBatchChecks.groupLeft (front := (layout entry.1).front) (suffix := (layout entry.1).suffix) (p first.1 query entry.1).query)
      (NativeBatchChecks.right (front := (layout entry.1).front) (suffix := (layout entry.1).suffix) (p first.1 query entry.1).query)
      (p first.1 query entry.1).testResponse (fun matrix response group => (p first.1 query entry.1).groupResponse group.val matrix response) entry.2.1

  apply MultiCommitmentPrefix.event_bound enc dummy (fun cfg => Skeleton.perfect (heights cfg))
    (requests tag factors) commit (continuation enc domain build selectQuery enabled start factors)
    (Wrong enc dummy domain capacity radius build)
    (fun first last => SharedSequence.AnyBad (fun _ => arithmetic first last.1.1) last.1.2.results) _
  · intro first
    apply SharedContinuation.later_event_le enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (selectQuery first.1) (fun query => if enabled first.1 query then
        DependentShortCircuitSequence.program (fun factor => RectangularBatchVerifier.step (p first.1 query factor))
          factors (start first.1 query)
        else pure ⟨[], start first.1 query, false⟩)
      (RecordRoots.state _ (requests tag factors first.1) first.2)
      (fun query outcome => SharedSequence.AnyBad (fun _ => arithmetic first query) outcome.1.results)
    intro query initial
    cases gate : enabled first.1 query with
    | false => simp [SharedSequence.AnyBad, prEvent_norm]
    | true =>
      simp only [reduceIte]
      apply ShortCircuitSequence.arithmetic_union_bound enc dummy (fun cfg => Skeleton.perfect (heights cfg))
        (DependentShortCircuitSequence.step (fun factor => RectangularBatchVerifier.step (p first.1 query factor)))
        (fun _ => arithmetic first query)
        (fun factor => error (domain factor) (layout factor).m (symbolWidth factor) (width factor) (layout factor).queries (radius factor)) factors _ (start first.1 query) initial
      intro factor _ memory state
      simp only [DependentShortCircuitSequence.step, simulateQ_map, StateT.run_map, prEvent_map]
      exact RectangularBatchVerifier.arithmetic_bound (p first.1 query factor) dummy
        (fun cfg => Skeleton.perfect (heights cfg)) (enough factor) (capacity factor) (radius factor)
        (AmbientRectangularSource.word enc dummy heights (tag factor) (snapshots heights tag first factor)) memory state (large factor) (small factor)
  · intro first last supported accepted
    obtain ⟨passed, factor, claim, different⟩ := accepted
    have recorded := CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy
      (fun cfg => Skeleton.perfect (heights cfg)) (tag factor) (snapshots heights tag first factor)
      (continuation enc domain build selectQuery enabled start factors first.1)
      (RecordRoots.state _ (requests tag factors first.1) first.2)
      (snapshots_recorded heights tag factors complete first factor) last supported
    obtain ⟨selected, _, opened, openedSupported, equal⟩ :=
      (SharedContinuation.support_program enc dummy (fun cfg => Skeleton.perfect (heights cfg))
        (selectQuery first.1) (fun query => if enabled first.1 query then
          DependentShortCircuitSequence.program (fun factor => RectangularBatchVerifier.step (p first.1 query factor))
            factors (start first.1 query)
          else pure ⟨[], start first.1 query, false⟩)
        (RecordRoots.state _ (requests tag factors first.1) first.2) last).mp supported
    subst last
    cases gate : enabled first.1 selected.1 with
    | false =>
      simp only [gate, Bool.false_eq_true, reduceIte, simulateQ_pure, StateT.run_pure] at openedSupported
      have equal := eq_of_mem_support_pure _ openedSupported
      subst opened
      exact (Bool.false_ne_true passed).elim
    | true =>
      simp only [gate, reduceIte] at openedSupported
      have verified := DependentShortCircuitSequence.accepted_cache_results enc dummy (fun cfg => Skeleton.perfect (heights cfg))
        (fun factor => RectangularBatchVerifier.step (p first.1 selected.1 factor)) factors
        (fun factor data cache => RectangularBatchVerifier.checks (p first.1 selected.1 factor) data = true ∧
          ∀ column ∈ data.2, ParallelColumnAvailability.Replays enc heights
            (AuthenticatedColumnChecks.request heights (tag factor) (first.1.1 factor) column) cache)
        (by
          intro factor _ memory state outcome present accepted later extension
          have native := RectangularBatchVerifier.step_accepts_later (p first.1 selected.1 factor) dummy
            (fun cfg => Skeleton.perfect (heights cfg)) (tag factor) memory state outcome present accepted later extension
          simpa only [p, protocol, ParallelColumnAvailability.Replays, AuthenticatedColumnChecks.request] using native)
        (start first.1 selected.1) selected.2 opened openedSupported passed
      have allFactors := ShortCircuitSequence.accepted_indices enc dummy (fun cfg => Skeleton.perfect (heights cfg))
        (DependentShortCircuitSequence.step (fun factor => RectangularBatchVerifier.step (p first.1 selected.1 factor))) factors
        (start first.1 selected.1) selected.2 opened openedSupported passed
      have occurs : factor ∈ opened.1.results.map Prod.fst := by rw [allFactors]; exact complete factor
      obtain ⟨entry, member, same⟩ := List.mem_map.mp occurs
      subst factor
      obtain ⟨data, dataEq, checked, replayed⟩ := verified entry member
      obtain arithmeticBad | unavailable := RectangularVariableHeightVerifier.checks_wrong_implies_arithmetic_or_disagreement enc dummy
        heights (tag entry.1) (snapshots heights tag first entry.1) (domain entry.1) (p first.1 selected.1 entry.1).query
        (p first.1 selected.1 entry.1).values (capacity entry.1) (radius entry.1) (p first.1 selected.1 entry.1).testResponse
        (p first.1 selected.1 entry.1).groupResponse data opened.2 recorded replayed checked ⟨claim, different⟩
      · exact Or.inl ⟨entry, member, by simpa only [dataEq] using arithmeticBad⟩
      · exact Or.inr unavailable

end

end FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening
