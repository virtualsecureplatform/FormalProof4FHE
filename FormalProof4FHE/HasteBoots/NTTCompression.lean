module

public import FormalProof4FHE.HasteBoots.NTTRowOracle
public import FormalProof4FHE.HasteBoots.NTTSourceQuery
public import FormalProof4FHE.HasteBoots.GuardedCompression

@[expose] public section

/-!
# NTT row detection composed with fresh coefficient compression

The row prefix binds adaptive polynomial pairs and checks their transforms.
Only enabled prefixes draw the shared fresh coefficient-compression query.
Its two families of compressed values refer to the original coefficient and
evaluation sources at the exact native source queries. Acceptance against
truthful terminal values is bounded by the row-miss plus compression errors.
Concrete shared-test/shared-column batch openings must still authenticate these
terminals. No security assumption on those openings is hidden in this result.
-/

open OracleSpec OracleComp BinaryTree
open scoped BigOperators
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim

namespace FormalProof4FHE.HasteBoots.NTTCompression

noncomputable section

abbrev Position (c b : ℕ) := MatrixFold.Cube c × Fin b
abbrev Prefix (F Memory : Type) (c b r k : ℕ) :=
  (Fin k → Fin r → F) × NTTRowOracle.Checked F (Position c b) Memory k
abbrev Row (k : ℕ) := Bool × Fin k

variable {F Memory : Type} [Field F] {c b r k : ℕ}

def pack (polynomial : Position c b → F) : MatrixFold.Cube c → Fin b → F :=
  fun cell lane => polynomial (cell, lane)

omit [Field F] in
theorem pack_injective : Function.Injective (pack (F := F) (c := c) (b := b)) := by
  intro first second equal
  funext position
  exact congrFun (congrFun equal position.1) position.2

/-- Original polynomial blocks in native low-coefficient/high-row order. -/
def sourceRows (c r : ℕ) (table : MatrixFold.Cube (r + c) → Fin b → F) :
    MatrixFold.Cube r → Position c b → F :=
  fun row position => table (NTTSourceQuery.join c r position.1 row) position.2

def proposed (entry : Prefix F Memory c b r k) (row : Row k) : MatrixFold.Cube c → Fin b → F :=
  pack (if row.1 then entry.2.proposal.evaluations row.2 else entry.2.proposal.coefficients row.2)

def source (coefficients evaluations : MatrixFold.Cube (r + c) → Fin b → F) (side : Bool) :=
  if side then evaluations else coefficients

def correct (coefficients evaluations : MatrixFold.Cube (r + c) → Fin b → F)
    (entry : Prefix F Memory c b r k) (row : Row k) : MatrixFold.Cube c → Fin b → F :=
  pack (NTTRowCheck.fold (entry.1 row.2) (sourceRows c r (source coefficients evaluations row.1)))

def sourceQuery (entry : Prefix F Memory c b r k) (query : Query F b c) (row : Row k) :=
  NTTSourceQuery.append query (NTTSourceQuery.rowQuery (entry.1 row.2))

/-- Packed row folding is the same polynomial view used by source queries. -/
theorem pack_fold (point : Fin r → F) (table : MatrixFold.Cube (r + c) → Fin b → F) :
    pack (NTTRowCheck.fold point (sourceRows c r table)) =
      fun cell => ∑ row, PackedEqualityCube.weight point row • table (NTTSourceQuery.join c r cell row) := by
  funext cell lane
  simp only [pack, NTTRowCheck.fold, sourceRows, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem correct_evaluation (coefficients evaluations : MatrixFold.Cube (r + c) → Fin b → F)
    (entry : Prefix F Memory c b r k) (query : Query F b c) (row : Row k) :
    query.fold (correct coefficients evaluations entry row) =
      (sourceQuery entry query row).fold (source coefficients evaluations row.1) := by
  rw [correct, pack_fold]
  exact (NTTSourceQuery.source_evaluation query (entry.1 row.2) _).symm

/-- Any accepted wrong proposed coefficient/evaluation row gives one fixed
wrong row in the common-query family, before compression is sampled. -/
theorem wrong_family (coefficients evaluations : MatrixFold.Cube (r + c) → Fin b → F)
    (entry : Prefix F Memory c b r k)
    (wrong : NTTRowOracle.WrongAccepted (sourceRows c r coefficients) (sourceRows c r evaluations) entry) :
    ∃ row, proposed entry row ≠ correct coefficients evaluations entry row := by
  obtain ⟨_, repetition, coefficientWrong | evaluationWrong⟩ := wrong
  · refine ⟨(false, repetition), fun equal => coefficientWrong (pack_injective equal)⟩
  · refine ⟨(true, repetition), fun equal => evaluationWrong (pack_injective equal)⟩

/-- Truthfulness requires every computed terminal at its original source query.
It is an analysis event, not a certificate supplied to the operational code. -/
def TruthfulTerminals {Later : Type} (coefficients evaluations : MatrixFold.Cube (r + c) → Fin b → F)
    (result : Prefix F Memory c b r k × Option (Query F b c × Later)) : Prop :=
  result.1.2.accepted = true ∧ match result.2 with
    | none => False
    | some entry => ∀ row, entry.1.fold (proposed result.1 row) =
        (sourceQuery result.1 entry.1 row).fold (source coefficients evaluations row.1)

theorem truthful_iff {Later : Type} (coefficients evaluations : MatrixFold.Cube (r + c) → Fin b → F)
    (result : Prefix F Memory c b r k × Option (Query F b c × Later)) :
    TruthfulTerminals coefficients evaluations result ↔ result.1.2.accepted = true ∧
      GuardedCompression.Agreement (proposed result.1) (correct coefficients evaluations result.1) result.2 := by
  rcases result with ⟨entry, terminal⟩
  cases terminal with
  | none => rfl
  | some query => simp only [TruthfulTerminals, GuardedCompression.Agreement, correct_evaluation]

variable {Cfg Input Digest Payload Later : Type} [DecidableEq F]
  [SampleableType (Fin k → Fin r → F)] [SampleableType (Fin b → F)]

def program (nodes : PackedSumcheckRound.Node b ↪ F)
    (transform : (Position c b → F) →ₗ[F] (Position c b → F))
    (receive : (Fin k → Fin r → F) → Memory → OracleComp (GuardedCompression.Shared Cfg Input Digest)
      (NTTRowOracle.Proposal F (Position c b) Memory k))
    (bindRows : (Fin k → Fin r → F) → NTTRowOracle.Proposal F (Position c b) Memory k →
      OracleComp (GuardedCompression.Shared Cfg Input Digest) Memory)
    (memory : Memory)
    (afterQuery : Prefix F Memory c b r k → Query F b c → OracleComp (GuardedCompression.Shared Cfg Input Digest) Later) :=
  GuardedCompression.program nodes (NTTRowOracle.program transform receive bindRows memory)
    (fun entry => entry.2.accepted) afterQuery

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- Every supported truthful-terminal execution lies in the row-miss event or
the shared fresh-compression agreement event for a genuinely wrong row. -/
theorem truthful_implies_risks
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (nodes : PackedSumcheckRound.Node b ↪ F)
    (transform : (Position c b → F) →ₗ[F] (Position c b → F))
    (coefficients evaluations : MatrixFold.Cube (r + c) → Fin b → F)
    (receive : (Fin k → Fin r → F) → Memory → OracleComp (GuardedCompression.Shared Cfg Input Digest)
      (NTTRowOracle.Proposal F (Position c b) Memory k))
    (bindRows : (Fin k → Fin r → F) → NTTRowOracle.Proposal F (Position c b) Memory k →
      OracleComp (GuardedCompression.Shared Cfg Input Digest) Memory)
    (memory : Memory)
    (afterQuery : Prefix F Memory c b r k → Query F b c → OracleComp (GuardedCompression.Shared Cfg Input Digest) Later)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : (Prefix F Memory c b r k × Option (Query F b c × Later)) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program nodes transform receive bindRows memory afterQuery)).run state))
    (truthful : TruthfulTerminals coefficients evaluations outcome.1) :
    NTTRowCheck.RowsPass transform (sourceRows c r coefficients) (sourceRows c r evaluations) outcome.1.1.1 ∨
      GuardedCompression.WrongAgreement proposed (correct coefficients evaluations) outcome.1 := by
  obtain ⟨earlier, earlierSupported, finished, _, equal⟩ :=
    (SharedContinuation.support_program enc dummy shape _ _ state outcome).mp supported
  subst outcome
  have terminal := (truthful_iff coefficients evaluations _).mp truthful
  obtain missed | wrong := NTTRowOracle.accepted_implies_risks enc dummy shape transform
    (sourceRows c r coefficients) (sourceRows c r evaluations) receive bindRows memory state earlier earlierSupported terminal.1
  · exact Or.inl missed
  · exact Or.inr ⟨wrong_family coefficients evaluations earlier.1 wrong, terminal.2⟩

variable [Fintype F] [SampleableType F] [SampleableType (Fin r → F)]

/-- The two NTT arithmetic errors on one shared execution, against truthful
original-source terminals. No union over coefficient/evaluation repetitions is
needed: every row uses one common compression query sampled after binding. -/
theorem truthful_bound
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (nodes : PackedSumcheckRound.Node b ↪ F)
    (transform : (Position c b → F) →ₗ[F] (Position c b → F))
    (coefficients evaluations : MatrixFold.Cube (r + c) → Fin b → F)
    (receive : (Fin k → Fin r → F) → Memory → OracleComp (GuardedCompression.Shared Cfg Input Digest)
      (NTTRowOracle.Proposal F (Position c b) Memory k))
    (bindRows : (Fin k → Fin r → F) → NTTRowOracle.Proposal F (Position c b) Memory k →
      OracleComp (GuardedCompression.Shared Cfg Input Digest) Memory)
    (memory : Memory)
    (afterQuery : Prefix F Memory c b r k → Query F b c → OracleComp (GuardedCompression.Shared Cfg Input Digest) Later)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (falseRelation : ¬NTTRowCheck.Relation transform (sourceRows c r coefficients) (sourceRows c r evaluations)) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program nodes transform receive bindRows memory afterQuery)).run state}[
        TruthfulTerminals coefficients evaluations outcome.1] ≤
      (((r : ENNReal) / Fintype.card F) ^ k) +
        (c : ENNReal) * (((((2 * b - 1 : ℕ) : ENNReal) / Fintype.card F) ^ b)) := by
  have rowBound := NTTRowOracle.continued_miss_bound enc dummy shape transform
    (sourceRows c r coefficients) (sourceRows c r evaluations) receive bindRows memory
    (fun entry => GuardedCompression.finish nodes entry.2.accepted (afterQuery entry)) state falseRelation
  have compressionBound := GuardedCompression.wrong_agreement_bound enc dummy shape nodes
    (NTTRowOracle.program transform receive bindRows memory) (fun entry => entry.2.accepted) afterQuery
    proposed (correct coefficients evaluations) state
  apply le_trans (prEvent_mono_of_support _ _ (fun outcome =>
    NTTRowCheck.RowsPass transform (sourceRows c r coefficients) (sourceRows c r evaluations) outcome.1.1.1 ∨
      GuardedCompression.WrongAgreement proposed (correct coefficients evaluations) outcome.1) ?_)
  · exact (prEvent_or_le _ _ _).trans (add_le_add rowBound compressionBound)
  · intro outcome supported truthful
    exact truthful_implies_risks enc dummy shape nodes transform coefficients evaluations receive bindRows memory afterQuery state
      outcome supported truthful

end

end FormalProof4FHE.HasteBoots.NTTCompression
