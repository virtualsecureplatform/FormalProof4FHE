module
public import FormalProof4FHE.HasteBoots.PaddedMixedWidthLookupOpeningFamily
public import FormalProof4FHE.HasteBoots.RectangularBatchVerifier
public import FormalProof4FHE.HasteBoots.RectangularSubclaimSourceLayout
@[expose] public section

/-! The padded lookup terminal uses the existing original source/helper queries
and values while retaining independent code-symbol widths. The operational bind
fixes those vectors in the rectangular worker verifier. No helper commitment or
challenge is added, and every original sum/identity obligation is preserved. -/
open Matrix
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim
namespace FormalProof4FHE.HasteBoots.RectangularPaddedLookupOpeningFamily
open PaddedMixedWidthLookupOpeningFamily
noncomputable section
variable {F K : Type} [Field F] [Field K] [Algebra F K]
  {d padding helperPadding c row count repetitions : ℕ}
  {Cfg Input Digest Response Memory : Type} [DecidableEq F]
  {heights : Cfg → ℕ} {tag : Root count repetitions → Cfg}
  {g : Geometry c row count repetitions} {symbolWidth : Root count repetitions → ℕ}

/-- Trusted terminal data fixes every original query and value in the actual
rectangular verifier; providers retain control of response work and scheduling. -/
def bind (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2^c)
    (packet : Packet F K (d+padding) count (c+row) repetitions) (root : Root count repetitions)
    (behavior : RectangularBatchVerifier.Protocol F Input Digest Cfg Response Memory
      (packedWidth (d+padding) (d+helperPadding) root) (symbolWidth root)
      (g.front root) (g.suffix root) (layout g root).claims (g.m root) (g.queries root) (heights (tag root))) :
    RectangularBatchVerifier.Protocol F Input Digest Cfg Response Memory
      (packedWidth (d+padding) (d+helperPadding) root) (symbolWidth root)
      (g.front root) (g.suffix root) (layout g root).claims (g.m root) (g.queries root) (heights (tag root)) :=
  { behavior with query := queries basis shape g packet root, values := values basis g packet root }

def sourceTables
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * symbolWidth root) (radius : Root count repetitions → ℕ)
    (words : ∀ root, Fin (2 ^ heights (tag root)) → (Fin (2 ^ g.front root) × Fin (packedWidth (d + padding) (d + helperPadding) root)) → Fin (symbolWidth root) → F)
    (source : Fin count) : MatrixFold.Cube row → Fin (d + padding) → F :=
  QueryHighZeroPadding.source (g.extra (.inl source)) (PackedQueryArity.table (g.sourceArity source)
    (RectangularSubclaimSourceLayout.decodedSource (domain (.inl source)) (capacity (.inl source)) (radius (.inl source)) (words (.inl source))))

def helperTables
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * symbolWidth root) (radius : Root count repetitions → ℕ)
    (words : ∀ root, Fin (2 ^ heights (tag root)) → (Fin (2 ^ g.front root) × Fin (packedWidth (d + padding) (d + helperPadding) root)) → Fin (symbolWidth root) → F)
    (pair : Fin repetitions) : MatrixFold.Cube (c + row) → Fin (d + helperPadding) → F :=
  QueryHighZeroPadding.source (g.extra (.inr pair)) (PackedQueryArity.table (g.helperArity pair)
    (RectangularSubclaimSourceLayout.decodedSource (domain (.inr pair)) (capacity (.inr pair)) (radius (.inr pair)) (words (.inr pair))))

/-- The literal wrong-value predicate used by native heterogeneous PCS. -/
def WrongValue (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (packet : Packet F K (d + padding) count (c + row) repetitions)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * symbolWidth root) (radius : Root count repetitions → ℕ)
    (words : ∀ root, Fin (2 ^ heights (tag root)) → (Fin (2 ^ g.front root) × Fin (packedWidth (d + padding) (d + helperPadding) root)) → Fin (symbolWidth root) → F)
    (root : Root count repetitions) (claim : Fin (layout g root).claims) : Prop :=
  values basis g packet root claim ≠ matrixEvaluation
    (NativeBatchChecks.left (queries basis shape g packet root) claim)
    (NativeBatchChecks.right (queries basis shape g packet root) claim)
    (RectangularMatrixOpeningKernel.extract (domain root) (capacity root) (radius root) (words root))

/-- Source claims remain raw vectors on their original root, including the
zero-row scalar bridge whose optional post-map is not the identity. -/
theorem source_wrong_iff (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (packet : Packet F K (d + padding) count (c + row) repetitions)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * symbolWidth root) (radius : Root count repetitions → ℕ)
    (words : ∀ root, Fin (2 ^ heights (tag root)) → (Fin (2 ^ g.front root) × Fin (packedWidth (d + padding) (d + helperPadding) root)) → Fin (symbolWidth root) → F)
    (source : Fin count) :
    WrongValue basis shape packet domain capacity radius words (.inl source) (0 : Fin 1) ↔
      packet.sources source ≠
        (ExtensionLookupTerminal.sourceQuery basis shape packet.point).query.fold
          (sourceTables domain capacity radius words source) := by
  unfold WrongValue values queries sourceQuery NativeBatchChecks.left NativeBatchChecks.right
  erw [← RectangularSubclaimSourceLayout.fold_decodedSource, PackedQueryArity.fold, ← QueryHighZeroPadding.fold]
  rfl

/-- Both original helper obligations, in native [sum, identity] order. -/
theorem helper_wrong_iff (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (packet : Packet F K (d + padding) count (c + row) repetitions)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * symbolWidth root) (radius : Root count repetitions → ℕ)
    (words : ∀ root, Fin (2 ^ heights (tag root)) → (Fin (2 ^ g.front root) × Fin (packedWidth (d + padding) (d + helperPadding) root)) → Fin (symbolWidth root) → F)
    (pair : Fin repetitions) (claim : Fin 2) :
    WrongValue basis shape packet domain capacity radius words (.inr pair) claim ↔
      (if claim = 0 then PaddedExtension.encode (padding := helperPadding) basis (packet.sumExpected pair)
        else PaddedExtension.encode (padding := helperPadding) basis (packet.helpers pair)) ≠
      (if claim = 0 then (ExtensionQuery.coefficientsQuery (padding := helperPadding) basis packet.point).query
        else (ExtensionQuery.coefficientsQuery (padding := helperPadding) basis packet.point).query).fold
          (helperTables domain capacity radius words pair) := by
  unfold WrongValue values queries helperQuery NativeBatchChecks.left NativeBatchChecks.right
  erw [← RectangularSubclaimSourceLayout.fold_decodedSource, PackedQueryArity.fold, ← QueryHighZeroPadding.fold]
  rfl

/-- With every source used by some job, the job-local wrong-opening union
is exactly the one-source/two-helper original PCS event. Slot coverage is a
structural property of the request schedule, not an authentication premise. -/
theorem any_job_wrong_iff (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (packet : Packet F K (d + padding) count (c + row) repetitions)
    {columns : Fin repetitions → ℕ}
    (slots : (job : Fin repetitions) → Fin (columns job) → Fin count)
    (coverage : ∀ source, ∃ job column, slots job column = source)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * symbolWidth root) (radius : Root count repetitions → ℕ)
    (words : ∀ root, Fin (2 ^ heights (tag root)) → (Fin (2 ^ g.front root) × Fin (packedWidth (d + padding) (d + helperPadding) root)) → Fin (symbolWidth root) → F) :
    (∃ job, WrongOpenings basis shape
      (fun column => sourceTables domain capacity radius words (slots job column))
      (helperTables domain capacity radius words job) (pairPacket slots packet job).sumClaim
      (pairPacket slots packet job).zeroClaim (pairPacket slots packet job).values.sources
      (pairPacket slots packet job).values.helper) ↔
    ∃ root claim, WrongValue basis shape packet domain capacity radius words root claim := by
  have pointEq : ScalarSumcheckQuery.point (ScalarSumcheckQuery.query (c + row) packet.point) = packet.point :=
    ScalarSumcheckQuery.point_query _
  constructor
  · rintro ⟨job, wrong⟩
    rcases wrong with sumWrong | ⟨column, sourceWrong⟩ | helperWrong
    · refine ⟨.inr job, (0 : Fin 2), ?_⟩
      apply (helper_wrong_iff basis shape packet domain capacity radius words job 0).mpr
      simpa only [pairPacket, pointEq, ite_true] using sumWrong
    · refine ⟨.inl (slots job column), (0 : Fin 1), ?_⟩
      apply (source_wrong_iff basis shape packet domain capacity radius words (slots job column)).mpr
      simpa only [pairPacket, pointEq] using sourceWrong
    · refine ⟨.inr job, (1 : Fin 2), ?_⟩
      apply (helper_wrong_iff basis shape packet domain capacity radius words job 1).mpr
      simpa only [pairPacket, pointEq, Fin.one_eq_zero_iff, Nat.reduceEqDiff, ite_false] using helperWrong
  · rintro ⟨root, claim, wrong⟩
    cases root with
    | inl source =>
      obtain ⟨job,column,equal⟩ := coverage source
      have sourceWrong := (source_wrong_iff basis shape packet domain capacity radius words source).mp
        (by fin_cases claim; exact wrong)
      refine ⟨job, Or.inr (Or.inl ⟨column, ?_⟩)⟩
      simpa only [pairPacket, pointEq, equal] using sourceWrong
    | inr job =>
      change Fin 2 at claim
      refine ⟨job, ?_⟩
      fin_cases claim
      · left
        simpa only [pairPacket, pointEq, ite_true] using
          (helper_wrong_iff basis shape packet domain capacity radius words job 0).mp wrong
      · right; right
        simpa only [pairPacket, pointEq, Fin.one_eq_zero_iff, Nat.reduceEqDiff, ite_false] using
          (helper_wrong_iff basis shape packet domain capacity radius words job 1).mp wrong

end
end FormalProof4FHE.HasteBoots.RectangularPaddedLookupOpeningFamily
