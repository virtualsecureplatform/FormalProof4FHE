module

public import FormalProof4FHE.HasteBoots.LookupOpeningFamily
public import FormalProof4FHE.HasteBoots.SharedScalarBatchQuery
public import FormalProof4FHE.HasteBoots.StagedVariableWidthBatchOpening

@[expose] public section

/-!
# Common-point original-root openings with unequal packed widths

Every original source has exactly one raw vector claim at the common scalar
point. Each helper has two ordered claims [sum, identity] at that same point.
Jobs gather their own ordered slots from the global source registry, preserving
aliases. No repeated source claims or replacement roots are introduced. Source and helper widths are independent; no helper payload padding is added.
Byte/transcript refinement and arithmetic composition remain separate.
-/

open Matrix
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim
open FormalProof4FHE.HasteBoots.VariableWidthBatchOpening

namespace FormalProof4FHE.HasteBoots.MixedWidthLookupOpeningFamily

noncomputable section

abbrev Root (count repetitions : ℕ) := Fin count ⊕ Fin repetitions

/-- Original source/helper PCS splits, never padded replacement commitments. -/
structure Geometry (c row count repetitions : ℕ) where
  front : Root count repetitions → ℕ
  suffix : Root count repetitions → ℕ
  m : Root count repetitions → ℕ
  queries : Root count repetitions → ℕ
  sourceArity : ∀ source, front (.inl source) + suffix (.inl source) = row
  helperArity : ∀ pair, front (.inr pair) + suffix (.inr pair) = c + row

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  {d padding helperPadding c row count repetitions : ℕ}

/-- Physical payload width of each original root. Helpers may use the bare
extension degree while source roots retain power-of-two packing. -/
def packedWidth (sourceWidth helperWidth : ℕ) : Root count repetitions → ℕ
  | .inl _ => sourceWidth
  | .inr _ => helperWidth

def layout (g : Geometry c row count repetitions) (root : Root count repetitions) : Layout :=
  ⟨g.front root, g.suffix root, (match root with | .inl _ => 1 | .inr _ => 2), g.m root, g.queries root⟩

/-- Terminal data contains a single point and a single global source vector
family. All job subclaims are constructed from this data, not certified equal. -/
structure Packet (F K : Type) (width count n jobs : ℕ) where
  point : Fin n → K
  sources : Fin count → Fin width → F
  sumExpected : Fin jobs → K
  identityExpected : Fin jobs → K
  helpers : Fin jobs → K
  equalityPoints : Fin jobs → Fin n → K

def pairPacket {columns : Fin repetitions → ℕ}
    (slots : (job : Fin repetitions) → Fin (columns job) → Fin count)
    (packet : Packet F K (d + padding) count (c + row) repetitions) (job : Fin repetitions) :
    PreparedLookupPair.Packet F K (d + padding) (columns job) (c + row) :=
  ⟨⟨ScalarSumcheckQuery.query _ packet.point,fun _ => packet.sumExpected job⟩,
    packet.equalityPoints job,
    ⟨ScalarSumcheckQuery.query _ packet.point,fun _ => packet.identityExpected job⟩,
    ⟨fun column => packet.sources (slots job column),packet.helpers job⟩⟩

/-- Deterministic extraction from the batch result and received terminal
vectors. The reference equation chooses the shared point; validity below is
proved by batch execution, not checked or supplied by the prover. -/
def ofBatch (claims : (Fin repetitions × Bool) → Subclaim K 1 (c + row))
    (reference : Fin repetitions × Bool) (sources : Fin count → Fin (d + padding) → F)
    (helpers : Fin repetitions → K) (equalityPoints : Fin repetitions → Fin (c + row) → K) :
    Packet F K (d + padding) count (c + row) repetitions :=
  ⟨ScalarSumcheckQuery.point (claims reference).query,sources,
    fun job => (claims (job,false)).expected 0,fun job => (claims (job,true)).expected 0,
    helpers,equalityPoints⟩

theorem rebuild_claim {Equation : Type} (claims : Equation → Subclaim K 1 (c + row))
    (valid : SharedScalarBatchQuery.Valid (some (claims,()))) (reference equation : Equation) :
    (⟨ScalarSumcheckQuery.query (c + row) (ScalarSumcheckQuery.point (claims reference).query),
      fun _ => (claims equation).expected 0⟩ : Subclaim K 1 (c + row)) = claims equation := by
  have queryEq := (valid.1 reference).symm.trans (valid.2 reference equation)
  have expectedEq : (fun _ : Fin 1 => (claims equation).expected 0) = (claims equation).expected := by
    funext lane
    fin_cases lane
    rfl
  exact congrArg₂ Subclaim.mk queryEq expectedEq

omit [Field F] [Algebra F K] in
/-- Each job packet contains the actual returned sum and identity subclaims,
with its ordered original source slots. Common-query validity suffices; no
source-dependent certificate or resampling is introduced. -/
theorem pairPacket_ofBatch {columns : Fin repetitions → ℕ}
    (slots : (job : Fin repetitions) → Fin (columns job) → Fin count)
    (claims : (Fin repetitions × Bool) → Subclaim K 1 (c + row))
    (valid : SharedScalarBatchQuery.Valid (some (claims,()))) (reference : Fin repetitions × Bool)
    (sources : Fin count → Fin (d + padding) → F) (helpers : Fin repetitions → K)
    (equalityPoints : Fin repetitions → Fin (c + row) → K) (job : Fin repetitions) :
    pairPacket slots (ofBatch claims reference sources helpers equalityPoints) job =
      ⟨claims (job,false),equalityPoints job,claims (job,true),
        ⟨fun column => sources (slots job column),helpers job⟩⟩ := by
  unfold pairPacket ofBatch
  rw [rebuild_claim claims valid reference (job,false),rebuild_claim claims valid reference (job,true)]

def sourceQuery (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (g : Geometry c row count repetitions) (packet : Packet F K (d + padding) count (c + row) repetitions)
    (source : Fin count) : Query F (d + padding) (g.front (.inl source) + g.suffix (.inl source)) :=
  PackedQueryArity.query (g.sourceArity source).symm
    (ExtensionLookupTerminal.sourceQuery basis shape packet.point).query

def helperQuery (basis : Module.Basis (Fin d) F K)
    (g : Geometry c row count repetitions) (packet : Packet F K (d + padding) count (c + row) repetitions)
    (pair : Fin repetitions) (claim : Fin 2) : Query F (d + helperPadding) (g.front (.inr pair) + g.suffix (.inr pair)) :=
  PackedQueryArity.query (g.helperArity pair).symm
    (if claim = 0 then (ExtensionQuery.coefficientsQuery (padding := helperPadding) basis packet.point).query
      else (ExtensionQuery.coefficientsQuery (padding := helperPadding) basis packet.point).query)

def queries (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (g : Geometry c row count repetitions) (packet : Packet F K (d + padding) count (c + row) repetitions) :
    (root : Root count repetitions) → NativeBatchChecks.QueryFamily F (packedWidth (d + padding) (d + helperPadding) root)
      (layout g root).front (layout g root).suffix (layout g root).claims
  | .inl source => fun _ => sourceQuery basis shape g packet source
  | .inr pair => helperQuery basis g packet pair

def values (basis : Module.Basis (Fin d) F K) (g : Geometry c row count repetitions)
    (packet : Packet F K (d + padding) count (c + row) repetitions) :
    (root : Root count repetitions) → Fin (layout g root).claims → Fin (packedWidth (d + padding) (d + helperPadding) root) → F
  | .inl source => fun _ => packet.sources source
  | .inr pair => fun claim : Fin 2 => if claim = 0 then PaddedExtension.encode (padding := helperPadding) basis (packet.sumExpected pair)
      else PaddedExtension.encode (padding := helperPadding) basis (packet.helpers pair)

variable {Cfg Input Digest Response Memory : Type} [DecidableEq F]
  {heights : Cfg → ℕ} {tag : Root count repetitions → Cfg}

/-- Behavior supplies messages/workers; trusted construction fixes the query
and claim vectors. Encoding/domain/root remain parameters of the grouped
opening wrapper. No ghost decoded source enters this operational map. -/
def bind (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (g : Geometry c row count repetitions) (packet : Packet F K (d + padding) count (c + row) repetitions)
    (root : Root count repetitions)
    (behavior : Protocol F Input Digest Cfg Response Memory (packedWidth (d + padding) (d + helperPadding)) heights tag (layout g) root) :
    Protocol F Input Digest Cfg Response Memory (packedWidth (d + padding) (d + helperPadding)) heights tag (layout g) root :=
  { behavior with query := queries basis shape g packet root, values := values basis g packet root }

variable {g : Geometry c row count repetitions}

def sourceTables
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * packedWidth (d + padding) (d + helperPadding) root) (radius : Root count repetitions → ℕ)
    (words : ∀ root, Fin (2 ^ heights (tag root)) → (Fin (2 ^ g.front root) × Fin (packedWidth (d + padding) (d + helperPadding) root)) → Fin (packedWidth (d + padding) (d + helperPadding) root) → F)
    (source : Fin count) : MatrixFold.Cube row → Fin (d + padding) → F :=
  PackedQueryArity.table (g.sourceArity source).symm
    (SubclaimSourceLayout.decodedSource (domain (.inl source)) (capacity (.inl source)) (radius (.inl source)) (words (.inl source)))

def helperTables
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * packedWidth (d + padding) (d + helperPadding) root) (radius : Root count repetitions → ℕ)
    (words : ∀ root, Fin (2 ^ heights (tag root)) → (Fin (2 ^ g.front root) × Fin (packedWidth (d + padding) (d + helperPadding) root)) → Fin (packedWidth (d + padding) (d + helperPadding) root) → F)
    (pair : Fin repetitions) : MatrixFold.Cube (c + row) → Fin (d + helperPadding) → F :=
  PackedQueryArity.table (g.helperArity pair).symm
    (SubclaimSourceLayout.decodedSource (domain (.inr pair)) (capacity (.inr pair)) (radius (.inr pair)) (words (.inr pair)))

/-- The literal wrong-value predicate used by native heterogeneous PCS. -/
def WrongValue (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (packet : Packet F K (d + padding) count (c + row) repetitions)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * packedWidth (d + padding) (d + helperPadding) root) (radius : Root count repetitions → ℕ)
    (words : ∀ root, Fin (2 ^ heights (tag root)) → (Fin (2 ^ g.front root) × Fin (packedWidth (d + padding) (d + helperPadding) root)) → Fin (packedWidth (d + padding) (d + helperPadding) root) → F)
    (root : Root count repetitions) (claim : Fin (layout g root).claims) : Prop :=
  values basis g packet root claim ≠ matrixEvaluation
    (NativeBatchChecks.left (queries basis shape g packet root) claim)
    (NativeBatchChecks.right (queries basis shape g packet root) claim)
    (MatrixOpeningSecurity.extract (domain root) (capacity root) (radius root) (words root))

/-- Source claims remain raw vectors on their original root, including the
zero-row scalar bridge whose optional post-map is not the identity. -/
theorem source_wrong_iff (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (packet : Packet F K (d + padding) count (c + row) repetitions)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * packedWidth (d + padding) (d + helperPadding) root) (radius : Root count repetitions → ℕ)
    (words : ∀ root, Fin (2 ^ heights (tag root)) → (Fin (2 ^ g.front root) × Fin (packedWidth (d + padding) (d + helperPadding) root)) → Fin (packedWidth (d + padding) (d + helperPadding) root) → F)
    (source : Fin count) :
    WrongValue basis shape packet domain capacity radius words (.inl source) (0 : Fin 1) ↔
      packet.sources source ≠
        (ExtensionLookupTerminal.sourceQuery basis shape packet.point).query.fold
          (sourceTables domain capacity radius words source) := by
  unfold WrongValue values queries sourceQuery NativeBatchChecks.left NativeBatchChecks.right
  erw [← SubclaimSourceLayout.fold_decodedSource, PackedQueryArity.fold]
  rfl

/-- Both original helper obligations, in native [sum, identity] order. -/
theorem helper_wrong_iff (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (packet : Packet F K (d + padding) count (c + row) repetitions)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * packedWidth (d + padding) (d + helperPadding) root) (radius : Root count repetitions → ℕ)
    (words : ∀ root, Fin (2 ^ heights (tag root)) → (Fin (2 ^ g.front root) × Fin (packedWidth (d + padding) (d + helperPadding) root)) → Fin (packedWidth (d + padding) (d + helperPadding) root) → F)
    (pair : Fin repetitions) (claim : Fin 2) :
    WrongValue basis shape packet domain capacity radius words (.inr pair) claim ↔
      (if claim = 0 then PaddedExtension.encode (padding := helperPadding) basis (packet.sumExpected pair)
        else PaddedExtension.encode (padding := helperPadding) basis (packet.helpers pair)) ≠
      (if claim = 0 then (ExtensionQuery.coefficientsQuery (padding := helperPadding) basis packet.point).query
        else (ExtensionQuery.coefficientsQuery (padding := helperPadding) basis packet.point).query).fold
          (helperTables domain capacity radius words pair) := by
  unfold WrongValue values queries helperQuery NativeBatchChecks.left NativeBatchChecks.right
  erw [← SubclaimSourceLayout.fold_decodedSource, PackedQueryArity.fold]
  rfl

/-- Three original opening obligations with independent source/helper widths. -/
def WrongOpenings {columns : ℕ} (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (sources : Fin columns → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + helperPadding) → F)
    (sumClaim zeroClaim : Subclaim K 1 (c + row))
    (claims : Fin columns → Fin (d + padding) → F) (helper : K) : Prop :=
  PaddedExtension.encode (padding := helperPadding) basis (sumClaim.expected 0) ≠
      (ExtensionQuery.coefficientsQuery basis (ScalarSumcheckQuery.point sumClaim.query)).query.fold helpers ∨
    (∃ i, claims i ≠ (ExtensionLookupTerminal.sourceQuery basis shape (ScalarSumcheckQuery.point zeroClaim.query)).query.fold (sources i)) ∨
    PaddedExtension.encode (padding := helperPadding) basis helper ≠
      (ExtensionQuery.coefficientsQuery basis (ScalarSumcheckQuery.point zeroClaim.query)).query.fold helpers

/-- With every source used by some job, the job-local wrong-opening union
is exactly the one-source/two-helper original PCS event. Slot coverage is a
structural property of the request schedule, not an authentication premise. -/
theorem any_job_wrong_iff (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (packet : Packet F K (d + padding) count (c + row) repetitions)
    {columns : Fin repetitions → ℕ}
    (slots : (job : Fin repetitions) → Fin (columns job) → Fin count)
    (coverage : ∀ source, ∃ job column, slots job column = source)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * packedWidth (d + padding) (d + helperPadding) root) (radius : Root count repetitions → ℕ)
    (words : ∀ root, Fin (2 ^ heights (tag root)) → (Fin (2 ^ g.front root) × Fin (packedWidth (d + padding) (d + helperPadding) root)) → Fin (packedWidth (d + padding) (d + helperPadding) root) → F) :
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

end FormalProof4FHE.HasteBoots.MixedWidthLookupOpeningFamily
