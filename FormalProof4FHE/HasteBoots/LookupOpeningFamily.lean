module

public import FormalProof4FHE.HasteBoots.PackedQueryArity
public import FormalProof4FHE.HasteBoots.PreparedLookupPair
public import FormalProof4FHE.HasteBoots.StagedHeterogeneousBatchOpening

@[expose] public section

/-!
# Exact original-root query and value families of extension lookup

Each helper root has sum/identity queries in that order. Each source root has
one scalar query per repetition. Values are the original raw packed vectors,
not the optional post-map's finished extension values. Trusted construction
fixes claim counts, queries and values; behavior factories cannot replace them.
Lookup and PCS analysis extension fields remain separate in the soundness use.
-/

open Matrix
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim
open FormalProof4FHE.HasteBoots.HeterogeneousBatchOpening

namespace FormalProof4FHE.HasteBoots.LookupOpeningFamily

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
  {d padding c row count repetitions : ℕ}

def layout (g : Geometry c row count repetitions) (root : Root count repetitions) : Layout :=
  ⟨g.front root, g.suffix root, (match root with | .inl _ => repetitions | .inr _ => 2), g.m root, g.queries root⟩

abbrev Packets (F K : Type) (width count n repetitions : ℕ) :=
  Fin repetitions → PreparedLookupPair.Packet F K width count n

def sourceQuery (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (g : Geometry c row count repetitions) (packets : Packets F K (d + padding) count (c + row) repetitions)
    (source : Fin count) (pair : Fin repetitions) : Query F (d + padding) (g.front (.inl source) + g.suffix (.inl source)) :=
  PackedQueryArity.query (g.sourceArity source).symm
    (ExtensionLookupTerminal.sourceQuery basis shape (ScalarSumcheckQuery.point (packets pair).zeroClaim.query)).query

def helperQuery (basis : Module.Basis (Fin d) F K)
    (g : Geometry c row count repetitions) (packets : Packets F K (d + padding) count (c + row) repetitions)
    (pair : Fin repetitions) (claim : Fin 2) : Query F (d + padding) (g.front (.inr pair) + g.suffix (.inr pair)) :=
  PackedQueryArity.query (g.helperArity pair).symm
    (if claim = 0 then (ExtensionQuery.coefficientsQuery basis (ScalarSumcheckQuery.point (packets pair).sumClaim.query)).query
      else (ExtensionQuery.coefficientsQuery basis (ScalarSumcheckQuery.point (packets pair).zeroClaim.query)).query)

def queries (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (g : Geometry c row count repetitions) (packets : Packets F K (d + padding) count (c + row) repetitions) :
    (root : Root count repetitions) → NativeBatchChecks.QueryFamily F (d + padding)
      (layout g root).front (layout g root).suffix (layout g root).claims
  | .inl source => sourceQuery basis shape g packets source
  | .inr pair => helperQuery basis g packets pair

def values (basis : Module.Basis (Fin d) F K) (g : Geometry c row count repetitions)
    (packets : Packets F K (d + padding) count (c + row) repetitions) :
    (root : Root count repetitions) → Fin (layout g root).claims → Fin (d + padding) → F
  | .inl source => fun pair => (packets pair).values.sources source
  | .inr pair => fun claim : Fin 2 => if claim = 0 then PaddedExtension.encode basis ((packets pair).sumClaim.expected 0)
      else PaddedExtension.encode basis (packets pair).values.helper

variable {Cfg Input Digest Response Memory : Type} [DecidableEq F]
  {heights : Cfg → ℕ} {tag : Root count repetitions → Cfg}

/-- Native behavior supplies messages/workers, never the trusted lookup query
and claim vectors. Encoding/domain/root are additionally fixed by the existing
staged native wrapper. No ghost decoded source enters this operational map. -/
def bind (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (g : Geometry c row count repetitions) (packets : Packets F K (d + padding) count (c + row) repetitions)
    (root : Root count repetitions)
    (behavior : Protocol F Input Digest Cfg Response Memory (d + padding) heights tag (layout g) root) :
    Protocol F Input Digest Cfg Response Memory (d + padding) heights tag (layout g) root :=
  { behavior with query := queries basis shape g packets root, values := values basis g packets root }

variable {g : Geometry c row count repetitions}

def sourceTables
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * (d + padding)) (radius : Root count repetitions → ℕ)
    (words : ∀ root, Fin (2 ^ heights (tag root)) → (Fin (2 ^ g.front root) × Fin (d + padding)) → Fin (d + padding) → F)
    (source : Fin count) : MatrixFold.Cube row → Fin (d + padding) → F :=
  PackedQueryArity.table (g.sourceArity source).symm
    (SubclaimSourceLayout.decodedSource (domain (.inl source)) (capacity (.inl source)) (radius (.inl source)) (words (.inl source)))

def helperTables
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * (d + padding)) (radius : Root count repetitions → ℕ)
    (words : ∀ root, Fin (2 ^ heights (tag root)) → (Fin (2 ^ g.front root) × Fin (d + padding)) → Fin (d + padding) → F)
    (pair : Fin repetitions) : MatrixFold.Cube (c + row) → Fin (d + padding) → F :=
  PackedQueryArity.table (g.helperArity pair).symm
    (SubclaimSourceLayout.decodedSource (domain (.inr pair)) (capacity (.inr pair)) (radius (.inr pair)) (words (.inr pair)))

/-- The literal wrong-value predicate used by native heterogeneous PCS. -/
def WrongValue (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (packets : Packets F K (d + padding) count (c + row) repetitions)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * (d + padding)) (radius : Root count repetitions → ℕ)
    (words : ∀ root, Fin (2 ^ heights (tag root)) → (Fin (2 ^ g.front root) × Fin (d + padding)) → Fin (d + padding) → F)
    (root : Root count repetitions) (claim : Fin (layout g root).claims) : Prop :=
  values basis g packets root claim ≠ matrixEvaluation
    (NativeBatchChecks.left (queries basis shape g packets root) claim)
    (NativeBatchChecks.right (queries basis shape g packets root) claim)
    (MatrixOpeningSecurity.extract (domain root) (capacity root) (radius root) (words root))

/-- Source claims remain raw vectors on their original root, including the
zero-row scalar bridge whose optional post-map is not the identity. -/
theorem source_wrong_iff (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (packets : Packets F K (d + padding) count (c + row) repetitions)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * (d + padding)) (radius : Root count repetitions → ℕ)
    (words : ∀ root, Fin (2 ^ heights (tag root)) → (Fin (2 ^ g.front root) × Fin (d + padding)) → Fin (d + padding) → F)
    (source : Fin count) (pair : Fin repetitions) :
    WrongValue basis shape packets domain capacity radius words (.inl source) pair ↔
      (packets pair).values.sources source ≠
        (ExtensionLookupTerminal.sourceQuery basis shape (ScalarSumcheckQuery.point (packets pair).zeroClaim.query)).query.fold
          (sourceTables domain capacity radius words source) := by
  unfold WrongValue values queries sourceQuery NativeBatchChecks.left NativeBatchChecks.right
  erw [← SubclaimSourceLayout.fold_decodedSource, PackedQueryArity.fold]
  rfl

/-- Both original helper obligations, in native [sum, identity] order. -/
theorem helper_wrong_iff (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (packets : Packets F K (d + padding) count (c + row) repetitions)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * (d + padding)) (radius : Root count repetitions → ℕ)
    (words : ∀ root, Fin (2 ^ heights (tag root)) → (Fin (2 ^ g.front root) × Fin (d + padding)) → Fin (d + padding) → F)
    (pair : Fin repetitions) (claim : Fin 2) :
    WrongValue basis shape packets domain capacity radius words (.inr pair) claim ↔
      (if claim = 0 then PaddedExtension.encode basis ((packets pair).sumClaim.expected 0)
        else PaddedExtension.encode basis (packets pair).values.helper) ≠
      (if claim = 0 then (ExtensionQuery.coefficientsQuery basis (ScalarSumcheckQuery.point (packets pair).sumClaim.query)).query
        else (ExtensionQuery.coefficientsQuery basis (ScalarSumcheckQuery.point (packets pair).zeroClaim.query)).query).fold
          (helperTables domain capacity radius words pair) := by
  unfold WrongValue values queries helperQuery NativeBatchChecks.left NativeBatchChecks.right
  erw [← SubclaimSourceLayout.fold_decodedSource, PackedQueryArity.fold]
  rfl

/-- Exactly the three original opening failures per pair, with no per-query
probability union: they are the same wrong-value event of the native family. -/
theorem any_pair_wrong_iff (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (packets : Packets F K (d + padding) count (c + row) repetitions)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * (d + padding)) (radius : Root count repetitions → ℕ)
    (words : ∀ root, Fin (2 ^ heights (tag root)) → (Fin (2 ^ g.front root) × Fin (d + padding)) → Fin (d + padding) → F) :
    (∃ pair, LookupPairTerminal.WrongOpenings basis shape (sourceTables domain capacity radius words)
      (helperTables domain capacity radius words pair) (packets pair).sumClaim (packets pair).zeroClaim
      (packets pair).values.sources (packets pair).values.helper) ↔
    ∃ root claim, WrongValue basis shape packets domain capacity radius words root claim := by
  constructor
  · rintro ⟨pair, wrong⟩
    rcases wrong with sumWrong | ⟨source, sourceWrong⟩ | helperWrong
    · refine ⟨.inr pair, (0 : Fin 2), ?_⟩
      exact (helper_wrong_iff basis shape packets domain capacity radius words pair 0).mpr (by simpa using sumWrong)
    · exact ⟨.inl source, pair, (source_wrong_iff basis shape packets domain capacity radius words source pair).mpr sourceWrong⟩
    · refine ⟨.inr pair, (1 : Fin 2), ?_⟩
      exact (helper_wrong_iff basis shape packets domain capacity radius words pair 1).mpr (by simpa using helperWrong)
  · rintro ⟨root, claim, wrong⟩
    cases root with
    | inl source =>
      refine ⟨claim, Or.inr (Or.inl ⟨source, ?_⟩)⟩
      exact (source_wrong_iff basis shape packets domain capacity radius words source claim).mp wrong
    | inr pair =>
      change Fin 2 at claim
      refine ⟨pair, ?_⟩
      fin_cases claim
      · left
        simpa using (helper_wrong_iff basis shape packets domain capacity radius words pair 0).mp wrong
      · right; right
        simpa using
          (helper_wrong_iff basis shape packets domain capacity radius words pair 1).mp wrong

end

end FormalProof4FHE.HasteBoots.LookupOpeningFamily
