module

public import FormalProof4FHE.HasteBoots.RectangularMatrixOpeningKernel
@[expose] public section

/-! Any false original matrix query in a grouped batch has the same rectangular
fixed-word bound. A single decoded table, random matrix and later ordered draw
vector serve every group. Finishing uses every original right query; no union
bound over queries, groups or lanes is introduced. Native grouping/refinement
and production Fiat–Shamir composition remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.RectangularBatchOpeningKernel
open ProbabilityTheory Matrix OracleComp
noncomputable section
variable {F Position Left Group Query Response : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype Position] [DecidableEq Position] [Fintype Left] {m packingWidth codeWidth size : ℕ}

abbrev Test := Group × Fin packingWidth

def weights (left : Group → Left → Matrix (Fin packingWidth) (Fin packingWidth) F) (test : Test (Group := Group) (packingWidth := packingWidth)) :=
  RectangularMatrixResponse.weights (left test.1) test.2

def finishEncoded (domain : Position → F) (capacity : size ≤ m*codeWidth) (groupOf : Query → Group)
    (right : Query → Fin size → Matrix (Fin packingWidth) (Fin packingWidth) F)
    (encoded : Test (Group := Group) (packingWidth := packingWidth) → Position → Fin codeWidth → F) : Query → Fin packingWidth → F :=
  fun query => RectangularMatrixResponse.finishEncoded domain capacity (right query) (fun lane => encoded (groupOf query,lane))

def finishMessage (groupOf : Query → Group) (right : Query → Fin size → Matrix (Fin packingWidth) (Fin packingWidth) F)
    (messages : Group → Fin packingWidth → Fin size → F) : Query → Fin packingWidth → F :=
  fun query => RectangularMatrixResponse.finishMessage (right query) (messages (groupOf query))

omit [Fintype F] [DecidableEq F] [DecidableEq Position] in
theorem finishEncoded_padded (domain : Position ↪ F) (enough : m ≤ Fintype.card Position) (capacity : size ≤ m*codeWidth)
    (groupOf : Query → Group) (right : Query → Fin size → Matrix (Fin packingWidth) (Fin packingWidth) F)
    (messages : Group → Fin packingWidth → Fin size → F) :
    finishEncoded domain capacity groupOf right
      (fun test => BlockEncoder.encode domain (RowLayout.padded (m := m) (messages test.1 test.2))) = finishMessage groupOf right messages := by
  funext query
  exact RectangularMatrixResponse.finishEncoded_padded domain enough capacity (right query) (messages (groupOf query))

omit [Fintype F] [DecidableEq F] [DecidableEq Position] in
theorem finish_structured [NeZero m] [NeZero codeWidth] (domain : Position ↪ F)
    (enough : m ≤ Fintype.card Position) (capacity : size ≤ m*codeWidth)
    (groupOf : Query → Group) (left : Group → Left → Matrix (Fin packingWidth) (Fin packingWidth) F)
    (right : Query → Fin size → Matrix (Fin packingWidth) (Fin packingWidth) F)
    (source : Position → (Left × Fin packingWidth) → Fin codeWidth → F)
    (coded : CommonSource.RowsIn (BlockCode.code domain m codeWidth) source) :
    finishEncoded domain capacity groupOf right (fun test => StructuredOpening.combine (weights left test) source) =
      fun query => matrixEvaluation (left (groupOf query)) (right query) (RectangularMatrixResponse.extractTable domain capacity source) := by
  funext query
  exact RectangularMatrixResponse.finish_structured_eq_evaluation domain enough capacity (left (groupOf query)) (right query) source coded

/-- The error event is any false original query, rather than a selected query.
The right side contains neither the group count nor the original query count. -/
theorem soundness_bound [NeZero m] [NeZero codeWidth] (domain : Position ↪ F)
    (enough : m ≤ Fintype.card Position) (capacity : size ≤ m*codeWidth) (radius testWidth queries : ℕ)
    (word : Position → (Left × Fin packingWidth) → Fin codeWidth → F)
    (groupOf : Query → Group) (left : Group → Left → Matrix (Fin packingWidth) (Fin packingWidth) F)
    (right : Query → Fin size → Matrix (Fin packingWidth) (Fin packingWidth) F)
    (respond : (Fin testWidth → (Left × Fin packingWidth) → F) → ProbComp Response)
    (testResponse : (Fin testWidth → (Left × Fin packingWidth) → F) → Response → Fin testWidth → Fin size → F)
    (structuredResponse : (Fin testWidth → (Left × Fin packingWidth) → F) → Response → Group → Fin packingWidth → Fin size → F)
    [SampleableType ((Left × Fin packingWidth) → F)]
    [SampleableType (Fin testWidth → (Left × Fin packingWidth) → F)] [SampleableType (Fin queries → Position)]
    [SampleableType (Submodule.span F (Set.range (RectangularBaseProximity.stack word)))]
    [SampleableType (ModuleCodeProximity.toSpan (F := F) (RectangularBaseProximity.stack word)).toAddMonoidHom.ker]
    (large : radius < Fintype.card F)
    (small : 3*radius < Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F))) :
    Pr{let pair ← RectangularOpeningKernel.experiment (F := F) (Row := Left × Fin packingWidth) (Position := Position) testWidth queries respond}[
      (∃ query, finishMessage groupOf right (structuredResponse pair.1.1 pair.1.2) query ≠
        matrixEvaluation (left (groupOf query)) (right query) (RectangularMatrixOpeningKernel.extract domain capacity radius word)) ∧
      RectangularMatrixOpeningKernel.Checks (m := m) domain word pair.1.1 (testResponse pair.1.1 pair.1.2) pair.2 ∧
      ∀ test : Test (Group := Group) (packingWidth := packingWidth), ColumnOpening.Agrees
        (StructuredOpening.combine (weights left test) word)
        (BlockEncoder.encode domain (RowLayout.padded (m := m) (structuredResponse pair.1.1 pair.1.2 test.1 test.2))) pair.2] ≤
      ((Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)) : ENNReal) / Fintype.card F)^testWidth +
      max (ColumnOpening.missBound Position queries (Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)) - radius))
        (ColumnOpening.missBound Position queries (radius+1)) := by
  classical
  let source := CommonSource.decode (BlockCode.code domain m codeWidth) radius word
  have sourceC := CommonSource.decode_rowsIn (BlockCode.code domain m codeWidth) radius (BlockCode.code domain m codeWidth).zero_mem word
  let randomClaim := fun matrix response => RectangularMatrixOpeningKernel.encodeMessages (m := m) (codeWidth := codeWidth) domain (testResponse matrix response)
  let structuredClaim := fun matrix response (test : Test (Group := Group) (packingWidth := packingWidth)) =>
    BlockEncoder.encode domain (RowLayout.padded (m := m) (b := codeWidth) (structuredResponse matrix response test.1 test.2))
  let finish := finishEncoded domain capacity groupOf right
  have bound := RectangularOpeningKernel.soundness_bound domain m radius testWidth queries word (weights left) respond
    randomClaim structuredClaim finish large small
    (fun matrix response lane => BlockEncoder.encode_mem_code domain _)
    (fun matrix response test => BlockEncoder.encode_mem_code domain _)
  dsimp only at bound
  let coreEvent := fun pair : ((Fin testWidth → (Left × Fin packingWidth) → F) × Response) × (Fin queries → Position) =>
    finish (structuredClaim pair.1.1 pair.1.2) ≠ finish (fun test => StructuredOpening.combine (weights left test) source) ∧
    RectangularMatrixOpeningKernel.Checks (m := m) domain word pair.1.1 (testResponse pair.1.1 pair.1.2) pair.2 ∧
    ∀ test, ColumnOpening.Agrees (StructuredOpening.combine (weights left test) word) (structuredClaim pair.1.1 pair.1.2 test) pair.2
  change Pr{let pair ← RectangularOpeningKernel.experiment (F := F) (Row := Left × Fin packingWidth) (Position := Position) testWidth queries respond}[coreEvent pair] ≤ _ at bound
  let event := fun pair : ((Fin testWidth → (Left × Fin packingWidth) → F) × Response) × (Fin queries → Position) =>
    (∃ query, finishMessage groupOf right (structuredResponse pair.1.1 pair.1.2) query ≠
      matrixEvaluation (left (groupOf query)) (right query) (RectangularMatrixOpeningKernel.extract domain capacity radius word)) ∧
    RectangularMatrixOpeningKernel.Checks (m := m) domain word pair.1.1 (testResponse pair.1.1 pair.1.2) pair.2 ∧
    ∀ test, ColumnOpening.Agrees (StructuredOpening.combine (weights left test) word) (structuredClaim pair.1.1 pair.1.2 test) pair.2
  change Pr{let pair ← RectangularOpeningKernel.experiment (F := F) (Row := Left × Fin packingWidth) (Position := Position) testWidth queries respond}[event pair] ≤ _
  refine (prEvent_mono _ event coreEvent ?_).trans bound
  intro pair accepted
  refine ⟨?_,accepted.2⟩
  obtain ⟨query,different⟩ := accepted.1
  change finishEncoded domain capacity groupOf right (structuredClaim pair.1.1 pair.1.2) ≠
    finishEncoded domain capacity groupOf right (fun test => StructuredOpening.combine (weights left test) source)
  rw [finish_structured domain enough capacity groupOf left right source sourceC]
  change finishEncoded domain capacity groupOf right
    (fun test => BlockEncoder.encode domain (RowLayout.padded (m := m) (structuredResponse pair.1.1 pair.1.2 test.1 test.2))) ≠ _
  rw [finishEncoded_padded domain enough capacity groupOf right]
  intro same
  exact different (congrFun same query)
end
end FormalProof4FHE.HasteBoots.RectangularBatchOpeningKernel
