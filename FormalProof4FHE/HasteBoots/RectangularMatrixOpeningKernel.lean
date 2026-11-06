module

public import FormalProof4FHE.HasteBoots.RectangularMatrixResponse
public import FormalProof4FHE.HasteBoots.RectangularOpeningKernel
@[expose] public section

/-! Fixed-word matrix opening soundness with independent test, packing and
code-symbol widths, arbitrary probabilistic response state, and one later
shared ordered column vector. One query-independent coefficient table is
extracted from the common decoder. This is an interactive algebraic theorem;
native Fiat–Shamir composition and efficient public extraction remain open. -/
namespace FormalProof4FHE.HasteBoots.RectangularMatrixOpeningKernel
open ProbabilityTheory Matrix OracleComp
noncomputable section
variable {F Position Left Response : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype Position] [DecidableEq Position] [Fintype Left] {m packingWidth codeWidth size : ℕ}

def encodeMessages {lanes : ℕ} (domain : Position → F) (messages : Fin lanes → Fin size → F) :
    Fin lanes → Position → Fin codeWidth → F :=
  fun lane => BlockEncoder.encode domain (RowLayout.padded (m := m) (messages lane))

/-- Depends only on the available word, code, original message length and radius. -/
def extract (domain : Position ↪ F) (capacity : size ≤ m*codeWidth) (radius : ℕ)
    (word : Position → (Left × Fin packingWidth) → Fin codeWidth → F) : Left → Fin size → Fin packingWidth → F :=
  RectangularMatrixResponse.extractTable domain capacity (CommonSource.decode (BlockCode.code domain m codeWidth) radius word)

omit [Fintype F] [DecidableEq Position] in
/-- The common decoder and coefficient inverse recover an honestly encoded
table exactly, without depending on any left/right opening query. -/
theorem extract_encoded [NeZero codeWidth] (domain : Position ↪ F) (enough : m ≤ Fintype.card Position) (capacity : size ≤ m*codeWidth)
    (table : Left → Fin size → Fin packingWidth → F) :
    extract domain capacity 0 (fun pos row => BlockEncoder.encode domain
      (RowLayout.padded (m := m) (b := codeWidth) (fun right => table row.1 right row.2)) pos) = table := by
  classical
  let word := fun pos (row : Left × Fin packingWidth) => BlockEncoder.encode domain
    (RowLayout.padded (m := m) (b := codeWidth) (fun right => table row.1 right row.2)) pos
  have coded : CommonSource.RowsIn (BlockCode.code domain m codeWidth) word :=
    fun row => BlockEncoder.encode_mem_code domain _
  have close := (CommonSource.decode_nearby (BlockCode.code domain m codeWidth) 0 word ⟨word,coded,by simp⟩).2
  have same := (hammingDist_eq_zero.mp (Nat.le_zero.mp close)).symm
  change RectangularMatrixResponse.extractTable domain capacity (CommonSource.decode (BlockCode.code domain m codeWidth) 0 word) = table
  rw [same]
  exact RectangularMatrixResponse.extractTable_encoded domain enough capacity table

def Checks {lanes : ℕ} (domain : Position → F)
    (word : Position → (Left × Fin packingWidth) → Fin codeWidth → F)
    (weights : Fin lanes → (Left × Fin packingWidth) → F) (messages : Fin lanes → Fin size → F)
    {queries : ℕ} (draw : Fin queries → Position) : Prop :=
  ∀ lane, ColumnOpening.Agrees (StructuredOpening.combine (weights lane) word) (encodeMessages (m := m) domain messages lane) draw

theorem soundness_bound [NeZero m] [NeZero codeWidth] (domain : Position ↪ F)
    (enough : m ≤ Fintype.card Position) (capacity : size ≤ m*codeWidth) (radius testWidth queries : ℕ)
    (word : Position → (Left × Fin packingWidth) → Fin codeWidth → F)
    (left : Left → Matrix (Fin packingWidth) (Fin packingWidth) F)
    (right : Fin size → Matrix (Fin packingWidth) (Fin packingWidth) F)
    (respond : (Fin testWidth → (Left × Fin packingWidth) → F) → ProbComp Response)
    (testResponse : (Fin testWidth → (Left × Fin packingWidth) → F) → Response → Fin testWidth → Fin size → F)
    (structuredResponse : (Fin testWidth → (Left × Fin packingWidth) → F) → Response → Fin packingWidth → Fin size → F)
    [SampleableType ((Left × Fin packingWidth) → F)]
    [SampleableType (Fin testWidth → (Left × Fin packingWidth) → F)] [SampleableType (Fin queries → Position)]
    [SampleableType (Submodule.span F (Set.range (RectangularBaseProximity.stack word)))]
    [SampleableType (ModuleCodeProximity.toSpan (F := F) (RectangularBaseProximity.stack word)).toAddMonoidHom.ker]
    (large : radius < Fintype.card F)
    (small : 3*radius < Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F))) :
    Pr{let pair ← RectangularOpeningKernel.experiment (F := F) (Row := Left × Fin packingWidth) (Position := Position) testWidth queries respond}[
      RectangularMatrixResponse.finishMessage right (structuredResponse pair.1.1 pair.1.2) ≠
        matrixEvaluation left right (extract domain capacity radius word) ∧
      Checks (m := m) domain word pair.1.1 (testResponse pair.1.1 pair.1.2) pair.2 ∧
      Checks (m := m) domain word (RectangularMatrixResponse.weights left) (structuredResponse pair.1.1 pair.1.2) pair.2] ≤
      ((Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)) : ENNReal) / Fintype.card F)^testWidth +
      max (ColumnOpening.missBound Position queries (Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)) - radius))
        (ColumnOpening.missBound Position queries (radius+1)) := by
  classical
  let source := CommonSource.decode (BlockCode.code domain m codeWidth) radius word
  have sourceC := CommonSource.decode_rowsIn (BlockCode.code domain m codeWidth) radius (BlockCode.code domain m codeWidth).zero_mem word
  let randomClaim := fun matrix response => encodeMessages (m := m) (codeWidth := codeWidth) domain (testResponse matrix response)
  let structuredClaim := fun matrix response => encodeMessages (m := m) (codeWidth := codeWidth) domain (structuredResponse matrix response)
  let finish := RectangularMatrixResponse.finishEncoded domain capacity right
  have bound := RectangularOpeningKernel.soundness_bound domain m radius testWidth queries word
    (RectangularMatrixResponse.weights left) respond randomClaim structuredClaim finish large small
    (fun matrix response lane => BlockEncoder.encode_mem_code domain (RowLayout.padded (m := m) (testResponse matrix response lane)))
    (fun matrix response lane => BlockEncoder.encode_mem_code domain (RowLayout.padded (m := m) (structuredResponse matrix response lane)))
  dsimp only at bound
  let coreEvent := fun pair : ((Fin testWidth → (Left × Fin packingWidth) → F) × Response) × (Fin queries → Position) =>
    finish (structuredClaim pair.1.1 pair.1.2) ≠ finish (fun lane => StructuredOpening.combine (RectangularMatrixResponse.weights left lane) source) ∧
    Checks (m := m) domain word pair.1.1 (testResponse pair.1.1 pair.1.2) pair.2 ∧
    Checks (m := m) domain word (RectangularMatrixResponse.weights left) (structuredResponse pair.1.1 pair.1.2) pair.2
  change Pr{let pair ← RectangularOpeningKernel.experiment (F := F) (Row := Left × Fin packingWidth) (Position := Position) testWidth queries respond}[coreEvent pair] ≤ _ at bound
  let event := fun pair : ((Fin testWidth → (Left × Fin packingWidth) → F) × Response) × (Fin queries → Position) =>
    RectangularMatrixResponse.finishMessage right (structuredResponse pair.1.1 pair.1.2) ≠ matrixEvaluation left right (extract domain capacity radius word) ∧
    Checks (m := m) domain word pair.1.1 (testResponse pair.1.1 pair.1.2) pair.2 ∧
    Checks (m := m) domain word (RectangularMatrixResponse.weights left) (structuredResponse pair.1.1 pair.1.2) pair.2
  change Pr{let pair ← RectangularOpeningKernel.experiment (F := F) (Row := Left × Fin packingWidth) (Position := Position) testWidth queries respond}[event pair] ≤ _
  refine (prEvent_mono _ event coreEvent ?_).trans bound
  intro pair accepted
  refine ⟨?_,accepted.2⟩
  change RectangularMatrixResponse.finishEncoded domain capacity right
    (fun lane => BlockEncoder.encode domain (RowLayout.padded (m := m) (structuredResponse pair.1.1 pair.1.2 lane))) ≠
      RectangularMatrixResponse.finishEncoded domain capacity right (fun lane => StructuredOpening.combine (RectangularMatrixResponse.weights left lane) source)
  rw [RectangularMatrixResponse.finish_structured_eq_evaluation domain enough capacity left right source sourceC,
    RectangularMatrixResponse.finishEncoded_padded domain enough capacity]
  exact accepted.1
end
end FormalProof4FHE.HasteBoots.RectangularMatrixOpeningKernel
