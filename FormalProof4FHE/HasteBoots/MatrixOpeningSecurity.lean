module

public import FormalProof4FHE.HasteBoots.CommonSourceOpening
public import FormalProof4FHE.HasteBoots.ResponseAssembly
public import FormalProof4FHE.HasteBoots.MatrixResponse

@[expose] public section

/-!
# Matrix opening soundness on the native semantic response layout

The prover supplies base-field, lane-major message arrays. The verifier encodes
them with zero padding, checks all lanes against the same available columns,
and finishes the structured messages by the ordered right matrix fold.
No scalar-field response or code-membership certificate is a protocol input.
This is still an interactive, fixed-available-word theorem. Rust/NTT refinement,
Merkle availability and the production transcript law remain separate.
-/

open ProbabilityTheory Matrix

namespace FormalProof4FHE.HasteBoots.MatrixOpeningSecurity

noncomputable section

variable {F K Position Left : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [Fintype K] [DecidableEq F] [DecidableEq K]
  [Fintype Position] [DecidableEq Position] [Fintype Left] {m b size : ℕ}

/-- The semantic native response encoder, one padded message per output lane. -/
def encodeMessages (domain : Position → F) (messages : Fin b → Fin size → F) :
    Fin b → Position → Fin b → F :=
  fun lane => BlockEncoder.encode domain (RowLayout.padded (m := m) (messages lane))

/-- One extracted coefficient table per available word, independent of the opening query. -/
def extract (domain : Position ↪ F) (capacity : size ≤ m * b) (radius : ℕ)
    (word : Position → (Left × Fin b) → Fin b → F) : Left → Fin size → Fin b → F :=
  MatrixResponse.extractTable domain capacity
    (CommonSource.decode (BlockCode.code domain m b) radius word)

/-- Native coordinate checks for one complete response family on the shared draws. -/
def Checks (domain : Position → F) (word : Position → (Left × Fin b) → Fin b → F)
    (weights : Fin b → (Left × Fin b) → F) (messages : Fin b → Fin size → F)
    {queries : ℕ} (draw : Fin queries → Position) : Prop :=
  ∀ lane, ColumnOpening.Agrees (StructuredOpening.combine (weights lane) word)
    (encodeMessages (m := m) domain messages lane) draw

/-- Fixed-available-word opening soundness for arbitrary native response arrays
chosen after the full random test matrix. The extracted table is common to all queries. -/
theorem fixedWord_bound [NeZero m] [NeZero b]
    (basis : Module.Basis (Fin b) F K) (domain : Position ↪ F)
    (enough : m ≤ Fintype.card Position) (capacity : size ≤ m * b) (radius queries : ℕ)
    (word : Position → (Left × Fin b) → Fin b → F)
    (left : Left → Matrix (Fin b) (Fin b) F) (right : Fin size → Matrix (Fin b) (Fin b) F)
    (testResponse structuredResponse : (Fin b → (Left × Fin b) → F) → Fin b → Fin size → F)
    [SampleableType (Fin b → (Left × Fin b) → F)]
    [SampleableType ((Left × Fin b) → K)] [SampleableType (Fin queries → Position)]
    [SampleableType (Matrix.rowSpan (BaseMatrixProximity.stack basis word))]
    [SampleableType (RowSpanSampling.toSpan (BaseMatrixProximity.stack basis word)).toAddMonoidHom.ker]
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Position → K)) : ℚ≥0) / 3) :
    Pr{let pair ← CommonSourceOpening.experiment (F := F) (Row := Left × Fin b)
        (Position := Position) b queries}[
      MatrixResponse.finishMessage right (structuredResponse pair.1) ≠
        matrixEvaluation left right (extract domain capacity radius word) ∧
      Checks (m := m) domain word pair.1 (testResponse pair.1) pair.2 ∧
      Checks (m := m) domain word (MatrixResponse.weights left) (structuredResponse pair.1) pair.2] ≤
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Position → K)) : ENNReal) / (Fintype.card F ^ b) +
      max (ColumnOpening.missBound Position queries
        (Code.minDist (BlockCode.code domain m b : Set (Position → Fin b → F)) - radius))
        (ColumnOpening.missBound Position queries (radius + 1)) := by
  let source := CommonSource.decode (BlockCode.code domain m b) radius word
  have sourceC := CommonSource.decode_rowsIn (BlockCode.code domain m b) radius
    (BlockCode.code domain m b).zero_mem word
  let randomClaim := fun matrix => ResponseAssembly.assemble basis
    (encodeMessages (m := m) domain (testResponse matrix))
  let structuredClaim := fun matrix => encodeMessages (m := m) domain (structuredResponse matrix)
  let finish := MatrixResponse.finishEncoded domain capacity right
  have bound := CommonSourceOpening.soundness_bound basis domain radius queries word
    (MatrixResponse.weights left) randomClaim structuredClaim finish small
    (fun matrix => ResponseAssembly.assemble_encoded_mem basis domain
      (fun lane => RowLayout.padded (m := m) (testResponse matrix lane)))
    (fun matrix lane => BlockEncoder.encode_mem_code domain
      (RowLayout.padded (m := m) (structuredResponse matrix lane)))
  dsimp only at bound
  let coreEvent := fun (pair : (Fin b → (Left × Fin b) → F) × (Fin queries → Position)) =>
    finish (structuredClaim pair.1) ≠
      finish (fun lane => StructuredOpening.combine (MatrixResponse.weights left lane) source) ∧
    ColumnOpening.Agrees (ProximityOpening.randomWord basis word pair.1) (randomClaim pair.1) pair.2 ∧
    ∀ lane, ColumnOpening.Agrees (StructuredOpening.combine (MatrixResponse.weights left lane) word)
      (structuredClaim pair.1 lane) pair.2
  change Pr{let pair ← CommonSourceOpening.experiment (F := F) (Row := Left × Fin b) (Position := Position) b queries}[
    coreEvent pair] ≤ _ at bound
  let event := fun (pair : (Fin b → (Left × Fin b) → F) × (Fin queries → Position)) =>
    MatrixResponse.finishMessage right (structuredResponse pair.1) ≠
      matrixEvaluation left right (extract domain capacity radius word) ∧
    Checks (m := m) domain word pair.1 (testResponse pair.1) pair.2 ∧
    Checks (m := m) domain word (MatrixResponse.weights left) (structuredResponse pair.1) pair.2
  change Pr{let pair ← CommonSourceOpening.experiment (F := F) (Row := Left × Fin b) (Position := Position) b queries}[
    event pair] ≤ _
  refine (prEvent_mono (CommonSourceOpening.experiment b queries) event coreEvent ?_).trans bound
  intro pair accepted
  refine ⟨?_, ResponseAssembly.agrees_of_lanes basis word pair.1 _ pair.2 accepted.2.1,
    accepted.2.2⟩
  change MatrixResponse.finishEncoded domain capacity right
      (encodeMessages (m := m) domain (structuredResponse pair.1)) ≠
    MatrixResponse.finishEncoded domain capacity right
      (fun lane => StructuredOpening.combine (MatrixResponse.weights left lane) source)
  rw [MatrixResponse.finish_structured_eq_evaluation domain enough capacity left right source sourceC]
  change MatrixResponse.finishEncoded domain capacity right
      (fun lane => BlockEncoder.encode domain (RowLayout.padded (m := m) (structuredResponse pair.1 lane))) ≠ _
  rw [MatrixResponse.finishEncoded_padded domain enough capacity]
  exact accepted.1

end

end FormalProof4FHE.HasteBoots.MatrixOpeningSecurity
