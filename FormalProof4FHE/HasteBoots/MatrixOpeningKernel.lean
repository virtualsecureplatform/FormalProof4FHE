module

public import FormalProof4FHE.HasteBoots.MatrixOpeningSecurity
public import FormalProof4FHE.HasteBoots.CommonSourceOpeningKernel

@[expose] public section

/-!
# Native matrix opening soundness with randomized adaptive responses

A response computation can keep private coins, a complete oracle cache and any
other state in its result. The uniform test matrix is earlier and the shared
column draw is later. Native padded message encodings supply code membership
automatically. One query-independent extracted table is used for all queries.
This is the interactive fixed-word component; production transcript freshness,
authenticated-execution probability composition and physical work remain open.
-/

open ProbabilityTheory Matrix OracleComp

namespace FormalProof4FHE.HasteBoots.MatrixOpeningKernel

noncomputable section

variable {F K Position Left Response : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [Fintype K] [DecidableEq F] [DecidableEq K]
  [Fintype Position] [DecidableEq Position] [Fintype Left] {m b size : ℕ}

open MatrixOpeningSecurity

theorem soundness_bound [NeZero m] [NeZero b]
    (basis : Module.Basis (Fin b) F K) (domain : Position ↪ F)
    (enough : m ≤ Fintype.card Position) (capacity : size ≤ m * b) (radius queries : ℕ)
    (word : Position → (Left × Fin b) → Fin b → F)
    (left : Left → Matrix (Fin b) (Fin b) F) (right : Fin size → Matrix (Fin b) (Fin b) F)
    (respond : (Fin b → (Left × Fin b) → F) → ProbComp Response)
    (testResponse structuredResponse : (Fin b → (Left × Fin b) → F) → Response → Fin b → Fin size → F)
    [SampleableType (Fin b → (Left × Fin b) → F)]
    [SampleableType ((Left × Fin b) → K)] [SampleableType (Fin queries → Position)]
    [SampleableType (Matrix.rowSpan (BaseMatrixProximity.stack basis word))]
    [SampleableType (RowSpanSampling.toSpan (BaseMatrixProximity.stack basis word)).toAddMonoidHom.ker]
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Position → K)) : ℚ≥0) / 3) :
    Pr{let pair ← CommonSourceOpeningKernel.experiment (F := F) (Row := Left × Fin b)
        (Position := Position) b queries respond}[
      MatrixResponse.finishMessage right (structuredResponse pair.1.1 pair.1.2) ≠
        matrixEvaluation left right (extract domain capacity radius word) ∧
      Checks (m := m) domain word pair.1.1 (testResponse pair.1.1 pair.1.2) pair.2 ∧
      Checks (m := m) domain word (MatrixResponse.weights left) (structuredResponse pair.1.1 pair.1.2) pair.2] ≤
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Position → K)) : ENNReal) / (Fintype.card F ^ b) +
      max (ColumnOpening.missBound Position queries
        (Code.minDist (BlockCode.code domain m b : Set (Position → Fin b → F)) - radius))
        (ColumnOpening.missBound Position queries (radius + 1)) := by
  let source := CommonSource.decode (BlockCode.code domain m b) radius word
  have sourceC := CommonSource.decode_rowsIn (BlockCode.code domain m b) radius
    (BlockCode.code domain m b).zero_mem word
  let randomClaim := fun matrix response => ResponseAssembly.assemble basis
    (encodeMessages (m := m) domain (testResponse matrix response))
  let structuredClaim := fun matrix response => encodeMessages (m := m) domain (structuredResponse matrix response)
  let finish := MatrixResponse.finishEncoded domain capacity right
  have bound := CommonSourceOpeningKernel.soundness_bound basis domain radius queries word
    (MatrixResponse.weights left) respond randomClaim structuredClaim finish small
    (fun matrix response => ResponseAssembly.assemble_encoded_mem basis domain
      (fun lane => RowLayout.padded (m := m) (testResponse matrix response lane)))
    (fun matrix response lane => BlockEncoder.encode_mem_code domain
      (RowLayout.padded (m := m) (structuredResponse matrix response lane)))
  dsimp only at bound
  let coreEvent := fun (pair : ((Fin b → (Left × Fin b) → F) × Response) × (Fin queries → Position)) =>
    finish (structuredClaim pair.1.1 pair.1.2) ≠
      finish (fun lane => StructuredOpening.combine (MatrixResponse.weights left lane) source) ∧
    ColumnOpening.Agrees (ProximityOpening.randomWord basis word pair.1.1) (randomClaim pair.1.1 pair.1.2) pair.2 ∧
    ∀ lane, ColumnOpening.Agrees (StructuredOpening.combine (MatrixResponse.weights left lane) word)
      (structuredClaim pair.1.1 pair.1.2 lane) pair.2
  change Pr{let pair ← CommonSourceOpeningKernel.experiment (F := F) (Row := Left × Fin b) (Position := Position) b queries respond}[
    coreEvent pair] ≤ _ at bound
  let event := fun (pair : ((Fin b → (Left × Fin b) → F) × Response) × (Fin queries → Position)) =>
    MatrixResponse.finishMessage right (structuredResponse pair.1.1 pair.1.2) ≠
      matrixEvaluation left right (extract domain capacity radius word) ∧
    Checks (m := m) domain word pair.1.1 (testResponse pair.1.1 pair.1.2) pair.2 ∧
    Checks (m := m) domain word (MatrixResponse.weights left) (structuredResponse pair.1.1 pair.1.2) pair.2
  change Pr{let pair ← CommonSourceOpeningKernel.experiment (F := F) (Row := Left × Fin b) (Position := Position) b queries respond}[
    event pair] ≤ _
  refine (prEvent_mono (CommonSourceOpeningKernel.experiment b queries respond) event coreEvent ?_).trans bound
  intro pair accepted
  refine ⟨?_, ResponseAssembly.agrees_of_lanes basis word pair.1.1 _ pair.2 accepted.2.1,
    accepted.2.2⟩
  change MatrixResponse.finishEncoded domain capacity right
      (encodeMessages (m := m) domain (structuredResponse pair.1.1 pair.1.2)) ≠
    MatrixResponse.finishEncoded domain capacity right
      (fun lane => StructuredOpening.combine (MatrixResponse.weights left lane) source)
  rw [MatrixResponse.finish_structured_eq_evaluation domain enough capacity left right source sourceC]
  change MatrixResponse.finishEncoded domain capacity right
      (fun lane => BlockEncoder.encode domain (RowLayout.padded (m := m) (structuredResponse pair.1.1 pair.1.2 lane))) ≠ _
  rw [MatrixResponse.finishEncoded_padded domain enough capacity]
  exact accepted.1


end

end FormalProof4FHE.HasteBoots.MatrixOpeningKernel
