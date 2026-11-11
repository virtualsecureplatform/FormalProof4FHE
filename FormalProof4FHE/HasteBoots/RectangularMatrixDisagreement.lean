module
public import FormalProof4FHE.HasteBoots.RectangularMatrixOpeningKernel
@[expose] public section

/-! Deterministic witnesses for one matrix opening. A false finished claim
near a common source forces a structured response disagreement. A random
row outside code proximity disagrees with any encoded response. -/
namespace FormalProof4FHE.HasteBoots.RectangularMatrixDisagreement
noncomputable section
variable {F Left Position : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype Left] [Fintype Position] [DecidableEq Position] {m packingWidth codeWidth size : ℕ}

omit [Fintype F] [DecidableEq Position] in
theorem near_witness [NeZero m] [NeZero codeWidth] (domain : Position ↪ F)
    (enough : m ≤ Fintype.card Position) (capacity : size ≤ m*codeWidth) (radius : ℕ)
    (word : Position → (Left × Fin packingWidth) → Fin codeWidth → F)
    (left : Left → Matrix (Fin packingWidth) (Fin packingWidth) F)
    (right : Fin size → Matrix (Fin packingWidth) (Fin packingWidth) F)
    (messages : Fin packingWidth → Fin size → F)
    (near : ∃ source, CommonSource.RowsIn (BlockCode.code domain m codeWidth) source ∧ hammingDist word source ≤ radius)
    (falseClaim : RectangularMatrixResponse.finishMessage right messages ≠
      matrixEvaluation left right (RectangularMatrixOpeningKernel.extract domain capacity radius word)) :
    ∃ lane : Fin packingWidth,
      Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)) - radius ≤
        hammingDist (StructuredOpening.combine (RectangularMatrixResponse.weights left lane) word)
          (BlockEncoder.encode domain (RowLayout.padded (m := m) (b := codeWidth) (messages lane))) := by
  classical
  let decoded := CommonSource.decode (BlockCode.code domain m codeWidth) radius word
  have source := CommonSource.decode_nearby (BlockCode.code domain m codeWidth) radius word near
  let claimed := fun lane : Fin packingWidth =>
    BlockEncoder.encode domain (RowLayout.padded (m := m) (b := codeWidth) (messages lane))
  have different : (fun lane => StructuredOpening.combine (RectangularMatrixResponse.weights left lane) decoded) ≠ claimed := by
    intro same
    have equal := congrArg (RectangularMatrixResponse.finishEncoded domain capacity right) same
    rw [RectangularMatrixResponse.finish_structured_eq_evaluation domain enough capacity left right decoded source.1,
      RectangularMatrixResponse.finishEncoded_padded domain enough capacity right messages] at equal
    exact falseClaim equal.symm
  have witness : ∃ lane, StructuredOpening.combine (RectangularMatrixResponse.weights left lane) decoded ≠ claimed lane := by
    by_contra absent
    apply different
    funext lane
    exact Classical.not_not.mp (fun unequal => absent ⟨lane,unequal⟩)
  obtain ⟨lane,unequal⟩ := witness
  exact ⟨lane,CommonSource.falseResponse_distance (BlockCode.code domain m codeWidth) radius _ _ _
    (StructuredOpening.combine_mem _ _ decoded source.1) (BlockEncoder.encode_mem_code domain _) unequal
    ((StructuredOpening.combine_distance_le _ word decoded).trans source.2)⟩

omit [Fintype F] [DecidableEq Position] in
theorem far_witness {Row : Type} [Fintype Row] (domain : Position ↪ F) (radius testWidth : ℕ)
    (word : Position → Row → Fin codeWidth → F) (matrix : Fin testWidth → Row → F)
    (claimed : Fin testWidth → Position → Fin codeWidth → F)
    (coded : ∀ lane, claimed lane ∈ BlockCode.code domain m codeWidth)
    (outside : ¬∀ lane, Code.distFromCode (StructuredOpening.combine (matrix lane) word)
      (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)) ≤ radius) :
    ∃ lane, radius+1 ≤ hammingDist (StructuredOpening.combine (matrix lane) word) (claimed lane) := by
  classical
  simp only [not_forall] at outside
  obtain ⟨lane,notClose⟩ := outside
  exact ⟨lane,ColumnOpening.farResponse_distance (BlockCode.code domain m codeWidth) radius _ _ (coded lane) (lt_of_not_ge notClose)⟩
end
end FormalProof4FHE.HasteBoots.RectangularMatrixDisagreement
