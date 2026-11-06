module
public import FormalProof4FHE.HasteBoots.RectangularBatchOpeningKernel
@[expose] public section

/-! Deterministic witnesses for the shared-column loss. A false original
finished claim in the near branch supplies a disagreeing structured response;
outside random proximity, a coded test response supplies a far witness.
These lemmas add no probabilistic independence or attacker-work assumption. -/
namespace FormalProof4FHE.HasteBoots.RectangularBatchDisagreement
open OracleComp
noncomputable section
variable {F Left Position Group Query : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype Left] [Fintype Position] [DecidableEq Position] {m packingWidth codeWidth size : ℕ}

omit [Fintype F] [DecidableEq Position] in
/-- Any false original message finishing forces one shared structured test
at distance at least the code distance minus the source radius. -/
theorem near_witness [NeZero m] [NeZero codeWidth] (domain : Position ↪ F)
    (enough : m ≤ Fintype.card Position) (capacity : size ≤ m*codeWidth) (radius : ℕ)
    (word : Position → (Left × Fin packingWidth) → Fin codeWidth → F)
    (groupOf : Query → Group) (left : Group → Left → Matrix (Fin packingWidth) (Fin packingWidth) F)
    (right : Query → Fin size → Matrix (Fin packingWidth) (Fin packingWidth) F)
    (messages : Group → Fin packingWidth → Fin size → F)
    (near : ∃ source, CommonSource.RowsIn (BlockCode.code domain m codeWidth) source ∧ hammingDist word source ≤ radius)
    (falseClaim : ∃ query, RectangularBatchOpeningKernel.finishMessage groupOf right messages query ≠
      matrixEvaluation (left (groupOf query)) (right query) (RectangularMatrixOpeningKernel.extract domain capacity radius word)) :
    ∃ test : Group × Fin packingWidth,
      Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)) - radius ≤
        hammingDist (StructuredOpening.combine (RectangularBatchOpeningKernel.weights left test) word)
          (BlockEncoder.encode domain (RowLayout.padded (m := m) (b := codeWidth) (messages test.1 test.2))) := by
  classical
  let decoded := CommonSource.decode (BlockCode.code domain m codeWidth) radius word
  have source := CommonSource.decode_nearby (BlockCode.code domain m codeWidth) radius word near
  let claimed := fun test : Group × Fin packingWidth =>
    BlockEncoder.encode domain (RowLayout.padded (m := m) (b := codeWidth) (messages test.1 test.2))
  have different : (fun test => StructuredOpening.combine (RectangularBatchOpeningKernel.weights left test) decoded) ≠ claimed := by
    intro same
    have equal := congrArg (RectangularBatchOpeningKernel.finishEncoded domain capacity groupOf right) same
    rw [RectangularBatchOpeningKernel.finish_structured domain enough capacity groupOf left right decoded source.1,
      RectangularBatchOpeningKernel.finishEncoded_padded domain enough capacity groupOf right messages] at equal
    obtain ⟨query,falseQuery⟩ := falseClaim
    exact falseQuery (congrFun equal query).symm
  have witness : ∃ test, StructuredOpening.combine (RectangularBatchOpeningKernel.weights left test) decoded ≠ claimed test := by
    by_contra absent
    apply different
    funext test
    exact Classical.not_not.mp (fun unequal => absent ⟨test,unequal⟩)
  obtain ⟨test,unequal⟩ := witness
  exact ⟨test,CommonSource.falseResponse_distance (BlockCode.code domain m codeWidth) radius _ _ _
    (StructuredOpening.combine_mem _ _ decoded source.1) (BlockEncoder.encode_mem_code domain _) unequal
    ((StructuredOpening.combine_distance_le _ word decoded).trans source.2)⟩

omit [Fintype F] [DecidableEq Position] in
/-- A random test outside proximity disagrees with every coded claimed
response on at least radius+1 columns, even after adaptive response selection. -/
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
end FormalProof4FHE.HasteBoots.RectangularBatchDisagreement
