module
public import FormalProof4FHE.HasteBoots.CommonSourceReindex
public import FormalProof4FHE.HasteBoots.ExecutableSourceCoefficients
public import FormalProof4FHE.HasteBoots.RectangularMatrixOpeningKernel
@[expose] public section

/-! Executable extraction with the product-row and independent code-symbol
layout used by rectangular matrix opening soundness. The flat row index is
left-major/channel-minor; source padding is removed before returning the table. -/
namespace FormalProof4FHE.HasteBoots.ExecutableRectangularMatrixExtraction
variable {F : Type} [Field F] [DecidableEq F] {n leftSize m packingWidth codeWidth size : ℕ}

def extractWithCost (e : ℕ) (points : Fin n → F) (capacity : size ≤ m*codeWidth)
    (raw : Fin n → (Fin leftSize × Fin packingWidth) → Fin codeWidth → F) :
    SolverOperationCost.Run (Vector (Vector (Vector F packingWidth) size) leftSize) :=
  DenseSourceExtraction.extractRectangular e (Vector.ofFn points) capacity
    (ExecutableCommonSource.prepareRaw (CommonSourceReindex.reindex finProdFinEquiv.symm raw))

def extract (e : ℕ) (points : Fin n → F) (capacity : size ≤ m*codeWidth)
    (raw : Fin n → (Fin leftSize × Fin packingWidth) → Fin codeWidth → F) :
    Vector (Vector (Vector F packingWidth) size) leftSize := (extractWithCost e points capacity raw).value

theorem extract_get (e : ℕ) (points : Fin n → F) (capacity : size ≤ m*codeWidth)
    (raw : Fin n → (Fin leftSize × Fin packingWidth) → Fin codeWidth → F)
    (left : Fin leftSize) (right : Fin size) (channel : Fin packingWidth) :
    (((extract e points capacity raw).get left).get right).get channel =
      ((ExecutableSourceCoefficients.extract e points capacity (CommonSourceReindex.reindex finProdFinEquiv.symm raw)).get
        (finProdFinEquiv (left,channel))).get right :=
  DenseSourceExtraction.extractRectangular_get e (Vector.ofFn points) capacity
    (ExecutableCommonSource.prepareRaw (CommonSourceReindex.reindex finProdFinEquiv.symm raw)) left right channel

theorem extractWithCost_cost (e : ℕ) (points : Fin n → F) (capacity : size ≤ m*codeWidth)
    (raw : Fin n → (Fin leftSize × Fin packingWidth) → Fin codeWidth → F) :
    (extractWithCost e points capacity raw).cost ≤ DenseCommonSource.operationBound n (leftSize*packingWidth) m codeWidth e+
      (leftSize*packingWidth)*(7*size+2)+leftSize*(size*(5*packingWidth+2)+2)+4 :=
  DenseSourceExtraction.extractRectangular_cost _ _ _ _

def table (e : ℕ) (points : Fin n → F) (capacity : size ≤ m * codeWidth)
    (raw : Fin n → (Fin leftSize × Fin packingWidth) → Fin codeWidth → F) :
    Fin leftSize → Fin size → Fin packingWidth → F :=
  let values := extract e points capacity raw
  fun left right channel => ((values.get left).get right).get channel

theorem extract_eq_analysis [NeZero n] [NeZero m] [NeZero codeWidth]
    (e : ℕ) (points : Fin n ↪ F) (capacity : size ≤ m * codeWidth)
    (raw : Fin n → (Fin leftSize × Fin packingWidth) → Fin codeWidth → F)
    (radius : 2 * e < n - m + 1) (dimension : m ≤ n)
    (left : Fin leftSize) (right : Fin size) (channel : Fin packingWidth) :
    (((extract e points capacity raw).get left).get right).get channel =
      RectangularMatrixOpeningKernel.extract points capacity e raw left right channel := by
  simp only [extract_get,
    ExecutableSourceCoefficients.extract_eq_analysis e points capacity _ radius dimension]
  have margin : 2 * e < Code.minDist (BlockCode.code points m codeWidth : Set (Fin n → Fin codeWidth → F)) := by
    simpa only [BlockCode.minDist points m codeWidth (Nat.pos_of_ne_zero (NeZero.ne m)),Fintype.card_fin] using radius
  rw [CommonSourceReindex.decode finProdFinEquiv.symm _ e margin raw]
  simp only [CommonSourceReindex.reindex,Equiv.symm_apply_apply,
    RectangularMatrixOpeningKernel.extract,RectangularMatrixResponse.extractTable]
theorem table_eq_analysis [NeZero n] [NeZero m] [NeZero codeWidth]
    (e : ℕ) (points : Fin n ↪ F) (capacity : size ≤ m * codeWidth)
    (raw : Fin n → (Fin leftSize × Fin packingWidth) → Fin codeWidth → F)
    (radius : 2 * e < n - m + 1) (dimension : m ≤ n) :
    table e points capacity raw = RectangularMatrixOpeningKernel.extract points capacity e raw := by
  funext left right channel
  exact extract_eq_analysis e points capacity raw radius dimension left right channel
end FormalProof4FHE.HasteBoots.ExecutableRectangularMatrixExtraction
