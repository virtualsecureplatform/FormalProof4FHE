module
public import FormalProof4FHE.HasteBoots.ExecutableCommonSource
public import FormalProof4FHE.HasteBoots.ResponseCoefficients
@[expose] public section

/-! Query-independent executable coefficient recovery for the common source.
This replaces the two choice-based analysis selections at the finite block-code
interface; native byte parsing, cost refinement, and the application registry
remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.ExecutableSourceCoefficients
variable {F : Type} [Field F] [DecidableEq F] {n rows m b size : ℕ}

/-- Materialize the original message coordinates, dropping source padding. -/
def extract (e : ℕ) (points : Fin n → F) (capacity : size ≤ m * b)
    (raw : Fin n → Fin rows → Fin b → F) : Vector (Vector F size) rows :=
  let table : ExecutableCommonSource.Table F rows m b := ExecutableCommonSource.decode e points raw
  Vector.ofFn (fun row => Vector.ofFn (fun index =>
    RowLayout.recover capacity (ExecutableCommonSource.input table row) index))

theorem coefficients_eq_analysis [NeZero n] [NeZero m] [NeZero b]
    (e : ℕ) (points : Fin n ↪ F) (raw : Fin n → Fin rows → Fin b → F)
    (radius : 2 * e < n - m + 1) (dimension : m ≤ n) (row : Fin rows) :
    ExecutableCommonSource.input (ExecutableCommonSource.decode e points raw : ExecutableCommonSource.Table F rows m b) row =
      ResponseCoefficients.decode points (fun pos => CommonSource.decode (BlockCode.code points m b) e raw pos row) := by
  rw [← ExecutableCommonSource.decode_eq_commonSource e points raw radius dimension]
  exact (ResponseCoefficients.decode_encode points (by simpa using dimension) _).symm

theorem extract_eq_analysis [NeZero n] [NeZero m] [NeZero b]
    (e : ℕ) (points : Fin n ↪ F) (capacity : size ≤ m * b)
    (raw : Fin n → Fin rows → Fin b → F)
    (radius : 2 * e < n - m + 1) (dimension : m ≤ n) (row : Fin rows) (index : Fin size) :
    ((extract e points capacity raw).get row).get index =
      RowLayout.recover capacity (ResponseCoefficients.decode points
        (fun pos => CommonSource.decode (BlockCode.code points m b) e raw pos row)) index := by
  simp only [extract,FiniteLinearSolver.get_ofFn,coefficients_eq_analysis e points raw radius dimension row]
end FormalProof4FHE.HasteBoots.ExecutableSourceCoefficients
