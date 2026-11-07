module
public import FormalProof4FHE.HasteBoots.ExecutableBerlekampWelch
public import FormalProof4FHE.HasteBoots.CodeCorrespondence
@[expose] public section

/-! A materialized decoder for an entire matrix of block symbols.
Scalar decoding alone is insufficient: the final check counts disagreement of
whole columns, containing all rows and lanes. Outside this joint promise the
returned coefficient table is zero. -/
namespace FormalProof4FHE.HasteBoots.ExecutableCommonSource
open scoped BigOperators
variable {F : Type} [Field F] [DecidableEq F] {n rows m b : ℕ}

abbrev Table (F : Type) (rows m b : ℕ) := Vector (Vector (Vector F b) m) rows

def input (table : Table F rows m b) (row : Fin rows) (j : Fin m) (lane : Fin b) : F :=
  ((table.get row).get j).get lane

def word (points : Fin n → F) (table : Table F rows m b) : Fin n → Fin rows → Fin b → F :=
  fun pos row lane => BlockEncoder.encode points (input table row) pos lane

-- Position-major materialization; each whole symbol contains every row and lane.
def materialize (points : Fin n → F) (table : Table F rows m b) :
    Vector (Vector (Vector F b) rows) n :=
  Vector.ofFn (fun pos => Vector.ofFn (fun row => Vector.ofFn (fun lane =>
    ∑ j : Fin m, input table row j lane * points pos ^ j.val)))

def candidates (e : ℕ) (points : Fin n → F) (raw : Fin n → Fin rows → Fin b → F) : Table F rows m b :=
  let polynomials := Vector.ofFn (fun row : Fin rows => Vector.ofFn (fun lane : Fin b =>
    (ExecutableBerlekampWelch.decoder e m points (fun pos => raw pos row lane)).getD ExecutablePolynomial.zero))
  Vector.ofFn (fun row => Vector.ofFn (fun j => Vector.ofFn (fun lane =>
    ((polynomials.get row).get lane).coeff j.val)))

def zeroTable : Table F rows m b :=
  Vector.ofFn (fun _ => Vector.ofFn (fun _ => Vector.ofFn (fun _ => 0)))

def decode (e : ℕ) (points : Fin n → F) (raw : Fin n → Fin rows → Fin b → F) : Table F rows m b :=
  let table := candidates e points raw
  let evaluated := materialize points table
  if hammingDist raw (fun pos row lane => ((evaluated.get pos).get row).get lane) ≤ e then table
  else zeroTable

omit [DecidableEq F] in
theorem materialize_get (points : Fin n → F) (table : Table F rows m b)
    (pos : Fin n) (row : Fin rows) (lane : Fin b) :
    (((materialize points table).get pos).get row).get lane = word points table pos row lane := by
  simp only [materialize,FiniteLinearSolver.get_ofFn,word,BlockEncoder.encode]

omit [DecidableEq F] in
@[simp] theorem zeroTable_input (row : Fin rows) (j : Fin m) (lane : Fin b) :
    input (zeroTable : Table F rows m b) row j lane = 0 := by
  simp only [input,zeroTable,FiniteLinearSolver.get_ofFn]

omit [DecidableEq F] in
@[simp] theorem zeroTable_word (points : Fin n → F) : word points (zeroTable : Table F rows m b) = 0 := by
  funext pos row lane
  simp [word,BlockEncoder.encode]

omit [DecidableEq F] in
theorem word_rowsIn [NeZero b] (points : Fin n ↪ F) (table : Table F rows m b) :
    CommonSource.RowsIn (BlockCode.code points m b) (word points table) := by
  intro row
  exact BlockEncoder.encode_mem_code points (input table row)

theorem candidates_complete [NeZero n] [NeZero m]
    (e : ℕ) (points : Fin n ↪ F) (raw : Fin n → Fin rows → Fin b → F)
    (source : Table F rows m b) (radius : 2 * e < n - m + 1) (dimension : m ≤ n)
    (nearby : hammingDist raw (word points source) ≤ e) :
    candidates e points raw = source := by
  have scalar (row : Fin rows) (lane : Fin b) :
      ExecutableBerlekampWelch.decoder e m points (fun pos => raw pos row lane) =
        some (BlockEncoder.polynomial (input source row) lane) := by
    apply ExecutableBerlekampWelch.complete radius dimension points.injective
    · by_cases zero : BlockEncoder.polynomial (input source row) lane = 0
      · simpa [zero] using Nat.pos_of_ne_zero (NeZero.ne m)
      · exact (Polynomial.natDegree_lt_iff_degree_lt zero).mpr (BlockEncoder.degree_polynomial_lt _ _)
    · have rowBound := CommonSource.row_distance_le raw (word points source) row
      have laneBound := hammingDist_comp_le_hammingDist (x := fun pos => raw pos row)
        (y := fun pos => word points source pos row) (fun _ (symbol : Fin b → F) => symbol lane)
      have bound := laneBound.trans (rowBound.trans nearby)
      simpa only [word,Function.comp_def,BlockEncoder.encode_eq_eval] using bound
  apply Vector.ext
  intro row hrow
  apply Vector.ext
  intro j hj
  apply Vector.ext
  intro lane hlane
  change input (candidates e points raw) ⟨row,hrow⟩ ⟨j,hj⟩ ⟨lane,hlane⟩ =
    input source ⟨row,hrow⟩ ⟨j,hj⟩ ⟨lane,hlane⟩
  simp only [input,candidates,FiniteLinearSolver.get_ofFn,scalar,Option.getD_some,BlockEncoder.coeff_polynomial]

theorem decode_complete [NeZero n] [NeZero m]
    (e : ℕ) (points : Fin n ↪ F) (raw : Fin n → Fin rows → Fin b → F)
    (source : Table F rows m b) (radius : 2 * e < n - m + 1) (dimension : m ≤ n)
    (nearby : hammingDist raw (word points source) ≤ e) : decode e points raw = source := by
  unfold decode
  rw [candidates_complete e points raw source radius dimension nearby]
  simp only [materialize_get,ite_eq_left nearby]

omit [DecidableEq F] in
theorem word_representation [NeZero m] [NeZero b] (points : Fin n ↪ F)
    (source : Fin n → Fin rows → Fin b → F)
    (coded : CommonSource.RowsIn (BlockCode.code points m b) source) :
    ∃ table : Table F rows m b, word points table = source := by
  classical
  have represented := fun row => CodeCorrespondence.baseRepresentation points
    (fun pos => source pos row) (coded row)
  choose coefficients encoded using represented
  refine ⟨Vector.ofFn (fun row => Vector.ofFn (fun j => Vector.ofFn (fun lane => coefficients row j lane))),?_⟩
  funext pos row lane
  simpa only [word,BlockEncoder.encode,input,FiniteLinearSolver.get_ofFn] using congrFun (congrFun (encoded row) pos) lane

theorem decode_fallback [NeZero b] (e : ℕ) (points : Fin n ↪ F)
    (raw : Fin n → Fin rows → Fin b → F)
    (far : ¬∃ source, CommonSource.RowsIn (BlockCode.code points m b) source ∧ hammingDist raw source ≤ e) :
    decode e points raw = (zeroTable : Table F rows m b) := by
  unfold decode
  simp only [materialize_get]
  apply ite_eq_right
  intro close
  exact far ⟨word points (candidates e points raw),word_rowsIn points _,close⟩

/-- Equality to the previous analysis decoder, including its zero fallback.
The final joint check is essential: scalar errors can occur in different columns. -/
theorem decode_eq_commonSource [NeZero n] [NeZero m] [NeZero b]
    (e : ℕ) (points : Fin n ↪ F) (raw : Fin n → Fin rows → Fin b → F)
    (radius : 2 * e < n - m + 1) (dimension : m ≤ n) :
    word points (decode e points raw : Table F rows m b) =
      CommonSource.decode (BlockCode.code points m b) e raw := by
  by_cases near : ∃ source, CommonSource.RowsIn (BlockCode.code points m b) source ∧ hammingDist raw source ≤ e
  · obtain ⟨source,coded,close⟩ := near
    obtain ⟨table,equal⟩ := word_representation points source coded
    have tableClose : hammingDist raw (word points table) ≤ e := by rwa [equal]
    rw [decode_complete e points raw table radius dimension tableClose,equal]
    symm
    apply CommonSource.decode_eq_of_nearby _ e _ raw source coded close
    simpa only [BlockCode.minDist points m b (Nat.pos_of_ne_zero (NeZero.ne m)),Fintype.card_fin] using radius
  · rw [decode_fallback e points raw near,zeroTable_word,CommonSource.decode_fallback _ e raw near]

end FormalProof4FHE.HasteBoots.ExecutableCommonSource
