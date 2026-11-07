module
public import FormalProof4FHE.HasteBoots.ExecutableBerlekampWelch
public import FormalProof4FHE.HasteBoots.BlockEvaluationCost
public import FormalProof4FHE.HasteBoots.ColumnDistanceCost
public import FormalProof4FHE.HasteBoots.DenseCommonSource
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
-- The charge begins after the input-point vector has been prepared.
def materializeWithCost (points : Fin n → F) (table : Table F rows m b) :
    SolverOperationCost.Run (Vector (Vector (Vector F b) rows) n) :=
  BlockEvaluationCost.evaluate (Vector.ofFn points) table

def materialize (points : Fin n → F) (table : Table F rows m b) :
    Vector (Vector (Vector F b) rows) n :=
  (materializeWithCost points table).value

omit [DecidableEq F] in
theorem materializeWithCost_cost (points : Fin n → F) (table : Table F rows m b) :
    (materializeWithCost points table).cost = n*(5*m+rows*(b*(6*m+2)+2)+10)+1 :=
  BlockEvaluationCost.evaluate_cost _ _

def prepareRaw (raw : Fin n → Fin rows → Fin b → F) : DenseCommonSource.Columns F n rows b :=
  Vector.ofFn (fun pos => Vector.ofFn (fun row => Vector.ofFn (raw pos row)))

omit [Field F] [DecidableEq F] in
theorem prepareRaw_input (raw : Fin n → Fin rows → Fin b → F) (pos : Fin n) (row : Fin rows) (lane : Fin b) :
    DenseCommonSource.input (prepareRaw raw) pos row lane = raw pos row lane := by
  simp only [prepareRaw,DenseCommonSource.input,FiniteLinearSolver.get_ofFn]

omit [Field F] [DecidableEq F] in
theorem prepareRaw_word (raw : Fin n → Fin rows → Fin b → F) :
    ColumnDistanceCost.word (prepareRaw raw) = raw := by
  funext pos row lane
  exact prepareRaw_input raw pos row lane

omit [Field F] [DecidableEq F] in
/-- Reading a stored input and materializing it again preserves every entry.
Used only as a specification bridge: prepared extraction avoids this copy. -/
theorem prepareRaw_input_eq (raw : DenseCommonSource.Columns F n rows b) :
    prepareRaw (DenseCommonSource.input raw) = raw := by
  apply Vector.ext
  intro pos hp
  simp only [prepareRaw,Vector.getElem_ofFn]
  apply Vector.ext
  intro row hr
  simp only [Vector.getElem_ofFn]
  apply Vector.ext
  intro lane hl
  simp only [Vector.getElem_ofFn,DenseCommonSource.input]
  rfl

omit [DecidableEq F] in
theorem prepared_word (points : Fin n → F) (table : Table F rows m b) :
    DenseCommonSource.word (Vector.ofFn points) table = word points table := by
  funext pos row lane
  simp only [DenseCommonSource.word,FiniteLinearSolver.get_ofFn,word]
  rfl

/-- Initial point/raw function evaluation and materialization are separate costs. -/
def candidatesWithCost (e : ℕ) (points : Fin n → F) (raw : Fin n → Fin rows → Fin b → F) :
    SolverOperationCost.Run (Table F rows m b) :=
  DenseCommonSource.candidates e m (Vector.ofFn points) (prepareRaw raw)

def candidates (e : ℕ) (points : Fin n → F) (raw : Fin n → Fin rows → Fin b → F) : Table F rows m b :=
  (candidatesWithCost e points raw).value

theorem candidates_get (e : ℕ) (points : Fin n → F) (raw : Fin n → Fin rows → Fin b → F)
    (row : Fin rows) (j : Fin m) (lane : Fin b) :
    (((candidates e points raw).get row).get j).get lane =
      ((ExecutableBerlekampWelch.decoder e m points (fun pos => raw pos row lane)).getD ExecutablePolynomial.zero).coeff j.val := by
  simpa only [candidates,candidatesWithCost,FiniteLinearSolver.get_ofFn,prepareRaw_input] using
    DenseCommonSource.candidates_get e m (Vector.ofFn points) (prepareRaw raw) row j lane

theorem candidatesWithCost_cost (e : ℕ) (points : Fin n → F) (raw : Fin n → Fin rows → Fin b → F) :
    (candidatesWithCost e points raw : SolverOperationCost.Run (Table F rows m b)).cost ≤
      DenseCommonSource.candidatesBound n rows m b e :=
  DenseCommonSource.candidates_cost _ _ _ _

def zeroTable : Table F rows m b :=
  Vector.ofFn (fun _ => Vector.ofFn (fun _ => Vector.ofFn (fun _ => 0)))

/-- Scan charge starts after materialization of the raw input functions. -/
def distanceWithCost (raw : Fin n → Fin rows → Fin b → F)
    (evaluated : ColumnDistanceCost.Columns F n rows b) : SolverOperationCost.Run ℕ :=
  ColumnDistanceCost.distance
    (Vector.ofFn (fun pos => Vector.ofFn (fun row => Vector.ofFn (raw pos row)))) evaluated

omit [Field F] in
theorem distanceWithCost_value (raw : Fin n → Fin rows → Fin b → F)
    (evaluated : ColumnDistanceCost.Columns F n rows b) :
    (distanceWithCost raw evaluated).value =
      hammingDist raw (fun pos row lane => ((evaluated.get pos).get row).get lane) := by
  have rawEq : ColumnDistanceCost.word
      (Vector.ofFn (fun pos => Vector.ofFn (fun row => Vector.ofFn (raw pos row)))) = raw := by
    funext pos row lane
    simp only [ColumnDistanceCost.word,FiniteLinearSolver.get_ofFn]
  rw [distanceWithCost,ColumnDistanceCost.distance_value,rawEq]
  rfl

omit [Field F] in
theorem distanceWithCost_cost (raw : Fin n → Fin rows → Fin b → F)
    (evaluated : ColumnDistanceCost.Columns F n rows b) :
    (distanceWithCost raw evaluated).cost = n*(rows*(6*b+7)+8)+2 :=
  ColumnDistanceCost.distance_cost _ _

omit [DecidableEq F] in
theorem materialize_get (points : Fin n → F) (table : Table F rows m b)
    (pos : Fin n) (row : Fin rows) (lane : Fin b) :
    (((materialize points table).get pos).get row).get lane = word points table pos row lane := by
  simp only [materialize,materializeWithCost,BlockEvaluationCost.evaluate_get,FiniteLinearSolver.get_ofFn,word]
  rfl

/-- Cost of the final candidate evaluation, joint distance scan and comparison.
Preparation of input point/raw vectors is excluded. This is not candidate decoding. -/
def checkWithCost (e : ℕ) (points : Fin n → F) (raw : Fin n → Fin rows → Fin b → F)
    (table : Table F rows m b) : SolverOperationCost.Run Bool :=
  let evaluated := materializeWithCost points table
  let scanned := distanceWithCost raw evaluated.value
  ⟨decide (scanned.value ≤ e),evaluated.cost+scanned.cost+1⟩

theorem checkWithCost_value (e : ℕ) (points : Fin n → F) (raw : Fin n → Fin rows → Fin b → F)
    (table : Table F rows m b) :
    (checkWithCost e points raw table).value = decide (hammingDist raw (word points table) ≤ e) := by
  change decide ((distanceWithCost raw (materialize points table)).value ≤ e) = _
  simp only [distanceWithCost_value,materialize_get]

theorem checkWithCost_cost (e : ℕ) (points : Fin n → F) (raw : Fin n → Fin rows → Fin b → F)
    (table : Table F rows m b) :
    (checkWithCost e points raw table).cost = n*(5*m+rows*(b*(6*m+8)+9)+18)+4 := by
  simp only [checkWithCost,materializeWithCost_cost,distanceWithCost_cost]
  ring

/-- Full prepared-vector matrix phase. Initial function materialization and
physical/backend refinement are separate obligations. -/
def decodeWithCost (e : ℕ) (points : Fin n → F) (raw : Fin n → Fin rows → Fin b → F) :
    SolverOperationCost.Run (Table F rows m b) :=
  DenseCommonSource.decode e m (Vector.ofFn points) (prepareRaw raw)

def decode (e : ℕ) (points : Fin n → F) (raw : Fin n → Fin rows → Fin b → F) : Table F rows m b :=
  (decodeWithCost e points raw).value

theorem decodeWithCost_cost (e : ℕ) (points : Fin n → F) (raw : Fin n → Fin rows → Fin b → F) :
    (decodeWithCost e points raw : SolverOperationCost.Run (Table F rows m b)).cost ≤
      DenseCommonSource.operationBound n rows m b e := DenseCommonSource.decode_cost _ _ _ _

omit [DecidableEq F] in
private theorem dense_zeroTable_eq :
    (DenseCommonSource.zeroTable : SolverOperationCost.Run (Table F rows m b)).value = zeroTable := by
  apply Vector.ext
  intro row rowBound
  apply Vector.ext
  intro j jBound
  apply Vector.ext
  intro lane laneBound
  change (((DenseCommonSource.zeroTable : SolverOperationCost.Run (Table F rows m b)).value.get ⟨row,rowBound⟩).get ⟨j,jBound⟩).get ⟨lane,laneBound⟩ =
    (((zeroTable : Table F rows m b).get ⟨row,rowBound⟩).get ⟨j,jBound⟩).get ⟨lane,laneBound⟩
  simp only [DenseCommonSource.zeroTable_get,zeroTable,FiniteLinearSolver.get_ofFn]

theorem decode_eq_checked (e : ℕ) (points : Fin n → F) (raw : Fin n → Fin rows → Fin b → F) :
    (decode e points raw : Table F rows m b) =
      if (checkWithCost e points raw (candidates e points raw : Table F rows m b)).value then candidates e points raw else zeroTable := by
  unfold decode decodeWithCost
  rw [DenseCommonSource.decode_value]
  simp only [DenseCommonSource.check_value,prepareRaw_word,prepared_word,checkWithCost_value,
    candidates,candidatesWithCost,dense_zeroTable_eq]

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
  simp only [input,candidates_get,scalar,Option.getD_some]
  exact BlockEncoder.coeff_polynomial (input source ⟨row,hrow⟩) ⟨lane,hlane⟩ ⟨j,hj⟩

theorem decode_complete [NeZero n] [NeZero m]
    (e : ℕ) (points : Fin n ↪ F) (raw : Fin n → Fin rows → Fin b → F)
    (source : Table F rows m b) (radius : 2 * e < n - m + 1) (dimension : m ≤ n)
    (nearby : hammingDist raw (word points source) ≤ e) : decode e points raw = source := by
  rw [decode_eq_checked]
  rw [candidates_complete e points raw source radius dimension nearby]
  simp only [checkWithCost_value,decide_eq_true_eq,ite_eq_left nearby]

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
  rw [decode_eq_checked]
  simp only [checkWithCost_value,decide_eq_true_eq]
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
