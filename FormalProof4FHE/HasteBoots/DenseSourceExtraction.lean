module
public import FormalProof4FHE.HasteBoots.DenseCommonSource
public import FormalProof4FHE.HasteBoots.RowLayout
@[expose] public section

/-! Measured removal of source padding and rectangular output layout. Inputs are
prepared arrays; address arithmetic and every nested load/store are charged in
the abstract access model. Field/backend and physical refinement are separate. -/
namespace FormalProof4FHE.HasteBoots.DenseSourceExtraction
open SolverOperationCost
open scoped BigOperators
variable {F : Type} [Field F] [DecidableEq F] {n rows m b size left packing : ℕ}

def project (capacity : size ≤ m*b) (table : DenseCommonSource.Table F rows m b) : Run (Vector (Vector F size) rows) :=
  tabulate (fun row : Fin rows => tabulate (fun index : Fin size =>
    let pair := finProdFinEquiv.symm (⟨index.val,index.isLt.trans_le capacity⟩ : Fin (m*b))
    ⟨((table.get row).get pair.1).get pair.2,6⟩))

omit [Field F] [DecidableEq F] in
theorem project_get (capacity : size ≤ m*b) (table : DenseCommonSource.Table F rows m b)
    (row : Fin rows) (index : Fin size) :
    ((project capacity table).value.get row).get index =
      RowLayout.recover capacity (fun j lane => ((table.get row).get j).get lane) index := by
  simp only [project,tabulate_value,FiniteLinearSolver.get_ofFn,RowLayout.recover]

omit [Field F] [DecidableEq F] in
theorem project_cost (capacity : size ≤ m*b) (table : DenseCommonSource.Table F rows m b) :
    (project capacity table).cost = rows*(7*size+2)+1 := by
  simp only [project,tabulate_cost,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring

def extract (e : ℕ) (points : Vector F n) (capacity : size ≤ m*b)
    (raw : DenseCommonSource.Columns F n rows b) : Run (Vector (Vector F size) rows) :=
  let decoded := DenseCommonSource.decode e m points raw
  let output := project capacity decoded.value
  ⟨output.value,decoded.cost+output.cost+1⟩

theorem extract_get (e : ℕ) (points : Vector F n) (capacity : size ≤ m*b)
    (raw : DenseCommonSource.Columns F n rows b) (row : Fin rows) (index : Fin size) :
    ((extract e points capacity raw).value.get row).get index =
      RowLayout.recover capacity (fun j lane => (((DenseCommonSource.decode e m points raw).value.get row).get j).get lane) index := by
  simp only [extract,project_get]

theorem extract_cost (e : ℕ) (points : Vector F n) (capacity : size ≤ m*b)
    (raw : DenseCommonSource.Columns F n rows b) :
    (extract e points capacity raw).cost ≤ DenseCommonSource.operationBound n rows m b e+rows*(7*size+2)+2 := by
  have bound := DenseCommonSource.decode_cost e m points raw
  simp only [extract,project_cost]
  omega

def rectangular (values : Vector (Vector F size) (left*packing)) :
    Run (Vector (Vector (Vector F packing) size) left) :=
  tabulate (fun i : Fin left => tabulate (fun j : Fin size => tabulate (fun lane : Fin packing =>
    ⟨(values.get (finProdFinEquiv (i,lane))).get j,4⟩)))

omit [Field F] [DecidableEq F] in
theorem rectangular_get (values : Vector (Vector F size) (left*packing)) (i : Fin left) (j : Fin size) (lane : Fin packing) :
    ((((rectangular values).value).get i).get j).get lane = (values.get (finProdFinEquiv (i,lane))).get j := by
  simp only [rectangular,tabulate_value,FiniteLinearSolver.get_ofFn]

omit [Field F] [DecidableEq F] in
theorem rectangular_cost (values : Vector (Vector F size) (left*packing)) :
    (rectangular values).cost = left*(size*(5*packing+2)+2)+1 := by
  simp only [rectangular,tabulate_cost,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring

def extractRectangular (e : ℕ) (points : Vector F n) (capacity : size ≤ m*b)
    (raw : DenseCommonSource.Columns F n (left*packing) b) :
    Run (Vector (Vector (Vector F packing) size) left) :=
  let flat := extract e points capacity raw
  let output := rectangular flat.value
  ⟨output.value,flat.cost+output.cost+1⟩

theorem extractRectangular_get (e : ℕ) (points : Vector F n) (capacity : size ≤ m*b)
    (raw : DenseCommonSource.Columns F n (left*packing) b) (i : Fin left) (j : Fin size) (lane : Fin packing) :
    ((((extractRectangular e points capacity raw).value).get i).get j).get lane =
      ((extract e points capacity raw).value.get (finProdFinEquiv (i,lane))).get j := by
  simp only [extractRectangular,rectangular_get]

theorem extractRectangular_cost (e : ℕ) (points : Vector F n) (capacity : size ≤ m*b)
    (raw : DenseCommonSource.Columns F n (left*packing) b) :
    (extractRectangular e points capacity raw).cost ≤ DenseCommonSource.operationBound n (left*packing) m b e+
      (left*packing)*(7*size+2)+left*(size*(5*packing+2)+2)+4 := by
  have bound := extract_cost e points capacity raw
  simp only [extractRectangular,rectangular_cost]
  omega
end FormalProof4FHE.HasteBoots.DenseSourceExtraction
