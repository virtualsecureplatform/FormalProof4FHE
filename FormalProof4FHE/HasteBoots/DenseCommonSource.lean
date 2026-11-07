module
public import FormalProof4FHE.HasteBoots.ExecutableBerlekampWelch
public import FormalProof4FHE.HasteBoots.BlockEvaluationCost
public import FormalProof4FHE.HasteBoots.ColumnDistanceCost
@[expose] public section

/-! Matrix candidate construction from prepared position-major columns. Scalar
words are loaded explicitly, decoded once per row/lane and projected directly
from coefficient vectors. No intermediate polynomial is constructed at runtime.
Charges use the abstract field/access model, excluding initial input preparation
and physical/backend costs. -/
namespace FormalProof4FHE.HasteBoots.DenseCommonSource
open SolverOperationCost
open scoped BigOperators
variable {F : Type} [Field F] [DecidableEq F] {n rows m b : ℕ}
abbrev Columns (F : Type) (n rows b : ℕ) := ColumnDistanceCost.Columns F n rows b
abbrev Table (F : Type) (rows m b : ℕ) := BlockEvaluationCost.Table F rows m b

def input (raw : Columns F n rows b) (pos : Fin n) (row : Fin rows) (lane : Fin b) : F :=
  ((raw.get pos).get row).get lane

def laneWord (raw : Columns F n rows b) (row : Fin rows) (lane : Fin b) : Run (Vector F n) :=
  tabulate (fun pos : Fin n => ⟨input raw pos row lane,3⟩)

omit [Field F] [DecidableEq F] in
theorem laneWord_get (raw : Columns F n rows b) (row : Fin rows) (lane : Fin b) (pos : Fin n) :
    (laneWord raw row lane).value.get pos = input raw pos row lane := by
  simp only [laneWord,tabulate_value,FiniteLinearSolver.get_ofFn]

omit [Field F] [DecidableEq F] in
theorem laneWord_cost (raw : Columns F n rows b) (row : Fin rows) (lane : Fin b) :
    (laneWord raw row lane).cost = 4*n+1 := by
  simp only [laneWord,tabulate_cost,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  omega

def project (e m : ℕ) (decoded : Option (Vector F (e+m+1))) : Run (Vector F m) :=
  tabulate (fun j : Fin m => match decoded with
    | none => ⟨0,1⟩
    | some candidate => ⟨candidate.get ⟨j.val,by omega⟩,2⟩)

theorem project_get (e m : ℕ) (decoded : Option (Vector F (e+m+1))) (j : Fin m) :
    (project e m decoded).value.get j =
      ((decoded.map PolynomialShapeCost.polynomial).getD ExecutablePolynomial.zero).coeff j.val := by
  cases decoded with
  | none => simp only [project,tabulate_value,FiniteLinearSolver.get_ofFn,Option.map_none,Option.getD_none,
      ExecutablePolynomial.zero_eq,Polynomial.coeff_zero]
  | some candidate =>
    simp only [project,tabulate_value,FiniteLinearSolver.get_ofFn,Option.map_some,Option.getD_some]
    rw [DensePolynomialStepCost.polynomial_coeff_fin candidate ⟨j.val,by omega⟩]

omit [DecidableEq F] in
theorem project_cost (e m : ℕ) (decoded : Option (Vector F (e+m+1))) :
    (project e m decoded).cost ≤ 3*m+1 := by
  cases decoded <;> simp only [project,tabulate_cost,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] <;> omega

def decodeLane (e m : ℕ) (points : Vector F n) (raw : Columns F n rows b)
    (row : Fin rows) (lane : Fin b) : Run (Vector F m) :=
  let received := laneWord raw row lane
  let decoded := DenseBerlekampWelch.decode e m points received.value
  let coefficients := project e m decoded.value
  ⟨coefficients.value,received.cost+decoded.cost+coefficients.cost+2⟩

theorem decodeLane_get (e m : ℕ) (points : Vector F n) (raw : Columns F n rows b)
    (row : Fin rows) (lane : Fin b) (j : Fin m) :
    (decodeLane e m points raw row lane).value.get j =
      ((ExecutableBerlekampWelch.decoder e m (fun i => points.get i)
        (fun pos => input raw pos row lane)).getD ExecutablePolynomial.zero).coeff j.val := by
  have equal : (DenseBerlekampWelch.decode e m points (laneWord raw row lane).value).value.map PolynomialShapeCost.polynomial =
      ExecutableBerlekampWelch.decoder e m (fun i => points.get i) (fun pos => input raw pos row lane) := by
    rw [← ExecutableBerlekampWelch.decodeWithCost_of_vectors,ExecutableBerlekampWelch.decodeWithCost_value]
    congr 1
    funext pos
    exact laneWord_get raw row lane pos
  simp only [decodeLane,project_get,equal]

theorem decodeLane_cost (e m : ℕ) (points : Vector F n) (raw : Columns F n rows b)
    (row : Fin rows) (lane : Fin b) :
    (decodeLane e m points raw row lane).cost ≤ DenseBerlekampWelch.operationBound n e m+4*n+3*m+4 := by
  have decoded := DenseBerlekampWelch.decode_cost e m points (laneWord raw row lane).value
  have projected := project_cost e m (DenseBerlekampWelch.decode e m points (laneWord raw row lane).value).value
  simp only [decodeLane,laneWord_cost]
  omega

def candidates (e m : ℕ) (points : Vector F n) (raw : Columns F n rows b) : Run (Table F rows m b) :=
  let lanes := tabulate (fun row : Fin rows => tabulate (fun lane : Fin b => decodeLane e m points raw row lane))
  let output := tabulate (fun row : Fin rows => tabulate (fun j : Fin m => tabulate (fun lane : Fin b =>
    ⟨(((lanes.value.get row).get lane).get j),3⟩)))
  ⟨output.value,lanes.cost+output.cost+1⟩

theorem candidates_get (e m : ℕ) (points : Vector F n) (raw : Columns F n rows b)
    (row : Fin rows) (j : Fin m) (lane : Fin b) :
    (((candidates e m points raw).value.get row).get j).get lane =
      ((ExecutableBerlekampWelch.decoder e m (fun i => points.get i)
        (fun pos => input raw pos row lane)).getD ExecutablePolynomial.zero).coeff j.val := by
  simp only [candidates,tabulate_value,FiniteLinearSolver.get_ofFn,decodeLane_get]

def candidatesBound (n rows m b e : ℕ) : ℕ :=
  rows*(b*(DenseBerlekampWelch.operationBound n e m+4*n+3*m+5)+2)+
    rows*(m*(4*b+2)+2)+3

theorem candidates_cost (e m : ℕ) (points : Vector F n) (raw : Columns F n rows b) :
    (candidates e m points raw).cost ≤ candidatesBound n rows m b e := by
  have lanes (row : Fin rows) :
      (tabulate (fun lane : Fin b => decodeLane e m points raw row lane)).cost ≤
        b*(DenseBerlekampWelch.operationBound n e m+4*n+3*m+5)+1 := by
    have bound := Finset.sum_le_sum (fun lane (_ : lane ∈ (Finset.univ : Finset (Fin b))) => decodeLane_cost e m points raw row lane)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at bound
    simp only [tabulate_cost]
    nlinarith
  have bound := Finset.sum_le_sum (fun row (_ : row ∈ (Finset.univ : Finset (Fin rows))) => lanes row)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at bound
  simp only [tabulate_cost] at bound
  simp only [candidates,tabulate_cost,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,candidatesBound]
  nlinarith
def zeroTable : Run (Table F rows m b) :=
  tabulate (fun _ => tabulate (fun _ => tabulate (fun _ => SolverOperationCost.pure 0)))

omit [DecidableEq F] in
theorem zeroTable_get (row : Fin rows) (j : Fin m) (lane : Fin b) :
    ((((zeroTable : Run (Table F rows m b)).value).get row).get j).get lane = 0 := by
  simp only [zeroTable,tabulate_value,FiniteLinearSolver.get_ofFn,SolverOperationCost.pure]

omit [DecidableEq F] in
theorem zeroTable_cost : (zeroTable : Run (Table F rows m b)).cost = rows*(m*(b+2)+2)+1 := by
  simp only [zeroTable,tabulate_cost,SolverOperationCost.pure,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring

def word (points : Vector F n) (table : Table F rows m b) : Fin n → Fin rows → Fin b → F :=
  fun pos row lane => BlockEncoder.encode (fun i => points.get i) (fun j lane => ((table.get row).get j).get lane) pos lane

omit [DecidableEq F] in
theorem evaluated_word (points : Vector F n) (table : Table F rows m b) :
    ColumnDistanceCost.word (BlockEvaluationCost.evaluate points table).value = word points table := by
  funext pos row lane
  exact BlockEvaluationCost.evaluate_get points table pos row lane

def check (e : ℕ) (points : Vector F n) (raw : Columns F n rows b) (table : Table F rows m b) : Run Bool :=
  let evaluated := BlockEvaluationCost.evaluate points table
  let distance := ColumnDistanceCost.distance raw evaluated.value
  ⟨decide (distance.value ≤ e),evaluated.cost+distance.cost+1⟩

theorem check_value (e : ℕ) (points : Vector F n) (raw : Columns F n rows b) (table : Table F rows m b) :
    (check e points raw table).value = decide (hammingDist (ColumnDistanceCost.word raw) (word points table) ≤ e) := by
  simp only [check,ColumnDistanceCost.distance_value,evaluated_word]

theorem check_cost (e : ℕ) (points : Vector F n) (raw : Columns F n rows b) (table : Table F rows m b) :
    (check e points raw table).cost = n*(5*m+rows*(b*(6*m+8)+9)+18)+4 := by
  simp only [check,BlockEvaluationCost.evaluate_cost,ColumnDistanceCost.distance_cost]
  ring

def decode (e m : ℕ) (points : Vector F n) (raw : Columns F n rows b) : Run (Table F rows m b) :=
  let table := candidates e m points raw
  let checked := check e points raw table.value
  if checked.value then ⟨table.value,table.cost+checked.cost+5⟩
  else
    let zero := zeroTable (F := F) (rows := rows) (m := m) (b := b)
    ⟨zero.value,table.cost+checked.cost+zero.cost+5⟩

theorem decode_value (e m : ℕ) (points : Vector F n) (raw : Columns F n rows b) :
    (decode e m points raw).value =
      if (check e points raw (candidates e m points raw).value).value then (candidates e m points raw).value
      else (zeroTable : Run (Table F rows m b)).value := by
  unfold decode
  dsimp only
  split_ifs <;> rfl

def operationBound (n rows m b e : ℕ) : ℕ :=
  candidatesBound n rows m b e + (n*(5*m+rows*(b*(6*m+8)+9)+18)+4) +
    (rows*(m*(b+2)+2)+1)+5

theorem decode_cost (e m : ℕ) (points : Vector F n) (raw : Columns F n rows b) :
    (decode e m points raw).cost ≤ operationBound n rows m b e := by
  have candidateBound := candidates_cost e m points raw
  unfold decode
  dsimp only
  split_ifs <;> simp only [check_cost,zeroTable_cost] <;> unfold operationBound <;> omega
end FormalProof4FHE.HasteBoots.DenseCommonSource
