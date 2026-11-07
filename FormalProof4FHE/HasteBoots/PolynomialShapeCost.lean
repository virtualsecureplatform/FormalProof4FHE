module
public import FormalProof4FHE.HasteBoots.ExecutablePolynomial
@[expose] public section

/-! Degree and leading coefficient from prepared ascending coefficient vectors.
The full scan charges a field load/test and four structural steps per entry;
vector/list conversion charges two accesses per entry plus initialization.
This is an abstract field/access phase, excluding coefficient preparation and
backend/physical costs. Zero and trailing-zero representations are supported. -/
namespace FormalProof4FHE.HasteBoots.PolynomialShapeCost
open SolverOperationCost
open Polynomial
variable {F : Type} [Field F] [DecidableEq F]

def coefficient (values : List F) (i : ℕ) : F := values[i]?.getD 0

-- The effective length is one past the last nonzero coefficient, or zero.
def scan : List F → Run ℕ
  | [] => ⟨0,1⟩
  | head :: rest =>
    let tail := scan rest
    let tested := zeroTest (load head)
    ⟨if tail.value = 0 then if tested.value then 0 else 1 else tail.value+1,
      tail.cost+tested.cost+4⟩

theorem scan_cost (values : List F) : (scan values).cost = 6*values.length+1 := by
  induction values with
  | nil => rfl
  | cons head rest ih => simp only [scan,zeroTest,load,List.length_cons,ih]; omega

theorem scan_bound (values : List F) : (scan values).value ≤ values.length := by
  induction values with
  | nil => rfl
  | cons head rest ih =>
    by_cases tailzero : (scan rest).value = 0
    · by_cases headzero : head = 0 <;> simp [scan,zeroTest,load,tailzero,headzero]
    · simp only [scan,tailzero,ite_false,List.length_cons]
      omega

theorem scan_above (values : List F) (i : ℕ) (bound : (scan values).value ≤ i) : coefficient values i = 0 := by
  induction values generalizing i with
  | nil => simp [coefficient]
  | cons head rest ih =>
    by_cases tailzero : (scan rest).value = 0
    · by_cases headzero : head = 0
      · cases i with
        | zero => simp [coefficient,headzero]
        | succ i => simpa [coefficient] using ih i (by omega)
      · have positive : 1 ≤ i := by simpa [scan,zeroTest,load,tailzero,headzero] using bound
        cases i with
        | zero => omega
        | succ i => simpa [coefficient] using ih i (by omega)
    · have next : (scan rest).value+1 ≤ i := by simpa [scan,tailzero] using bound
      cases i with
      | zero => omega
      | succ i => simpa [coefficient] using ih i (by omega)

theorem scan_last (values : List F) (nonzero : (scan values).value ≠ 0) :
    coefficient values ((scan values).value-1) ≠ 0 := by
  induction values with
  | nil => simp [scan] at nonzero
  | cons head rest ih =>
    by_cases tailzero : (scan rest).value = 0
    · by_cases headzero : head = 0
      · simp [scan,tailzero,zeroTest,load,headzero] at nonzero
      · simp [scan,tailzero,zeroTest,load,headzero,coefficient]
    · have positive : 0 < (scan rest).value := by omega
      have prior := ih tailzero
      obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero tailzero
      simpa [scan,tailzero,hk,coefficient] using prior

def effectiveLength {n : ℕ} (values : Vector F n) : Run ℕ :=
  let result := scan values.toList
  ⟨result.value,result.cost+2*n+1⟩

theorem effectiveLength_cost {n : ℕ} (values : Vector F n) : (effectiveLength values).cost = 8*n+2 := by
  simp only [effectiveLength,scan_cost,Vector.length_toList]
  omega

theorem effectiveLength_bound {n : ℕ} (values : Vector F n) : (effectiveLength values).value ≤ n := by
  simpa only [effectiveLength,Vector.length_toList] using scan_bound values.toList

def polynomial {n : ℕ} (values : Vector F n) : F[X] :=
  ExecutablePolynomial.ofCoefficients n (coefficient values.toList)

theorem polynomial_coeff {n : ℕ} (values : Vector F n) (i : ℕ) :
    (polynomial values).coeff i = coefficient values.toList i := by
  simp only [polynomial,ExecutablePolynomial.coeff_ofCoefficients]
  split_ifs with bound
  · rfl
  · have absent : values.toList[i]? = none := List.getElem?_eq_none
      (by simpa only [Vector.length_toList] using Nat.le_of_not_gt bound)
    simp only [coefficient,absent,Option.getD_none]

theorem polynomial_eq_zero_iff {n : ℕ} (values : Vector F n) :
    polynomial values = 0 ↔ (effectiveLength values).value = 0 := by
  constructor
  · intro zero
    by_contra nonzero
    have last := scan_last values.toList nonzero
    rw [← polynomial_coeff,zero,Polynomial.coeff_zero] at last
    exact last rfl
  · intro zero
    apply Polynomial.ext
    intro i
    rw [polynomial_coeff,Polynomial.coeff_zero]
    exact scan_above values.toList i (by simpa only [effectiveLength] using Nat.le_trans (Nat.le_of_eq zero) (Nat.zero_le i))

theorem polynomial_natDegree {n : ℕ} (values : Vector F n) :
    (polynomial values).natDegree = (effectiveLength values).value-1 := by
  have upper : (polynomial values).natDegree ≤ (scan values.toList).value-1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [polynomial_coeff]
    exact scan_above _ i (by omega)
  by_cases zero : (scan values.toList).value = 0
  · simpa [effectiveLength,zero] using Nat.eq_zero_of_le_zero (by simpa [zero] using upper)
  · exact natDegree_eq_of_le_of_coeff_ne_zero upper (by rw [polynomial_coeff]; exact scan_last _ zero)

def inspect {n : ℕ} (values : Vector F n) : Run (ℕ × F) :=
  let length := effectiveLength values
  let degree := length.value-1
  let leading := if length.value = 0 then 0 else values.toArray[degree]?.getD 0
  ⟨(degree,leading),length.cost+4⟩

theorem inspect_degree {n : ℕ} (values : Vector F n) :
    (inspect values).value.1 = (polynomial values).natDegree := by
  simp only [inspect,polynomial_natDegree]

theorem inspect_leading {n : ℕ} (values : Vector F n) :
    (inspect values).value.2 = (polynomial values).leadingCoeff := by
  simp only [inspect,Polynomial.leadingCoeff,polynomial_natDegree,polynomial_coeff]
  by_cases zero : (scan values.toList).value = 0
  · have vanished := scan_above values.toList 0 (by omega)
    simpa only [effectiveLength,zero,ite_true,Nat.zero_sub] using vanished.symm
  · simp only [effectiveLength,zero,ite_false]
    simp [coefficient]

theorem inspect_eq {n : ℕ} (values : Vector F n) :
    (inspect values).value = ((polynomial values).natDegree,(polynomial values).leadingCoeff) :=
  Prod.ext (inspect_degree values) (inspect_leading values)

theorem inspect_cost {n : ℕ} (values : Vector F n) : (inspect values).cost = 8*n+6 := by
  simp only [inspect,effectiveLength_cost]
end FormalProof4FHE.HasteBoots.PolynomialShapeCost
