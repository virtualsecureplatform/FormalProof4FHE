module
public import FormalProof4FHE.HasteBoots.SolverOperationBounds
@[expose] public section
namespace FormalProof4FHE.HasteBoots.BerlekampWelchPowers
open SolverOperationCost
variable {F : Type} [Field F]

/-! Compute consecutive powers by successive multiplication, then convert the
linear list into a vector once. No indexed list lookup or repeated exponentiation
is used. Charges follow the abstract field/access model: one multiplication,
one stored list element and one cons step per generated element; conversion
charges a load and store per element plus initialization. -/
def powerList (point current : F) : ℕ → Run (List F)
  | 0 => ⟨[],1⟩
  | length+1 =>
    let next := multiply (SolverOperationCost.pure current) (SolverOperationCost.pure point)
    let rest := powerList point next.value length
    ⟨current :: rest.value,next.cost+rest.cost+2⟩

theorem powerList_value (point current : F) (length : ℕ) :
    (powerList point current length).value = List.ofFn (fun i : Fin length => current * point ^ i.val) := by
  induction length generalizing current with
  | zero => rfl
  | succ length ih =>
    simp only [powerList,multiply,SolverOperationCost.pure,ih,List.ofFn_succ,Fin.val_zero,pow_zero,mul_one,Fin.val_succ,pow_succ]
    congr 1
    apply congrArg List.ofFn
    funext i
    ring

theorem powerList_length (point current : F) (length : ℕ) : (powerList point current length).value.length = length := by
  rw [powerList_value,List.length_ofFn]

theorem powerList_cost (point current : F) (length : ℕ) : (powerList point current length).cost = 3*length+1 := by
  induction length generalizing current with
  | zero => rfl
  | succ length ih => simp only [powerList,multiply,SolverOperationCost.pure,ih]; omega

def powers (point : F) (degree : ℕ) : Run (Vector F (degree+1)) :=
  let generated := powerList point 1 (degree+1)
  ⟨⟨generated.value.toArray,by simp only [generated,List.size_toArray,powerList_length]⟩,
    generated.cost+2*(degree+1)+1⟩

@[simp] theorem powers_get (point : F) (degree : ℕ) (i : Fin (degree+1)) :
    (powers point degree).value.get i = point ^ i.val := by
  simp only [powers,Vector.get,List.getElem_toArray,powerList_value,List.getElem_ofFn,one_mul]
  rfl

@[simp] theorem powers_cost (point : F) (degree : ℕ) : (powers point degree).cost = 5*degree+7 := by
  simp only [powers,powerList_cost]
  omega
end FormalProof4FHE.HasteBoots.BerlekampWelchPowers
