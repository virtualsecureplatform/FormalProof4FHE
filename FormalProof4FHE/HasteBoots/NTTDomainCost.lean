module
public import FormalProof4FHE.HasteBoots.NTTButterfly
public import FormalProof4FHE.HasteBoots.SolverOperationErasure
@[expose] public section

/-! Materialized negacyclic domain nodes in native bit-reversed order. A binary
point tree shares each ratio square across its children and concatenates their
stored arrays. No per-node exponentiation or arbitrary function callback is used.
Charges cover field multiplication, array copying and structural operations in
an abstract field/access model; native backend/physical refinement is separate. -/
namespace FormalProof4FHE.HasteBoots.NTTDomainCost
open SolverOperationCost NTTButterfly
variable {F : Type} [Field F]

def appendHalves {A : Type} (n : ℕ) (first second : Vector A (2^n)) : Vector A (2^(n+1)) :=
  ⟨first.toArray++second.toArray,by simp [Nat.pow_succ,Nat.mul_two]⟩

theorem appendHalves_get {A : Type} (n : ℕ) (first second : Vector A (2^n))
    (bit : Bool) (tail : MatrixFold.Cube n) :
    (appendHalves n first second).get (outputIndex (n+1) (bit,tail)) =
      if bit then second.get (outputIndex n tail) else first.get (outputIndex n tail) := by
  change (first.toArray++second.toArray)[(outputIndex (n+1) (bit,tail)).val]'(by
    simpa only [Array.size_append,Vector.size_toArray,Nat.pow_succ,Nat.mul_two] using
      (outputIndex (n+1) (bit,tail)).isLt) = _
  rw [Array.getElem_append]
  cases bit
  · simp only [outputIndex_succ_val,Bool.false_eq_true,ite_false,Nat.zero_add,Vector.size_toArray]
    rw [dite_eq_left (outputIndex n tail).isLt]
    rfl
  · simp only [outputIndex_succ_val,ite_true,Vector.size_toArray]
    rw [dite_eq_right (show ¬2^n+(outputIndex n tail).val < 2^n by omega)]
    simp only [Nat.add_sub_cancel_left]
    rfl

def tree : (n : ℕ) → F → F → Run (Vector F (2^n))
  | 0,base,_ => ⟨⟨#[base],rfl⟩,2⟩
  | n+1,base,ratio =>
    let squared := multiply (SolverOperationCost.pure ratio) (SolverOperationCost.pure ratio)
    let upper := multiply (SolverOperationCost.pure base) (SolverOperationCost.pure ratio)
    let first := tree n base squared.value
    let second := tree n upper.value squared.value
    ⟨appendHalves n first.value second.value,
      first.cost+second.cost+squared.cost+upper.cost+2*(2^n+2^n)+5⟩

theorem tree_get (n : ℕ) (base ratio : F) (cell : MatrixFold.Cube n) :
    (tree n base ratio).value.get (outputIndex n cell) = point n base ratio cell := by
  induction n generalizing base ratio with
  | zero =>
    have address : outputIndex 0 cell = 0 := by apply Fin.ext; have bound := (outputIndex 0 cell).isLt; norm_num at bound ⊢
    have exponent : FlatMatrixFold.index 0 cell = 0 := by apply Fin.ext; have bound := (FlatMatrixFold.index 0 cell).isLt; norm_num at bound ⊢
    simp only [tree,address,point,exponent,Fin.val_zero,pow_zero,mul_one]
    rfl
  | succ n ih =>
    rcases cell with ⟨bit,tail⟩
    rw [point_succ]
    simp only [tree,multiply,SolverOperationCost.pure,appendHalves_get]
    cases bit <;> simp only [Bool.false_eq_true,ite_false,ite_true,mul_one,pow_two,ih]

theorem tree_cost (n : ℕ) (base ratio : F) :
    (tree n base ratio).cost+7 = 2^n*(2*n+9) := by
  induction n generalizing base ratio with
  | zero => rfl
  | succ n ih =>
    have first := ih base (ratio*ratio)
    have second := ih (base*ratio) (ratio*ratio)
    simp only [tree,multiply,SolverOperationCost.pure,Nat.pow_succ]
    nlinarith

def nodes (n : ℕ) (psi : F) : Run (Vector F (2^n)) :=
  let root := load psi
  let squared := multiply (SolverOperationCost.pure root.value) (SolverOperationCost.pure root.value)
  let result := tree n root.value squared.value
  ⟨result.value,root.cost+squared.cost+result.cost⟩

theorem nodes_get (n : ℕ) (psi : F) (i : Fin (2^n)) :
    (nodes n psi).value.get i = NTTButterfly.nodes n psi i := by
  rw [NTTButterfly.nodes_eq_point]
  have stored := tree_get n psi (psi*psi) ((outputIndex n).symm i)
  simp only [Equiv.apply_symm_apply] at stored
  simpa only [nodes,load,multiply,SolverOperationCost.pure,pow_two] using stored

theorem nodes_cost (n : ℕ) (psi : F) : (nodes n psi).cost+5 = 2^n*(2*n+9) := by
  have bound := tree_cost n psi (psi*psi)
  simp only [nodes,load,multiply,SolverOperationCost.pure]
  omega
end FormalProof4FHE.HasteBoots.NTTDomainCost
