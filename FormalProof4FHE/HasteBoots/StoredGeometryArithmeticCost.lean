module
public import FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning
public import FormalProof4FHE.HasteBoots.SolverOperationCost
public import Mathlib.Data.Nat.Bits
@[expose] public section

/-! Explicit arithmetic loops for stored native geometry. Doubling powers and
halving bit lengths have charged steps; no row-code or table callback executes.
Word/backend/physical refinement remains separate from this operation model. -/
namespace FormalProof4FHE.HasteBoots.StoredGeometryArithmeticCost
open SolverOperationCost (Run)

def power2 : ℕ → Run ℕ
  | 0 => ⟨1,1⟩
  | count+1 =>
    let rest := power2 count
    ⟨2*rest.value,rest.cost+3⟩

theorem power2_value (count : ℕ) : (power2 count).value = 2^count := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [power2,ih,pow_succ]; omega

theorem power2_cost (count : ℕ) : (power2 count).cost = 3*count+1 := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [power2,ih]; omega

def bitLength (value : ℕ) : Run ℕ :=
  if value = 0 then ⟨0,1⟩
  else
    let rest := bitLength (value/2)
    ⟨rest.value+1,rest.cost+4⟩
termination_by value
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

theorem size_halves (value : ℕ) (positive : value ≠ 0) : value.size = (value/2).size+1 := by
  have nonzero : Nat.bit value.bodd value.div2 ≠ 0 := by rw [Nat.bit_bodd_div2]; exact positive
  have sized := Nat.size_bit nonzero
  rw [Nat.bit_bodd_div2,Nat.div2_val] at sized
  exact sized

theorem bitLength_value (value : ℕ) : (bitLength value).value = value.size := by
  induction value using Nat.strong_induction_on with
  | h value ih =>
    rw [bitLength]
    split
    · rename_i zero; subst value; rfl
    · rename_i nonzero
      have rest := ih (value/2) (Nat.div_lt_self (by omega) (by decide))
      dsimp only
      rw [rest,size_halves value nonzero]

theorem bitLength_cost (value : ℕ) : (bitLength value).cost = 4*value.size+1 := by
  induction value using Nat.strong_induction_on with
  | h value ih =>
    rw [bitLength]
    split
    · rename_i zero; subst value; rfl
    · rename_i nonzero
      have rest := ih (value/2) (Nat.div_lt_self (by omega) (by decide))
      dsimp only
      rw [rest,size_halves value nonzero]
      omega
end FormalProof4FHE.HasteBoots.StoredGeometryArithmeticCost
