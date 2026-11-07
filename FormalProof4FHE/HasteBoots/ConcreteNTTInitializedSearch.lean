module
public import FormalProof4FHE.HasteBoots.ConcreteNTTInitializedPower
public import FormalProof4FHE.HasteBoots.ConcreteNTTWordSearch
@[expose] public section

/-! Retained-state arithmetic and inner root search. Natural arguments model
stored u64 values; casts are proved inert on the source word domains. No
reciprocal is reconstructed during search/power. Machine/compiler/physical
refinement remains separate. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTInitializedSearch
open ConcreteNTTLimbArithmetic (radix Limb)
open ConcreteNTTDiv64Initialization (State Correct)

def word (value : ℕ) : Limb := Fin.ofNat radix value

theorem word_value (value : ℕ) (fits : value < radix) : (word value).val = value := by
  simp only [word,Fin.val_ofNat,Nat.mod_eq_of_lt fits]

def multiply (state : State) (left right : ℕ) : ℕ :=
  (ConcreteNTTDiv64Initialization.mulMod state (word left) (word right)).val

def power (state : State) (base exponent : ℕ) : ℕ :=
  (ConcreteNTTInitializedPower.power state (word base) (word exponent)).val

theorem multiply_lt (state : State) (left right : ℕ) : multiply state left right < radix :=
  (ConcreteNTTDiv64Initialization.mulMod state (word left) (word right)).isLt

theorem power_lt (state : State) (base exponent : ℕ) : power state base exponent < radix :=
  (ConcreteNTTInitializedPower.power state (word base) (word exponent)).isLt

theorem multiply_eq (state : State) (correct : Correct state) (left right : ℕ)
    (leftFits : left < radix) (rightFits : right < radix) :
    multiply state left right = ConcreteNTTDiv64.mulMod state.divisor.val left right := by
  simp only [multiply,ConcreteNTTInitializedPower.mulMod_formula state correct,word_value left leftFits,word_value right rightFits]

theorem power_eq (state : State) (correct : Correct state) (base exponent : ℕ)
    (baseFits : base < radix) (exponentFits : exponent < radix) :
    power state base exponent = ConcreteNTTModularPower.power state.divisor.val base exponent := by
  simp only [power,ConcreteNTTInitializedPower.power_formula state correct,word_value base baseFits,word_value exponent exponentFits]

def search (state : State) : ℕ → ℕ → ℕ × ℕ
  | 0,t => (0,t)
  | remaining+1,t =>
    let squared := multiply state t t
    if squared = 1 then (1,squared) else
      let rest := search state remaining squared
      (rest.1+1,rest.2)

theorem search_le (state : State) (limit t : ℕ) : (search state limit t).1 ≤ limit := by
  induction limit generalizing t with
  | zero => rfl
  | succ limit ih =>
    simp only [search]
    split
    · dsimp only; omega
    · have bound := ih (multiply state t t); dsimp only; omega

theorem search_eq (state : State) (correct : Correct state) (limit t : ℕ) (tFits : t < radix) :
    search state limit t = ConcreteNTTWordSearch.search state.divisor.val limit t := by
  induction limit generalizing t with
  | zero => rfl
  | succ limit ih =>
    rw [search,ConcreteNTTWordSearch.search]
    have squared := multiply_eq state correct t t tFits tFits
    rw [← squared]
    split
    · rfl
    · rw [ih _ (multiply_lt state t t)]

end FormalProof4FHE.HasteBoots.ConcreteNTTInitializedSearch
