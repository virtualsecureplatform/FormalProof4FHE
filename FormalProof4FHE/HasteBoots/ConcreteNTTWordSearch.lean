module
public import FormalProof4FHE.HasteBoots.ConcreteNTTModularPower
public import FormalProof4FHE.HasteBoots.ConcreteNTTSquareRoot
public import Mathlib.Algebra.Field.ZMod
@[expose] public section

/-! Natural-word square-before-test search from concrete-ntt sqrt_mod_ex64.
Comparisons of canonical words are related to the field semantics. The reducer
is the proved Div64 formula; actual limb/instruction refinement remains open. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTWordSearch
open ConcreteNTTDiv64 (wordLimit mulMod)

def search (modulus : ℕ) : ℕ → ℕ → ℕ × ℕ
  | 0,t => (0,t)
  | remaining+1,t =>
    let squared := mulMod modulus t t
    if squared = 1 then (1,squared) else
      let rest := search modulus remaining squared
      (rest.1+1,rest.2)

theorem search_le (modulus limit t : ℕ) : (search modulus limit t).1 ≤ limit := by
  induction limit generalizing t with
  | zero => rfl
  | succ limit ih =>
    simp only [search]
    split
    · dsimp only; omega
    · have bound := ih (mulMod modulus t t); dsimp only; omega

theorem cast_injective (modulus left right : ℕ) (leftBound : left < modulus) (rightBound : right < modulus) :
    (left : ZMod modulus) = (right : ZMod modulus) ↔ left = right := by
  constructor
  · intro same
    have values := congrArg ZMod.val same
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt leftBound,Nat.mod_eq_of_lt rightBound] using values
  · intro same; rw [same]

theorem search_lt (modulus limit t : ℕ) (valid : 1 < modulus) (modulusFits : modulus < wordLimit)
    (tBound : t < modulus) : (search modulus limit t).2 < modulus := by
  induction limit generalizing t with
  | zero => exact tBound
  | succ limit ih =>
    have squared := ConcreteNTTDiv64.mulMod_lt modulus t t valid modulusFits
      (tBound.trans modulusFits) (tBound.trans modulusFits)
    simp only [search]
    split
    · exact squared
    · exact ih _ squared

theorem search_cast (modulus limit t : ℕ) [Fact (Nat.Prime modulus)]
    (valid : 1 < modulus) (modulusFits : modulus < wordLimit) (tBound : t < modulus) :
    ((search modulus limit t).1,((search modulus limit t).2 : ZMod modulus)) =
      ConcreteNTTSquareRoot.search limit (t : ZMod modulus) := by
  induction limit generalizing t with
  | zero => rfl
  | succ limit ih =>
    let squared := mulMod modulus t t
    have squaredBound : squared < modulus := ConcreteNTTDiv64.mulMod_lt modulus t t valid modulusFits
      (tBound.trans modulusFits) (tBound.trans modulusFits)
    have squaredCast : (squared : ZMod modulus) = (t : ZMod modulus)*t := ConcreteNTTDiv64.mulMod_cast modulus t t valid modulusFits
      (tBound.trans modulusFits) (tBound.trans modulusFits)
    have compared : ((squared : ZMod modulus) = 1) ↔ squared = 1 := by
      simpa only [Nat.cast_one] using cast_injective modulus squared 1 squaredBound valid
    rw [search,ConcreteNTTSquareRoot.search,← squaredCast]
    simp only [compared]
    by_cases found : mulMod modulus t t = 1
    · simp only [squared,found,ite_true]
    · simp only [squared,found,ite_false]
      have continued := ih squared squaredBound
      exact congrArg (fun result : ℕ × ZMod modulus => (result.1+1,result.2)) continued

end FormalProof4FHE.HasteBoots.ConcreteNTTWordSearch
