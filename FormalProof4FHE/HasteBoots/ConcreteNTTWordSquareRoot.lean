module
public import FormalProof4FHE.HasteBoots.ConcreteNTTWordSearch
@[expose] public section

/-! Word-formula Tonelli-Shanks with distinct native no-root/assertion exits.
Its rejection erasure simulates the earlier field loop. All multiplication and
power calls use proved reciprocal-reduction formulas, not callbacks. u256 limbs,
u64 machine instructions, plan/cache provenance and physical work remain open. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTWordSquareRoot
open ConcreteNTTDiv64 (wordLimit mulMod)
open ConcreteNTTModularPower (power)
open ConcreteNTTWordSearch (search)

inductive Outcome where
  | root (value : ℕ)
  | noRoot
  | assertionFailure
  deriving DecidableEq, Repr

def Outcome.erase : Outcome → Option ℕ
  | .root value => some value
  | .noRoot | .assertionFailure => none

def loop (modulus m c t r : ℕ) : Outcome :=
  if t = 0 then .root 0 else
  if t = 1 then .root r else
    let found := search modulus m t
    if found.1 = m then
      if found.2 = 1 then .noRoot else .assertionFailure
    else
      let b := power modulus c (2^(m-found.1-1))
      let nextC := mulMod modulus b b
      loop modulus found.1 nextC (mulMod modulus t nextC) (mulMod modulus r b)
termination_by m
decreasing_by
  have bound := ConcreteNTTWordSearch.search_le modulus m t
  have different : (search modulus m t).1 ≠ m := by assumption
  omega

theorem continuing_shift_lt (modulus m t : ℕ) (wordBound : m ≤ 64) : m-(search modulus m t).1-1 < 64 := by
  omega

theorem continuing_exponent_fits (modulus m t : ℕ) (wordBound : m ≤ 64) :
    2^(m-(search modulus m t).1-1) < wordLimit := by
  exact Nat.pow_lt_pow_right (by decide) (continuing_shift_lt modulus m t wordBound)

theorem initialization_exponents_fit (q : ℕ) (qBound : q+1 < wordLimit) :
    q < wordLimit ∧ (q+1)/2 < wordLimit := by
  have divided := Nat.div_le_self (q+1) 2
  omega

theorem loop_root_lt (modulus m c t r answer : ℕ) (valid : 1 < modulus) (modulusFits : modulus < wordLimit)
    (cBound : c < modulus) (tBound : t < modulus) (rBound : r < modulus)
    (returned : loop modulus m c t r = .root answer) : answer < modulus := by
  induction m using Nat.strong_induction_on generalizing c t r with
  | h m ih =>
    rw [loop] at returned
    split at returned
    · have same := Outcome.root.inj returned; omega
    · split at returned
      · have same := Outcome.root.inj returned; omega
      · dsimp only at returned
        split at returned
        · split at returned <;> contradiction
        · rename_i continued
          let i := (search modulus m t).1
          let b := power modulus c (2^(m-i-1))
          let nextC := mulMod modulus b b
          have bBound : b < modulus := ConcreteNTTModularPower.power_lt modulus c _ valid modulusFits (cBound.trans modulusFits)
          have cNext : nextC < modulus := ConcreteNTTDiv64.mulMod_lt modulus b b valid modulusFits
            (bBound.trans modulusFits) (bBound.trans modulusFits)
          have tNext := ConcreteNTTDiv64.mulMod_lt modulus t nextC valid modulusFits (tBound.trans modulusFits) (cNext.trans modulusFits)
          have rNext := ConcreteNTTDiv64.mulMod_lt modulus r b valid modulusFits (rBound.trans modulusFits) (bBound.trans modulusFits)
          have smaller : i < m := by have bound := ConcreteNTTWordSearch.search_le modulus m t; dsimp only [i]; omega
          exact ih i smaller _ _ _ cNext tNext rNext returned

theorem loop_simulation (modulus m c t r : ℕ) [Fact (Nat.Prime modulus)]
    (valid : 1 < modulus) (modulusFits : modulus < wordLimit)
    (cBound : c < modulus) (tBound : t < modulus) (rBound : r < modulus) :
    (loop modulus m c t r).erase.map (fun n : ℕ => (n : ZMod modulus)) =
      ConcreteNTTSquareRoot.loop m (c : ZMod modulus) (t : ZMod modulus) (r : ZMod modulus) := by
  induction m using Nat.strong_induction_on generalizing c t r with
  | h m ih =>
    have zeroTest : ((t : ZMod modulus) = 0) ↔ t = 0 := by
      simpa only [Nat.cast_zero] using ConcreteNTTWordSearch.cast_injective modulus t 0 tBound (by omega)
    have oneTest : ((t : ZMod modulus) = 1) ↔ t = 1 := by
      simpa only [Nat.cast_one] using ConcreteNTTWordSearch.cast_injective modulus t 1 tBound valid
    rw [loop,ConcreteNTTSquareRoot.loop]
    simp only [zeroTest,oneTest]
    by_cases zero : t = 0
    · simp only [zero,ite_true,Outcome.erase,Option.map_some,Nat.cast_zero]
    · simp only [zero,ite_false]
      by_cases one : t = 1
      · simp only [one,ite_true,Outcome.erase,Option.map_some]
      · simp only [one,ite_false]
        have sameSearch := ConcreteNTTWordSearch.search_cast modulus m t valid modulusFits tBound
        rw [← sameSearch]
        dsimp only
        by_cases stopped : (search modulus m t).1 = m
        · simp only [stopped,ite_true]
          split <;> rfl
        · simp only [stopped,ite_false]
          let i := (search modulus m t).1
          let exponent := 2^(m-i-1)
          let b := power modulus c exponent
          let nextC := mulMod modulus b b
          let nextT := mulMod modulus t nextC
          let nextR := mulMod modulus r b
          have bBound : b < modulus := ConcreteNTTModularPower.power_lt modulus c exponent valid modulusFits (cBound.trans modulusFits)
          have cNext : nextC < modulus := ConcreteNTTDiv64.mulMod_lt modulus b b valid modulusFits
            (bBound.trans modulusFits) (bBound.trans modulusFits)
          have tNext : nextT < modulus := ConcreteNTTDiv64.mulMod_lt modulus t nextC valid modulusFits
            (tBound.trans modulusFits) (cNext.trans modulusFits)
          have rNext : nextR < modulus := ConcreteNTTDiv64.mulMod_lt modulus r b valid modulusFits
            (rBound.trans modulusFits) (bBound.trans modulusFits)
          have bCast : (b : ZMod modulus) = (c : ZMod modulus)^exponent :=
            ConcreteNTTModularPower.power_cast modulus c exponent valid modulusFits (cBound.trans modulusFits)
          have cCast : (nextC : ZMod modulus) = (c : ZMod modulus)^exponent*(c : ZMod modulus)^exponent := by
            change (mulMod modulus b b : ZMod modulus) = _
            rw [ConcreteNTTDiv64.mulMod_cast modulus b b valid modulusFits (bBound.trans modulusFits) (bBound.trans modulusFits),bCast]
          have tCast : (nextT : ZMod modulus) = (t : ZMod modulus)*((c : ZMod modulus)^exponent*(c : ZMod modulus)^exponent) := by
            change (mulMod modulus t nextC : ZMod modulus) = _
            rw [ConcreteNTTDiv64.mulMod_cast modulus t nextC valid modulusFits (tBound.trans modulusFits) (cNext.trans modulusFits),cCast]
          have rCast : (nextR : ZMod modulus) = (r : ZMod modulus)*(c : ZMod modulus)^exponent := by
            change (mulMod modulus r b : ZMod modulus) = _
            rw [ConcreteNTTDiv64.mulMod_cast modulus r b valid modulusFits (rBound.trans modulusFits) (bBound.trans modulusFits),bCast]
          have smaller : i < m := by have bound := ConcreteNTTWordSearch.search_le modulus m t; dsimp only [i]; omega
          have continued := ih i smaller nextC nextT nextR cNext tNext rNext
          simpa only [cCast,tCast,rCast] using continued

def sqrt (modulus q s z n : ℕ) : Outcome :=
  loop modulus s (power modulus z q) (power modulus n q) (power modulus n ((q+1)/2))

theorem sqrt_simulation (modulus q s z n : ℕ) [Fact (Nat.Prime modulus)]
    (valid : 1 < modulus) (modulusFits : modulus < wordLimit) (zFits : z < wordLimit) (nFits : n < wordLimit) :
    (sqrt modulus q s z n).erase.map (fun a : ℕ => (a : ZMod modulus)) =
      ConcreteNTTSquareRoot.sqrt q s (z : ZMod modulus) (n : ZMod modulus) := by
  have cBound := ConcreteNTTModularPower.power_lt modulus z q valid modulusFits zFits
  have tBound := ConcreteNTTModularPower.power_lt modulus n q valid modulusFits nFits
  have rBound := ConcreteNTTModularPower.power_lt modulus n ((q+1)/2) valid modulusFits nFits
  have same := loop_simulation modulus s _ _ _ valid modulusFits cBound tBound rBound
  rw [ConcreteNTTModularPower.power_cast modulus z q valid modulusFits zFits,
    ConcreteNTTModularPower.power_cast modulus n q valid modulusFits nFits,
    ConcreteNTTModularPower.power_cast modulus n ((q+1)/2) valid modulusFits nFits] at same
  exact same

theorem sqrt_root_lt (modulus q s z n answer : ℕ) (valid : 1 < modulus) (modulusFits : modulus < wordLimit)
    (zFits : z < wordLimit) (nFits : n < wordLimit) (returned : sqrt modulus q s z n = .root answer) : answer < modulus :=
  loop_root_lt modulus s _ _ _ answer valid modulusFits
    (ConcreteNTTModularPower.power_lt modulus z q valid modulusFits zFits)
    (ConcreteNTTModularPower.power_lt modulus n q valid modulusFits nFits)
    (ConcreteNTTModularPower.power_lt modulus n ((q+1)/2) valid modulusFits nFits) returned

theorem sqrt_sound (modulus q s z n answer : ℕ) [Fact (Nat.Prime modulus)]
    (valid : 1 < modulus) (modulusFits : modulus < wordLimit) (zFits : z < wordLimit) (nFits : n < wordLimit)
    (odd : q%2 = 1) (nonzero : (z : ZMod modulus) ≠ 0)
    (returned : sqrt modulus q s z n = .root answer) : (answer : ZMod modulus)*answer = (n : ZMod modulus) := by
  have same := sqrt_simulation modulus q s z n valid modulusFits zFits nFits
  simp only [returned,Outcome.erase,Option.map_some] at same
  exact ConcreteNTTSquareRoot.sqrt_sound q s (z : ZMod modulus) (n : ZMod modulus) (answer : ZMod modulus) odd nonzero same.symm

end FormalProof4FHE.HasteBoots.ConcreteNTTWordSquareRoot
