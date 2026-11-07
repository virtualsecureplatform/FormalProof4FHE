module
public import FormalProof4FHE.HasteBoots.ConcreteNTTInitializedSearch
public import FormalProof4FHE.HasteBoots.ConcreteNTTWordSquareRoot
@[expose] public section

/-! Tonelli-Shanks retaining one Div64 state through all searches, powers and
updates. The complete outcome simulates the proved word loop, preserving
no-root versus assertion failure. Actual machine/compiler/physical and native
plan/cache refinement remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTInitializedSquareRoot
open ConcreteNTTLimbArithmetic (radix)
open ConcreteNTTDiv64Initialization (State Correct)
open ConcreteNTTInitializedSearch (search multiply power)
open ConcreteNTTWordSquareRoot (Outcome)

def loop (state : State) (m c t r : ℕ) : Outcome :=
  if t = 0 then .root 0 else
  if t = 1 then .root r else
    let found := search state m t
    if found.1 = m then
      if found.2 = 1 then .noRoot else .assertionFailure
    else
      let b := power state c (2^(m-found.1-1))
      let nextC := multiply state b b
      loop state found.1 nextC (multiply state t nextC) (multiply state r b)
termination_by m
decreasing_by
  have bound := ConcreteNTTInitializedSearch.search_le state m t
  have different : (search state m t).1 ≠ m := by assumption
  omega

theorem loop_eq (state : State) (correct : Correct state) (m c t r : ℕ)
    (mBound : m ≤ 64) (cFits : c < radix) (tFits : t < radix) (rFits : r < radix) :
    loop state m c t r = ConcreteNTTWordSquareRoot.loop state.divisor.val m c t r := by
  induction m using Nat.strong_induction_on generalizing c t r with
  | h m ih =>
    rw [loop,ConcreteNTTWordSquareRoot.loop]
    by_cases zero : t = 0
    · simp only [zero,ite_true]
    · simp only [zero,ite_false]
      by_cases one : t = 1
      · simp only [one,ite_true]
      · simp only [one,ite_false,ConcreteNTTInitializedSearch.search_eq state correct m t tFits]
        by_cases stopped : (ConcreteNTTWordSearch.search state.divisor.val m t).1 = m
        · simp only [stopped,ite_true]
        · simp only [stopped,ite_false]
          let i := (ConcreteNTTWordSearch.search state.divisor.val m t).1
          let exponent := 2^(m-i-1)
          let b := power state c exponent
          let nextC := multiply state b b
          let nextT := multiply state t nextC
          let nextR := multiply state r b
          have smaller : i < m := by have bound := ConcreteNTTWordSearch.search_le state.divisor.val m t; dsimp only [i]; omega
          have exponentFits : exponent < radix := ConcreteNTTWordSquareRoot.continuing_exponent_fits state.divisor.val m t mBound
          have bFits : b < radix := ConcreteNTTInitializedSearch.power_lt state c exponent
          have cNext : nextC < radix := ConcreteNTTInitializedSearch.multiply_lt state b b
          have tNext : nextT < radix := ConcreteNTTInitializedSearch.multiply_lt state t nextC
          have rNext : nextR < radix := ConcreteNTTInitializedSearch.multiply_lt state r b
          have bEq : b = ConcreteNTTModularPower.power state.divisor.val c exponent :=
            ConcreteNTTInitializedSearch.power_eq state correct c exponent cFits exponentFits
          have cEq : nextC = ConcreteNTTDiv64.mulMod state.divisor.val b b :=
            ConcreteNTTInitializedSearch.multiply_eq state correct b b bFits bFits
          have tEq : nextT = ConcreteNTTDiv64.mulMod state.divisor.val t (ConcreteNTTDiv64.mulMod state.divisor.val b b) := by
            rw [show nextT = multiply state t nextC from rfl,
              ConcreteNTTInitializedSearch.multiply_eq state correct t nextC tFits cNext,cEq]
          have rEq : nextR = ConcreteNTTDiv64.mulMod state.divisor.val r b :=
            ConcreteNTTInitializedSearch.multiply_eq state correct r b rFits bFits
          have continued := ih i smaller nextC nextT nextR (by omega) cNext tNext rNext
          change loop state i nextC nextT nextR = _
          calc
            loop state i nextC nextT nextR = ConcreteNTTWordSquareRoot.loop state.divisor.val i nextC nextT nextR := continued
            _ = _ := by rw [cEq,tEq,rEq,bEq]

def sqrt (state : State) (q s z n : ℕ) : Outcome :=
  loop state s (power state z q) (power state n q) (power state n ((q+1)/2))

theorem sqrt_eq (state : State) (correct : Correct state) (q s z n : ℕ)
    (qBound : q+1 < radix) (sBound : s ≤ 64) (zFits : z < radix) (nFits : n < radix) :
    sqrt state q s z n = ConcreteNTTWordSquareRoot.sqrt state.divisor.val q s z n := by
  have exponents := ConcreteNTTWordSquareRoot.initialization_exponents_fit q qBound
  simp only [sqrt,ConcreteNTTWordSquareRoot.sqrt]
  rw [loop_eq state correct s _ _ _ sBound (ConcreteNTTInitializedSearch.power_lt state z q)
    (ConcreteNTTInitializedSearch.power_lt state n q) (ConcreteNTTInitializedSearch.power_lt state n ((q+1)/2)),
    ConcreteNTTInitializedSearch.power_eq state correct z q zFits exponents.1,
    ConcreteNTTInitializedSearch.power_eq state correct n q nFits exponents.1,
    ConcreteNTTInitializedSearch.power_eq state correct n ((q+1)/2) nFits exponents.2]

end FormalProof4FHE.HasteBoots.ConcreteNTTInitializedSquareRoot
