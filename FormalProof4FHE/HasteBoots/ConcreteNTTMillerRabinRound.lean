module
public import FormalProof4FHE.HasteBoots.ConcreteNTTMillerRabinField
public import FormalProof4FHE.HasteBoots.ConcreteNTTInitializedSearch
@[expose] public section

/-! Literal retained-state Miller-Rabin round from locked prime.rs. Comparison
and power/square semantics are derived from constructed Div64 arithmetic. This
proves prime-field round completeness, not twelve-base composite-test soundness
or machine/compiler/physical refinement. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTMillerRabinRound
open ConcreteNTTLimbArithmetic (radix)
open ConcreteNTTDiv64Initialization (State Correct)
open ConcreteNTTInitializedSearch (multiply power)

def squares (state : State) : ℕ → ℕ → Bool
  | 0,_ => false
  | remaining+1,x =>
    let next := multiply state x x
    if next = state.divisor.val-1 then true else squares state remaining next

def round (state : State) (s q base : ℕ) : Bool :=
  let x := power state base q
  if x = 1 ∨ x = state.divisor.val-1 then true else squares state (s-1) x

theorem negative_test (modulus value : ℕ) (valid : 1 < modulus) (bound : value < modulus) :
    (value : ZMod modulus) = -1 ↔ value = modulus-1 := by
  have cast : ((modulus-1 : ℕ) : ZMod modulus) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ modulus),ZMod.natCast_self,Nat.cast_one,zero_sub]
  rw [← cast]
  exact ConcreteNTTWordSearch.cast_injective modulus value (modulus-1) bound (by omega)

theorem squares_simulation (state : State) (correct : Correct state) [Fact (Nat.Prime state.divisor.val)]
    (remaining x : ℕ) (xFits : x < radix) :
    squares state remaining x = ConcreteNTTMillerRabinField.squares remaining (x : ZMod state.divisor.val) := by
  induction remaining generalizing x with
  | zero => rfl
  | succ remaining ih =>
    let next := multiply state x x
    have nextEq : next = ConcreteNTTDiv64.mulMod state.divisor.val x x :=
      ConcreteNTTInitializedSearch.multiply_eq state correct x x xFits xFits
    have nextBound : next < state.divisor.val := by
      rw [nextEq]
      exact ConcreteNTTDiv64.mulMod_lt state.divisor.val x x correct.1 state.divisor.isLt xFits xFits
    have nextCast : (next : ZMod state.divisor.val) = (x : ZMod state.divisor.val)*x := by
      rw [nextEq]
      exact ConcreteNTTDiv64.mulMod_cast state.divisor.val x x correct.1 state.divisor.isLt xFits xFits
    have compared := negative_test state.divisor.val next correct.1 nextBound
    rw [squares,ConcreteNTTMillerRabinField.squares,← nextCast]
    simp only [compared]
    by_cases found : multiply state x x = state.divisor.val-1
    · simp only [next,found,ite_true]
    · simp only [next,found,ite_false]
      exact ih _ (ConcreteNTTInitializedSearch.multiply_lt state x x)

theorem round_simulation (state : State) (correct : Correct state) [Fact (Nat.Prime state.divisor.val)]
    (s q base : ℕ) (qFits : q < radix) (baseFits : base < radix) :
    round state s q base = ConcreteNTTMillerRabinField.check s ((base : ZMod state.divisor.val)^q) := by
  let x := power state base q
  have xEq : x = ConcreteNTTModularPower.power state.divisor.val base q :=
    ConcreteNTTInitializedSearch.power_eq state correct base q baseFits qFits
  have xBound : x < state.divisor.val := by
    rw [xEq]
    exact ConcreteNTTModularPower.power_lt state.divisor.val base q correct.1 state.divisor.isLt baseFits
  have xCast : (x : ZMod state.divisor.val) = (base : ZMod state.divisor.val)^q := by
    rw [xEq]
    exact ConcreteNTTModularPower.power_cast state.divisor.val base q correct.1 state.divisor.isLt baseFits
  have oneTest : ((x : ZMod state.divisor.val) = 1) ↔ x = 1 := by
    simpa only [Nat.cast_one] using ConcreteNTTWordSearch.cast_injective state.divisor.val x 1 xBound correct.1
  have negativeTest := negative_test state.divisor.val x correct.1 xBound
  rw [round,ConcreteNTTMillerRabinField.check,← xCast]
  simp only [oneTest,negativeTest]
  by_cases initial : power state base q = 1 ∨ power state base q = state.divisor.val-1
  · simp only [x,initial,ite_true]
  · simp only [x,initial,ite_false]
    exact squares_simulation state correct (s-1) _ (ConcreteNTTInitializedSearch.power_lt state base q)

theorem round_passes (state : State) (correct : Correct state) [Fact (Nat.Prime state.divisor.val)]
    (s q base : ℕ) (qFits : q < radix) (baseFits : base < radix)
    (nonzero : (base : ZMod state.divisor.val) ≠ 0) (decomposition : state.divisor.val-1 = q*2^s) :
    round state s q base = true := by
  rw [round_simulation state correct s q base qFits baseFits]
  exact ConcreteNTTMillerRabinField.prime_round state.divisor.val q s _ nonzero decomposition

end FormalProof4FHE.HasteBoots.ConcreteNTTMillerRabinRound
