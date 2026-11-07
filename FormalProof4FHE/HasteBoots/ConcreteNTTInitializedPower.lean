module
public import FormalProof4FHE.HasteBoots.ConcreteNTTDiv64Initialization
public import FormalProof4FHE.HasteBoots.ConcreteNTTModularPower
@[expose] public section

/-! Literal exponentiation retaining one initialized Div64 state across every
modular product. Correctness is derived from the actual constructor outcome;
no reciprocal or modular-product certificate is supplied by the caller. Actual
Rust instructions/compiler, plan/cache and physical refinement remain open. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTInitializedPower
open ConcreteNTTLimbArithmetic (Limb)
open ConcreteNTTDiv64Initialization (State Correct mulMod)

def loop (state : State) (exponent : ℕ) (x y : Limb) : Limb :=
  if exponent ≤ 1 then mulMod state x y else
    let nextY := if exponent%2 = 1 then mulMod state x y else y
    loop state (exponent/2) (mulMod state x x) nextY
termination_by exponent
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

def power (state : State) (base exponent : Limb) : Limb :=
  if exponent.val = 0 then 1 else loop state exponent.val base 1

theorem mulMod_formula (state : State) (correct : Correct state) (left right : Limb) :
    (mulMod state left right).val = ConcreteNTTDiv64.mulMod state.divisor.val left.val right.val := by
  rw [ConcreteNTTDiv64Initialization.mulMod_correct state correct left right,
    ConcreteNTTDiv64.mulMod_eq state.divisor.val left.val right.val correct.1 state.divisor.isLt left.isLt right.isLt]

theorem loop_formula (state : State) (correct : Correct state) (exponent : ℕ) (x y : Limb) :
    (loop state exponent x y).val = ConcreteNTTModularPower.loop state.divisor.val exponent x.val y.val := by
  induction exponent using Nat.strong_induction_on generalizing x y with
  | h exponent ih =>
    rw [loop,ConcreteNTTModularPower.loop]
    split
    · exact mulMod_formula state correct x y
    · rename_i large
      have smaller : exponent/2 < exponent := Nat.div_lt_self (by omega) (by decide)
      by_cases odd : exponent%2 = 1
      · simp only [odd,ite_true]
        rw [ih (exponent/2) smaller,mulMod_formula state correct x x,mulMod_formula state correct x y]
      · simp only [odd,ite_false]
        rw [ih (exponent/2) smaller,mulMod_formula state correct x x]

theorem power_formula (state : State) (correct : Correct state) (base exponent : Limb) :
    (power state base exponent).val = ConcreteNTTModularPower.power state.divisor.val base.val exponent.val := by
  simp only [power,ConcreteNTTModularPower.power]
  split
  · rfl
  · exact loop_formula state correct exponent.val base 1

theorem power_correct (state : State) (correct : Correct state) (base exponent : Limb) :
    (power state base exponent).val = base.val^exponent.val%state.divisor.val := by
  rw [power_formula state correct base exponent]
  exact ConcreteNTTModularPower.power_eq state.divisor.val base.val exponent.val correct.1 state.divisor.isLt base.isLt

theorem new_power (divisor : Limb) (state : State)
    (executed : ConcreteNTTDiv64Initialization.new divisor = .initialized state) (base exponent : Limb) :
    (power state base exponent).val = base.val^exponent.val%divisor.val := by
  obtain ⟨valid,rfl⟩ := ConcreteNTTDiv64Initialization.new_origin divisor state executed
  exact power_correct _ (ConcreteNTTDiv64Initialization.initialize_correct divisor valid) base exponent

end FormalProof4FHE.HasteBoots.ConcreteNTTInitializedPower
