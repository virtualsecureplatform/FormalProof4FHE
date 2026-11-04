module

public import FormalProof4FHE.HasteBoots.NativeInterpolationCore
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Mathematical arithmetic for the literal interpolation core

Division is checked at zero to preserve the native inverse precondition.
This is the field interpretation of the native algorithm, not a replacement
Lagrange implementation. Its polynomial correspondence is a further theorem.
-/

namespace FormalProof4FHE.HasteBoots.NativeInterpolationField

open NativeInterpolationCore

noncomputable section

def arithmetic (K : Type) [Field K] : Arithmetic K := by
  classical
  exact ⟨0, 1, (· + ·), (· - ·), (· * ·), (- ·), fun left right => decide (left = right),
    fun left right => if right = 0 then none else some (left / right)⟩

theorem factorial_value {K : Type} [Field K] (count : ℕ) :
    factorial (arithmetic K) count = ((count.factorial : K), ((count + 1 : ℕ) : K)) := by
  induction count with
  | zero => simp only [factorial, Function.iterate_zero_apply, arithmetic, Nat.factorial_zero, Nat.zero_add, Nat.cast_one]
  | succ count ih =>
    change (factorialStep (arithmetic K))^[count + 1] ((arithmetic K).one, (arithmetic K).one) = _
    rw [Function.iterate_succ_apply']
    change factorialStep (arithmetic K) (factorial (arithmetic K) count) = _
    rw [ih]
    simp only [factorialStep, arithmetic, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    congr 1; ring

end

end FormalProof4FHE.HasteBoots.NativeInterpolationField
