module
public import FormalProof4FHE.HasteBoots.NTTRootCheck
@[expose] public section

/-! Field semantics of concrete-ntt roots.rs sqrt_mod_ex64 at locked revision
cdeba793e46208320b30d78be19f7be78d49016a. The original search, zero/one exits,
failed-search exit and m-decreasing updates are retained. This is not a Div64,
u64, allocation or Rust refinement, and supplies no physical operation bound. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTSquareRoot
variable {F : Type} [Field F] [DecidableEq F]

/-- Square before increment/testing, as in the native inner while loop. -/
def search : ℕ → F → ℕ × F
  | 0,t => (0,t)
  | remaining+1,t =>
    let squared := t*t
    if squared = 1 then (1,squared) else
      let rest := search remaining squared
      (rest.1+1,rest.2)

theorem search_le (limit : ℕ) (t : F) : (search limit t).1 ≤ limit := by
  induction limit generalizing t with
  | zero => rfl
  | succ limit ih =>
    simp only [search]
    split
    · dsimp only; omega
    · have bounded := ih (t*t); dsimp only; omega

/-- A failed terminal assertion is represented by rejection too. Refining the
native panic/error distinction is a separate obligation; neither returns a root. -/
def loop (m : ℕ) (c t r : F) : Option F :=
  if t = 0 then some 0 else
  if t = 1 then some r else
    let i := (search m t).1
    if i = m then none else
      let b := c^(2^(m-i-1))
      loop i (b*b) (t*(b*b)) (r*b)
termination_by m
decreasing_by
  have bound := search_le m t
  omega

/-- The actual update preserves r²=n*t, and c never becomes zero. -/
def Invariant (n c t r : F) : Prop := r*r = n*t ∧ c ≠ 0 ∧ (t = 0 → n = 0)

omit [DecidableEq F] in
theorem invariant_step (n c t r : F) (valid : Invariant n c t r) (exponent : ℕ) :
    Invariant n ((c^exponent)*(c^exponent)) (t*((c^exponent)*(c^exponent))) (r*(c^exponent)) := by
  rcases valid with ⟨square,nonzero,zero⟩
  have power : c^exponent ≠ 0 := pow_ne_zero _ nonzero
  refine ⟨?_,mul_ne_zero power power,?_⟩
  · calc
      (r*c^exponent)*(r*c^exponent) = (r*r)*((c^exponent)*(c^exponent)) := by ring
      _ = n*(t*((c^exponent)*(c^exponent))) := by rw [square]; ring
  · intro vanished
    exact zero ((mul_eq_zero.mp vanished).resolve_right (mul_ne_zero power power))

theorem loop_sound (m : ℕ) (n c t r answer : F) (valid : Invariant n c t r)
    (returned : loop m c t r = some answer) : answer*answer = n := by
  induction m using Nat.strong_induction_on generalizing c t r with
  | h m ih =>
    rw [loop] at returned
    split at returned
    · rename_i zero
      have result := Option.some.inj returned
      rw [← result,valid.2.2 zero]
      simp only [mul_zero]
    · split at returned
      · rename_i one
        have result := Option.some.inj returned
        rw [← result]
        simpa only [one,mul_one] using valid.1
      · dsimp only at returned
        split at returned
        · contradiction
        · rename_i smaller
          have bound := search_le m t
          exact ih (search m t).1 (by omega) _ _ _
            (invariant_step n c t r valid (2^(m-(search m t).1-1))) returned

/-- The outer initialization uses exactly the native exponents. -/
def sqrt (q s : ℕ) (z n : F) : Option F :=
  loop s (z^q) (n^q) (n^((q+1)/2))

omit [DecidableEq F] in
theorem initial_invariant (q : ℕ) (z n : F) (odd : q%2 = 1) (nonzero : z ≠ 0) :
    Invariant n (z^q) (n^q) (n^((q+1)/2)) := by
  have exponent : (q+1)/2*2 = q+1 := by omega
  refine ⟨?_,pow_ne_zero _ nonzero,?_⟩
  · calc
      n^((q+1)/2)*n^((q+1)/2) = n^((q+1)/2*2) := by rw [pow_mul,pow_two]
      _ = n^(q+1) := by rw [exponent]
      _ = n*(n^q) := by rw [pow_succ]; ring
  · intro vanished
    by_contra nonzeroN
    exact pow_ne_zero q nonzeroN vanished

theorem sqrt_sound (q s : ℕ) (z n answer : F) (odd : q%2 = 1) (nonzero : z ≠ 0)
    (returned : sqrt q s z n = some answer) : answer*answer = n :=
  loop_sound s n _ _ _ answer (initial_invariant q z n odd nonzero) returned

end FormalProof4FHE.HasteBoots.ConcreteNTTSquareRoot
