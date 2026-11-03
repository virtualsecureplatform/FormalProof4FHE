module

public import FormalProof4FHE.HasteBoots.NTTButterfly

@[expose] public section

/-!
# Power-of-two primitive-root validation

The native field helper rejects zero and tests root^(degree/2)=-1 for a
power-of-two degree greater than one. In odd characteristic this test is
equivalent to the exact primitive-root condition used by the NTT proofs.
The concrete-ntt default constructs roots by repeated square roots instead;
its integer implementation and cache refinement remain separate obligations.
-/

namespace FormalProof4FHE.HasteBoots.NTTRootCheck

variable {F : Type} [Field F]

theorem primitive_of_half_power (n : ℕ) (root : F) (odd : (-1 : F) ≠ 1)
    (half : root ^ (2 ^ n) = -1) : IsPrimitiveRoot root (2 ^ (n + 1)) := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  apply orderOf_eq_prime_pow (p := 2) (n := n)
  · rwa [half]
  · rw [Nat.pow_succ, pow_mul, half]
    ring

theorem half_power_iff (n : ℕ) (root : F) (odd : (-1 : F) ≠ 1) :
    root ^ (2 ^ n) = -1 ↔ IsPrimitiveRoot root (2 ^ (n + 1)) :=
  ⟨primitive_of_half_power n root odd, NTTButterfly.half_power⟩

variable [DecidableEq F]

def check (n : ℕ) (root : F) : Bool :=
  decide (root ≠ 0) && decide (root ^ (2 ^ n) = -1)

/-- A computed root check supplies exactly the needed mathematical condition,
including sound rejection of roots of smaller order and zero. -/
theorem check_iff (n : ℕ) (root : F) (odd : (-1 : F) ≠ 1) :
    check n root = true ↔ IsPrimitiveRoot root (2 ^ (n + 1)) := by
  simp only [check, Bool.and_eq_true_iff, decide_eq_true_eq]
  constructor
  · intro passed
    exact primitive_of_half_power n root odd passed.2
  · intro primitive
    exact ⟨primitive.ne_zero (by positivity), NTTButterfly.half_power primitive⟩

end FormalProof4FHE.HasteBoots.NTTRootCheck
