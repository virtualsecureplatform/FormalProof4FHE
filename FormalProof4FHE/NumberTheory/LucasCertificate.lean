/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import Mathlib.NumberTheory.LucasPrimality

/-! A small executable wrapper around `lucas_primality`. -/

namespace FormalProof4FHE.NumberTheory.LucasCertificate

def check (prime generator : ℕ) (factors : List ℕ) : Bool :=
  decide (prime - 1 = factors.prod) &&
  factors.all (fun factor => decide factor.Prime) &&
  decide ((generator : ZMod prime) ^ (prime - 1) = 1) &&
  factors.all (fun factor =>
    decide ((generator : ZMod prime) ^ ((prime - 1) / factor) ≠ 1))

theorem prime_of_check {prime generator : ℕ} {factors : List ℕ}
    (checked : check prime generator factors = true) : prime.Prime := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at checked
  rcases checked with ⟨⟨⟨product, factorPrimes⟩, generatorOrder⟩, factorOrders⟩
  apply lucas_primality prime (generator : ZMod prime) generatorOrder
  intro divisor divisorPrime divisorDvd
  have divisorDvdProduct : divisor ∣ factors.prod := by
    rw [← product]
    exact divisorDvd
  have member := mem_list_primes_of_dvd_prod (Nat.prime_iff.mp divisorPrime)
    (fun factor member => Nat.prime_iff.mp (factorPrimes factor member))
    divisorDvdProduct
  exact factorOrders divisor member

end FormalProof4FHE.NumberTheory.LucasCertificate
