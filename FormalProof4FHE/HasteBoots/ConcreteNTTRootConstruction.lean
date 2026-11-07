module
public import FormalProof4FHE.HasteBoots.ConcreteNTTSquareRoot
public import FormalProof4FHE.HasteBoots.NativeFields
@[expose] public section

/-! Field semantics of concrete-ntt roots.rs get_q_s64, get_z64 and
find_primitive_root64 at cdeba793e46208320b30d78be19f7be78d49016a.
Successful construction produces a primitive root without a supplied root
certificate. Matching u64/Div64 operations and actual plan/cache returns remains
an explicit refinement obligation; this is not a replacement native backend. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTRootConstruction

/-- Zero is unreachable after the native odd-prime preflight. -/
def factorTwos (value : ℕ) : ℕ × ℕ :=
  if value = 0 then (0,0) else
  if value%2 = 0 then
    let rest := factorTwos (value/2)
    (rest.1,rest.2+1)
  else (value,0)
termination_by value
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

theorem factorTwos_odd (value : ℕ) (positive : 0 < value) : (factorTwos value).1%2 = 1 := by
  induction value using Nat.strong_induction_on with
  | h value ih =>
    rw [factorTwos]
    split
    · omega
    · split
      · rename_i nonzero even
        have halfPositive : 0 < value/2 := by omega
        exact ih (value/2) (Nat.div_lt_self positive (by decide)) halfPositive
      · rename_i nonzero odd
        dsimp only
        omega

theorem factorTwos_decomposition (value : ℕ) :
    value = (factorTwos value).1*2^(factorTwos value).2 := by
  induction value using Nat.strong_induction_on with
  | h value ih =>
    rw [factorTwos]
    split
    · rename_i zero
      simp only [zero,zero_mul]
    · split
      · rename_i nonzero even
        have half := ih (value/2) (Nat.div_lt_self (by omega) (by decide))
        dsimp only
        rw [Nat.pow_succ,← Nat.mul_assoc,← half]
        omega
      · simp only [Nat.pow_zero,mul_one]

variable {F : Type} [Field F] [DecidableEq F]

/-- Original ascending candidate scan, with exactly p-2 possible candidates
2,...,p-1. This public modulus range is not an adversary trial limit. -/
def nonresidue (exponent : ℕ) : ℕ → ℕ → Option F
  | 0,_ => none
  | remaining+1,candidate =>
    if (candidate : F)^exponent = -1 then some (candidate : F)
    else nonresidue exponent remaining (candidate+1)

theorem nonresidue_sound (exponent remaining candidate : ℕ) (z : F)
    (returned : nonresidue exponent remaining candidate = some z) : z^exponent = -1 := by
  induction remaining generalizing candidate with
  | zero => cases returned
  | succ remaining ih =>
    simp only [nonresidue] at returned
    split at returned
    · rename_i found
      have same := Option.some.inj returned
      rw [← same]; exact found
    · exact ih (candidate+1) returned

theorem nonresidue_nonzero (exponent remaining candidate : ℕ) (positive : 0 < exponent) (z : F)
    (returned : nonresidue exponent remaining candidate = some z) : z ≠ 0 := by
  have found := nonresidue_sound exponent remaining candidate z returned
  intro zero
  rw [zero,zero_pow (Nat.ne_of_gt positive)] at found
  exact neg_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0) found.symm

/-- Each successful square root becomes the input of the next original step. -/
def lift (q s : ℕ) (z : F) : ℕ → F → Option F
  | 0,root => some root
  | remaining+1,root => (ConcreteNTTSquareRoot.sqrt q s z root).bind (fun next => lift q s z remaining next)

theorem lift_power (q s : ℕ) (z : F) (odd : q%2 = 1) (nonzero : z ≠ 0)
    (steps : ℕ) (root answer : F) (returned : lift q s z steps root = some answer) :
    answer^(2^steps) = root := by
  induction steps generalizing root with
  | zero =>
    have same := Option.some.inj returned
    rw [← same]; simp only [pow_zero,pow_one]
  | succ steps ih =>
    obtain ⟨next,squared,rest⟩ := Option.bind_eq_some_iff.mp returned
    have half := ih next rest
    have square := ConcreteNTTSquareRoot.sqrt_sound q s z root next odd nonzero squared
    rw [Nat.pow_succ,pow_mul,pow_two,half]
    exact square

/-- degree=2^(logSize+1), so the source repeats square roots logSize times. -/
def construct (modulus logSize : ℕ) : Option F :=
  let parts := factorTwos (modulus-1)
  (nonresidue ((modulus-1)/2) (modulus-2) 2).bind (fun z => lift parts.1 parts.2 z logSize (-1))

theorem construct_half (modulus logSize : ℕ) (domain : 3 ≤ modulus) (answer : F)
    (returned : construct modulus logSize = some answer) : answer^(2^logSize) = -1 := by
  obtain ⟨z,selected,lifted⟩ := Option.bind_eq_some_iff.mp returned
  have odd := factorTwos_odd (modulus-1) (by omega)
  have nonzero := nonresidue_nonzero ((modulus-1)/2) (modulus-2) 2 (by omega) z selected
  exact lift_power _ _ z odd nonzero logSize (-1) answer lifted

theorem construct_primitive (modulus logSize : ℕ) (domain : 3 ≤ modulus) (answer : F)
    (odd : (-1 : F) ≠ 1) (returned : construct modulus logSize = some answer) :
    IsPrimitiveRoot answer (2^(logSize+1)) :=
  NTTRootCheck.primitive_of_half_power logSize answer odd (construct_half modulus logSize domain answer returned)

/-- The semantic Goldilocks root path uses the actual public modulus. -/
def goldilocks (logSize : ℕ) : Option NativeFields.Goldilocks := construct NativeFields.goldilocksModulus logSize

theorem goldilocks_primitive (logSize : ℕ) (root : NativeFields.Goldilocks)
    (returned : goldilocks logSize = some root) : IsPrimitiveRoot root (2^(logSize+1)) :=
  construct_primitive NativeFields.goldilocksModulus logSize (by decide) root NativeFields.goldilocks_odd returned

end FormalProof4FHE.HasteBoots.ConcreteNTTRootConstruction
