module
public import FormalProof4FHE.HasteBoots.ConcreteNTTWordSquareRoot
public import FormalProof4FHE.HasteBoots.ConcreteNTTRootConstruction
@[expose] public section

/-! Bounded natural-word root construction using the proved reciprocal modular
operations and word Tonelli-Shanks. The field simulation retains distinct
assertion failure until rejection erasure. Actual limbs/instructions and native
plan/cache/compiler/physical refinement remain explicit obligations. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTWordRootConstruction
open ConcreteNTTDiv64 (wordLimit)
open ConcreteNTTModularPower (power)
open ConcreteNTTWordSquareRoot (Outcome)

def nonresidue (modulus exponent : ℕ) : ℕ → ℕ → Option ℕ
  | 0,_ => none
  | remaining+1,candidate =>
    if power modulus candidate exponent = modulus-1 then some candidate else
      nonresidue modulus exponent remaining (candidate+1)

theorem nonresidue_lt (modulus exponent remaining candidate z : ℕ)
    (range : candidate+remaining ≤ modulus) (returned : nonresidue modulus exponent remaining candidate = some z) : z < modulus := by
  induction remaining generalizing candidate with
  | zero => cases returned
  | succ remaining ih =>
    simp only [nonresidue] at returned
    split at returned
    · have same := Option.some.inj returned; omega
    · exact ih (candidate+1) (by omega) returned

theorem nonresidue_simulation (modulus exponent remaining candidate : ℕ) [Fact (Nat.Prime modulus)]
    (valid : 1 < modulus) (modulusFits : modulus < wordLimit) (range : candidate+remaining ≤ modulus) :
    (nonresidue modulus exponent remaining candidate).map (fun n : ℕ => (n : ZMod modulus)) =
      ConcreteNTTRootConstruction.nonresidue exponent remaining candidate := by
  induction remaining generalizing candidate with
  | zero => rfl
  | succ remaining ih =>
    have candidateBound : candidate < modulus := by omega
    have valueBound := ConcreteNTTModularPower.power_lt modulus candidate exponent valid modulusFits (candidateBound.trans modulusFits)
    have valueCast := ConcreteNTTModularPower.power_cast modulus candidate exponent valid modulusFits (candidateBound.trans modulusFits)
    have minusOne : ((modulus-1 : ℕ) : ZMod modulus) = -1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ modulus),ZMod.natCast_self,Nat.cast_one,zero_sub]
    have compared : (candidate : ZMod modulus)^exponent = -1 ↔ power modulus candidate exponent = modulus-1 := by
      rw [← valueCast,← minusOne]
      exact ConcreteNTTWordSearch.cast_injective modulus _ _ valueBound (by omega)
    rw [nonresidue,ConcreteNTTRootConstruction.nonresidue]
    simp only [compared]
    split
    · rfl
    · exact ih (candidate+1) (by omega)

def lift (modulus q s z : ℕ) : ℕ → ℕ → Outcome
  | 0,root => .root root
  | remaining+1,root =>
    match ConcreteNTTWordSquareRoot.sqrt modulus q s z root with
    | .root next => lift modulus q s z remaining next
    | .noRoot => .noRoot
    | .assertionFailure => .assertionFailure

theorem lift_simulation (modulus q s z steps root : ℕ) [Fact (Nat.Prime modulus)]
    (valid : 1 < modulus) (modulusFits : modulus < wordLimit) (zBound : z < modulus) (rootBound : root < modulus) :
    (lift modulus q s z steps root).erase.map (fun n : ℕ => (n : ZMod modulus)) =
      ConcreteNTTRootConstruction.lift q s (z : ZMod modulus) steps (root : ZMod modulus) := by
  induction steps generalizing root with
  | zero => rfl
  | succ steps ih =>
    have square := ConcreteNTTWordSquareRoot.sqrt_simulation modulus q s z root valid modulusFits
      (zBound.trans modulusFits) (rootBound.trans modulusFits)
    rw [lift,ConcreteNTTRootConstruction.lift]
    cases computed : ConcreteNTTWordSquareRoot.sqrt modulus q s z root with
    | root next =>
      have nextBound := ConcreteNTTWordSquareRoot.sqrt_root_lt modulus q s z root next valid modulusFits
        (zBound.trans modulusFits) (rootBound.trans modulusFits) computed
      simp only [computed,Outcome.erase,Option.map_some] at square
      rw [← square,Option.bind_some]
      exact ih next nextBound
    | noRoot =>
      simp only [computed,Outcome.erase,Option.map_none] at square
      rw [← square,Option.bind_none]
      rfl
    | assertionFailure =>
      simp only [computed,Outcome.erase,Option.map_none] at square
      rw [← square,Option.bind_none]
      rfl

theorem lift_root_lt (modulus q s z steps root answer : ℕ) (valid : 1 < modulus)
    (modulusFits : modulus < wordLimit) (zBound : z < modulus) (rootBound : root < modulus)
    (returned : lift modulus q s z steps root = .root answer) : answer < modulus := by
  induction steps generalizing root with
  | zero => have same := Outcome.root.inj returned; omega
  | succ steps ih =>
    simp only [lift] at returned
    cases computed : ConcreteNTTWordSquareRoot.sqrt modulus q s z root with
    | root next =>
      simp only [computed] at returned
      have nextBound := ConcreteNTTWordSquareRoot.sqrt_root_lt modulus q s z root next valid modulusFits
        (zBound.trans modulusFits) (rootBound.trans modulusFits) computed
      exact ih next nextBound returned
    | noRoot => simp only [computed] at returned; contradiction
    | assertionFailure => simp only [computed] at returned; contradiction

def construct (modulus logSize : ℕ) : Outcome :=
  let parts := ConcreteNTTRootConstruction.factorTwos (modulus-1)
  match nonresidue modulus ((modulus-1)/2) (modulus-2) 2 with
  | none => .noRoot
  | some z => lift modulus parts.1 parts.2 z logSize (modulus-1)

theorem construct_simulation (modulus logSize : ℕ) [Fact (Nat.Prime modulus)]
    (valid : 3 ≤ modulus) (modulusFits : modulus < wordLimit) :
    (construct modulus logSize).erase.map (fun n : ℕ => (n : ZMod modulus)) =
      ConcreteNTTRootConstruction.construct modulus logSize := by
  have selected := nonresidue_simulation modulus ((modulus-1)/2) (modulus-2) 2 (by omega) modulusFits (by omega)
  rw [construct,ConcreteNTTRootConstruction.construct,← selected]
  cases computed : nonresidue modulus ((modulus-1)/2) (modulus-2) 2 with
  | none => rfl
  | some z =>
    have zBound := nonresidue_lt modulus ((modulus-1)/2) (modulus-2) 2 z (by omega) computed
    simp only [Option.map_some,Option.bind_some]
    have minusOne : ((modulus-1 : ℕ) : ZMod modulus) = -1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ modulus),ZMod.natCast_self,Nat.cast_one,zero_sub]
    rw [← minusOne]
    exact lift_simulation modulus _ _ z logSize (modulus-1) (by omega) modulusFits zBound (by omega)

theorem construct_root_lt (modulus logSize answer : ℕ) (valid : 3 ≤ modulus) (modulusFits : modulus < wordLimit)
    (returned : construct modulus logSize = .root answer) : answer < modulus := by
  simp only [construct] at returned
  split at returned
  · contradiction
  · rename_i z selected
    have zBound := nonresidue_lt modulus ((modulus-1)/2) (modulus-2) 2 z (by omega) selected
    exact lift_root_lt modulus _ _ z logSize (modulus-1) answer (by omega) modulusFits zBound (by omega) returned

theorem parameters_fit (modulus : ℕ) (valid : 3 ≤ modulus) (modulusFits : modulus < wordLimit) :
    (ConcreteNTTRootConstruction.factorTwos (modulus-1)).1+1 < wordLimit ∧
    (ConcreteNTTRootConstruction.factorTwos (modulus-1)).2 < 64 := by
  let q := (ConcreteNTTRootConstruction.factorTwos (modulus-1)).1
  let s := (ConcreteNTTRootConstruction.factorTwos (modulus-1)).2
  have odd := ConcreteNTTRootConstruction.factorTwos_odd (modulus-1) (by omega)
  have positive : 0 < q := by change q%2 = 1 at odd; omega
  have decomposed := ConcreteNTTRootConstruction.factorTwos_decomposition (modulus-1)
  change modulus-1 = q*2^s at decomposed
  have qLe : q ≤ q*2^s := Nat.le_mul_of_pos_right q (by positivity)
  have powerLe : 2^s ≤ q*2^s := Nat.le_mul_of_pos_left (2^s) positive
  refine ⟨by dsimp only [q] at *; omega,?_⟩
  change s < 64
  by_contra large
  have bound : 64 ≤ s := by omega
  have powers : 2^64 ≤ 2^s := Nat.pow_le_pow_right (by decide) bound
  change modulus < 2^64 at modulusFits
  omega

theorem construct_primitive (modulus logSize answer : ℕ) [Fact (Nat.Prime modulus)]
    (valid : 3 ≤ modulus) (modulusFits : modulus < wordLimit) (odd : (-1 : ZMod modulus) ≠ 1)
    (returned : construct modulus logSize = .root answer) : IsPrimitiveRoot (answer : ZMod modulus) (2^(logSize+1)) := by
  have same := construct_simulation modulus logSize valid modulusFits
  simp only [returned,Outcome.erase,Option.map_some] at same
  exact ConcreteNTTRootConstruction.construct_primitive modulus logSize valid (answer : ZMod modulus) odd same.symm

def goldilocks (logSize : ℕ) : Outcome := construct NativeFields.goldilocksModulus logSize

theorem goldilocks_primitive (logSize answer : ℕ) (returned : goldilocks logSize = .root answer) :
    IsPrimitiveRoot (answer : NativeFields.Goldilocks) (2^(logSize+1)) :=
  construct_primitive NativeFields.goldilocksModulus logSize answer (by decide) (by decide) NativeFields.goldilocks_odd returned

end FormalProof4FHE.HasteBoots.ConcreteNTTWordRootConstruction
