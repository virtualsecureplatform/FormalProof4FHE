module
public import FormalProof4FHE.HasteBoots.ConcreteNTTInitializedSquareRoot
public import FormalProof4FHE.HasteBoots.ConcreteNTTWordRootConstruction
@[expose] public section

/-! Root construction from a single actual word-formula Div64 initialization.
One retained state serves every nonresidue test, square root and modular product.
Complete outcomes simulate the proved word root constructor, with no caller
reciprocal/arithmetic/root certificate. Actual Rust instructions/compiler,
plan/cache/retained-code provenance and physical refinement remain open. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTInitializedRootConstruction
open ConcreteNTTLimbArithmetic (radix Limb)
open ConcreteNTTDiv64Initialization (State Correct)
open ConcreteNTTInitializedSearch (power)
open ConcreteNTTWordSquareRoot (Outcome)

def nonresidue (state : State) (exponent : ℕ) : ℕ → ℕ → Option ℕ
  | 0,_ => none
  | remaining+1,candidate =>
    if power state candidate exponent = state.divisor.val-1 then some candidate else
      nonresidue state exponent remaining (candidate+1)

theorem nonresidue_eq (state : State) (correct : Correct state) (exponent remaining candidate : ℕ)
    (exponentFits : exponent < radix) (range : candidate+remaining ≤ state.divisor.val) :
    nonresidue state exponent remaining candidate =
      ConcreteNTTWordRootConstruction.nonresidue state.divisor.val exponent remaining candidate := by
  induction remaining generalizing candidate with
  | zero => rfl
  | succ remaining ih =>
    have candidateFits : candidate < radix := by have bound := state.divisor.isLt; omega
    rw [nonresidue,ConcreteNTTWordRootConstruction.nonresidue,
      ConcreteNTTInitializedSearch.power_eq state correct candidate exponent candidateFits exponentFits]
    split
    · rfl
    · exact ih (candidate+1) (by omega)

def lift (state : State) (q s z : ℕ) : ℕ → ℕ → Outcome
  | 0,root => .root root
  | remaining+1,root =>
    match ConcreteNTTInitializedSquareRoot.sqrt state q s z root with
    | .root next => lift state q s z remaining next
    | .noRoot => .noRoot
    | .assertionFailure => .assertionFailure

theorem lift_eq (state : State) (correct : Correct state) (q s z steps root : ℕ)
    (qBound : q+1 < radix) (sBound : s ≤ 64) (zFits : z < radix) (rootFits : root < radix) :
    lift state q s z steps root = ConcreteNTTWordRootConstruction.lift state.divisor.val q s z steps root := by
  induction steps generalizing root with
  | zero => rfl
  | succ steps ih =>
    rw [lift,ConcreteNTTWordRootConstruction.lift,
      ConcreteNTTInitializedSquareRoot.sqrt_eq state correct q s z root qBound sBound zFits rootFits]
    cases computed : ConcreteNTTWordSquareRoot.sqrt state.divisor.val q s z root with
    | root next =>
      have nextBound := ConcreteNTTWordSquareRoot.sqrt_root_lt state.divisor.val q s z root next correct.1 state.divisor.isLt zFits rootFits computed
      exact ih next (nextBound.trans state.divisor.isLt)
    | noRoot => rfl
    | assertionFailure => rfl

def construct (state : State) (logSize : ℕ) : Outcome :=
  let modulus := state.divisor.val
  let parts := ConcreteNTTRootConstruction.factorTwos (modulus-1)
  match nonresidue state ((modulus-1)/2) (modulus-2) 2 with
  | none => .noRoot
  | some z => lift state parts.1 parts.2 z logSize (modulus-1)

theorem construct_eq (state : State) (correct : Correct state) (logSize : ℕ) (domain : 3 ≤ state.divisor.val) :
    construct state logSize = ConcreteNTTWordRootConstruction.construct state.divisor.val logSize := by
  have parameters := ConcreteNTTWordRootConstruction.parameters_fit state.divisor.val domain state.divisor.isLt
  have exponentFits : (state.divisor.val-1)/2 < radix := by
    have divided := Nat.div_le_self (state.divisor.val-1) 2
    have bound := state.divisor.isLt
    omega
  rw [construct,ConcreteNTTWordRootConstruction.construct,
    nonresidue_eq state correct ((state.divisor.val-1)/2) (state.divisor.val-2) 2 exponentFits (by omega)]
  cases selected : ConcreteNTTWordRootConstruction.nonresidue state.divisor.val ((state.divisor.val-1)/2) (state.divisor.val-2) 2 with
  | none => rfl
  | some z =>
    have zBound := ConcreteNTTWordRootConstruction.nonresidue_lt state.divisor.val ((state.divisor.val-1)/2) (state.divisor.val-2) 2 z (by omega) selected
    exact lift_eq state correct _ _ z logSize (state.divisor.val-1) parameters.1 (by omega)
      (zBound.trans state.divisor.isLt) (by have bound := state.divisor.isLt; omega)

def newRoot (divisor : Limb) (logSize : ℕ) : Outcome :=
  match ConcreteNTTDiv64Initialization.new divisor with
  | .assertionFailure => .assertionFailure
  | .initialized state => construct state logSize

theorem newRoot_eq (divisor : Limb) (logSize : ℕ) (domain : 3 ≤ divisor.val) :
    newRoot divisor logSize = ConcreteNTTWordRootConstruction.construct divisor.val logSize := by
  have valid : 1 < divisor.val := by omega
  have built : ConcreteNTTDiv64Initialization.new divisor = .initialized (ConcreteNTTDiv64Initialization.buildState divisor valid) := by
    simp only [ConcreteNTTDiv64Initialization.new,dite_eq_left valid]
  simp only [newRoot,built]
  exact construct_eq _ (ConcreteNTTDiv64Initialization.initialize_correct divisor valid) logSize domain

theorem newRoot_lt (divisor : Limb) (logSize answer : ℕ) (domain : 3 ≤ divisor.val)
    (returned : newRoot divisor logSize = .root answer) : answer < divisor.val := by
  rw [newRoot_eq divisor logSize domain] at returned
  exact ConcreteNTTWordRootConstruction.construct_root_lt divisor.val logSize answer domain divisor.isLt returned

theorem newRoot_primitive (divisor : Limb) [Fact (Nat.Prime divisor.val)] (logSize answer : ℕ)
    (domain : 3 ≤ divisor.val) (odd : (-1 : ZMod divisor.val) ≠ 1)
    (returned : newRoot divisor logSize = .root answer) : IsPrimitiveRoot (answer : ZMod divisor.val) (2^(logSize+1)) := by
  rw [newRoot_eq divisor logSize domain] at returned
  exact ConcreteNTTWordRootConstruction.construct_primitive divisor.val logSize answer domain divisor.isLt odd returned

theorem newRoot_rejected (divisor : Limb) (logSize : ℕ) (invalid : divisor.val ≤ 1) :
    newRoot divisor logSize = .assertionFailure := by
  have rejected := (ConcreteNTTDiv64Initialization.new_rejected divisor).mpr invalid
  simp only [newRoot,rejected]

def goldilocks (logSize : ℕ) : Outcome :=
  newRoot ⟨NativeFields.goldilocksModulus,by decide⟩ logSize

theorem goldilocks_primitive (logSize answer : ℕ) (returned : goldilocks logSize = .root answer) :
    IsPrimitiveRoot (answer : NativeFields.Goldilocks) (2^(logSize+1)) :=
  newRoot_primitive ⟨NativeFields.goldilocksModulus,by decide⟩ logSize answer (by decide) NativeFields.goldilocks_odd returned

end FormalProof4FHE.HasteBoots.ConcreteNTTInitializedRootConstruction
