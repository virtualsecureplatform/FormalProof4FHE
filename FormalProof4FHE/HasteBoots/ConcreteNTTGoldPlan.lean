module
public import FormalProof4FHE.HasteBoots.ConcreteNTTPlanConstants
@[expose] public section

/-! All original stored fields of the Goldilocks non-Shoup Plan constructor,
assembled from the literal proved stages. The input specializes polynomial size
to 2^logSize. No successful builder, arithmetic/root or array certificate is a
constructor input. This is word-formula semantics: allocation failure/effects,
Rust/Charon/Aeneas instruction/compiler and SIMD/cache/physical refinement are
still mandatory, separate obligations. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTGoldPlan
open ConcreteNTTLimbArithmetic (Limb radix)
open ConcreteNTTDiv64Initialization (State Correct)

structure Plan where
  root : Limb
  rootPowers : Array Limb
  rootPowersShoup : Array Limb
  twiddle : Array Limb
  twiddleShoup : Array Limb
  inverseTwiddle : Array Limb
  inverseTwiddleShoup : Array Limb
  modulus : Limb
  divisor : State
  pBarrett : Limb
  bigQ : Limb
  nInverse : Limb
  nInverseShoup : Limb
  reverseLsbs : Array ℕ
  deriving DecidableEq, Repr

def assemble (logSize : ℕ) (stage : ConcreteNTTConstructedTwiddles.Stage) : Plan :=
  let constants := ConcreteNTTPlanConstants.build stage.rootPowers.state (2^logSize) 64
  { root := stage.rootPowers.root
    rootPowers := stage.rootPowers.powers
    rootPowersShoup := #[]
    twiddle := stage.forward
    twiddleShoup := #[]
    inverseTwiddle := stage.inverse
    inverseTwiddleShoup := #[]
    modulus := ConcreteNTTPlanRootPowers.goldilocksDivisor
    divisor := stage.rootPowers.state
    pBarrett := constants.pBarrett
    bigQ := constants.bigQ
    nInverse := constants.nInverse
    nInverseShoup := constants.nInverseShoup
    reverseLsbs := ((List.range (2^logSize)).map (ConcreteNTTBitReverse.word logSize)).toArray }

inductive Outcome where
  | constructed (plan : Plan)
  | rejected
  | assertionFailure
  | indexFailure
  deriving DecidableEq, Repr

def goldilocks (logSize : ℕ) : Outcome :=
  match ConcreteNTTConstructedTwiddles.goldilocks logSize with
  | .rejected => .rejected
  | .assertionFailure => .assertionFailure
  | .indexFailure => .indexFailure
  | .prepared stage => .constructed (assemble logSize stage)

theorem origin (logSize : ℕ) (plan : Plan) (returned : goldilocks logSize = .constructed plan) :
    ∃ stage, ConcreteNTTConstructedTwiddles.goldilocks logSize = .prepared stage ∧ plan = assemble logSize stage := by
  unfold goldilocks at returned
  split at returned
  · cases returned
  · cases returned
  · cases returned
  · rename_i stage executed
    cases returned
    exact ⟨stage,executed,rfl⟩

theorem prefix_size_lt (logSize : ℕ) (table : ConcreteNTTPlanRootPowers.Table)
    (returned : ConcreteNTTPlanRootPowers.goldilocks logSize = .prepared table) :
    2^logSize < NativeFields.goldilocksModulus := by
  have root := ConcreteNTTPlanRootPowers.goldilocks_primitive logSize table returned
  have nonzero := root.ne_zero (by have positive : 0 < 2^(logSize+1) := Nat.pow_pos (by decide); omega)
  have divides : 2^(logSize+1) ∣ NativeFields.goldilocksModulus-1 := by
    rw [root.eq_orderOf]
    exact ZMod.orderOf_dvd_card_sub_one nonzero
  have bound := Nat.le_of_dvd (by decide : 0 < NativeFields.goldilocksModulus-1) divides
  have positive : 0 < 2^logSize := Nat.pow_pos (by decide)
  rw [Nat.pow_succ] at bound
  omega

structure Certified (plan : Plan) (logSize : ℕ) : Prop where
  modulus : plan.modulus = ConcreteNTTPlanRootPowers.goldilocksDivisor
  retainedDivisor : plan.divisor.divisor = plan.modulus
  initialized : Correct plan.divisor
  root : IsPrimitiveRoot (plan.root.val : NativeFields.Goldilocks) (2^(logSize+1))
  rootPowerLength : plan.rootPowers.size = 2*(2^logSize)
  rootPowerValues : ConcreteNTTRootPowerArray.Stored plan.divisor plan.root plan.rootPowers plan.rootPowers.size
  forwardLength : plan.twiddle.size = 2^logSize
  inverseLength : plan.inverseTwiddle.size = 2^logSize
  twiddleValues : ConcreteNTTTwiddleArray.Stored plan.divisor plan.root logSize plan.twiddle plan.inverseTwiddle (2^logSize)
  shoupArrays : plan.rootPowersShoup = #[] ∧ plan.twiddleShoup = #[] ∧ plan.inverseTwiddleShoup = #[]
  inverseCanonical : plan.nInverse.val < NativeFields.goldilocksModulus
  inverseField : ((2^logSize : ℕ) : NativeFields.Goldilocks)*(plan.nInverse.val : NativeFields.Goldilocks) = 1
  inverseShoup : plan.nInverseShoup.val = plan.nInverse.val*radix/NativeFields.goldilocksModulus
  bigQ : plan.bigQ.val = 64
  barrett : plan.pBarrett.val = 2^127/NativeFields.goldilocksModulus
  reverseLength : plan.reverseLsbs.size = 2^logSize
  reverseValue : ∀ (i : ℕ) (bound : i < plan.reverseLsbs.size), plan.reverseLsbs[i] = ConcreteNTTBitReverse.word logSize i
  reverseBound : ∀ (i : ℕ) (bound : i < plan.reverseLsbs.size), plan.reverseLsbs[i] < 2^logSize

theorem assemble_certified (logSize : ℕ) (stage : ConcreteNTTConstructedTwiddles.Stage)
    (returned : ConcreteNTTConstructedTwiddles.goldilocks logSize = .prepared stage) :
    Certified (assemble logSize stage) logSize := by
  have previous := ConcreteNTTConstructedTwiddles.goldilocks_origin logSize stage returned
  have certified := ConcreteNTTConstructedTwiddles.goldilocks_certified logSize stage returned
  have stateEq := ConcreteNTTPlanRootPowers.goldilocks_state logSize stage.rootPowers previous
  have modulusEq : stage.rootPowers.state.divisor.val = NativeFields.goldilocksModulus := by rw [stateEq]; rfl
  have divisorEq : stage.rootPowers.state.divisor = ConcreteNTTPlanRootPowers.goldilocksDivisor := by rw [stateEq]; rfl
  have sizeBound := prefix_size_lt logSize stage.rootPowers previous
  have domain := ConcreteNTTConstructedTwiddles.goldilocks_prefix_domain logSize stage.rootPowers previous
  have width : logSize ≤ 64 := by omega
  have fits : 2^logSize < radix := sizeBound.trans ConcreteNTTPlanRootPowers.goldilocksDivisor.isLt
  have correct := certified.1.1
  refine {
    modulus := rfl
    retainedDivisor := divisorEq
    initialized := correct
    root := ConcreteNTTPlanRootPowers.goldilocks_primitive logSize stage.rootPowers previous
    rootPowerLength := certified.1.2.1
    rootPowerValues := certified.1.2.2.1
    forwardLength := certified.2.1
    inverseLength := certified.2.2.1
    twiddleValues := certified.2.2.2
    shoupArrays := ⟨rfl,rfl,rfl⟩
    inverseCanonical := ?_
    inverseField := ?_
    inverseShoup := ?_
    bigQ := ConcreteNTTPlanConstants.goldilocks_bitLength _ modulusEq
    barrett := ConcreteNTTPlanConstants.goldilocks_barrett_formula _ modulusEq
    reverseLength := ?_
    reverseValue := ?_
    reverseBound := ?_ }
  · have canonical := ConcreteNTTPlanConstants.inverse_canonical stage.rootPowers.state correct (2^logSize) fits
    simpa only [assemble,ConcreteNTTPlanConstants.build,modulusEq] using canonical
  · change ((2^logSize : ℕ) : NativeFields.Goldilocks)*
      ((ConcreteNTTPlanConstants.inverse stage.rootPowers.state (2^logSize)).val : NativeFields.Goldilocks) = 1
    have value := ConcreteNTTPlanConstants.inverse_value stage.rootPowers.state correct (2^logSize) fits
    rw [modulusEq] at value
    rw [value,ZMod.natCast_mod]
    simp only [Nat.cast_pow]
    have nonzero : ((2^logSize : ℕ) : NativeFields.Goldilocks) ≠ 0 := by
      intro zero
      have divisible := (ZMod.natCast_eq_zero_iff (2^logSize) NativeFields.goldilocksModulus).mp zero
      have remainder := Nat.mod_eq_of_lt sizeBound
      have zeroRem := Nat.mod_eq_zero_of_dvd divisible
      have positive : 0 < 2^logSize := Nat.pow_pos (by decide)
      omega
    have exponent : NativeFields.goldilocksModulus-2+1 = NativeFields.goldilocksModulus-1 := by decide
    rw [mul_comm,← pow_succ,exponent]
    simpa only [Nat.cast_pow] using ZMod.pow_card_sub_one_eq_one nonzero
  · have value := ConcreteNTTPlanConstants.build_shoup64_value stage.rootPowers.state correct (2^logSize) fits
    simpa only [assemble,ConcreteNTTPlanConstants.build,modulusEq] using value
  · simp [assemble]
  · intro i bound
    simp [assemble]
  · intro i bound
    have value : (assemble logSize stage).reverseLsbs[i] = ConcreteNTTBitReverse.word logSize i := by simp [assemble]
    rw [value]
    exact ConcreteNTTBitReverse.word_lt logSize i width

theorem goldilocks_certified (logSize : ℕ) (plan : Plan) (returned : goldilocks logSize = .constructed plan) :
    Certified plan logSize := by
  obtain ⟨stage,executed,rfl⟩ := origin logSize plan returned
  exact assemble_certified logSize stage executed

theorem root_canonical (logSize : ℕ) (plan : Plan) (returned : goldilocks logSize = .constructed plan) :
    plan.root.val < NativeFields.goldilocksModulus := by
  obtain ⟨stage,executed,rfl⟩ := origin logSize plan returned
  have previous := ConcreteNTTConstructedTwiddles.goldilocks_origin logSize stage executed
  have rooted := ConcreteNTTConstructedTwiddles.goldilocks_prefix_root logSize stage.rootPowers previous
  have certified := ConcreteNTTPlanRootPowers.goldilocks_certified logSize stage.rootPowers previous
  have stateEq := ConcreteNTTPlanRootPowers.goldilocks_state logSize stage.rootPowers previous
  have modulusEq : stage.rootPowers.state.divisor.val = NativeFields.goldilocksModulus := by rw [stateEq]; rfl
  have domain : 3 ≤ stage.rootPowers.state.divisor.val := by rw [modulusEq]; decide
  rw [ConcreteNTTInitializedRootConstruction.construct_eq stage.rootPowers.state certified.1 logSize domain] at rooted
  have bound := ConcreteNTTWordRootConstruction.construct_root_lt stage.rootPowers.state.divisor.val logSize
    stage.rootPowers.root.val domain stage.rootPowers.state.divisor.isLt rooted
  simpa only [assemble,modulusEq] using bound

theorem original_initialization (logSize : ℕ) (plan : Plan) (returned : goldilocks logSize = .constructed plan) :
    ConcreteNTTDiv64Initialization.new plan.modulus = .initialized plan.divisor := by
  obtain ⟨stage,executed,rfl⟩ := origin logSize plan returned
  have previous := ConcreteNTTConstructedTwiddles.goldilocks_origin logSize stage executed
  exact ConcreteNTTPlanRootPowers.goldilocks_original_init logSize stage.rootPowers previous

theorem no_indexFailure (logSize : ℕ) : goldilocks logSize ≠ .indexFailure := by
  unfold goldilocks
  cases executed : ConcreteNTTConstructedTwiddles.goldilocks logSize with
  | rejected => exact Outcome.noConfusion
  | assertionFailure => exact Outcome.noConfusion
  | indexFailure => exact (ConcreteNTTConstructedTwiddles.goldilocks_no_indexFailure logSize executed).elim
  | prepared stage => exact Outcome.noConfusion

end FormalProof4FHE.HasteBoots.ConcreteNTTGoldPlan
