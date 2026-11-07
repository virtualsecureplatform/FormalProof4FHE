module
public import FormalProof4FHE.HasteBoots.ConcreteNTTTwiddleArray
@[expose] public section

/-! The original non-Shoup twiddle initializer constructs a separate Div64 state
and calls the root constructor again. Its unwrap failure is assertion failure,
not Plan rejection. An actual accepted Goldilocks root-power prefix determines
that repeated state/root and supplies paired-array construction internally.
This is not yet a complete Plan/cache or Rust/physical refinement. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTConstructedTwiddles
open ConcreteNTTLimbArithmetic (Limb)
open ConcreteNTTDiv64Initialization (State Correct)

structure Tables where
  state : State
  root : Limb
  forward : Array Limb
  inverse : Array Limb
  deriving DecidableEq, Repr

inductive Outcome where
  | initializedTables (tables : Tables)
  | assertionFailure
  | indexFailure
  deriving DecidableEq, Repr

def build (divisor : Limb) (logSize : ℕ) : Outcome :=
  match ConcreteNTTDiv64Initialization.new divisor with
  | .assertionFailure => .assertionFailure
  | .initialized state =>
    match ConcreteNTTInitializedRootConstruction.construct state logSize with
    | .noRoot => .assertionFailure
    | .assertionFailure => .assertionFailure
    | .root answer =>
      let root := ConcreteNTTInitializedSearch.word answer
      match ConcreteNTTTwiddleArray.build state root logSize with
      | none => .indexFailure
      | some arrays => .initializedTables ⟨state,root,arrays.1,arrays.2⟩

theorem prefix_finish_root (state : State) (correct : Correct state) (domain : 3 ≤ state.divisor.val)
    (logSize size : ℕ) (table : ConcreteNTTPlanRootPowers.Table)
    (returned : ConcreteNTTPlanRootPowers.finish state logSize size = .prepared table) :
    ConcreteNTTInitializedRootConstruction.construct table.state logSize = .root table.root.val := by
  unfold ConcreteNTTPlanRootPowers.finish at returned
  cases rootResult : ConcreteNTTInitializedRootConstruction.construct state logSize with
  | noRoot => simp only [rootResult] at returned; cases returned
  | assertionFailure => simp only [rootResult] at returned; cases returned
  | root answer =>
    simp only [rootResult] at returned
    have wordResult : ConcreteNTTWordRootConstruction.construct state.divisor.val logSize = .root answer := by
      rw [← ConcreteNTTInitializedRootConstruction.construct_eq state correct logSize domain]
      exact rootResult
    have bound := ConcreteNTTWordRootConstruction.construct_root_lt state.divisor.val logSize answer domain state.divisor.isLt wordResult
    cases arrays : ConcreteNTTRootPowerArray.build state (2*size) (ConcreteNTTInitializedSearch.word answer) with
    | none => rw [arrays] at returned; cases returned
    | some powers =>
      rw [arrays] at returned
      cases returned
      rw [ConcreteNTTInitializedSearch.word_value answer (bound.trans state.divisor.isLt)]
      exact rootResult

theorem goldilocks_prefix_root (logSize : ℕ) (table : ConcreteNTTPlanRootPowers.Table)
    (returned : ConcreteNTTPlanRootPowers.goldilocks logSize = .prepared table) :
    ConcreteNTTInitializedRootConstruction.construct table.state logSize = .root table.root.val := by
  have valid : 1 < ConcreteNTTPlanRootPowers.goldilocksDivisor.val := by decide
  simp only [ConcreteNTTPlanRootPowers.goldilocks,ConcreteNTTDiv64Initialization.new,dite_eq_left valid] at returned
  split at returned
  · cases returned
  · rw [ConcreteNTTPlanRootPowers.goldilocks_prime_gate] at returned
    exact prefix_finish_root _ (ConcreteNTTDiv64Initialization.initialize_correct _ valid)
      (by change 3 ≤ NativeFields.goldilocksModulus; decide) logSize (2^logSize) table returned

theorem goldilocks_prefix_order_fits (logSize : ℕ) (table : ConcreteNTTPlanRootPowers.Table)
    (returned : ConcreteNTTPlanRootPowers.goldilocks logSize = .prepared table) :
    2^(logSize+1) < ConcreteNTTLimbArithmetic.radix := by
  have root := ConcreteNTTPlanRootPowers.goldilocks_primitive logSize table returned
  have nonzero := root.ne_zero (by have positive : 0 < 2^(logSize+1) := Nat.pow_pos (by decide); omega)
  have divides : 2^(logSize+1) ∣ NativeFields.goldilocksModulus-1 := by
    rw [root.eq_orderOf]
    exact ZMod.orderOf_dvd_card_sub_one nonzero
  have bound := Nat.le_of_dvd (by decide : 0 < NativeFields.goldilocksModulus-1) divides
  have fieldFits := ConcreteNTTPlanRootPowers.goldilocksDivisor.isLt
  change NativeFields.goldilocksModulus < ConcreteNTTLimbArithmetic.radix at fieldFits
  omega

theorem goldilocks_prefix_domain (logSize : ℕ) (table : ConcreteNTTPlanRootPowers.Table)
    (returned : ConcreteNTTPlanRootPowers.goldilocks logSize = .prepared table) :
    4 ≤ logSize ∧ logSize+1 < 64 ∧ 2*(2^logSize) < ConcreteNTTLimbArithmetic.radix ∧ 64-logSize < 64 := by
  have fits := goldilocks_prefix_order_fits logSize table returned
  have exponent : logSize+1 < 64 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp fits
  have orderFits : 2*(2^logSize) < ConcreteNTTLimbArithmetic.radix := by
    simpa only [Nat.pow_succ,Nat.mul_comm] using fits
  have valid : 1 < ConcreteNTTPlanRootPowers.goldilocksDivisor.val := by decide
  simp only [ConcreteNTTPlanRootPowers.goldilocks,ConcreteNTTDiv64Initialization.new,dite_eq_left valid] at returned
  split at returned
  · cases returned
  · rename_i notSmall
    have lower : 4 ≤ logSize := by
      by_contra below
      have cases : logSize = 0 ∨ logSize = 1 ∨ logSize = 2 ∨ logSize = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl <;> norm_num at notSmall
    exact ⟨lower,exponent,orderFits,by omega⟩

theorem goldilocks_after_prefix (logSize : ℕ)
    (table : ConcreteNTTPlanRootPowers.Table)
    (returned : ConcreteNTTPlanRootPowers.goldilocks logSize = .prepared table) :
    ∃ tables, build ConcreteNTTPlanRootPowers.goldilocksDivisor logSize = .initializedTables tables ∧
      tables.state = table.state ∧ tables.root = table.root ∧
      tables.forward.size = 2^logSize ∧ tables.inverse.size = 2^logSize ∧
      ConcreteNTTTwiddleArray.Stored table.state table.root logSize tables.forward tables.inverse (2^logSize) := by
  have width : logSize ≤ 64 := by have domain := goldilocks_prefix_domain logSize table returned; omega
  have initialized := ConcreteNTTPlanRootPowers.goldilocks_original_init logSize table returned
  have rooted := goldilocks_prefix_root logSize table returned
  have certified := ConcreteNTTPlanRootPowers.goldilocks_certified logSize table returned
  have wordSame : ConcreteNTTInitializedSearch.word table.root.val = table.root := by
    apply Fin.ext
    exact ConcreteNTTInitializedSearch.word_value table.root.val table.root.isLt
  obtain ⟨arrays,built,lengthF,lengthI,contents⟩ := ConcreteNTTTwiddleArray.build_correct table.state certified.1 table.root logSize width
  refine ⟨⟨table.state,table.root,arrays.1,arrays.2⟩,?_,rfl,rfl,lengthF,lengthI,contents⟩
  simp only [build,initialized,rooted,wordSame,built]

structure Stage where
  rootPowers : ConcreteNTTPlanRootPowers.Table
  forward : Array Limb
  inverse : Array Limb
  deriving DecidableEq, Repr

inductive StageOutcome where
  | prepared (stage : Stage)
  | rejected
  | assertionFailure
  | indexFailure
  deriving DecidableEq, Repr

def goldilocks (logSize : ℕ) : StageOutcome :=
  match ConcreteNTTPlanRootPowers.goldilocks logSize with
  | .rejected => .rejected
  | .assertionFailure => .assertionFailure
  | .indexFailure => .indexFailure
  | .prepared rootPowers =>
    match build ConcreteNTTPlanRootPowers.goldilocksDivisor logSize with
    | .assertionFailure => .assertionFailure
    | .indexFailure => .indexFailure
    | .initializedTables tables => .prepared ⟨rootPowers,tables.forward,tables.inverse⟩

def Certified (stage : Stage) (logSize : ℕ) : Prop :=
  ConcreteNTTPlanRootPowers.Certified stage.rootPowers logSize (2^logSize) ∧
  stage.forward.size = 2^logSize ∧ stage.inverse.size = 2^logSize ∧
  ConcreteNTTTwiddleArray.Stored stage.rootPowers.state stage.rootPowers.root logSize
    stage.forward stage.inverse (2^logSize)

theorem goldilocks_certified (logSize : ℕ) (stage : Stage)
    (returned : goldilocks logSize = .prepared stage) : Certified stage logSize := by
  unfold goldilocks at returned
  cases priorResult : ConcreteNTTPlanRootPowers.goldilocks logSize with
  | rejected => simp only [priorResult] at returned; cases returned
  | assertionFailure => simp only [priorResult] at returned; cases returned
  | indexFailure => simp only [priorResult] at returned; cases returned
  | prepared rootPowers =>
    simp only [priorResult] at returned
    obtain ⟨tables,built,_,_,lengthF,lengthI,contents⟩ := goldilocks_after_prefix logSize rootPowers priorResult
    rw [built] at returned
    cases returned
    exact ⟨ConcreteNTTPlanRootPowers.goldilocks_certified logSize rootPowers priorResult,lengthF,lengthI,contents⟩

theorem goldilocks_origin (logSize : ℕ) (stage : Stage)
    (returned : goldilocks logSize = .prepared stage) :
    ConcreteNTTPlanRootPowers.goldilocks logSize = .prepared stage.rootPowers := by
  unfold goldilocks at returned
  split at returned
  · cases returned
  · cases returned
  · cases returned
  · rename_i rootPowers priorResult
    split at returned
    · cases returned
    · cases returned
    · cases returned
      exact priorResult

theorem goldilocks_no_indexFailure (logSize : ℕ) : goldilocks logSize ≠ .indexFailure := by
  unfold goldilocks
  cases priorResult : ConcreteNTTPlanRootPowers.goldilocks logSize with
  | rejected => exact StageOutcome.noConfusion
  | assertionFailure => exact StageOutcome.noConfusion
  | indexFailure => exact (ConcreteNTTPlanRootPowers.goldilocks_no_indexFailure logSize priorResult).elim
  | prepared rootPowers =>
    obtain ⟨tables,built,_,_,_,_,_⟩ := goldilocks_after_prefix logSize rootPowers priorResult
    simp only [built]
    exact StageOutcome.noConfusion

theorem goldilocks_canonical_tables (logSize : ℕ) (stage : Stage)
    (returned : goldilocks logSize = .prepared stage) (index : ℕ) (bound : index < 2^logSize) :
    ∃ fwd inv : Limb,
      stage.forward[ConcreteNTTTwiddleIndices.forward logSize index]? = some fwd ∧
      stage.inverse[ConcreteNTTTwiddleIndices.inverse logSize index]? = some inv ∧
      fwd.val < NativeFields.goldilocksModulus ∧ inv.val < NativeFields.goldilocksModulus := by
  have certified := goldilocks_certified logSize stage returned
  have origin := goldilocks_origin logSize stage returned
  have stateEq := ConcreteNTTPlanRootPowers.goldilocks_state logSize stage.rootPowers origin
  have modulusEq : stage.rootPowers.state.divisor.val = NativeFields.goldilocksModulus := by rw [stateEq]; rfl
  let : Fact (Nat.Prime stage.rootPowers.state.divisor.val) := ⟨by rw [modulusEq]; exact NativeFields.goldilocks_prime⟩
  have correct := certified.1.1
  have root := certified.1.2.2.2
  have nonzero := root.ne_zero (by have positive : 0 < 2^(logSize+1) := Nat.pow_pos (by decide); omega)
  obtain ⟨forwardStored,inverseStored⟩ := certified.2.2.2 index bound
  refine ⟨_,_,forwardStored,inverseStored,?_,?_⟩
  · simpa only [modulusEq] using ConcreteNTTTwiddleArray.powerWord_canonical stage.rootPowers.state correct stage.rootPowers.root index
  · simpa only [modulusEq] using ConcreteNTTTwiddleArray.inverseWord_canonical stage.rootPowers.state correct stage.rootPowers.root nonzero index

theorem goldilocks_field_tables (logSize : ℕ) (stage : Stage)
    (returned : goldilocks logSize = .prepared stage) (index : ℕ) (bound : index < 2^logSize) :
    ∃ fwd inv : Limb,
      stage.forward[ConcreteNTTTwiddleIndices.forward logSize index]? = some fwd ∧
      stage.inverse[ConcreteNTTTwiddleIndices.inverse logSize index]? = some inv ∧
      (fwd.val : NativeFields.Goldilocks) = (stage.rootPowers.root.val : NativeFields.Goldilocks)^index ∧
      (inv.val : NativeFields.Goldilocks) =
        if index = 0 then 1 else -(stage.rootPowers.root.val : NativeFields.Goldilocks)^index := by
  have certified := goldilocks_certified logSize stage returned
  have origin := goldilocks_origin logSize stage returned
  have stateEq := ConcreteNTTPlanRootPowers.goldilocks_state logSize stage.rootPowers origin
  have modulusEq : stage.rootPowers.state.divisor.val = NativeFields.goldilocksModulus := by rw [stateEq]; rfl
  obtain ⟨forwardStored,inverseStored⟩ := certified.2.2.2 index bound
  refine ⟨_,_,forwardStored,inverseStored,?_,?_⟩
  · have value := ConcreteNTTTwiddleArray.powerWord_cast stage.rootPowers.state certified.1.1 stage.rootPowers.root index
    rw [modulusEq] at value
    exact value
  · have value := ConcreteNTTTwiddleArray.inverseWord_cast stage.rootPowers.state certified.1.1 stage.rootPowers.root index
    rw [modulusEq] at value
    exact value

end FormalProof4FHE.HasteBoots.ConcreteNTTConstructedTwiddles
