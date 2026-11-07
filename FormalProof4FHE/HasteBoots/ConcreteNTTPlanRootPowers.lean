module
public import FormalProof4FHE.HasteBoots.ConcreteNTTRootPowerArray
public import FormalProof4FHE.HasteBoots.ConcreteNTTPrimeGate
@[expose] public section

/-! The original Goldilocks Plan constructor prefix through root-power writes.
The first Div64 state is retained through root construction and array filling;
the separate prime gate executes in its original position. This is explicitly
a constructor prefix, not a complete Plan: twiddle initialization, inverse and
Barrett constants, reverse indices, allocation/machine and cache refinement
remain obligations. The log-size input specializes the original power-of-two
size path; usize casts/overflow still require machine refinement. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTPlanRootPowers
open ConcreteNTTLimbArithmetic (Limb radix)
open ConcreteNTTDiv64Initialization (State Correct)

structure Table where
  state : State
  root : Limb
  powers : Array Limb
  deriving DecidableEq, Repr

inductive Outcome where
  | prepared (table : Table)
  | rejected
  | assertionFailure
  | indexFailure
  deriving DecidableEq, Repr

def finish (state : State) (logSize size : ℕ) : Outcome :=
  match ConcreteNTTInitializedRootConstruction.construct state logSize with
  | .noRoot => .rejected
  | .assertionFailure => .assertionFailure
  | .root answer =>
    let root := ConcreteNTTInitializedSearch.word answer
    match ConcreteNTTRootPowerArray.build state (2*size) root with
    | none => .indexFailure
    | some powers => .prepared ⟨state,root,powers⟩

def Certified (table : Table) (logSize size : ℕ) : Prop :=
  Correct table.state ∧ table.powers.size = 2*size ∧
  ConcreteNTTRootPowerArray.Stored table.state table.root table.powers table.powers.size ∧
  IsPrimitiveRoot (table.root.val : ZMod table.state.divisor.val) (2^(logSize+1))

theorem finish_certified (state : State) (correct : Correct state)
    [Fact (Nat.Prime state.divisor.val)] (domain : 3 ≤ state.divisor.val)
    (odd : (-1 : ZMod state.divisor.val) ≠ 1) (logSize size : ℕ)
    (sizePositive : 1 ≤ size) (table : Table) (returned : finish state logSize size = .prepared table) :
    Certified table logSize size := by
  unfold finish at returned
  cases rootResult : ConcreteNTTInitializedRootConstruction.construct state logSize with
  | noRoot => simp only [rootResult] at returned; cases returned
  | assertionFailure => simp only [rootResult] at returned; cases returned
  | root answer =>
    simp only [rootResult] at returned
    have wordResult : ConcreteNTTWordRootConstruction.construct state.divisor.val logSize = .root answer := by
      rw [← ConcreteNTTInitializedRootConstruction.construct_eq state correct logSize domain]
      exact rootResult
    have bound := ConcreteNTTWordRootConstruction.construct_root_lt state.divisor.val logSize answer domain state.divisor.isLt wordResult
    have fits : answer < radix := bound.trans state.divisor.isLt
    have wordValue := ConcreteNTTInitializedSearch.word_value answer fits
    have canonical : (ConcreteNTTInitializedSearch.word answer).val < state.divisor.val := by rw [wordValue]; exact bound
    obtain ⟨powers,built,length,stored⟩ := ConcreteNTTRootPowerArray.build_correct state correct (2*size)
      (ConcreteNTTInitializedSearch.word answer) (by omega) canonical
    rw [built] at returned
    cases returned
    refine ⟨correct,length,stored,?_⟩
    rw [wordValue]
    exact ConcreteNTTWordRootConstruction.construct_primitive state.divisor.val logSize answer domain state.divisor.isLt odd wordResult

theorem finish_state (state : State) (logSize size : ℕ) (table : Table)
    (returned : finish state logSize size = .prepared table) : table.state = state := by
  unfold finish at returned
  split at returned
  · cases returned
  · cases returned
  · dsimp only at returned
    split at returned
    · cases returned
    · cases returned
      rfl

theorem finish_no_indexFailure (state : State) (correct : Correct state)
    (domain : 3 ≤ state.divisor.val) (logSize size : ℕ) (sizePositive : 1 ≤ size) :
    finish state logSize size ≠ .indexFailure := by
  unfold finish
  cases rootResult : ConcreteNTTInitializedRootConstruction.construct state logSize with
  | noRoot => simp
  | assertionFailure => simp
  | root answer =>
    have wordResult : ConcreteNTTWordRootConstruction.construct state.divisor.val logSize = .root answer := by
      rw [← ConcreteNTTInitializedRootConstruction.construct_eq state correct logSize domain]
      exact rootResult
    have bound := ConcreteNTTWordRootConstruction.construct_root_lt state.divisor.val logSize answer domain state.divisor.isLt wordResult
    have canonical : (ConcreteNTTInitializedSearch.word answer).val < state.divisor.val := by
      rw [ConcreteNTTInitializedSearch.word_value answer (bound.trans state.divisor.isLt)]
      exact bound
    obtain ⟨powers,built,_,_⟩ := ConcreteNTTRootPowerArray.build_correct state correct (2*size)
      (ConcreteNTTInitializedSearch.word answer) (by omega) canonical
    simp only [built]
    exact Outcome.noConfusion

def goldilocksDivisor : Limb := ⟨NativeFields.goldilocksModulus,by decide⟩

theorem goldilocks_prime_gate : ConcreteNTTPrimeGate.check goldilocksDivisor = .checked true :=
  ConcreteNTTPrimeGate.goldilocks_passes

def goldilocks (logSize : ℕ) : Outcome :=
  match ConcreteNTTDiv64Initialization.new goldilocksDivisor with
  | .assertionFailure => .assertionFailure
  | .initialized state =>
    if 2^logSize < 16 then .rejected else
      match ConcreteNTTPrimeGate.check goldilocksDivisor with
      | .assertionFailure => .assertionFailure
      | .checked false => .rejected
      | .checked true => finish state logSize (2^logSize)

theorem goldilocks_certified (logSize : ℕ) (table : Table)
    (returned : goldilocks logSize = .prepared table) : Certified table logSize (2^logSize) := by
  have valid : 1 < goldilocksDivisor.val := by decide
  let state := ConcreteNTTDiv64Initialization.buildState goldilocksDivisor valid
  have initialized : ConcreteNTTDiv64Initialization.new goldilocksDivisor = .initialized state := by
    simp only [ConcreteNTTDiv64Initialization.new,dite_eq_left valid]
    rfl
  simp only [goldilocks,initialized] at returned
  split at returned
  · cases returned
  · rw [goldilocks_prime_gate] at returned
    let : Fact (Nat.Prime state.divisor.val) := ⟨NativeFields.goldilocks_prime⟩
    exact finish_certified state (ConcreteNTTDiv64Initialization.initialize_correct goldilocksDivisor valid)
      (by change 3 ≤ NativeFields.goldilocksModulus; decide) NativeFields.goldilocks_odd logSize (2^logSize) (by have positive : 0 < 2^logSize := Nat.pow_pos (by decide); omega) table returned

theorem goldilocks_state (logSize : ℕ) (table : Table)
    (returned : goldilocks logSize = .prepared table) :
    table.state = ConcreteNTTDiv64Initialization.buildState goldilocksDivisor (by decide) := by
  have valid : 1 < goldilocksDivisor.val := by decide
  simp only [goldilocks,ConcreteNTTDiv64Initialization.new,dite_eq_left valid] at returned
  split at returned
  · cases returned
  · rw [goldilocks_prime_gate] at returned
    exact finish_state _ logSize (2^logSize) table returned

theorem goldilocks_primitive (logSize : ℕ) (table : Table)
    (returned : goldilocks logSize = .prepared table) :
    IsPrimitiveRoot (table.root.val : NativeFields.Goldilocks) (2^(logSize+1)) := by
  have certified := goldilocks_certified logSize table returned
  have stateEq := goldilocks_state logSize table returned
  have primeRoot := certified.2.2.2
  have modulusEq : table.state.divisor.val = NativeFields.goldilocksModulus := by rw [stateEq]; rfl
  rw [modulusEq] at primeRoot
  exact primeRoot

theorem goldilocks_values (logSize : ℕ) (table : Table)
    (returned : goldilocks logSize = .prepared table) (i : ℕ) (bound : i < table.powers.size) :
    (table.powers[i]).val = table.root.val^i % NativeFields.goldilocksModulus := by
  have certified := goldilocks_certified logSize table returned
  have entry := ConcreteNTTRootPowerArray.stored_value table.state certified.1 table.root
    table.powers table.powers.size certified.2.2.1 i bound bound
  have stateEq := goldilocks_state logSize table returned
  have modulusEq : table.state.divisor.val = NativeFields.goldilocksModulus := by rw [stateEq]; rfl
  simpa only [modulusEq] using entry

theorem goldilocks_original_init (logSize : ℕ) (table : Table)
    (returned : goldilocks logSize = .prepared table) :
    ConcreteNTTDiv64Initialization.new goldilocksDivisor = .initialized table.state := by
  rw [goldilocks_state logSize table returned]
  simp only [ConcreteNTTDiv64Initialization.new,dite_eq_left (by decide : 1 < goldilocksDivisor.val)]

theorem goldilocks_branches : ¬goldilocksDivisor.val < 2^63 ∧ ¬goldilocksDivisor.val < 2^51 := by decide

theorem goldilocks_no_indexFailure (logSize : ℕ) : goldilocks logSize ≠ .indexFailure := by
  have valid : 1 < goldilocksDivisor.val := by decide
  simp only [goldilocks,ConcreteNTTDiv64Initialization.new,dite_eq_left valid]
  split
  · exact Outcome.noConfusion
  · rw [goldilocks_prime_gate]
    exact finish_no_indexFailure _ (ConcreteNTTDiv64Initialization.initialize_correct goldilocksDivisor valid)
      (by change 3 ≤ NativeFields.goldilocksModulus; decide) logSize (2^logSize) (by have positive : 0 < 2^logSize := Nat.pow_pos (by decide); omega)

end FormalProof4FHE.HasteBoots.ConcreteNTTPlanRootPowers
