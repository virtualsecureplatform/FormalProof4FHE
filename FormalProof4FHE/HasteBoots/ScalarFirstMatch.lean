module
public import FormalProof4FHE.HasteBoots.ScalarPriorStability
@[expose] public section

/-! A finite native run which reaches the selected reader has a least
matching control state. Stopped replay retains that exact original state and
log, independent of unused auxiliary budget. -/
namespace FormalProof4FHE.HasteBoots.ScalarFirstMatch
open InputIndexedOracle (Input World)
open NativeScalarBatchWire (Statement)
open NativeScalarBatchPreflight (Proof)
open NativeScalarBatchVerifier (Machine)

/-- Once native execution reaches its first matching reader, extra stopped
replay budget adds no observations or machine transitions. -/
theorem at_first (target : Input) (statement : Statement) (proof : Proof) (used budget : ℕ)
    (machine : Machine) (world : World) (enough : used ≤ budget)
    (matched : ScalarStoppedReplay.blocked target (NativeScalarBatchVerifier.execute statement proof used machine world).1 = true)
    (earlier : ∀ index < used, ScalarStoppedReplay.blocked target
      (NativeScalarBatchVerifier.execute statement proof index machine world).1 = false) :
    ScalarStoppedReplay.execute target statement proof budget machine world =
      ((true,(NativeScalarBatchVerifier.execute statement proof used machine world).1),
        (NativeScalarBatchVerifier.execute statement proof used machine world).2) := by
  induction used generalizing budget machine with
  | zero => exact ScalarStoppedReplay.stopped target statement proof budget machine world matched
  | succ used ih =>
    cases budget with
    | zero => omega
    | succ budget =>
      have allowed := earlier 0 (Nat.zero_lt_succ used)
      change ScalarStoppedReplay.blocked target machine = false at allowed
      have tail : ∀ index < used, ScalarStoppedReplay.blocked target
          (NativeScalarBatchVerifier.execute statement proof index
            (NativeScalarBatchVerifier.tickExecute statement proof machine world).1 world).1 = false := by
        intro index bound
        simpa only [NativeScalarBatchVerifier.execute] using earlier (index + 1) (by omega)
      have stopped := ih budget (NativeScalarBatchVerifier.tickExecute statement proof machine world).1
        (by omega) matched tail
      simp only [ScalarStoppedReplay.execute,allowed,Bool.false_eq_true,ite_false,stopped,NativeScalarBatchVerifier.execute]

/-- First matching time is bounded by the supplied original execution prefix.
It is a witness for analysis, not a runtime sampler-attempt cap. -/
theorem exists_first (target : Input) (statement : Statement) (proof : Proof) (fuel : ℕ)
    (machine : Machine) (world : World)
    (matched : ScalarStoppedReplay.blocked target (NativeScalarBatchVerifier.execute statement proof fuel machine world).1 = true) :
    ∃ used ≤ fuel,
      ScalarStoppedReplay.blocked target (NativeScalarBatchVerifier.execute statement proof used machine world).1 = true ∧
      (∀ index < used, ScalarStoppedReplay.blocked target (NativeScalarBatchVerifier.execute statement proof index machine world).1 = false) ∧
      ScalarStoppedReplay.execute target statement proof fuel machine world =
        ((true,(NativeScalarBatchVerifier.execute statement proof used machine world).1),
          (NativeScalarBatchVerifier.execute statement proof used machine world).2) := by
  let possible : ∃ used, ScalarStoppedReplay.blocked target (NativeScalarBatchVerifier.execute statement proof used machine world).1 = true := ⟨fuel,matched⟩
  let used := Nat.find possible
  have hit := Nat.find_spec possible
  have bound : used ≤ fuel := Nat.find_min' possible matched
  have prior : ∀ index < used, ScalarStoppedReplay.blocked target (NativeScalarBatchVerifier.execute statement proof index machine world).1 = false := by
    intro index inside
    exact Bool.eq_false_iff.mpr (Nat.find_min possible inside)
  exact ⟨used,bound,hit,prior,at_first target statement proof used fuel machine world bound hit prior⟩

/-- Once stopped replay reports a match, increasing its auxiliary budget
cannot change either the retained machine or its ordered observation log. -/
theorem stable_add (target : Input) (statement : Statement) (proof : Proof) (first extra : ℕ)
    (machine : Machine) (world : World)
    (matched : (ScalarStoppedReplay.execute target statement proof first machine world).1.1 = true) :
    ScalarStoppedReplay.execute target statement proof (first + extra) machine world =
      ScalarStoppedReplay.execute target statement proof first machine world := by
  induction first generalizing machine with
  | zero =>
    change ScalarStoppedReplay.blocked target machine = true at matched
    rw [Nat.zero_add,ScalarStoppedReplay.stopped target statement proof extra machine world matched]
    simp only [ScalarStoppedReplay.execute,matched]
  | succ first ih =>
    by_cases stop : ScalarStoppedReplay.blocked target machine = true
    · simp only [Nat.succ_add,ScalarStoppedReplay.execute,stop,ite_true]
    · have allowed : ScalarStoppedReplay.blocked target machine = false := Bool.eq_false_iff.mpr stop
      simp only [Nat.succ_add,ScalarStoppedReplay.execute,allowed,Bool.false_eq_true,ite_false] at matched ⊢
      rw [ih _ matched]

theorem stable (target : Input) (statement : Statement) (proof : Proof) (first later : ℕ) (ordered : first ≤ later)
    (machine : Machine) (world : World)
    (matched : (ScalarStoppedReplay.execute target statement proof first machine world).1.1 = true) :
    ScalarStoppedReplay.execute target statement proof later machine world =
      ScalarStoppedReplay.execute target statement proof first machine world := by
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le ordered
  exact stable_add target statement proof first extra machine world matched

end FormalProof4FHE.HasteBoots.ScalarFirstMatch
