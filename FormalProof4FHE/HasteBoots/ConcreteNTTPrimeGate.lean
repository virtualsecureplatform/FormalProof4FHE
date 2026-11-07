module
public import FormalProof4FHE.HasteBoots.ConcreteNTTMillerRabinRound
public import FormalProof4FHE.HasteBoots.ConcreteNTTWordRootConstruction
@[expose] public section

/-! Literal twelve-base prime::is_prime64 gate from locked concrete-ntt. Small
prime exits, factorization, a separate Div64 initialization and ordered rounds
are retained. Prime-input completeness is proved, including the fixed native
fields; generic twelve-base composite-test soundness, machine/compiler and
physical refinement remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTPrimeGate
open ConcreteNTTLimbArithmetic (radix Limb)
open ConcreteNTTDiv64Initialization (State)

def bases : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37]

def smallTrials (n : ℕ) : List ℕ → Option Bool
  | [] => none
  | p::tail => if n%p = 0 then some (decide (n = p)) else smallTrials n tail

def rounds (state : State) (s q : ℕ) : List ℕ → Bool
  | [] => true
  | base::tail => if ConcreteNTTMillerRabinRound.round state s q base then rounds state s q tail else false

inductive Outcome where
  | checked (result : Bool)
  | assertionFailure
  deriving DecidableEq, Repr

def check (modulus : Limb) : Outcome :=
  if modulus.val < 2 then .checked false else
    match smallTrials modulus.val bases with
    | some result => .checked result
    | none =>
      let parts := ConcreteNTTRootConstruction.factorTwos (modulus.val-1)
      match ConcreteNTTDiv64Initialization.new modulus with
      | .assertionFailure => .assertionFailure
      | .initialized state => .checked (rounds state parts.2 parts.1 bases)

theorem bases_prime : ∀ base ∈ bases, Nat.Prime base := by norm_num [bases]
theorem bases_bounds : ∀ base ∈ bases, 2 ≤ base ∧ base < radix := by norm_num [bases,radix]

theorem smallTrials_none (n : ℕ) (candidates : List ℕ) :
    smallTrials n candidates = none ↔ ∀ base ∈ candidates, n%base ≠ 0 := by
  induction candidates with
  | nil => simp [smallTrials]
  | cons base tail ih =>
    by_cases divisible : n%base = 0 <;> simp [smallTrials,divisible,ih]

theorem smallTrials_prime (n : ℕ) (prime : Nat.Prime n) (candidates : List ℕ)
    (bounds : ∀ base ∈ candidates, 2 ≤ base) (answer : Bool)
    (returned : smallTrials n candidates = some answer) : answer = true := by
  induction candidates with
  | nil => cases returned
  | cons base tail ih =>
    simp only [smallTrials] at returned
    split at returned
    · rename_i divisible
      have bound := bounds base (List.mem_cons_self)
      rcases prime.eq_one_or_self_of_dvd base (Nat.dvd_of_mod_eq_zero divisible) with one | same
      · omega
      · subst base
        simpa only [decide_true] using (Option.some.inj returned).symm
    · exact ih (fun b member => bounds b (List.mem_cons_of_mem _ member)) returned

theorem rounds_pass (state : State) (correct : ConcreteNTTDiv64Initialization.Correct state)
    [Fact (Nat.Prime state.divisor.val)] (s q : ℕ) (qFits : q < radix)
    (decomposition : state.divisor.val-1 = q*2^s) (candidates : List ℕ)
    (valid : ∀ base ∈ candidates, base < radix ∧ (base : ZMod state.divisor.val) ≠ 0) :
    rounds state s q candidates = true := by
  induction candidates with
  | nil => rfl
  | cons base tail ih =>
    have baseValid := valid base (List.mem_cons_self)
    rw [rounds,ConcreteNTTMillerRabinRound.round_passes state correct s q base qFits baseValid.1 baseValid.2 decomposition]
    exact ih (fun b member => valid b (List.mem_cons_of_mem _ member))

theorem checked_prime (modulus : Limb) [Fact (Nat.Prime modulus.val)] : check modulus = .checked true := by
  have prime : Nat.Prime modulus.val := Fact.out
  have large : ¬modulus.val < 2 := by have bound := prime.two_le; omega
  simp only [check,large,ite_false]
  cases trial : smallTrials modulus.val bases with
  | some answer =>
    have accepted := smallTrials_prime modulus.val prime bases (fun b member => (bases_bounds b member).1) answer trial
    subst answer
    rfl
  | none =>
    have noDivisors := (smallTrials_none modulus.val bases).mp trial
    have nondivTwo := noDivisors 2 (by simp [bases])
    have domain : 3 ≤ modulus.val := by omega
    have valid : 1 < modulus.val := by omega
    let state := ConcreteNTTDiv64Initialization.buildState modulus valid
    have built : ConcreteNTTDiv64Initialization.new modulus = .initialized state := by
      simp only [ConcreteNTTDiv64Initialization.new,dite_eq_left valid]
      rfl
    rw [built]
    apply congrArg Outcome.checked
    have parameters := ConcreteNTTWordRootConstruction.parameters_fit modulus.val domain modulus.isLt
    have qBound : (ConcreteNTTRootConstruction.factorTwos (modulus.val-1)).1+1 < radix := parameters.1
    have qFits : (ConcreteNTTRootConstruction.factorTwos (modulus.val-1)).1 < radix := by omega
    let : Fact (Nat.Prime state.divisor.val) := ⟨by change Nat.Prime modulus.val; exact prime⟩
    apply rounds_pass state (ConcreteNTTDiv64Initialization.initialize_correct modulus valid) _ _ qFits
      (ConcreteNTTRootConstruction.factorTwos_decomposition (modulus.val-1)) bases
    intro base member
    refine ⟨(bases_bounds base member).2,?_⟩
    intro zero
    have divides := (ZMod.natCast_eq_zero_iff base modulus.val).mp zero
    have same := (Nat.prime_dvd_prime_iff_eq prime (bases_prime base member)).mp divides
    exact noDivisors base member (by rw [← same,Nat.mod_self])

theorem check_total (modulus : Limb) : ∃ result, check modulus = .checked result := by
  simp only [check]
  split
  · exact ⟨false,rfl⟩
  · rename_i large
    cases trial : smallTrials modulus.val bases with
    | some result => exact ⟨result,rfl⟩
    | none =>
      cases initialized : ConcreteNTTDiv64Initialization.new modulus with
      | assertionFailure =>
        have invalid := (ConcreteNTTDiv64Initialization.new_rejected modulus).mp initialized
        omega
      | initialized state => exact ⟨_,rfl⟩

theorem goldilocks_passes : check ⟨NativeFields.goldilocksModulus,by decide⟩ = .checked true := checked_prime _
theorem babyBear_passes : check ⟨NativeFields.babyBearModulus,by decide⟩ = .checked true := checked_prime _

end FormalProof4FHE.HasteBoots.ConcreteNTTPrimeGate
