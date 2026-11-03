module

public import FormalProof4FHE.HasteBoots.LookupPairArithmetic

@[expose] public section

/-!
# Computed native lookup terminal checks and original opening obligations

Decode the supplied source vectors in order, apply the native public terminal
formula, and compare its value to the identity subclaim. Helper opening claims
are the exact encoded sumcheck/helper values. Successful checks imply the
joint arithmetic event or a false original source/helper opening. No PCS
acceptance flag, replay certificate or projected-source root is supplied.
Operational reception/binding and grouped authentication remain to compose.
-/

open scoped BigOperators Classical
open Matrix
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim

namespace FormalProof4FHE.HasteBoots.LookupPairTerminal

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] {d padding c row count : ℕ}

def decodeSources (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (point : Fin (c + row) → K) : (count : ℕ) → (Fin count → Fin (d + padding) → F) → Option (Fin count → K)
  | 0, _ => some Fin.elim0
  | count + 1, claims => do
    let first ← PaddedExtension.element basis ((ExtensionLookupTerminal.sourceQuery basis shape point).finish (claims 0))
    let rest ← decodeSources basis shape point count (fun i => claims i.succ)
    pure (Fin.cons first rest)

theorem decodeSources_sound (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (point : Fin (c + row) → K) (claims : Fin count → Fin (d + padding) → F) (values : Fin count → K)
    (decoded : decodeSources basis shape point count claims = some values) :
    ∀ i, PaddedExtension.element basis ((ExtensionLookupTerminal.sourceQuery basis shape point).finish (claims i)) = some (values i) := by
  induction count with
  | zero => exact fun i => Fin.elim0 i
  | succ count ih =>
    change (PaddedExtension.element basis ((ExtensionLookupTerminal.sourceQuery basis shape point).finish (claims 0))).bind
      (fun first => (decodeSources basis shape point count (fun i => claims i.succ)).bind
        (fun rest => some (Fin.cons first rest))) = some values at decoded
    obtain ⟨first, firstDecoded, tailDecoded⟩ := Option.bind_eq_some_iff.mp decoded
    obtain ⟨rest, restDecoded, equal⟩ := Option.bind_eq_some_iff.mp tailDecoded
    have vectorEq : Fin.cons first rest = values := Option.some.inj equal
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [← vectorEq, Fin.cons_zero] using firstDecoded
    · simpa only [← vectorEq, Fin.cons_succ] using ih _ _ restDecoded j

def check (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (eqPoint point : Fin (c + row) → K) (r y : K) (active : ℕ) (enough : active ≤ 2 ^ (c + row))
    (claims : Fin count → Fin (d + padding) → F) (helper expected : K) : Bool :=
  match decodeSources basis shape point count claims with
  | none => false
  | some values => decide (ExtensionLookupIdentity.terminal eqPoint point r (∑ i, y ^ i.val * values i) helper active enough = expected)

theorem check_sound (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (eqPoint point : Fin (c + row) → K) (r y : K) (active : ℕ) (enough : active ≤ 2 ^ (c + row))
    (claims : Fin count → Fin (d + padding) → F) (helper expected : K)
    (accepted : check basis shape eqPoint point r y active enough claims helper expected = true) :
    ∃ values : Fin count → K,
      (∀ i, PaddedExtension.element basis ((ExtensionLookupTerminal.sourceQuery basis shape point).finish (claims i)) = some (values i)) ∧
      ExtensionLookupIdentity.terminal eqPoint point r (∑ i, y ^ i.val * values i) helper active enough = expected := by
  unfold check at accepted
  cases decoded : decodeSources basis shape point count claims with
  | none => simp only [decoded, Bool.false_eq_true] at accepted
  | some values =>
    simp only [decoded, decide_eq_true_eq] at accepted
    exact ⟨values, decodeSources_sound basis shape point claims values decoded, accepted⟩

/-- Encoded helper claims are fixed points of the optional post-projection,
including the zero-variable helper opening. -/
theorem coefficients_finish_encode (basis : Module.Basis (Fin d) F K) {n : ℕ} (point : Fin n → K) (value : K) :
    (ExtensionQuery.coefficientsQuery (padding := padding) basis point).finish (PaddedExtension.encode basis value) =
      PaddedExtension.encode basis value := by
  cases n with
  | zero =>
    change PaddedExtension.multiplication basis 1 *ᵥ PaddedExtension.encode basis value = _
    rw [PaddedExtension.multiplication_encode, one_mul]
  | succ n => rfl

/-- The sumcheck's own terminal determines its helper opening value. A wrong
sum terminal is a false original helper opening, not an extra supplied factor. -/
theorem sum_truthful_or_wrong (basis : Module.Basis (Fin d) F K) {n : ℕ} (claim : Subclaim K 1 n)
    (helpers : MatrixFold.Cube n → Fin (d + padding) → F) :
    LookupPairSequence.SumTruthful (fun cell => PaddedExtension.decode basis (helpers cell)) (some (claim, ())) ∨
      PaddedExtension.encode basis (claim.expected 0) ≠ (ExtensionQuery.coefficientsQuery basis (ScalarSumcheckQuery.point claim.query)).query.fold helpers := by
  by_cases truthful : claim.expected 0 = ExtensionQuery.evaluate n (ScalarSumcheckQuery.point claim.query)
      (fun cell => PaddedExtension.decode basis (helpers cell))
  · left
    exact (LookupScalarSubclaim.sum_truthful_iff _ claim ()).mpr truthful
  · right
    apply ExtensionQuery.coefficients_false_claim basis (ScalarSumcheckQuery.point claim.query) helpers (claim.expected 0)
    · rw [coefficients_finish_encode, PaddedExtension.element_encode]
    · exact truthful

/-- A computed partial-table terminal check exposes exactly the original PCS
obligations needed by the concrete pair arithmetic theorem. -/
theorem partial_truthful_or_wrong (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (eqPoint : Fin (c + row) → K) (r y : K) (active : ℕ) (enough : active ≤ 2 ^ (c + row))
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + padding) → F)
    (claim : Subclaim K 1 (c + row)) (claims : Fin count → Fin (d + padding) → F) (helper : K)
    (accepted : check basis shape eqPoint (ScalarSumcheckQuery.point claim.query) r y active enough claims helper (claim.expected 0) = true) :
    ScalarSumcheckOracle.MLETruthful ExtensionLookupIdentity.partialArity
      (ExtensionLookupIdentity.partialCoefficient r) ExtensionLookupIdentity.partialIndices
      (ExtensionLookupIdentity.factors eqPoint y (fun i => LookupSourceFlattening.flatten shape (sources i))
        (fun cell => PaddedExtension.decode basis (helpers cell)) active) (some (claim, ())) ∨
      (∃ i, claims i ≠ (ExtensionLookupTerminal.sourceQuery basis shape (ScalarSumcheckQuery.point claim.query)).query.fold (sources i)) ∨
      PaddedExtension.encode basis helper ≠ (ExtensionQuery.coefficientsQuery basis (ScalarSumcheckQuery.point claim.query)).query.fold helpers := by
  obtain ⟨values, decoded, identity⟩ := check_sound basis shape eqPoint _ r y active enough claims helper _ accepted
  exact LookupScalarSubclaim.checked_partial_or_wrong basis shape eqPoint r y active enough sources helpers claim () claims
    (PaddedExtension.encode basis helper) values helper decoded
    (by rw [coefficients_finish_encode, PaddedExtension.element_encode]) identity

/-- Full-table checker uses the same literal formula and retains the
smaller degree-three arithmetic event. -/
theorem full_truthful_or_wrong (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (eqPoint : Fin (c + row) → K) (r y : K)
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + padding) → F)
    (claim : Subclaim K 1 (c + row)) (claims : Fin count → Fin (d + padding) → F) (helper : K)
    (accepted : check basis shape eqPoint (ScalarSumcheckQuery.point claim.query) r y (2 ^ (c + row)) le_rfl claims helper (claim.expected 0) = true) :
    ScalarSumcheckOracle.MLETruthful ExtensionLookupIdentity.fullArity
      (ExtensionLookupIdentity.fullCoefficient (K := K)) ExtensionLookupIdentity.fullIndices
      (fun factor cell => if factor = .hash then
        ExtensionLookupIdentity.hashTable y (fun i => LookupSourceFlattening.flatten shape (sources i)) cell + r else
        ExtensionLookupIdentity.factors eqPoint y (fun i => LookupSourceFlattening.flatten shape (sources i))
          (fun cell => PaddedExtension.decode basis (helpers cell)) (2 ^ (c + row)) factor cell) (some (claim, ())) ∨
      (∃ i, claims i ≠ (ExtensionLookupTerminal.sourceQuery basis shape (ScalarSumcheckQuery.point claim.query)).query.fold (sources i)) ∨
      PaddedExtension.encode basis helper ≠ (ExtensionQuery.coefficientsQuery basis (ScalarSumcheckQuery.point claim.query)).query.fold helpers := by
  obtain ⟨values, decoded, identity⟩ := check_sound basis shape eqPoint _ r y (2 ^ (c + row)) le_rfl claims helper _ accepted
  exact LookupScalarSubclaim.checked_full_or_wrong basis shape eqPoint r y sources helpers claim () claims
    (PaddedExtension.encode basis helper) values helper decoded
    (by rw [coefficients_finish_encode, PaddedExtension.element_encode]) identity

/-- Exactly the three original opening families issued for one lookup pair. -/
def WrongOpenings (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + padding) → F)
    (sumClaim zeroClaim : Subclaim K 1 (c + row)) (claims : Fin count → Fin (d + padding) → F) (helper : K) : Prop :=
  PaddedExtension.encode basis (sumClaim.expected 0) ≠
      (ExtensionQuery.coefficientsQuery basis (ScalarSumcheckQuery.point sumClaim.query)).query.fold helpers ∨
    (∃ i, claims i ≠ (ExtensionLookupTerminal.sourceQuery basis shape (ScalarSumcheckQuery.point zeroClaim.query)).query.fold (sources i)) ∨
    PaddedExtension.encode basis helper ≠
      (ExtensionQuery.coefficientsQuery basis (ScalarSumcheckQuery.point zeroClaim.query)).query.fold helpers

/-- The complete local partial check implies the joint arithmetic event or
one of the sum-helper, identity-helper and original-source opening failures. -/
theorem partial_joint_or_wrong (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (eqPoint : Fin (c + row) → K) (r y : K) (active : ℕ) (enough : active ≤ 2 ^ (c + row))
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + padding) → F)
    (sumClaim zeroClaim : Subclaim K 1 (c + row)) (claims : Fin count → Fin (d + padding) → F) (helper : K)
    (accepted : check basis shape eqPoint (ScalarSumcheckQuery.point zeroClaim.query) r y active enough claims helper (zeroClaim.expected 0) = true) :
    LookupPairSequence.JointTruthful ExtensionLookupIdentity.partialArity
      (ExtensionLookupIdentity.partialCoefficient r) ExtensionLookupIdentity.partialIndices
      (fun eqPoint => ExtensionLookupIdentity.factors eqPoint y (fun i => LookupSourceFlattening.flatten shape (sources i))
        (fun cell => PaddedExtension.decode basis (helpers cell)) active)
      (fun cell => PaddedExtension.decode basis (helpers cell))
      (some (sumClaim, ()), some (eqPoint, some (zeroClaim, ()))) ∨
      WrongOpenings basis shape sources helpers sumClaim zeroClaim claims helper := by
  rcases sum_truthful_or_wrong basis sumClaim helpers with sumTrue | sumWrong
  · rcases partial_truthful_or_wrong basis shape eqPoint r y active enough sources helpers zeroClaim claims helper accepted with
      zeroTrue | zeroWrong
    · exact Or.inl ⟨sumTrue, zeroTrue⟩
    · exact Or.inr (Or.inr zeroWrong)
  · exact Or.inr (Or.inl sumWrong)

/-- Full-table version retains its degree-three joint event and the same
three original opening obligations. -/
theorem full_joint_or_wrong (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (eqPoint : Fin (c + row) → K) (r y : K)
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + padding) → F)
    (sumClaim zeroClaim : Subclaim K 1 (c + row)) (claims : Fin count → Fin (d + padding) → F) (helper : K)
    (accepted : check basis shape eqPoint (ScalarSumcheckQuery.point zeroClaim.query) r y (2 ^ (c + row)) le_rfl claims helper (zeroClaim.expected 0) = true) :
    LookupPairSequence.JointTruthful ExtensionLookupIdentity.fullArity
      (ExtensionLookupIdentity.fullCoefficient (K := K)) ExtensionLookupIdentity.fullIndices
      (fun eqPoint => LookupPairArithmetic.fullTables eqPoint r y (fun i => LookupSourceFlattening.flatten shape (sources i))
        (fun cell => PaddedExtension.decode basis (helpers cell)))
      (fun cell => PaddedExtension.decode basis (helpers cell))
      (some (sumClaim, ()), some (eqPoint, some (zeroClaim, ()))) ∨
      WrongOpenings basis shape sources helpers sumClaim zeroClaim claims helper := by
  rcases sum_truthful_or_wrong basis sumClaim helpers with sumTrue | sumWrong
  · rcases full_truthful_or_wrong basis shape eqPoint r y sources helpers zeroClaim claims helper accepted with
      zeroTrue | zeroWrong
    · exact Or.inl ⟨sumTrue, zeroTrue⟩
    · exact Or.inr (Or.inr zeroWrong)
  · exact Or.inr (Or.inl sumWrong)

end

end FormalProof4FHE.HasteBoots.LookupPairTerminal
