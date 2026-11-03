module

public import FormalProof4FHE.HasteBoots.AuthenticatedZeroCheck

@[expose] public section

/-!
# The canonical complete-PBS Hadamard stage

The trusted native shape lists evaluation/key pairs, followed by the output:
`sum_i evaluation[i] * key[i] - output`. This module fixes that shape rather
than accepting prover-selected coefficients or factor roles. It relates the
zero relation to the pointwise external-product identity and instantiates the
actual authenticated shared ZeroCheck program. NTT meaning, public-key layout,
subsequent PBS stages, transcript compilation and Rust refinement are separate.
-/

open scoped BigOperators
open OracleSpec OracleComp BinaryTree Matrix
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening

namespace FormalProof4FHE.HasteBoots.PBSHadamard

noncomputable section

abbrev Factor (count : ℕ) := Sum (Fin count × Bool) Unit
abbrev Term (count : ℕ) := Option (Fin count)

variable {F : Type} [Field F] {count n b : ℕ}

def arity : Term count → ℕ
  | some _ => 2
  | none => 1

def coefficient : Term count → F
  | some _ => 1
  | none => -1

def indices : (term : Term count) → Fin (arity term) → Factor count
  | some index, position => .inl (index, position.val == 1)
  | none, _ => .inr ()

/-- Native pair roles have indices 2*i and 2*i+1; the output comes last. -/
def address : Factor count → Fin (2 * count + 1)
  | .inl (index, bit) => ⟨2 * index.val + if bit then 1 else 0, by split <;> omega⟩
  | .inr _ => ⟨2 * count, by omega⟩

theorem address_injective : Function.Injective (address (count := count)) := by
  intro first second equal
  have values := congrArg Fin.val equal
  rcases first with ⟨index, bit⟩ | ⟨⟩ <;> rcases second with ⟨other, otherBit⟩ | ⟨⟩
  · cases bit <;> cases otherBit
    all_goals simp only [address, Bool.false_eq_true, reduceIte] at values
    all_goals have hi := index.isLt
    all_goals have ho := other.isLt
    all_goals first | exact (by omega : False).elim | have same : index = other := Fin.ext (by omega); subst other; rfl
  · cases bit <;> simp only [address, Bool.false_eq_true, reduceIte] at values <;> have hi := index.isLt <;> omega
  · cases otherBit <;> simp only [address, Bool.false_eq_true, reduceIte] at values <;> have ho := other.isLt <;> omega
  · rfl

/-- The typed roles cover exactly the native array slots, without omissions. -/
theorem address_bijective : Function.Bijective (address (count := count)) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨address_injective, ?_⟩
  simp [Factor, Nat.mul_comm]

/-- All original factors are opened in the same order as the native registry. -/
def factors (count : ℕ) : List (Factor count) :=
  (List.finRange count).flatMap (fun index => [.inl (index, false), .inl (index, true)]) ++ [.inr ()]

theorem factors_complete (factor : Factor count) : factor ∈ factors count := by
  cases factor with
  | inl pair =>
    obtain ⟨index, bit⟩ := pair
    cases bit <;> simp [factors, List.mem_flatMap]
  | inr tag => cases tag; simp [factors]

theorem degree_bound (term : Term count) : arity term ≤ 2 := by
  cases term <;> simp [arity]

/-- The semantic expression is exactly the native trusted shape. -/
theorem expression (values : Factor count → F) :
    PackedSumcheckRound.expression arity coefficient indices values =
      (∑ index, values (.inl (index, false)) * values (.inl (index, true))) - values (.inr ()) := by
  have pairTerm (index : Fin count) : coefficient (some index) *
      (∏ position : Fin (arity (some index)), values (indices (some index) position)) =
      values (.inl (index, false)) * values (.inl (index, true)) := by
    change (1 : F) * (∏ position : Fin 2, values (.inl (index, position.val == 1))) = _
    simp [Fin.prod_univ_two]
  have outputTerm : coefficient (none : Term count) *
      (∏ position : Fin (arity (none : Term count)), values (indices none position)) = -values (.inr ()) := by
    change (-1 : F) * (∏ _ : Fin 1, values (.inr ())) = _
    simp
  rw [PackedSumcheckRound.expression, Fintype.sum_option]
  simp only [pairTerm, outputTerm, sub_eq_add_neg, add_comm]


/-- Pointwise multiplication of evaluation and public-key rows, with the
result occupying the final source slot. This makes no NTT refinement claim. -/
def Relation (tables : PackedSumcheckExecution.Tables F (Factor count) n b) : Prop :=
  ∀ cell lane, tables (.inr ()) cell lane =
    ∑ index, tables (.inl (index, false)) cell lane * tables (.inl (index, true)) cell lane

theorem vanishes_iff (tables : PackedSumcheckExecution.Tables F (Factor count) (n + 1) b) :
    PackedZeroCube.Vanishes arity coefficient indices tables ↔ Relation tables := by
  simp only [PackedZeroCube.Vanishes, Relation, expression, sub_eq_zero]
  exact forall_congr' (fun _ => forall_congr' (fun _ => eq_comm))

/-- Fix the relation and complete opening order from trusted stage geometry.
Other prover programs and commitment behavior remain arbitrary. -/
def stage {FirstMessage Message Input Digest Cfg Response Memory CommitMemory : Type}
    {front suffix m queries height : ℕ}
    (s : AuthenticatedZeroCheck.Scheme F (Factor count) (Term count) FirstMessage Message
      Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height) :=
  { s with arity := arity, coefficient := coefficient, indices := indices, factors := factors count }

variable {K Input Digest Cfg Response Memory CommitMemory : Type}
  [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {front suffix m queries height : ℕ}
  [SampleableType (Fin b → F)] [SampleableType F] [SampleableType (Fin n → F)]
  [SampleableType (PackedZeroReduction.Points F n b)] [SampleableType (Fin b → Fin b → F)]
  [SampleableType (Fin b → ((Fin b → F) × F))]
  [SampleableType (TestMatrix F (2 ^ front) b)] [SampleableType (Fin queries → Fin (2 ^ height))]
  [SampleableType Digest] [Fintype Digest] [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq K]
  [SampleableType ((Fin (2 ^ front) × Fin b) → K)]

/-- The first canonical complete-PBS verifier stage, with trusted degree-two
shape and only original-factor native openings, on one actual shared run.
This proves the decoded evaluation/key/output identity; NTT, public-key
preprocessing and composition with subsequent PBS stages are still required. -/
theorem native_soundness_from_empty [NeZero m] [NeZero b]
    (characteristic : ℕ) [CharP F characteristic]
    (firstSmall : (2 * b - 1) * 2 + 1 ≤ characteristic)
    (roundSmall : (2 * b - 1) * 3 + 1 ≤ characteristic)
    (nodesEnough : 2 * b ≤ (2 * b - 1) * 2 + 1)
    (s : AuthenticatedZeroCheck.Scheme F (Factor count) (Term count) (Fin b → Fin ((2 * b - 1) * 2 + 1) → F)
      (Fin ((2 * b - 1) * 3 + 1) → F) Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2 ^ height)))
    (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← (AuthenticatedZeroCheck.witness (AuthenticatedZeroCheck.nativeScheme characteristic 2 firstSmall roundSmall nodesEnough (stage s)) dummy)}[
      ¬Relation (AuthenticatedZeroCheck.sources s dummy capacity radius outcome.1) ∧
      AuthenticatedZeroCheck.accepted outcome.2.1 = true] ≤
      (((n : ENNReal) / Fintype.card F) ^ b +
        ((((((2 * b - 1) * 2 + 1 : ℕ) : ENNReal) / Fintype.card F) ^ b)) +
        (n : ENNReal) * ((((((2 * b - 1) * 3 : ℕ) : ENNReal) / Fintype.card F) ^ b)) +
      ((factors count).map (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius)).sum) +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (fun _ : Cfg => Skeleton.perfect height))
        (CheckpointCollision.loss unifSpec (fun _ : Cfg => Skeleton.perfect height)) (AuthenticatedZeroCheck.program (AuthenticatedZeroCheck.nativeScheme characteristic 2 firstSmall roundSmall nodesEnough (stage s)))
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) := by
  have bound := AuthenticatedZeroCheck.native_soundness_from_empty characteristic 2 firstSmall roundSmall nodesEnough
    (stage s) basis dummy factors_complete enough capacity radius degree_bound small
  have sameSource (first : AuthenticatedZeroCheck.Prefix (Factor := Factor count) (Digest := Digest)
      (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height)) :
      AuthenticatedZeroCheck.sources (stage s) dummy capacity radius first =
        AuthenticatedZeroCheck.sources s dummy capacity radius first := by
    rfl
  change Pr{let outcome ← (AuthenticatedZeroCheck.witness
    (AuthenticatedZeroCheck.nativeScheme characteristic 2 firstSmall roundSmall nodesEnough (stage s)) dummy)}[
      ¬PackedZeroCube.Vanishes arity coefficient indices
        (AuthenticatedZeroCheck.sources (stage s) dummy capacity radius outcome.1) ∧
      AuthenticatedZeroCheck.accepted outcome.2.1 = true] ≤ _ at bound
  simp only [vanishes_iff, sameSource] at bound
  exact bound

end

end FormalProof4FHE.HasteBoots.PBSHadamard
