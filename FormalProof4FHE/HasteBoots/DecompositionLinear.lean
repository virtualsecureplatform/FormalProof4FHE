module

public import FormalProof4FHE.HasteBoots.ConcreteLinearSecurity

@[expose] public section

/-!
# Trusted radix reconstruction and zero borrow endpoints

The native registry has the original input, d digit columns, then d+1 borrow
columns. Its three fixed linear relations reconstruct the input and set both
borrow endpoints to zero. This module supplies those exact coefficients and
indices to the authenticated linear stage. These field equalities alone do
not establish integer canonicity: digit ranges and borrow transitions require
the separate tuple lookup protocol. Native checked configuration, coefficient
normalization, raw decoding and whole-PBS/transcript refinement remain open.
-/

open scoped BigOperators
open OracleSpec OracleComp BinaryTree
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening

namespace FormalProof4FHE.HasteBoots.DecompositionLinear

noncomputable section

variable {F : Type} [Field F] {d b n : ℕ}

def input : Fin (2 * d + 2) := ⟨0, by omega⟩

def digit (i : Fin d) : Fin (2 * d + 2) := ⟨i.val + 1, by have := i.isLt; omega⟩

def borrow (i : Fin (d + 1)) : Fin (2 * d + 2) := ⟨d + 1 + i.val, by have := i.isLt; omega⟩

def firstBorrow : Fin (2 * d + 2) := borrow ⟨0, by omega⟩

def lastBorrow : Fin (2 * d + 2) := borrow ⟨d, by omega⟩

/-- Every native registry slot has an input, digit or borrow role. -/
theorem registry_complete (factor : Fin (2 * d + 2)) :
    factor = input ∨ (∃ i, digit i = factor) ∨ ∃ i, borrow i = factor := by
  by_cases zero : factor.val = 0
  · exact Or.inl (Fin.ext zero)
  by_cases digitRange : factor.val ≤ d
  · refine Or.inr (Or.inl ⟨⟨factor.val - 1, by omega⟩, Fin.ext ?_⟩)
    simp only [digit]
    omega
  · refine Or.inr (Or.inr ⟨⟨factor.val - (d + 1), by have := factor.isLt; omega⟩, Fin.ext ?_⟩)
    simp only [borrow]
    omega

/-- Literal native source order and coefficients, including padding cells. -/
def reconstruction (radix : F) : PackedLinear.Relation F (Fin (2 * d + 2)) :=
  (-1, input) :: List.ofFn (fun i : Fin d => (radix ^ i.val, digit i))

def relations (radix : F) : List (PackedLinear.Relation F (Fin (2 * d + 2))) :=
  [reconstruction radix, [(1, firstBorrow)], [(1, lastBorrow)]]

theorem reconstruction_evaluate (radix : F) (values : Fin (2 * d + 2) → Fin b → F) (lane : Fin b) :
    PackedLinear.evaluate (reconstruction radix) values lane =
      -values input lane + ∑ i : Fin d, radix ^ i.val * values (digit i) lane := by
  simp [PackedLinear.evaluate, reconstruction, List.map_ofFn, List.sum_ofFn,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]

def Relation (radix : F) (tables : Fin (2 * d + 2) → MatrixFold.Cube n → Fin b → F) : Prop :=
  ∀ cell lane,
    tables input cell lane = ∑ i : Fin d, radix ^ i.val * tables (digit i) cell lane ∧
    tables firstBorrow cell lane = 0 ∧ tables lastBorrow cell lane = 0

theorem holds_iff (radix : F) (tables : Fin (2 * d + 2) → MatrixFold.Cube n → Fin b → F) :
    PackedLinear.Holds (relations radix) tables ↔ Relation radix tables := by
  simp only [PackedLinear.Holds, relations, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq]
  have reconstruction_zero : PackedLinear.residual (reconstruction radix) tables = 0 ↔
      ∀ cell lane, -tables input cell lane + ∑ i : Fin d, radix ^ i.val * tables (digit i) cell lane = 0 := by
    simp only [PackedLinear.residual, funext_iff, Pi.zero_apply, reconstruction_evaluate]
  rw [reconstruction_zero]
  simp only [PackedLinear.residual, PackedLinear.evaluate, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, one_smul, add_zero, funext_iff, Pi.zero_apply]
  constructor
  · rintro ⟨reconstruct, first, last⟩ cell lane
    exact ⟨neg_add_eq_zero.mp (reconstruct cell lane), first cell lane, last cell lane⟩
  · intro valid
    exact ⟨fun cell lane => by rw [← (valid cell lane).1]; exact neg_add_cancel _,
      fun cell lane => (valid cell lane).2.1, fun cell lane => (valid cell lane).2.2⟩

variable [DecidableEq F]

/-- Honest local completeness needs no probabilistic or opening premise. -/
theorem honest_check (radix : F) (tables : Fin (2 * d + 2) → MatrixFold.Cube n → Fin b → F)
    (valid : Relation radix tables) (query : PackedSumcheckSubclaim.Query F b n) :
    PackedLinear.check (relations radix) (fun factor => query.fold (tables factor)) = true :=
  PackedLinear.honest_check _ _ ((holds_iff radix tables).mpr valid) query

def stage {Input Digest Cfg Response Memory CommitMemory : Type} {front suffix m queries height : ℕ}
    (radix : F)
    (s : AuthenticatedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory (2 * d + 2) b front suffix m queries height) :=
  { s with relations := relations radix }

omit [DecidableEq F] in
theorem preflight [Fintype F] {Input Digest Cfg Response Memory CommitMemory : Type}
    {front suffix m queries height : ℕ} (radix : F)
    (s : AuthenticatedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory (2 * d + 2) b front suffix m queries height)
    (positive : 0 < b) (large : 2 * b < Fintype.card F) :
    AuthenticatedLinear.preflight (stage radix s) = true := by
  simp [AuthenticatedLinear.preflight, stage, relations, reconstruction, positive, large]

variable {p front suffix m queries height : ℕ} [Fact p.Prime] [NeZero b] [NeZero m]
  {Input Digest Cfg Response Memory CommitMemory : Type}
  [DecidableEq Input] [DecidableEq Digest] [Fintype Digest] [SampleableType Digest]
  [SampleableType (Fin b → ZMod p)] [SampleableType (TestMatrix (ZMod p) (2 ^ front) b)]
  [SampleableType (Fin queries → Fin (2 ^ height))]

/-- Concrete-field soundness of the three trusted reconstruction/endpoint
relations, with all 2*d+2 original columns authenticated in registry order. -/
theorem soundness_from_empty
    (radix : ZMod p) (nodesEnough : 2 * b ≤ p)
    (s : AuthenticatedLinear.Scheme (ZMod p) Input Digest Cfg Response Memory CommitMemory (2 * d + 2) b front suffix m queries height)
    (dummy : Digest) (enough : m ≤ 2 ^ height) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (small : (radius : ℚ≥0) < (PCSParameters.distance height m : ℚ≥0) / 3) :
    Pr{let outcome ← AuthenticatedLinear.witness (AuthenticatedLinear.nativeScheme p nodesEnough (stage radix s)) dummy}[
      ¬Relation radix (AuthenticatedLinear.sources s dummy capacity radius outcome.1) ∧
        AuthenticatedLinear.accepted outcome.2.1 = true] ≤
      (((front + suffix : ℕ) : ENNReal) * (((((2 * b - 1 : ℕ) : ENNReal) / p) ^ b)) +
        ((2 * d + 2 : ℕ) : ENNReal) * PCSParameters.error p b height m queries radius) +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (fun _ : Cfg => Skeleton.perfect height))
        (CheckpointCollision.loss unifSpec (fun _ : Cfg => Skeleton.perfect height))
        (AuthenticatedLinear.program (AuthenticatedLinear.nativeScheme p nodesEnough (stage radix s)))
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) := by
  have bound := ConcreteLinearSecurity.soundness_from_empty nodesEnough (stage radix s) dummy enough capacity radius small
  change Pr{let outcome ← AuthenticatedLinear.witness (AuthenticatedLinear.nativeScheme p nodesEnough (stage radix s)) dummy}[
    ¬PackedLinear.Holds (relations radix) (AuthenticatedLinear.sources s dummy capacity radius outcome.1) ∧
      AuthenticatedLinear.accepted outcome.2.1 = true] ≤ _ at bound
  simp only [holds_iff] at bound
  have encoding : (stage radix s).encoding = s.encoding := rfl
  rw [encoding] at bound
  exact bound

end

end FormalProof4FHE.HasteBoots.DecompositionLinear
