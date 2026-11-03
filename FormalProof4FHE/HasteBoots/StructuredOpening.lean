module

public import FormalProof4FHE.HasteBoots.ColumnOpening

@[expose] public section

/-!
# Structured responses to one common nearby source

All row combinations use the same complete source matrix and the same column
draw vector. This proves the near branch without an independence assumption
between random and structured tests. Connecting the response finishing map to
the ordered matrix opening is a separate algebraic instantiation.
-/

open ProbabilityTheory
open scoped BigOperators

namespace FormalProof4FHE.HasteBoots.StructuredOpening

variable {F Position Row Symbol Test : Type} [Field F] [AddCommGroup Symbol]
  [Module F Symbol] [Fintype Position] [Fintype Row] [DecidableEq Position]
  [DecidableEq Symbol] [DecidableEq (Row → Symbol)]

/-- One base-linear response, evaluated independently in each shared column. -/
def combine (weights : Row → F) (word : Position → Row → Symbol) : Position → Symbol :=
  fun pos => ∑ row, weights row • word pos row

omit [Fintype Position] [DecidableEq Position] [DecidableEq Symbol] [DecidableEq (Row → Symbol)] in
/-- A common coded source gives a coded response for every choice of weights. -/
theorem combine_mem (C : Submodule F (Position → Symbol)) (weights : Row → F)
    (source : Position → Row → Symbol) (coded : CommonSource.RowsIn C source) :
    combine weights source ∈ C := by
  have equal : combine weights source = ∑ row, weights row • (fun pos => source pos row) := by
    ext pos
    simp only [combine, Finset.sum_apply, Pi.smul_apply]
  rw [equal]
  exact C.sum_mem (fun row _ => C.smul_mem _ (coded row))

omit [DecidableEq Position] in
/-- Every structured response inherits the complete matrix's common error columns. -/
theorem combine_distance_le (weights : Row → F) (left right : Position → Row → Symbol) :
    hammingDist (combine weights left) (combine weights right) ≤ hammingDist left right :=
  hammingDist_comp_le_hammingDist (x := left) (y := right)
    (fun (_ : Position) (column : Row → Symbol) => ∑ row : Row, weights row • column row)

/-- A false family of coded structured responses must avoid at least
distance-minus-radius columns. Every response check uses the same draws. -/
theorem near_bound (C : Submodule F (Position → Symbol)) (radius queries : ℕ)
    [SampleableType (Fin queries → Position)]
    (word source : Position → Row → Symbol) (weights : Test → Row → F)
    (claimed : Test → Position → Symbol) (sourceC : CommonSource.RowsIn C source)
    (close : hammingDist word source ≤ radius) (claimedC : ∀ test, claimed test ∈ C)
    (different : (fun test => combine (weights test) source) ≠ claimed) :
    Pr{let draw ← $ᵗ (Fin queries → Position)}[
      ∀ test, ColumnOpening.Agrees (combine (weights test) word) (claimed test) draw] ≤
      (((Fintype.card Position - (Code.minDist (C : Set (Position → Symbol)) - radius) : ℕ) :
        ENNReal) / Fintype.card Position) ^ queries := by
  classical
  have witness : ∃ test, combine (weights test) source ≠ claimed test := by
    by_contra noWitness
    apply different
    funext test
    exact Classical.not_not.mp (fun unequal => noWitness ⟨test, unequal⟩)
  obtain ⟨test, unequal⟩ := witness
  apply ColumnOpening.shared_bound
  refine ⟨test, CommonSource.falseResponse_distance _ radius _ _ _
    (combine_mem C (weights test) source sourceC) (claimedC test) unequal ?_⟩
  exact (combine_distance_le (weights test) word source).trans close

/-- Any deterministic response finishing map can detect a false claimed value.
An incorrect finished value forces a false response before the column test. -/
theorem near_falseValue_bound {Output : Type}
    (C : Submodule F (Position → Symbol)) (radius queries : ℕ)
    [SampleableType (Fin queries → Position)]
    (word source : Position → Row → Symbol) (weights : Test → Row → F)
    (claimed : Test → Position → Symbol) (finish : (Test → Position → Symbol) → Output)
    (sourceC : CommonSource.RowsIn C source) (close : hammingDist word source ≤ radius)
    (claimedC : ∀ test, claimed test ∈ C) :
    Pr{let draw ← $ᵗ (Fin queries → Position)}[
      finish claimed ≠ finish (fun test => combine (weights test) source) ∧
      ∀ test, ColumnOpening.Agrees (combine (weights test) word) (claimed test) draw] ≤
      (((Fintype.card Position - (Code.minDist (C : Set (Position → Symbol)) - radius) : ℕ) :
        ENNReal) / Fintype.card Position) ^ queries := by
  classical
  by_cases equal : finish claimed = finish (fun test => combine (weights test) source)
  · simp only [equal, ne_eq, not_true_eq_false, false_and, prEvent_false, zero_le]
  · have different : (fun test => combine (weights test) source) ≠ claimed := by
      intro same
      exact equal (congrArg finish same.symm)
    exact (prEvent_mono _ _ _ (fun _ accepted => accepted.2)).trans
      (near_bound C radius queries word source weights claimed sourceC close claimedC different)

/-- The near-branch bound remains valid for any earlier random experiment and
response choices depending on its entire outcome. The common source stays fixed. -/
theorem adaptive_near_falseValue_bound {Challenge Output : Type}
    (coins : ProbComp Challenge) (C : Submodule F (Position → Symbol)) (radius queries : ℕ)
    [SampleableType (Fin queries → Position)]
    (word source : Position → Row → Symbol) (weights : Test → Row → F)
    (claimed : Challenge → Test → Position → Symbol)
    (finish : (Test → Position → Symbol) → Output)
    (sourceC : CommonSource.RowsIn C source) (close : hammingDist word source ≤ radius)
    (claimedC : ∀ challenge test, claimed challenge test ∈ C) :
    Pr{let challenge ← coins; let draw ← $ᵗ (Fin queries → Position)}[
      finish (claimed challenge) ≠ finish (fun test => combine (weights test) source) ∧
      ∀ test, ColumnOpening.Agrees (combine (weights test) word) (claimed challenge test) draw] ≤
      (((Fintype.card Position - (Code.minDist (C : Set (Position → Symbol)) - radius) : ℕ) :
        ENNReal) / Fintype.card Position) ^ queries := by
  simpa only [prEvent_norm] using prEvent_bind_le_of_forall_le coins
    (fun challenge => do
      let draw ← $ᵗ (Fin queries → Position)
      pure (challenge, draw))
    (fun pair => finish (claimed pair.1) ≠ finish (fun test => combine (weights test) source) ∧
      ∀ test, ColumnOpening.Agrees (combine (weights test) word) (claimed pair.1 test) pair.2)
    (fun challenge => by
      simpa only [prEvent_norm] using near_falseValue_bound C radius queries word source weights
        (claimed challenge) finish sourceC close (claimedC challenge))

end FormalProof4FHE.HasteBoots.StructuredOpening
