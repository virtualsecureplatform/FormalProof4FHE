module

public import FormalProof4FHE.HasteBoots.NativePrefixMask
public import FormalProof4FHE.HasteBoots.ReciprocalMask
public import FormalProof4FHE.HasteBoots.TupleHash

@[expose] public section

/-!
# The native extension lookup identity

Public EQ and active-prefix factors are evaluated by the verifier. Hashing
commutes with ordinary scalar MLE evaluation. The identity is a product of
separate MLE factors, not the MLE of the pointwise residual off the cube.
Its three partial-table terms have arities 2, 4 and 2; the full-table variant
has arities 3 and 1, including the affine r+g operation. This supplies the
native degree bounds and literal terminal algebra, not yet the complete
shared lookup sumcheck/PCS execution or its final soundness bound.
-/

open scoped BigOperators Classical

namespace FormalProof4FHE.HasteBoots.ExtensionLookupIdentity

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] {n width : ℕ}

/-- Native zip/fold equality evaluator (both points have a trusted dimension). -/
def equality (first second : Fin n → K) : K :=
  ∏ i, (first i * second i + (1 - first i) * (1 - second i))

theorem evaluate_mul (point : Fin n → K) (coefficient : K) (table : MatrixFold.Cube n → K) :
    ExtensionQuery.evaluate n point (fun cell => coefficient * table cell) =
      coefficient * ExtensionQuery.evaluate n point table := by
  rw [ExtensionQuery.evaluate_eq_sum, ExtensionQuery.evaluate_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem evaluate_add (point : Fin n → K) (first second : MatrixFold.Cube n → K) :
    ExtensionQuery.evaluate n point (fun cell => first cell + second cell) =
      ExtensionQuery.evaluate n point first + ExtensionQuery.evaluate n point second := by
  simp only [ExtensionQuery.evaluate_eq_sum, mul_add, Finset.sum_add_distrib]

theorem evaluate_sum {Index : Type} [Fintype Index] (point : Fin n → K)
    (tables : Index → MatrixFold.Cube n → K) :
    ExtensionQuery.evaluate n point (fun cell => ∑ i, tables i cell) =
      ∑ i, ExtensionQuery.evaluate n point (tables i) := by
  simp only [ExtensionQuery.evaluate_eq_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem evaluate_const (point : Fin n → K) (value : K) :
    ExtensionQuery.evaluate n point (fun _ => value) = value := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ExtensionQuery.evaluate]
    have table : (fun _ : MatrixFold.Cube n => (1 - point 0) * value + point 0 * value) = fun _ => value := by
      funext cell
      ring
    rw [table, ih]

theorem evaluate_translate (point : Fin n → K) (table : MatrixFold.Cube n → K) (value : K) :
    ExtensionQuery.evaluate n point (fun cell => table cell + value) = ExtensionQuery.evaluate n point table + value := by
  rw [evaluate_add, evaluate_const]

/-- The verifier computes the public EQ factor; it is not another opening. -/
theorem evaluate_equality (eqPoint point : Fin n → K) :
    ExtensionQuery.evaluate n point (PackedEqualityCube.weight eqPoint) = equality eqPoint point := by
  induction n with
  | zero =>
    exact (PackedEqualityCube.weight_zero eqPoint ()).trans
      (show (1 : K) = equality eqPoint point by simp [equality])
  | succ n ih =>
    rw [ExtensionQuery.evaluate]
    have table : (fun suffix : MatrixFold.Cube n =>
        (1 - point 0) * PackedEqualityCube.weight eqPoint (false, suffix) +
          point 0 * PackedEqualityCube.weight eqPoint (true, suffix)) =
        fun suffix => ((eqPoint 0 * point 0) + (1 - eqPoint 0) * (1 - point 0)) *
          PackedEqualityCube.weight (fun i => eqPoint i.succ) suffix := by
      funext suffix
      simp only [PackedEqualityCube.weight_succ, Bool.false_eq_true, ite_false, ite_true]
      ring
    rw [table, evaluate_mul, ih]
    simp only [equality, Fin.prod_univ_succ]

/-- Native powers weight the original base-field source tuple. -/
def hashTable (y : K) (sources : Fin width → MatrixFold.Cube n → F) : MatrixFold.Cube n → K :=
  fun cell => TupleHash.hash y (fun i => sources i cell)

theorem evaluate_hash (y : K) (point : Fin n → K) (sources : Fin width → MatrixFold.Cube n → F) :
    ExtensionQuery.evaluate n point (hashTable y sources) =
      ∑ i : Fin width, y ^ i.val * ExtensionQuery.evaluate n point (fun cell => algebraMap F K (sources i cell)) := by
  unfold hashTable
  simp only [TupleHash.hash_eq_sum]
  rw [evaluate_sum]
  exact Finset.sum_congr rfl (fun _ _ => evaluate_mul _ _ _)

inductive Factor
  | eq | helper | hash | mask
  deriving DecidableEq

instance : Fintype Factor where
  elems := {.eq, .helper, .hash, .mask}
  complete factor := by cases factor <;> simp

inductive PartialTerm
  | reciprocal | product | subtractMask
  deriving DecidableEq

instance : Fintype PartialTerm where
  elems := {.reciprocal, .product, .subtractMask}
  complete term := by cases term <;> simp

def partialArity : PartialTerm → ℕ
  | .reciprocal => 2
  | .product => 4
  | .subtractMask => 2

def partialCoefficient (r : K) : PartialTerm → K
  | .reciprocal => r
  | .product => 1
  | .subtractMask => -1

def partialIndices : (term : PartialTerm) → Fin (partialArity term) → Factor
  | .reciprocal => ![.eq, .helper]
  | .product => ![.eq, .mask, .hash, .helper]
  | .subtractMask => ![.eq, .mask]

theorem partial_degree (term : PartialTerm) : partialArity term ≤ 4 := by cases term <;> decide

theorem partial_expression (r : K) (values : Factor → K) :
    PackedSumcheckRound.expression partialArity (partialCoefficient r) partialIndices values =
      values .eq * (r * values .helper + values .mask * values .hash * values .helper - values .mask) := by
  unfold PackedSumcheckRound.expression
  rw [show (Finset.univ : Finset PartialTerm) = {.reciprocal, .product, .subtractMask} from rfl]
  simp [partialArity, partialCoefficient, partialIndices]
  change r * (∏ j : Fin 2, values (![Factor.eq, .helper] j)) +
    ((∏ j : Fin 4, values (![Factor.eq, .mask, .hash, .helper] j)) +
    -(∏ j : Fin 2, values (![Factor.eq, .mask] j))) = _
  simp [Fin.prod_univ_succ]
  ring

inductive FullTerm
  | product | subtractOne
  deriving DecidableEq

instance : Fintype FullTerm where
  elems := {.product, .subtractOne}
  complete term := by cases term <;> simp

def fullArity : FullTerm → ℕ
  | .product => 3
  | .subtractOne => 1

def fullCoefficient : FullTerm → K
  | .product => 1
  | .subtractOne => -1

/-- The full-table native affine operation g↦g+r is represented as a derived
hash factor. It does not require a new committed source. -/
def fullIndices : (term : FullTerm) → Fin (fullArity term) → Factor
  | .product => ![.eq, .helper, .hash]
  | .subtractOne => ![.eq]

theorem full_degree (term : FullTerm) : fullArity term ≤ 3 := by cases term <;> decide

theorem full_expression (r : K) (values : Factor → K) :
    PackedSumcheckRound.expression fullArity (fullCoefficient (K := K)) fullIndices
      (fun factor => if factor = .hash then values .hash + r else values factor) =
      values .eq * (r * values .helper + values .hash * values .helper - 1) := by
  unfold PackedSumcheckRound.expression
  rw [show (Finset.univ : Finset FullTerm) = {.product, .subtractOne} from rfl]
  simp [fullArity, fullCoefficient, fullIndices]
  change (∏ j : Fin 3, if (![Factor.eq, .helper, .hash] j) = Factor.hash then values .hash + r else
    values (![Factor.eq, .helper, .hash] j)) + -values .eq ^ (Finset.univ : Finset (Fin 1)).card = _
  simp [Fin.prod_univ_succ]
  ring

/-- The literal Boolean active-prefix source, separate from helper padding. -/
def maskTable (count : ℕ) : MatrixFold.Cube n → K :=
  fun cell => if (FlatMatrixFold.index n cell).val < count then 1 else 0

def factors (eqPoint : Fin n → K) (y : K) (sources : Fin width → MatrixFold.Cube n → F)
    (helpers : MatrixFold.Cube n → K) (count : ℕ) : Factor → MatrixFold.Cube n → K
  | .eq => PackedEqualityCube.weight eqPoint
  | .helper => helpers
  | .hash => hashTable y sources
  | .mask => maskTable count

/-- Native local terminal formula, including the verifier-computed mask. -/
def terminal (eqPoint point : Fin n → K) (r source helper : K) (count : ℕ) (enough : count ≤ 2 ^ n) : K :=
  equality eqPoint point * (r * helper + NativePrefixMask.evaluatePrefix point count enough * source * helper -
    NativePrefixMask.evaluatePrefix point count enough)

theorem partial_terminal (eqPoint point : Fin n → K) (r y : K)
    (sources : Fin width → MatrixFold.Cube n → F) (helpers : MatrixFold.Cube n → K)
    (count : ℕ) (enough : count ≤ 2 ^ n) :
    PackedSumcheckRound.expression partialArity (partialCoefficient r) partialIndices
      (fun factor => ExtensionQuery.evaluate n point (factors eqPoint y sources helpers count factor)) =
      terminal eqPoint point r (ExtensionQuery.evaluate n point (hashTable y sources))
        (ExtensionQuery.evaluate n point helpers) count enough := by
  rw [partial_expression]
  simp only [factors, evaluate_equality]
  have maskEq : ExtensionQuery.evaluate n point (maskTable count) =
      NativePrefixMask.evaluatePrefix point count enough :=
    (NativePrefixMask.prefix_eq_evaluate point count enough).symm
  rw [maskEq]
  rfl

/-- The exact Boolean identity is EQ times the masked reciprocal residual.
Off the cube the separate MLE factors must remain separate. -/
theorem partial_boolean (eqPoint : Fin n → K) (r y : K)
    (sources : Fin width → MatrixFold.Cube n → F) (helpers : MatrixFold.Cube n → K) (count : ℕ)
    (cell : MatrixFold.Cube n) :
    PackedSumcheckRound.expression partialArity (partialCoefficient r) partialIndices
      (fun factor => factors eqPoint y sources helpers count factor cell) =
      PackedEqualityCube.weight eqPoint cell * ReciprocalMask.residual r (hashTable y sources cell) (helpers cell)
        (decide ((FlatMatrixFold.index n cell).val < count)) := by
  rw [partial_expression]
  simp only [factors, maskTable, ReciprocalMask.residual, decide_eq_true_eq]

/-- Every native partial-identity sum is exactly an EQ-weighted residual sum. -/
theorem partial_sum (eqPoint : Fin n → K) (r y : K)
    (sources : Fin width → MatrixFold.Cube n → F) (helpers : MatrixFold.Cube n → K) (count : ℕ) :
    (∑ cell, PackedSumcheckRound.expression partialArity (partialCoefficient r) partialIndices
      (fun factor => factors eqPoint y sources helpers count factor cell)) =
      ∑ cell, PackedEqualityCube.weight eqPoint cell * ReciprocalMask.residual r (hashTable y sources cell) (helpers cell)
        (decide ((FlatMatrixFold.index n cell).val < count)) := by
  exact Finset.sum_congr rfl (fun _ _ => partial_boolean _ _ _ _ _ _ _)

theorem terminal_full (eqPoint point : Fin n → K) (r source helper : K) :
    terminal eqPoint point r source helper (2 ^ n) le_rfl =
      equality eqPoint point * (r * helper + source * helper - 1) := by
  simp only [terminal, NativePrefixMask.prefix_full, one_mul]

/-- The native full-table affine hash factor folds as g(point)+r. The
shift is computed locally and needs no additional commitment. -/
theorem full_terminal (eqPoint point : Fin n → K) (r y : K)
    (sources : Fin width → MatrixFold.Cube n → F) (helpers : MatrixFold.Cube n → K) :
    PackedSumcheckRound.expression fullArity (fullCoefficient (K := K)) fullIndices
      (fun factor => ExtensionQuery.evaluate n point (fun cell =>
        if factor = .hash then hashTable y sources cell + r else factors eqPoint y sources helpers (2 ^ n) factor cell)) =
      terminal eqPoint point r (ExtensionQuery.evaluate n point (hashTable y sources))
        (ExtensionQuery.evaluate n point helpers) (2 ^ n) le_rfl := by
  have shifted : (fun factor => ExtensionQuery.evaluate n point (fun cell =>
      if factor = .hash then hashTable y sources cell + r else factors eqPoint y sources helpers (2 ^ n) factor cell)) =
      fun factor => if factor = Factor.hash then
        ExtensionQuery.evaluate n point (factors eqPoint y sources helpers (2 ^ n) .hash) + r else
        ExtensionQuery.evaluate n point (factors eqPoint y sources helpers (2 ^ n) factor) := by
    funext factor
    by_cases equal : factor = .hash
    · subst factor
      simp only [ite_true]
      exact evaluate_translate _ _ _
    · simp only [equal, ite_false]
  rw [shifted, full_expression r (fun factor => ExtensionQuery.evaluate n point
    (factors eqPoint y sources helpers (2 ^ n) factor)), terminal_full]
  simp only [factors, evaluate_equality]

theorem partial_round_degree {Suffix : Type} [Fintype Suffix] {k : ℕ}
    (nodes : PackedSumcheckRound.Node k ↪ K) (r : K) (tables : Factor → Bool → Suffix → Fin k → K) :
    (PackedSumcheckRound.polynomial nodes partialArity (partialCoefficient r) partialIndices tables).natDegree ≤
      (2 * k - 1) * 4 :=
  PackedSumcheckRound.polynomial_degree nodes partialArity (partialCoefficient r) partialIndices tables 4 partial_degree

theorem full_round_degree {Suffix : Type} [Fintype Suffix] {k : ℕ}
    (nodes : PackedSumcheckRound.Node k ↪ K) (tables : Factor → Bool → Suffix → Fin k → K) :
    (PackedSumcheckRound.polynomial nodes fullArity (fullCoefficient (K := K)) fullIndices tables).natDegree ≤
      (2 * k - 1) * 3 :=
  PackedSumcheckRound.polynomial_degree nodes fullArity fullCoefficient fullIndices tables 3 full_degree

/-- One fresh public EQ point detects a fixed false masked identity. Sources
and helpers precede this draw; adaptive post-draw helpers are not permitted. -/
theorem equality_miss_bound [Fintype K] [SampleableType K] [SampleableType (Fin n → K)]
    (r y : K) (sources : Fin width → MatrixFold.Cube n → F) (helpers : MatrixFold.Cube n → K) (count : ℕ)
    (bad : ∃ cell, ReciprocalMask.residual r (hashTable y sources cell) (helpers cell)
      (decide ((FlatMatrixFold.index n cell).val < count)) ≠ 0) :
    Pr{let eqPoint ← $ᵗ (Fin n → K)}[
      (∑ cell, PackedSumcheckRound.expression partialArity (partialCoefficient r) partialIndices
        (fun factor => factors eqPoint y sources helpers count factor cell)) = 0] ≤
      (n : ENNReal) / Fintype.card K := by
  obtain ⟨cell, nonzero⟩ := bad
  have detection := PackedZeroEquality.point_bound
    (fun bits : PackedZeroEquality.Cell n =>
      ReciprocalMask.residual r (hashTable y sources ((PackedEqualityCube.bits n).symm bits))
        (helpers ((PackedEqualityCube.bits n).symm bits))
        (decide ((FlatMatrixFold.index n ((PackedEqualityCube.bits n).symm bits)).val < count)))
    ⟨PackedEqualityCube.bits n cell, by simpa only [Equiv.symm_apply_apply] using nonzero⟩
  simpa only [partial_sum, PackedEqualityCube.weighted_sum] using detection

end

end FormalProof4FHE.HasteBoots.ExtensionLookupIdentity
