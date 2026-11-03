module

public import FormalProof4FHE.HasteBoots.PaddedExtension
public import FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim
public import FormalProof4FHE.HasteBoots.PackedEqualityCube

@[expose] public section

/-!
# Extension evaluations through original base-field queries

The ordered matrices and optional terminal matrix model packed_extension.rs.
No padding premise is imposed on committed source vectors. In particular,
zero-variable queries open the original constant vector before applying a
local projection or lane map. Scalar lane maps act on the right of the first
pair, before extension row multiplication. These identities transfer a false
extension terminal to a false original base-field PCS opening; they do not
postulate a commitment over the lookup extension field.
-/

open scoped BigOperators Classical
open Matrix

namespace FormalProof4FHE.HasteBoots.ExtensionQuery

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] {d padding n : ℕ}

abbrev Width (d padding : ℕ) := Fin (d + padding)

/-- The post-map is local and is applied after opening the original root. -/
structure Broadcast (F : Type) (width n : ℕ) where
  query : PackedSumcheckSubclaim.Query F width n
  post : Option (Matrix (Fin width) (Fin width) F)

def Broadcast.finish (query : Broadcast F (d + padding) n) (value : Width d padding → F) : Width d padding → F :=
  match query.post with
  | none => value
  | some matrix => matrix *ᵥ value

def Broadcast.evaluate (query : Broadcast F (d + padding) n) (table : MatrixFold.Cube n → Width d padding → F) :
    Width d padding → F := query.finish (query.query.fold table)

/-- Eliminate point coordinates in native low-bit-first row order. -/
def evaluate : (n : ℕ) → (Fin n → K) → (MatrixFold.Cube n → K) → K
  | 0, _, table => table ()
  | n + 1, point, table => evaluate n (fun i => point i.succ)
      (fun suffix => (1 - point 0) * table (false, suffix) + point 0 * table (true, suffix))

/-- The recurrence is the ordinary tensor MLE, with the first coordinate
corresponding to the low Boolean bit. -/
theorem evaluate_eq_sum (point : Fin n → K) (table : MatrixFold.Cube n → K) :
    evaluate n point table = ∑ cell, PackedEqualityCube.weight point cell * table cell := by
  induction n with
  | zero =>
    have : Subsingleton (MatrixFold.Cube 0) := inferInstanceAs (Subsingleton Unit)
    calc
      evaluate 0 point table = ∑ cell : MatrixFold.Cube 0, table cell :=
        (Fintype.sum_subsingleton table ()).symm
      _ = ∑ cell, PackedEqualityCube.weight point cell * table cell := by
        apply Finset.sum_congr rfl
        intro cell _
        rw [PackedEqualityCube.weight_zero, one_mul]
  | succ n ih =>
    change evaluate n (fun i => point i.succ)
      (fun suffix => (1 - point 0) * table (false, suffix) + point 0 * table (true, suffix)) =
        ∑ cell : Bool × MatrixFold.Cube n, PackedEqualityCube.weight point cell * table cell
    rw [ih]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, PackedEqualityCube.weight_succ,
      Bool.false_eq_true, ite_false, ite_true]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro cell _
    rw [mul_add]
    ac_rfl

def coefficients (basis : Module.Basis (Fin d) F K) : (n : ℕ) → (Fin n → K) → PackedSumcheckSubclaim.Query F (d + padding) n
  | 0, _ => .nil
  | n + 1, point => .cons (fun bit => PaddedExtension.multiplication basis (if bit then point 0 else 1 - point 0))
      (coefficients basis n (fun i => point i.succ))

/-- Even a source with arbitrary unused helper lanes folds to an encoding. -/
theorem foldFirst_coefficients (basis : Module.Basis (Fin d) F K) (x : K)
    (table : MatrixFold.Cube (n + 1) → Width d padding → F) :
    MatrixFold.foldFirst (fun bit => PaddedExtension.multiplication basis (if bit then x else 1 - x)) table =
      fun suffix => PaddedExtension.encode basis
        ((1 - x) * PaddedExtension.decode basis (table (false, suffix)) +
          x * PaddedExtension.decode basis (table (true, suffix))) := by
  funext suffix
  simp only [MatrixFold.foldFirst, Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true,
    PaddedExtension.multiplication_mulVec, map_add]
  exact add_comm _ _

theorem coefficients_encoded (basis : Module.Basis (Fin d) F K) (point : Fin n → K)
    (table : MatrixFold.Cube n → K) :
    (coefficients (padding := padding) basis n point).fold (fun cell => PaddedExtension.encode basis (table cell)) =
      PaddedExtension.encode basis (evaluate n point table) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [coefficients, PackedSumcheckSubclaim.Query.fold, foldFirst_coefficients]
    simp only [PaddedExtension.decode_encode]
    exact ih _ _

def coefficientsQuery (basis : Module.Basis (Fin d) F K) (point : Fin n → K) : Broadcast F (d + padding) n :=
  ⟨coefficients basis n point, if n = 0 then some (PaddedExtension.multiplication basis 1) else none⟩

theorem coefficients_evaluate (basis : Module.Basis (Fin d) F K) (point : Fin n → K)
    (table : MatrixFold.Cube n → Width d padding → F) :
    (coefficientsQuery basis point).evaluate table =
      PaddedExtension.encode basis (evaluate n point (fun cell => PaddedExtension.decode basis (table cell))) := by
  cases n with
  | zero => exact PaddedExtension.projection_mulVec basis (table ())
  | succ n =>
    change (coefficients basis (n + 1) point).fold table = _
    rw [coefficients, PackedSumcheckSubclaim.Query.fold, foldFirst_coefficients, coefficients_encoded]
    rfl

/-- This map reads every original scalar lane, including lanes that would be
ignored by the helper decoder. -/
def laneValue (weights : Width d padding → K) (values : Width d padding → F) : K :=
  ∑ lane, values lane • weights lane

def laneMatrix (basis : Module.Basis (Fin d) F K) (weights : Width d padding → K) :
    Matrix (Width d padding) (Width d padding) F := fun row column => PaddedExtension.encode basis (weights column) row

theorem laneValue_algebraMap (weights : Width d padding → K) (values : Width d padding → F) :
    laneValue weights values = ∑ lane, weights lane * algebraMap F K (values lane) := by
  simp only [laneValue, Algebra.smul_def, mul_comm]

theorem laneMatrix_mulVec (basis : Module.Basis (Fin d) F K) (weights : Width d padding → K)
    (values : Width d padding → F) :
    laneMatrix basis weights *ᵥ values = PaddedExtension.encode basis (laneValue weights values) := by
  funext row
  simp only [Matrix.mulVec, dotProduct, laneMatrix, laneValue, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- The first pair is M(weight)*L: L acts first. With no row variable,
the lane map replaces the helper projection as the local post-map. -/
def scalarQuery (basis : Module.Basis (Fin d) F K) (weights : Width d padding → K) :
    (n : ℕ) → (Fin n → K) → Broadcast F (d + padding) n
  | 0, _ => ⟨.nil, some (laneMatrix basis weights)⟩
  | n + 1, point => ⟨.cons
      (fun bit => PaddedExtension.multiplication basis (if bit then point 0 else 1 - point 0) * laneMatrix basis weights)
      (coefficients basis n (fun i => point i.succ)), none⟩

theorem foldFirst_scalar (basis : Module.Basis (Fin d) F K) (weights : Width d padding → K) (x : K)
    (table : MatrixFold.Cube (n + 1) → Width d padding → F) :
    MatrixFold.foldFirst
      (fun bit => PaddedExtension.multiplication basis (if bit then x else 1 - x) * laneMatrix basis weights) table =
      fun suffix => PaddedExtension.encode basis
        ((1 - x) * laneValue weights (table (false, suffix)) + x * laneValue weights (table (true, suffix))) := by
  funext suffix
  simp only [MatrixFold.foldFirst, Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true,
    ← Matrix.mulVec_mulVec, laneMatrix_mulVec, PaddedExtension.multiplication_encode, map_add]
  exact add_comm _ _

theorem scalar_evaluate (basis : Module.Basis (Fin d) F K) (weights : Width d padding → K) (point : Fin n → K)
    (table : MatrixFold.Cube n → Width d padding → F) :
    (scalarQuery basis weights n point).evaluate table =
      PaddedExtension.encode basis (evaluate n point (fun cell => laneValue weights (table cell))) := by
  cases n with
  | zero => exact laneMatrix_mulVec basis weights (table ())
  | succ n =>
    change (coefficients basis n (fun i => point i.succ)).fold (MatrixFold.foldFirst _ table) = _
    rw [foldFirst_scalar, coefficients_encoded]
    rfl

/-- Native low lane bits select tensor weights; the equivalence fixes their
address order without identifying lookup degree with the packing width. -/
def laneWeights {c : ℕ} (lanes : Width d padding ≃ MatrixFold.Cube c) (point : Fin c → K) : Width d padding → K :=
  fun lane => PackedEqualityCube.weight point (lanes lane)

/-- Canonical lane coordinates use the same low-bit address equivalence as
base-field PCS. The equality is the trusted power-of-two shape check. -/
def nativeLanes {c : ℕ} (shape : d + padding = 2 ^ c) : Width d padding ≃ MatrixFold.Cube c :=
  (finCongr shape).trans (FlatMatrixFold.index c).symm

theorem nativeLanes_index {c : ℕ} (shape : d + padding = 2 ^ c) (lane : Width d padding) :
    (FlatMatrixFold.index c (nativeLanes shape lane)).val = lane.val := by
  simp [nativeLanes]

theorem nativeLanes_bits {c : ℕ} (shape : d + padding = 2 ^ c) (lane : Width d padding) :
    lane.val = ∑ i : Fin c, 2 ^ i.val * (PackedEqualityCube.bits c (nativeLanes shape lane) i).val := by
  rw [← nativeLanes_index shape lane, PackedEqualityCube.index_eq_sum_bits]

/-- Tensor interpretation of the scalar source: lane bits are low and row
bits are high. The original base entries occur under the field embedding. -/
theorem scalar_evaluate_tensor (basis : Module.Basis (Fin d) F K) {c : ℕ}
    (lanes : Width d padding ≃ MatrixFold.Cube c) (lanePoint : Fin c → K) (rowPoint : Fin n → K)
    (table : MatrixFold.Cube n → Width d padding → F) :
    (scalarQuery basis (laneWeights lanes lanePoint) n rowPoint).evaluate table =
      PaddedExtension.encode basis (∑ row, PackedEqualityCube.weight rowPoint row *
        ∑ lane, PackedEqualityCube.weight lanePoint (lanes lane) * algebraMap F K (table row lane)) := by
  rw [scalar_evaluate, evaluate_eq_sum]
  simp only [laneValue_algebraMap, laneWeights]

/-- If the post-map decodes an incorrect extension claim successfully, the
underlying claim differs from the fold of the original base-field table. -/
theorem false_claim (basis : Module.Basis (Fin d) F K) (query : Broadcast F (d + padding) n)
    (table : MatrixFold.Cube n → Width d padding → F) (truth expected : K) (claimed : Width d padding → F)
    (semantics : query.evaluate table = PaddedExtension.encode basis truth)
    (accepted : PaddedExtension.element basis (query.finish claimed) = some expected) (wrong : expected ≠ truth) :
    claimed ≠ query.query.fold table := by
  intro equal
  rw [equal, ← Broadcast.evaluate, semantics, PaddedExtension.element_encode] at accepted
  exact wrong (Option.some.inj accepted.symm)

theorem coefficients_false_claim (basis : Module.Basis (Fin d) F K) (point : Fin n → K)
    (table : MatrixFold.Cube n → Width d padding → F) (expected : K) (claimed : Width d padding → F)
    (accepted : PaddedExtension.element basis ((coefficientsQuery basis point).finish claimed) = some expected)
    (wrong : expected ≠ evaluate n point (fun cell => PaddedExtension.decode basis (table cell))) :
    claimed ≠ (coefficientsQuery basis point).query.fold table :=
  false_claim basis _ table _ expected claimed (coefficients_evaluate basis point table) accepted wrong

theorem scalar_false_claim (basis : Module.Basis (Fin d) F K) (weights : Width d padding → K) (point : Fin n → K)
    (table : MatrixFold.Cube n → Width d padding → F) (expected : K) (claimed : Width d padding → F)
    (accepted : PaddedExtension.element basis ((scalarQuery basis weights n point).finish claimed) = some expected)
    (wrong : expected ≠ evaluate n point (fun cell => laneValue weights (table cell))) :
    claimed ≠ (scalarQuery basis weights n point).query.fold table :=
  false_claim basis _ table _ expected claimed (scalar_evaluate basis weights point table) accepted wrong

end

end FormalProof4FHE.HasteBoots.ExtensionQuery
