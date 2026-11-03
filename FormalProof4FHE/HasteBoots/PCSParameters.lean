module

public import FormalProof4FHE.HasteBoots.JointMatrixOpening

@[expose] public section

/-!
# Explicit PCS arithmetic parameters

For positive message and symbol widths, both scalar lifted RS and base block
RS have minimum distance L-m+1 (with truncating Nat subtraction). Expanding
the exact shared-column miss terms removes the auxiliary field and domain
from the arithmetic loss. The ordered query quota remains a public protocol
parameter; it is not a bound on adversary oracle work.
-/

namespace FormalProof4FHE.HasteBoots.PCSParameters

noncomputable section

def distance (height m : ℕ) : ℕ := 2 ^ height - m + 1

def miss (height queries delta : ℕ) : ENNReal :=
  (((2 ^ height - delta : ℕ) : ENNReal) / (2 ^ height : ℕ)) ^ queries

def error (q b height m queries radius : ℕ) : ENNReal :=
  (distance height m : ENNReal) / (q : ENNReal) ^ b +
    max (miss height queries (distance height m - radius)) (miss height queries (radius + 1))

/-- The same expression in finite nonnegative reals, for arithmetic checking. -/
def finiteError (q b height m queries radius : ℕ) : NNReal :=
  (distance height m : NNReal) / (q : NNReal) ^ b +
    max ((((2 ^ height - (distance height m - radius) : ℕ) : NNReal) / (2 ^ height : ℕ)) ^ queries)
      ((((2 ^ height - (radius + 1) : ℕ) : NNReal) / (2 ^ height : ℕ)) ^ queries)

/-- Nonzero alphabet size is essential: ENNReal division by zero cannot be
identified with finite-real division. No loss term is discarded in this bridge. -/
theorem finiteError_coe (q b height m queries radius : ℕ) (nonzero : q ≠ 0) :
    (finiteError q b height m queries radius : ENNReal) = error q b height m queries radius := by
  have alphabetNonzero : (q : NNReal) ^ b ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr nonzero)
  have lengthNonzero : ((2 ^ height : ℕ) : NNReal) ≠ 0 := by positivity
  simp only [finiteError, error, miss, ENNReal.coe_add, ENNReal.coe_max, ENNReal.coe_pow,
    ENNReal.coe_div alphabetNonzero, ENNReal.coe_div lengthNonzero, ENNReal.coe_natCast]

theorem error_ne_top (q b height m queries radius : ℕ) (nonzero : q ≠ 0) :
    error q b height m queries radius ≠ ⊤ := by
  rw [← finiteError_coe q b height m queries radius nonzero]
  exact ENNReal.coe_ne_top

variable {F K : Type} [Field F] [DecidableEq F] [Field K] [DecidableEq K]
  [Algebra F K] [Fintype F] [Fintype K] {height m b : ℕ} [NeZero m] [NeZero b]

omit [DecidableEq F] [Fintype F] [Fintype K] in
/-- Scalar distance is independent of which degree-b extension is constructed. -/
theorem lifted_distance (domain : Fin (2 ^ height) ↪ F) :
    Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
      Set (Fin (2 ^ height) → K)) = distance height m := by
  rw [ReedSolomon.minDist_eq_card_sub_min_add_1]
  simp only [Fintype.card_fin, distance]
  omega

omit [Fintype F] in
theorem block_distance (domain : Fin (2 ^ height) ↪ F) :
    Code.minDist (BlockCode.code domain m b : Set (Fin (2 ^ height) → Fin b → F)) = distance height m := by
  simpa only [Fintype.card_fin, distance] using BlockCode.minDist domain m b (Nat.pos_of_ne_zero (NeZero.ne m))

theorem miss_eq (queries delta : ℕ) :
    ColumnOpening.missBound (Fin (2 ^ height)) queries delta = miss height queries delta := by
  simp only [ColumnOpening.missBound, miss, Fintype.card_fin]

omit [Fintype K] in
/-- Exact equality, retaining both competing miss terms and the AHIV22 loss. -/
theorem error_eq (domain : Fin (2 ^ height) ↪ F) (queries radius : ℕ) :
    JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) domain radius =
      error (Fintype.card F) b height m queries radius := by
  simp only [JointMatrixOpening.error, lifted_distance, block_distance, miss_eq, error]

end

end FormalProof4FHE.HasteBoots.PCSParameters
