/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/
import FormalProof4FHE.LWE.GSWTranscriptCompiler

/-!
# Public two-sided quadratic corrections

Two retained same-secret source blocks give exact cancellation of the terms
linear in their errors. The remaining control residual is e₁ᵀ D e₂. The public
compiler is an instance of the complete stored ordinary-LWE source interface.
No efficient useful short-preimage builder or negligible failure guarantee is
asserted. In particular the tensor coefficient matrix is not assumed uniform.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.LWE.GSWTwoSidedCompiler

abbrev Builder (R : Type) (n p r k : ℕ) :=
  Matrix (Fin n) (Fin p) R → Matrix (Fin n) (Fin r) R →
    Fin k → Matrix (Fin p) (Fin r) R

def join {R : Type} {n p r : ℕ}
    (first : BatchTranscript R n p) (second : BatchTranscript R n r) :
    BatchTranscript R n (p + r) :=
  (fun row ↦ Fin.addCases (first.1 row) (second.1 row), Fin.addCases first.2 second.2)

def left {R : Type} {n p r : ℕ} (base : BatchTranscript R n (p + r)) :
    BatchTranscript R n p :=
  (fun row column ↦ base.1 row (Fin.castAdd r column), fun column ↦ base.2 (Fin.castAdd r column))

def right {R : Type} {n p r : ℕ} (base : BatchTranscript R n (p + r)) :
    BatchTranscript R n r :=
  (fun row column ↦ base.1 row (Fin.natAdd p column), fun column ↦ base.2 (Fin.natAdd p column))

@[simp] theorem left_join {R : Type} {n p r : ℕ}
    (first : BatchTranscript R n p) (second : BatchTranscript R n r) :
    left (join first second) = first := by
  simp [left, join]

@[simp] theorem right_join {R : Type} {n p r : ℕ}
    (first : BatchTranscript R n p) (second : BatchTranscript R n r) :
    right (join first second) = second := by
  simp [right, join]

def compiler {R : Type} [CommRing R] {n p r k : ℕ}
    (builder : Builder R n p r k) (linear : Matrix (Fin n) (Fin k) R)
    (offset : Fin k → R) : GSWTranscriptCompiler.Compiler R n (p + r) k :=
  fun base ↦
    let first := left base
    let second := right base
    (fun row column ↦ linear row column -
      (first.1.mulVec ((builder first.1 second.1 column).mulVec second.2)) row -
      (second.1.mulVec ((builder first.1 second.1 column).transpose.mulVec first.2)) row,
      fun column ↦ offset column + dotProduct first.2
        ((builder first.1 second.1 column).mulVec second.2))

theorem bilinear_cancellation {R : Type} [CommRing R] {p r : ℕ}
    (d : Matrix (Fin p) (Fin r) R) (x e : Fin p → R) (z f : Fin r → R) :
    dotProduct (x + e) (d.mulVec (z + f)) -
      dotProduct x (d.mulVec (z + f)) -
      dotProduct z (d.transpose.mulVec (x + e)) =
      -dotProduct x (d.mulVec z) + dotProduct e (d.mulVec f) := by
  rw [dotProduct_transpose_mulVec]
  simp only [mulVec_add, dotProduct_add, add_dotProduct]
  ring

theorem correction_real {R : Type} [CommRing R] {n p r k : ℕ}
    (builder : Builder R n p r k) (linear : Matrix (Fin n) (Fin k) R)
    (offset : Fin k → R) (a : Matrix (Fin n) (Fin p) R)
    (b : Matrix (Fin n) (Fin r) R) (secret : Fin n → R)
    (e : Fin p → R) (f : Fin r → R) (column : Fin k) :
    (compiler builder linear offset (join (a, vecMul secret a + e)
      (b, vecMul secret b + f))).2 column +
      vecMul secret (compiler builder linear offset (join (a, vecMul secret a + e)
        (b, vecMul secret b + f))).1 column =
      offset column + vecMul secret linear column -
        dotProduct secret ((a * builder a b column * b.transpose).mulVec secret) +
        dotProduct e ((builder a b column).mulVec f) := by
  simp only [compiler, left_join, right_join]
  change offset column + dotProduct (vecMul secret a + e)
      ((builder a b column).mulVec (vecMul secret b + f)) +
      dotProduct secret ((fun row ↦ linear row column) -
        a.mulVec ((builder a b column).mulVec (vecMul secret b + f)) -
        b.mulVec ((builder a b column).transpose.mulVec (vecMul secret a + e))) = _
  rw [dotProduct_sub, dotProduct_sub, dotProduct_mulVec secret a,
    dotProduct_mulVec secret b]
  have hc := bilinear_cancellation (builder a b column) (vecMul secret a) e (vecMul secret b) f
  have hq : dotProduct (vecMul secret a) ((builder a b column).mulVec (vecMul secret b)) =
      dotProduct secret ((a * builder a b column * b.transpose).mulVec secret) := by
    rw [← mulVec_transpose b secret, ← dotProduct_mulVec secret a,
      mulVec_mulVec, mulVec_mulVec]
  rw [hq] at hc
  change _ = offset column + dotProduct secret (fun row ↦ linear row column) - _ + _
  linear_combination hc

theorem quadratic_of_certificate {R : Type} [CommRing R] {n p r : ℕ}
    (a : Matrix (Fin n) (Fin p) R) (b : Matrix (Fin n) (Fin r) R)
    (d : Matrix (Fin p) (Fin r) R) (target witness : Matrix (Fin n) (Fin n) R)
    (hcertificate : a * d * b.transpose = -target + witness - witness.transpose)
    (secret : Fin n → R) :
    -dotProduct secret ((a * d * b.transpose).mulVec secret) =
      dotProduct secret (target.mulVec secret) := by
  rw [hcertificate, sub_mulVec, add_mulVec, neg_mulVec, dotProduct_sub,
    dotProduct_add, dotProduct_neg, dotProduct_transpose_mulVec]
  ring

theorem correction_of_certificate {R : Type} [CommRing R] {n p r k : ℕ}
    (builder : Builder R n p r k) (linear : Matrix (Fin n) (Fin k) R)
    (offset : Fin k → R) (a : Matrix (Fin n) (Fin p) R)
    (b : Matrix (Fin n) (Fin r) R) (secret : Fin n → R)
    (e : Fin p → R) (f : Fin r → R) (column : Fin k)
    (target witness : Matrix (Fin n) (Fin n) R)
    (hcertificate : a * builder a b column * b.transpose = -target + witness - witness.transpose) :
    (compiler builder linear offset (join (a, vecMul secret a + e)
      (b, vecMul secret b + f))).2 column +
      vecMul secret (compiler builder linear offset (join (a, vecMul secret a + e)
        (b, vecMul secret b + f))).1 column =
      offset column + vecMul secret linear column + dotProduct secret (target.mulVec secret) +
        dotProduct e ((builder a b column).mulVec f) := by
  rw [correction_real]
  have hq := quadratic_of_certificate a b (builder a b column) target witness hcertificate secret
  linear_combination hq

def nativeCompiler {q n p r : ℕ} [NeZero q] (params : GSWGadget.Parameters q)
    (builder : Builder (ZMod q) n p r (GSWQuadraticPreimageGSW.columns params n)) :=
  compiler builder (GSWQuadraticPreimageGSW.linear params n) 0

/-- Public diagonal coefficients can be absorbed into affine corrections for
binary secrets. The builder then only needs the off-diagonal constraints. -/
def diagonalCompiler {R : Type} [CommRing R] {n p r k : ℕ}
    (builder : Builder R n p r k) (linear : Matrix (Fin n) (Fin k) R)
    (offset : Fin k → R) : GSWTranscriptCompiler.Compiler R n (p + r) k :=
  fun base ↦ compiler builder
    (fun row column ↦ linear row column +
      ((left base).1 * builder (left base).1 (right base).1 column *
        (right base).1.transpose) row row) offset base

def nativeDiagonalCompiler {q n p r : ℕ} [NeZero q] (params : GSWGadget.Parameters q)
    (builder : Builder (ZMod q) n p r (GSWQuadraticPreimageGSW.columns params n)) :=
  diagonalCompiler builder (GSWQuadraticPreimageGSW.linear params n) 0

theorem binary_diagonal {R : Type} [CommRing R] {n : ℕ}
    (secret diagonalValues : Fin n → R)
    (hidempotent : ∀ row, secret row * secret row = secret row) :
    dotProduct secret ((Matrix.diagonal diagonalValues).mulVec secret) =
      dotProduct secret diagonalValues := by
  simp only [mulVec_diagonal, dotProduct]
  apply Finset.sum_congr rfl
  intro row _
  linear_combination diagonalValues row * hidempotent row

theorem quadratic_of_diagonal_certificate {R : Type} [CommRing R] {n p r : ℕ}
    (a : Matrix (Fin n) (Fin p) R) (b : Matrix (Fin n) (Fin r) R)
    (d : Matrix (Fin p) (Fin r) R) (target witness : Matrix (Fin n) (Fin n) R)
    (diagonalValues secret : Fin n → R)
    (hidempotent : ∀ row, secret row * secret row = secret row)
    (hcertificate : a * d * b.transpose =
      -target + Matrix.diagonal diagonalValues + witness - witness.transpose) :
    -dotProduct secret ((a * d * b.transpose).mulVec secret) =
      dotProduct secret (target.mulVec secret) - dotProduct secret diagonalValues := by
  rw [hcertificate, sub_mulVec, add_mulVec, add_mulVec, neg_mulVec,
    dotProduct_sub, dotProduct_add, dotProduct_add, dotProduct_neg,
    dotProduct_transpose_mulVec, binary_diagonal secret diagonalValues hidempotent]
  ring

theorem native_diagonal_discrepancy {q n p r : ℕ} [NeZero q] (params : GSWGadget.Parameters q)
    (builder : Builder (ZMod q) n p r (GSWQuadraticPreimageGSW.columns params n))
    (a : Matrix (Fin n) (Fin p) (ZMod q)) (b : Matrix (Fin n) (Fin r) (ZMod q))
    (secret : Fin n → ZMod q) (hidempotent : ∀ row, secret row * secret row = secret row)
    (e : Fin p → ZMod q) (f : Fin r → ZMod q)
    (column : Fin (GSWQuadraticPreimageGSW.columns params n))
    (witness : Matrix (Fin n) (Fin n) (ZMod q))
    (hcertificate : a * builder a b column * b.transpose =
      -GSWQuadraticPreimageGSW.quadratic params n column +
        Matrix.diagonal (fun row ↦ (a * builder a b column * b.transpose) row row) +
          witness - witness.transpose) :
    GSWTranscriptCompiler.discrepancy params (nativeDiagonalCompiler params builder) secret
      (join (a, vecMul secret a + e) (b, vecMul secret b + f)) column =
      dotProduct e ((builder a b column).mulVec f) := by
  unfold GSWTranscriptCompiler.discrepancy nativeDiagonalCompiler diagonalCompiler
  simp only [left_join, right_join]
  rw [correction_real]
  have hl : vecMul secret
      (fun row col ↦ GSWQuadraticPreimageGSW.linear params n row col +
        (a * builder a b col * b.transpose) row row) column =
      vecMul secret (GSWQuadraticPreimageGSW.linear params n) column +
        dotProduct secret (fun row ↦ (a * builder a b column * b.transpose) row row) := by
    simp [vecMul, dotProduct, mul_add, Finset.sum_add_distrib]
  rw [hl]
  have hq := quadratic_of_diagonal_certificate a b (builder a b column)
    (GSWQuadraticPreimageGSW.quadratic params n column) witness
    (fun row ↦ (a * builder a b column * b.transpose) row row) secret hidempotent hcertificate
  have ht := GSWQuadraticPreimageGSW.target_eq_phaseMessage params secret hidempotent column
  simp only [Pi.zero_apply] at *
  linear_combination hq + ht

theorem native_discrepancy {q n p r : ℕ} [NeZero q] (params : GSWGadget.Parameters q)
    (builder : Builder (ZMod q) n p r (GSWQuadraticPreimageGSW.columns params n))
    (a : Matrix (Fin n) (Fin p) (ZMod q)) (b : Matrix (Fin n) (Fin r) (ZMod q))
    (secret : Fin n → ZMod q) (hidempotent : ∀ row, secret row * secret row = secret row)
    (e : Fin p → ZMod q) (f : Fin r → ZMod q)
    (column : Fin (GSWQuadraticPreimageGSW.columns params n))
    (witness : Matrix (Fin n) (Fin n) (ZMod q))
    (hcertificate : a * builder a b column * b.transpose =
      -GSWQuadraticPreimageGSW.quadratic params n column + witness - witness.transpose) :
    GSWTranscriptCompiler.discrepancy params (nativeCompiler params builder) secret
      (join (a, vecMul secret a + e) (b, vecMul secret b + f)) column =
      dotProduct e ((builder a b column).mulVec f) := by
  unfold GSWTranscriptCompiler.discrepancy nativeCompiler
  rw [correction_of_certificate builder (GSWQuadraticPreimageGSW.linear params n) 0
    a b secret e f column (GSWQuadraticPreimageGSW.quadratic params n column) witness hcertificate]
  simp only [Pi.zero_apply, zero_add]
  rw [GSWQuadraticPreimageGSW.target_eq_phaseMessage params secret hidempotent column]
  ring

theorem residual_abs_le_l1 {p r : ℕ} (d : Matrix (Fin p) (Fin r) ℤ)
    (e : Fin p → ℤ) (f : Fin r → ℤ) (E1 E2 : ℤ) (hE1 : 0 ≤ E1)
    (he : ∀ row, |e row| ≤ E1) (hf : ∀ column, |f column| ≤ E2) :
    |dotProduct e (d.mulVec f)| ≤ E1 * E2 * ∑ row, ∑ column, |d row column| :=
  GSWQuadraticPreimage.residual_abs_le_l1 e d f E1 E2 hE1 he hf

open GSWQuadraticPreimageGSW GSWGadget

theorem control_noise {q n p r : ℕ} [NeZero q] (params : Parameters q)
    (builder : Builder (ZMod q) n p r (columns params n))
    (a : Matrix (Fin n) (Fin p) (ZMod q)) (b : Matrix (Fin n) (Fin r) (ZMod q))
    (secret : Fin n → ZMod q) (hidempotent : ∀ row, secret row * secret row = secret row)
    (e : Fin p → ZMod q) (f : Fin r → ZMod q)
    (mask : Matrix (Fin n) (Fin (columns params n)) (ZMod q))
    (error : Fin (columns params n) → ZMod q)
    (witness : Fin (columns params n) → Matrix (Fin n) (Fin n) (ZMod q))
    (hcertificate : ∀ column, a * builder a b column * b.transpose =
      -quadratic params n column + witness column - (witness column).transpose)
    (index : Fin n) :
    GSWOperations.noise (GSWOperations.extendedSecret secret) (gadget params (n + 1))
      (controlsEquiv params n (GSWTranscriptCompiler.simulate (nativeCompiler params builder)
        (join (a, vecMul secret a + e) (b, vecMul secret b + f),
          mask, vecMul secret mask + error)).2 index) (secret index) =
      fun column ↦ error (finProdFinEquiv (index, column)) +
        dotProduct e ((builder a b (finProdFinEquiv (index, column))).mulVec f) := by
  rw [GSWTranscriptCompiler.control_noise]
  funext column
  rw [native_discrepancy params builder a b secret hidempotent e f
    (finProdFinEquiv (index, column)) _ (hcertificate _)]

theorem diagonal_control_noise {q n p r : ℕ} [NeZero q] (params : Parameters q)
    (builder : Builder (ZMod q) n p r (columns params n))
    (a : Matrix (Fin n) (Fin p) (ZMod q)) (b : Matrix (Fin n) (Fin r) (ZMod q))
    (secret : Fin n → ZMod q) (hidempotent : ∀ row, secret row * secret row = secret row)
    (e : Fin p → ZMod q) (f : Fin r → ZMod q)
    (mask : Matrix (Fin n) (Fin (columns params n)) (ZMod q))
    (error : Fin (columns params n) → ZMod q)
    (witness : Fin (columns params n) → Matrix (Fin n) (Fin n) (ZMod q))
    (hcertificate : ∀ column, a * builder a b column * b.transpose =
      -quadratic params n column +
        Matrix.diagonal (fun row ↦ (a * builder a b column * b.transpose) row row) +
          witness column - (witness column).transpose)
    (index : Fin n) :
    GSWOperations.noise (GSWOperations.extendedSecret secret) (gadget params (n + 1))
      (controlsEquiv params n (GSWTranscriptCompiler.simulate (nativeDiagonalCompiler params builder)
        (join (a, vecMul secret a + e) (b, vecMul secret b + f),
          mask, vecMul secret mask + error)).2 index) (secret index) =
      fun column ↦ error (finProdFinEquiv (index, column)) +
        dotProduct e ((builder a b (finProdFinEquiv (index, column))).mulVec f) := by
  rw [GSWTranscriptCompiler.control_noise]
  funext column
  rw [native_diagonal_discrepancy params builder a b secret hidempotent e f
    (finProdFinEquiv (index, column)) _ (hcertificate _)]

/-- The complete stored adaptive game, with both retained source blocks.
This bound does not supply a short builder or a negligible loss family. -/
theorem stored_game_abs_advantage_le {q block n p r : ℕ} [NeZero q]
    (params : Parameters q)
    (builder : Builder (ZMod q) (n * block) p r (columns params (n * block)))
    (d : ℕ) (narrow wide : ProbComp (ZMod q))
    (adversary : StoredAdversary params (n * block) (p + r)) :
    |Pr[= true | GSWTranscriptCompiler.storedGame params (nativeCompiler params builder)
      wide adversary].toReal - 1 / 2| ≤
      GSWTranscriptCompiler.ordinaryLoss (b := block) (n := n) (nativeCompiler params builder)
        d narrow wide (fun view ↦ observe params (liftStoredAdversary params adversary)
          (viewEquiv params (n * block) (p + r) view)) +
        ((n * block + 1) * params.levels) *
          (Real.sqrt ((q : ℝ) ^ (n * block + 1) / (2 : ℝ) ^ (p + r)) / 2) :=
  GSWTranscriptCompiler.stored_game_abs_advantage_le params
    (nativeCompiler params builder) d narrow wide adversary

theorem diagonal_stored_game_abs_advantage_le {q block n p r : ℕ} [NeZero q]
    (params : Parameters q)
    (builder : Builder (ZMod q) (n * block) p r (columns params (n * block)))
    (d : ℕ) (narrow wide : ProbComp (ZMod q))
    (adversary : StoredAdversary params (n * block) (p + r)) :
    |Pr[= true | GSWTranscriptCompiler.storedGame params (nativeDiagonalCompiler params builder)
      wide adversary].toReal - 1 / 2| ≤
      GSWTranscriptCompiler.ordinaryLoss (b := block) (n := n) (nativeDiagonalCompiler params builder)
        d narrow wide (fun view ↦ observe params (liftStoredAdversary params adversary)
          (viewEquiv params (n * block) (p + r) view)) +
        ((n * block + 1) * params.levels) *
          (Real.sqrt ((q : ℝ) ^ (n * block + 1) / (2 : ℝ) ^ (p + r)) / 2) :=
  GSWTranscriptCompiler.stored_game_abs_advantage_le params
    (nativeDiagonalCompiler params builder) d narrow wide adversary

end FormalProof4FHE.LWE.GSWTwoSidedCompiler
