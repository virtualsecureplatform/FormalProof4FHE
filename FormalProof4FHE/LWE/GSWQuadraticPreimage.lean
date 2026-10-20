/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.TwoBlock
import FormalProof4FHE.Probability.FiniteProduct

/-!
# A correlated-control source transformation

Retain one LWE batch (A,y). For each second-batch column (a₀,y₀), publish
(a₀ - linear - B(A)y, y₀ + offset). This public triangular shear is a
bijection of the ENTIRE tape, independent of the encryption secret. Its
uniform endpoint is exactly uniform and its real-view advantage is exactly
that of one ordinary uniform-secret batch-LWE reduction.

The actual phase is linear(s)+offset+sᵀBAᵀs+e₀+sᵀBe. Thus a short public
quadratic-preimage builder could provide the quadratic mask phases of all
native GSW key-bit controls without expanding the decryption features.

NO efficient short builder is constructed or assumed to exist here. The
identities hold for any public builder, even an unsuitable one. In particular,
uniform-secret noise is not bounded by a binary-secret estimate; a usable
small-secret source must itself be reduced to ordinary LWE. The companion
GSWQuadraticPreimageBinary supplies that finite reduction with explicit losses;
parameters, complete gadget materialization and bootstrap closure remain
obligations. The actual integer residual bound and a division-free public
alternating certificate are proved below.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.LWE.GSWQuadraticPreimage

abbrev View (R : Type) (n m k : ℕ) :=
  BatchTranscript R n m × BatchTranscript R n k

abbrev Builder (R : Type) (n m k : ℕ) :=
  Matrix (Fin n) (Fin m) R → Fin k → Matrix (Fin n) (Fin m) R

def correction {R : Type} [CommRing R] {n m k : ℕ}
    (builder : Builder R n m k) (base : BatchTranscript R n m) :
    Matrix (Fin n) (Fin k) R :=
  fun row column ↦ (builder base.1 column).mulVec base.2 row

def simulate {R : Type} [CommRing R] {n m k : ℕ}
    (builder : Builder R n m k) (linear : Matrix (Fin n) (Fin k) R)
    (offset : Fin k → R) (raw : View R n m k) : View R n m k :=
  (raw.1, (raw.2.1 - linear - correction builder raw.1, raw.2.2 + offset))

def unsimulate {R : Type} [CommRing R] {n m k : ℕ}
    (builder : Builder R n m k) (linear : Matrix (Fin n) (Fin k) R)
    (offset : Fin k → R) (view : View R n m k) : View R n m k :=
  (view.1, (view.2.1 + linear + correction builder view.1, view.2.2 - offset))

def tapeEquiv {R : Type} [CommRing R] {n m k : ℕ}
    (builder : Builder R n m k) (linear : Matrix (Fin n) (Fin k) R)
    (offset : Fin k → R) : View R n m k ≃ View R n m k where
  toFun := simulate builder linear offset
  invFun := unsimulate builder linear offset
  left_inv raw := by
    rcases raw with ⟨base, mask, body⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · simp only [simulate, unsimulate]
        abel
      · simp only [simulate, unsimulate]
        abel
  right_inv view := by
    rcases view with ⟨base, mask, body⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · simp only [simulate, unsimulate]
        abel
      · simp only [simulate, unsimulate]
        abel

def splitEquiv (R : Type) (n m k : ℕ) :
    BatchTranscript R n (m + k) ≃ View R n m k where
  toFun := TwoBlock.toTranscriptPair ∘ TwoBlock.splitTranscript
  invFun := TwoBlock.appendTranscript ∘ TwoBlock.ofTranscriptPair
  left_inv raw := by simp
  right_inv view := by simp

def phase {R : Type} [CommRing R] {n k : ℕ}
    (secret : Fin n → R) (ciphertext : BatchTranscript R n k) (column : Fin k) : R :=
  ciphertext.2 column - dotProduct secret (fun row ↦ ciphertext.1 row column)

theorem phase_simulate {R : Type} [CommRing R] {n m k : ℕ}
    (builder : Builder R n m k) (linear : Matrix (Fin n) (Fin k) R)
    (offset : Fin k → R) (raw : View R n m k) (secret : Fin n → R) (column : Fin k) :
    phase secret (simulate builder linear offset raw).2 column =
      phase secret raw.2 column + vecMul secret linear column + offset column +
        dotProduct secret ((builder raw.1.1 column).mulVec raw.1.2) := by
  change (raw.2.2 column + offset column) -
    dotProduct secret ((fun row ↦ raw.2.1 row column) -
      (fun row ↦ linear row column) - (builder raw.1.1 column).mulVec raw.1.2) = _
  rw [dotProduct_sub, dotProduct_sub]
  change _ = (raw.2.2 column - dotProduct secret (fun row ↦ raw.2.1 row column)) +
    dotProduct secret (fun row ↦ linear row column) + offset column + _
  ring

theorem phase_real {R : Type} [CommRing R] {n m k : ℕ}
    (builder : Builder R n m k) (linear : Matrix (Fin n) (Fin k) R)
    (offset : Fin k → R) (secret : Fin n → R)
    (baseMask : Matrix (Fin n) (Fin m) R) (baseError : Fin m → R)
    (controlMask : Matrix (Fin n) (Fin k) R) (controlError : Fin k → R)
    (column : Fin k) :
    phase secret (simulate builder linear offset
      ((baseMask, vecMul secret baseMask + baseError),
        (controlMask, vecMul secret controlMask + controlError))).2 column =
      vecMul secret linear column + offset column +
        dotProduct secret ((builder baseMask column * baseMask.transpose).mulVec secret) +
        controlError column + dotProduct secret ((builder baseMask column).mulVec baseError) := by
  rw [phase_simulate]
  have hphase : phase secret (controlMask, vecMul secret controlMask + controlError) column =
      controlError column := by
    simp [phase, vecMul, dotProduct]
  have hbase : vecMul secret baseMask = baseMask.transpose.mulVec secret := by
    exact (mulVec_transpose baseMask secret).symm
  rw [hphase, hbase, mulVec_add, dotProduct_add, ← mulVec_mulVec]
  ring

/-- A division-free public certificate, valid also at even moduli. -/
theorem quadratic_eq_of_certificate {R : Type} [CommRing R] {n m : ℕ}
    (base : Matrix (Fin n) (Fin m) R) (preimage : Matrix (Fin n) (Fin m) R)
    (target alternatingWitness : Matrix (Fin n) (Fin n) R)
    (certificate : preimage * base.transpose =
      target + alternatingWitness - alternatingWitness.transpose)
    (secret : Fin n → R) :
    dotProduct secret ((preimage * base.transpose).mulVec secret) =
      dotProduct secret (target.mulVec secret) := by
  rw [certificate, sub_mulVec, add_mulVec, dotProduct_sub, dotProduct_add,
    dotProduct_transpose_mulVec]
  ring

/-- The integer error bound uses the actual l1 norm, as in the lattice diagnostic. -/
theorem residual_abs_le_l1 {n m : ℕ}
    (secret : Fin n → ℤ) (preimage : Matrix (Fin n) (Fin m) ℤ)
    (error : Fin m → ℤ) (S E : ℤ) (hS : 0 ≤ S)
    (hsecret : ∀ row, |secret row| ≤ S) (herror : ∀ column, |error column| ≤ E) :
    |dotProduct secret (preimage.mulVec error)| ≤
      S * E * ∑ row, ∑ column, |preimage row column| := by
  unfold dotProduct mulVec
  calc
    |∑ row, secret row * ∑ column, preimage row column * error column| ≤
        ∑ row, |secret row * ∑ column, preimage row column * error column| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ row, S * (E * ∑ column, |preimage row column|) := by
      apply Finset.sum_le_sum
      intro row _
      rw [abs_mul]
      apply mul_le_mul (hsecret row) _ (abs_nonneg _) hS
      calc
        |∑ column, preimage row column * error column| ≤
            ∑ column, |preimage row column * error column| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ column, |preimage row column| * E := by
          apply Finset.sum_le_sum
          intro column _
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (herror column) (abs_nonneg _)
        _ = E * ∑ column, |preimage row column| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro column _
          ring
    _ = S * E * ∑ row, ∑ column, |preimage row column| := by
      simp only [← Finset.mul_sum]
      ring

theorem total_error_abs_le_l1 {n m : ℕ}
    (secret : Fin n → ℤ) (preimage : Matrix (Fin n) (Fin m) ℤ)
    (error : Fin m → ℤ) (freshError S E E₀ : ℤ) (hS : 0 ≤ S)
    (hsecret : ∀ row, |secret row| ≤ S) (herror : ∀ column, |error column| ≤ E)
    (hfresh : |freshError| ≤ E₀) :
    |freshError + dotProduct secret (preimage.mulVec error)| ≤
      E₀ + S * E * ∑ row, ∑ column, |preimage row column| := by
  exact (abs_add_le _ _).trans (add_le_add hfresh
    (residual_abs_le_l1 secret preimage error S E hS hsecret herror))

noncomputable section

variable {q n m k : ℕ} [NeZero q]

noncomputable local instance : SampleableType (View (ZMod q) n m k) := inferInstance

def sourceEquiv (builder : Builder (ZMod q) n m k)
    (linear : Matrix (Fin n) (Fin k) (ZMod q)) (offset : Fin k → ZMod q) :
    BatchTranscript (ZMod q) n (m + k) ≃ View (ZMod q) n m k :=
  (splitEquiv (ZMod q) n m k).trans (tapeEquiv builder linear offset)

def realView (builder : Builder (ZMod q) n m k)
    (linear : Matrix (Fin n) (Fin k) (ZMod q)) (offset : Fin k → ZMod q)
    (errorSampler : ProbComp (ZMod q)) : ProbComp (View (ZMod q) n m k) :=
  sourceEquiv builder linear offset <$>
    LearningWithErrors.distr (zmodBatchProblem n (m + k) q errorSampler)

theorem uniform_source_evalDist (builder : Builder (ZMod q) n m k)
    (linear : Matrix (Fin n) (Fin k) (ZMod q)) (offset : Fin k → ZMod q)
    (errorSampler : ProbComp (ZMod q)) :
    𝒟[sourceEquiv builder linear offset <$>
      LearningWithErrors.uniformDistr (zmodBatchProblem n (m + k) q errorSampler)] =
        𝒟[$ᵗ View (ZMod q) n m k] := by
  have hsource : 𝒟[LearningWithErrors.uniformDistr
      (zmodBatchProblem n (m + k) q errorSampler)] =
      𝒟[$ᵗ BatchTranscript (ZMod q) n (m + k)] := by
    simpa only [LearningWithErrors.uniformDistr, zmodBatchProblem, batchProblem] using
      (FiniteProduct.evalDist_independent_uniform_product
        (first := Matrix (Fin n) (Fin (m + k)) (ZMod q))
        (second := Fin (m + k) → ZMod q))
  exact (evalDist_map_eq_of_evalDist_eq hsource (sourceEquiv builder linear offset)).trans
    (evalDist_map_bijective_uniform_cross
      (BatchTranscript (ZMod q) n (m + k)) (sourceEquiv builder linear offset)
      (sourceEquiv builder linear offset).bijective)

def reduction (builder : Builder (ZMod q) n m k)
    (linear : Matrix (Fin n) (Fin k) (ZMod q)) (offset : Fin k → ZMod q)
    (adversary : View (ZMod q) n m k → ProbComp Bool) :
    BatchTranscript (ZMod q) n (m + k) → ProbComp Bool :=
  fun raw ↦ adversary (sourceEquiv builder linear offset raw)

theorem advantage_eq_ordinaryLWE (builder : Builder (ZMod q) n m k)
    (linear : Matrix (Fin n) (Fin k) (ZMod q)) (offset : Fin k → ZMod q)
    (errorSampler : ProbComp (ZMod q)) (adversary : View (ZMod q) n m k → ProbComp Bool) :
    (realView builder linear offset errorSampler >>= adversary).boolDistAdvantage
      (($ᵗ View (ZMod q) n m k) >>= adversary) =
      LearningWithErrors.advantage (zmodBatchProblem n (m + k) q errorSampler)
        (reduction builder linear offset adversary) := by
  have hreal : realView builder linear offset errorSampler >>= adversary =
      LearningWithErrors.game0 (zmodBatchProblem n (m + k) q errorSampler)
        (reduction builder linear offset adversary) := by
    simp [realView, reduction, LearningWithErrors.game0, monad_norm]
  have hideal := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (uniform_source_evalDist builder linear offset errorSampler) adversary
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage, hreal]
  unfold ProbComp.boolDistAdvantage
  have hideal' : 𝒟[LearningWithErrors.game1 (zmodBatchProblem n (m + k) q errorSampler)
      (reduction builder linear offset adversary)] =
      𝒟[($ᵗ View (ZMod q) n m k) >>= adversary] := by
    simpa [LearningWithErrors.game1, reduction, monad_norm] using hideal
  rw [evalDist_ext_iff.mp hideal' true]

end

end FormalProof4FHE.LWE.GSWQuadraticPreimage
