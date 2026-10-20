/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.AffineCircular
import FormalProof4FHE.LWE.GSWGadget
import FormalProof4FHE.LWE.GSWMasking
import FormalProof4FHE.Probability.FiniteProduct

/-!
# A bit-specific KDM-first GSW format

The one underlying key is `(b,u)`, with one binary anchor b and an ordinary
uniform LWE secret vector u. Its decryption features are `(1,b,u_j,b*u_j)`.
Multiplication by b preserves this feature span. The complete fresh zero-table
and b-control view has a public randomized reduction to ordinary uniform-secret
LWE, with no binary-LWE or KDM assumption. The reduction samples b itself;
it never receives u. Every published coefficient is retained.

This is a restricted candidate, NOT a complete bootstrapper: it encrypts only
the anchor key bit as a GSW control. Encrypting all coordinates/bits of u,
converting between bit-specific formats, and repeatable refresh remain open.
The sampler below is a NEW law, not a projection of the full recursive-mask law.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.LWE.KDMStarGSW

abbrev Feature (n : ℕ) := Option (Unit ⊕ (Fin n ⊕ Fin n))
abbrev View (R : Type) (n k : ℕ) := Matrix (Feature n) (Fin k) R
abbrev Extra (R : Type) (n k : ℕ) := (Fin k → R) × Matrix (Fin n) (Fin k) R

def anchor {R : Type} [Zero R] [One R] (bit : Bool) : R := if bit then 1 else 0

theorem anchor_sq {R : Type} [Semiring R] (bit : Bool) :
    (anchor bit : R) * anchor bit = anchor bit := by
  cases bit <;> simp [anchor]

def feature {R : Type} [Semiring R] {n : ℕ} (bit : Bool) (secret : Fin n → R) :
    Feature n → R
  | none => 1
  | some (.inl _) => anchor bit
  | some (.inr (.inl row)) => secret row
  | some (.inr (.inr row)) => anchor bit * secret row

def phase {R : Type} [CommRing R] {n k : ℕ} (bit : Bool) (secret : Fin n → R)
    (view : View R n k) : Fin k → R := vecMul (feature bit secret) view

structure Plan (R : Type) (n k : ℕ) where
  row : Fin k → Feature n
  weight : Fin k → R

/-- Weight zero gives a zero/public-key column. Gadget weights on every row give
one full GSW encryption of the anchor, without discarding any matrix entry. -/
def message {R : Type} [CommRing R] {n k : ℕ} (plan : Plan R n k)
    (bit : Bool) (secret : Fin n → R) (column : Fin k) : R :=
  plan.weight column * anchor bit * feature bit secret (plan.row column)

/-- For fixed b, every target phase is affine in the still-unknown u. -/
def linear {R : Type} [CommRing R] {n k : ℕ} (plan : Plan R n k)
    (bit : Bool) : Matrix (Fin n) (Fin k) R := fun row column ↦
  match plan.row column with
  | none | some (.inl _) => 0
  | some (.inr (.inl index)) | some (.inr (.inr index)) =>
      if row = index then plan.weight column * anchor bit else 0

def offset {R : Type} [CommRing R] {n k : ℕ} (plan : Plan R n k)
    (bit : Bool) : Fin k → R := fun column ↦
  match plan.row column with
  | none | some (.inl _) => plan.weight column * anchor bit
  | some (.inr _) => 0

theorem message_affine {R : Type} [CommRing R] {n k : ℕ}
    (plan : Plan R n k) (bit : Bool) (secret : Fin n → R) (column : Fin k) :
    message plan bit secret column =
      vecMul secret (linear plan bit) column + offset plan bit column := by
  classical
  cases hrow : plan.row column with
  | none => simp [message, feature, linear, offset, hrow, vecMul, dotProduct]
  | some row =>
      cases row with
      | inl row =>
          simp only [message, hrow, feature, linear, offset, vecMul, dotProduct,
            mul_zero, Finset.sum_const_zero, zero_add]
          rw [mul_assoc, anchor_sq]
      | inr row =>
          cases row with
          | inl row => simp [message, feature, linear, offset, hrow, vecMul, dotProduct, mul_ite, mul_comm]
          | inr row =>
              simp only [message, hrow, feature, linear, offset, vecMul, dotProduct,
                mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, add_zero]
              rw [← mul_assoc (plan.weight column * anchor bit),
                mul_assoc (plan.weight column), anchor_sq]
              ring

/-- Public challenge transformation. b is fresh reduction randomness, not a
guess or a supplied coordinate of the unknown ordinary LWE secret u. -/
def simulate {R : Type} [CommRing R] {n k : ℕ} (plan : Plan R n k)
    (bit : Bool) (raw : BatchTranscript R n k) (extra : Extra R n k) : View R n k
  | none, column => raw.2 column - anchor bit * extra.1 column + offset plan bit column
  | some (.inl _), column => extra.1 column
  | some (.inr (.inl row)), column =>
      -raw.1 row column - anchor bit * extra.2 row column + linear plan bit row column
  | some (.inr (.inr row)), column => extra.2 row column

/-- The complete public tape has an explicit inverse, without a secret input. -/
def tapeEquiv {R : Type} [CommRing R] {n k : ℕ} (plan : Plan R n k) (bit : Bool) :
    BatchTranscript R n k × Extra R n k ≃ View R n k where
  toFun pair := simulate plan bit pair.1 pair.2
  invFun view :=
    ((fun row column ↦ -view (some (.inr (.inl row))) column -
        anchor bit * view (some (.inr (.inr row))) column + linear plan bit row column,
      fun column ↦ view none column + anchor bit * view (some (.inl ())) column -
        offset plan bit column),
      (view (some (.inl ())), fun row column ↦ view (some (.inr (.inr row))) column))
  left_inv pair := by
    rcases pair with ⟨⟨mask, body⟩, ⟨outer, star⟩⟩
    apply Prod.ext
    · apply Prod.ext
      · funext row column; simp only [simulate]; ring
      · funext column; simp only [simulate]; ring
    · rfl
  right_inv view := by
    funext row column
    cases row with
    | none => simp only [simulate]; ring
    | some row => cases row with
      | inl row => cases row; rfl
      | inr row => cases row with
        | inl row => simp only [simulate]; ring
        | inr row => rfl

/-- Honest private materialization, with the original one-key pair (b,u). -/
def fresh {R : Type} [CommRing R] {n k : ℕ} (plan : Plan R n k) (bit : Bool)
    (secret : Fin n → R) (mask : Matrix (Fin n) (Fin k) R)
    (error : Fin k → R) (extra : Extra R n k) : View R n k :=
  simulate plan bit (mask, vecMul secret mask + error) extra

theorem phase_fresh {R : Type} [CommRing R] {n k : ℕ}
    (plan : Plan R n k) (bit : Bool) (secret : Fin n → R)
    (mask : Matrix (Fin n) (Fin k) R) (error : Fin k → R) (extra : Extra R n k)
    (column : Fin k) :
    phase bit secret (fresh plan bit secret mask error extra) column =
      message plan bit secret column + error column := by
  rw [message_affine]
  simp only [phase, vecMul, dotProduct, Fintype.sum_option, Fintype.sum_sum_type,
    Fintype.sum_unique, feature, fresh, simulate, one_mul, Pi.add_apply]
  simp_rw [mul_add, mul_sub, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib]
  have hstar : (∑ row : Fin n, secret row * (anchor bit * extra.2 row column)) =
      ∑ row : Fin n, anchor bit * secret row * extra.2 row column := by
    apply Finset.sum_congr rfl
    intro row _
    ring
  rw [hstar]
  ring

def rows (n : ℕ) := 2 * n + 2

def unitEquiv : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv value := by cases value; rfl
  right_inv value := by apply Fin.ext; omega

def featureEquiv (n : ℕ) : Feature n ≃ Fin (rows n) :=
  ((Equiv.optionCongr
    ((Equiv.sumCongr unitEquiv finSumFinEquiv).trans finSumFinEquiv)).trans
      (finSuccEquiv (1 + (n + n))).symm).trans (finCongr (by unfold rows; omega))

/-- A public ordering of the small feature vector; no key enumeration. -/
def key {R : Type} [Semiring R] {n : ℕ} (bit : Bool) (secret : Fin n → R) :
    Fin (rows n) → R := fun row ↦ feature bit secret ((featureEquiv n).symm row)

/-- Fin-indexed materialization uses the existing GSW gadget/evaluator directly. -/
def matrix {R : Type} {n k : ℕ} (view : View R n k) : Matrix (Fin (rows n)) (Fin k) R :=
  fun row column ↦ view ((featureEquiv n).symm row) column

theorem vecMul_matrix {R : Type} [CommRing R] {n k : ℕ}
    (bit : Bool) (secret : Fin n → R) (view : View R n k) :
    vecMul (key bit secret) (matrix view) = phase bit secret view := by
  funext column
  change (∑ row : Fin (rows n), feature bit secret ((featureEquiv n).symm row) *
    view ((featureEquiv n).symm row) column) =
      ∑ row : Feature n, feature bit secret row * view row column
  exact Fintype.sum_equiv (featureEquiv n).symm
    (fun row ↦ feature bit secret ((featureEquiv n).symm row) *
      view ((featureEquiv n).symm row) column)
    (fun row ↦ feature bit secret row * view row column) (fun _ ↦ rfl)

abbrev Parameters := TFHE.Gadget.Base.Parameters

def controlPlan {q n : ℕ} [NeZero q] (params : Parameters q) :
    Plan (ZMod q) n (rows n * params.levels) where
  row column := (featureEquiv n).symm (finProdFinEquiv.symm column).1
  weight column := TFHE.Gadget.Base.gadget params (finProdFinEquiv.symm column).2

theorem controlPlan_message {q n : ℕ} [NeZero q] (params : Parameters q)
    (bit : Bool) (secret : Fin n → ZMod q) (column : Fin (rows n * params.levels)) :
    message (controlPlan params) bit secret column =
      anchor bit * vecMul (key bit secret) (GSWGadget.gadget params (rows n)) column := by
  classical
  simp [message, controlPlan, vecMul, dotProduct, GSWGadget.gadget, key]
  ring

/-- A real GSW control encrypting b in this new law, with exactly the original
scalar LWE error in each column. No secret-norm amplification is introduced. -/
theorem control_noise {q n : ℕ} [NeZero q] (params : Parameters q)
    (bit : Bool) (secret : Fin n → ZMod q)
    (mask : Matrix (Fin n) (Fin (rows n * params.levels)) (ZMod q))
    (error : Fin (rows n * params.levels) → ZMod q)
    (extra : Extra (ZMod q) n (rows n * params.levels)) :
    GSWOperations.noise (key bit secret) (GSWGadget.gadget params (rows n))
      (matrix (fresh (controlPlan params) bit secret mask error extra)) (anchor bit) = error := by
  funext column
  simp only [GSWOperations.noise, vecMul_matrix, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    phase_fresh, controlPlan_message]
  ring

theorem control_noiseBound {q n : ℕ} [NeZero q] (params : Parameters q)
    (bit : Bool) (secret : Fin n → ZMod q)
    (mask : Matrix (Fin n) (Fin (rows n * params.levels)) (ZMod q))
    (error : Fin (rows n * params.levels) → ZMod q)
    (extra : Extra (ZMod q) n (rows n * params.levels)) (bound : ℕ)
    (herror : ∀ column, (LatticeCrypto.centeredRepr (error column)).natAbs ≤ bound) :
    GSWGadget.NoiseBound params (key bit secret)
      (matrix (fresh (controlPlan params) bit secret mask error extra))
      (GSWGadget.bitMessage bit) bound := by
  unfold GSWGadget.NoiseBound
  change ∀ column, (LatticeCrypto.centeredRepr (GSWOperations.noise (key bit secret)
    (GSWGadget.gadget params (rows n))
    (matrix (fresh (controlPlan params) bit secret mask error extra)) (anchor bit) column)).natAbs ≤ bound
  rw [control_noise]
  exact herror

def joinedPlan {q n : ℕ} [NeZero q] (params : Parameters q) (publicSamples : ℕ) :
    Plan (ZMod q) n (publicSamples + rows n * params.levels) where
  row column := Sum.elim (fun _ : Fin publicSamples ↦ none)
    (controlPlan params).row (finSumFinEquiv.symm column)
  weight column := Sum.elim (fun _ : Fin publicSamples ↦ 0)
    (controlPlan params).weight (finSumFinEquiv.symm column)

abbrev Published {q n : ℕ} (params : Parameters q) (publicSamples : ℕ) :=
  Matrix (Fin (rows n)) (Fin publicSamples) (ZMod q) ×
    GSWGadget.Ciphertext params (rows n)

/-- Public materialization keeps the zero table and every control coefficient. -/
def publish {q n p : ℕ} (params : Parameters q)
    (view : View (ZMod q) n (p + rows n * params.levels)) : Published (n := n) params p :=
  (fun row column ↦ matrix view row (finSumFinEquiv (.inl column)),
    fun row column ↦ matrix view row (finSumFinEquiv (.inr column)))

def publishEquiv {q n p : ℕ} (params : Parameters q) :
    View (ZMod q) n (p + rows n * params.levels) ≃ Published (n := n) params p where
  toFun := publish params
  invFun pair := fun row column ↦ Sum.elim
    (pair.1 (featureEquiv n row)) (pair.2 (featureEquiv n row)) (finSumFinEquiv.symm column)
  left_inv view := by
    funext row column
    simp only [publish, matrix, Equiv.symm_apply_apply]
    cases hcolumn : finSumFinEquiv.symm column with
    | inl index =>
        simpa only [hcolumn, Sum.elim_inl] using
          (congrArg (view row) (finSumFinEquiv.apply_symm_apply column))
    | inr index =>
        simpa only [hcolumn, Sum.elim_inr] using
          (congrArg (view row) (finSumFinEquiv.apply_symm_apply column))
  right_inv pair := by
    apply Prod.ext
    · funext row column
      simp [publish, matrix]
    · funext row column
      simp [publish, matrix]

theorem published_zero_phase {q n p : ℕ} [NeZero q] (params : Parameters q)
    (bit : Bool) (secret : Fin n → ZMod q)
    (mask : Matrix (Fin n) (Fin (p + rows n * params.levels)) (ZMod q))
    (error : Fin (p + rows n * params.levels) → ZMod q)
    (extra : Extra (ZMod q) n (p + rows n * params.levels)) (column : Fin p) :
    vecMul (key bit secret)
      (publish params (fresh (joinedPlan params p) bit secret mask error extra)).1 column =
        error (finSumFinEquiv (.inl column)) := by
  have h := phase_fresh (joinedPlan params p) bit secret mask error extra
    (finSumFinEquiv (.inl column))
  have hzero : message (joinedPlan params p) bit secret
      (finSumFinEquiv (.inl column)) = 0 := by simp [message, joinedPlan]
  rw [hzero, zero_add] at h
  change vecMul (key bit secret)
    (matrix (fresh (joinedPlan params p) bit secret mask error extra))
      (finSumFinEquiv (.inl column)) = _
  rw [vecMul_matrix]
  exact h

theorem published_control_noise {q n p : ℕ} [NeZero q] (params : Parameters q)
    (bit : Bool) (secret : Fin n → ZMod q)
    (mask : Matrix (Fin n) (Fin (p + rows n * params.levels)) (ZMod q))
    (error : Fin (p + rows n * params.levels) → ZMod q)
    (extra : Extra (ZMod q) n (p + rows n * params.levels)) :
    GSWOperations.noise (key bit secret) (GSWGadget.gadget params (rows n))
      (publish params (fresh (joinedPlan params p) bit secret mask error extra)).2 (anchor bit) =
        fun column ↦ error (finSumFinEquiv (.inr column)) := by
  funext column
  have h := phase_fresh (joinedPlan params p) bit secret mask error extra
    (finSumFinEquiv (.inr column))
  have hmessage : message (joinedPlan params p) bit secret (finSumFinEquiv (.inr column)) =
      message (controlPlan params) bit secret column := by simp [message, joinedPlan]
  rw [hmessage, controlPlan_message] at h
  unfold GSWOperations.noise
  change vecMul (key bit secret)
      (publish params (fresh (joinedPlan params p) bit secret mask error extra)).2 column -
        anchor bit * vecMul (key bit secret) (GSWGadget.gadget params (rows n)) column = _
  have hphase : vecMul (key bit secret)
      (publish params (fresh (joinedPlan params p) bit secret mask error extra)).2 column =
        phase bit secret (fresh (joinedPlan params p) bit secret mask error extra)
          (finSumFinEquiv (.inr column)) := by
    change vecMul (key bit secret)
      (matrix (fresh (joinedPlan params p) bit secret mask error extra))
        (finSumFinEquiv (.inr column)) = _
    exact congrFun (vecMul_matrix bit secret _) (finSumFinEquiv (.inr column))
  rw [hphase, h]
  ring

/-- Public encryption uses short selector coefficients and the published zero table. -/
def encryptInputs {q n p : ℕ} [NeZero q] (params : Parameters q)
    (table : Matrix (Fin (rows n)) (Fin p) (ZMod q)) (plaintext : ZMod q)
    (selector : Matrix (Fin p) (Fin (rows n * params.levels)) (ZMod q)) :
    GSWGadget.Ciphertext params (rows n) :=
  table * selector + plaintext • GSWGadget.gadget params (rows n)

theorem encryptInputs_noise {q n p : ℕ} [NeZero q] (params : Parameters q)
    (bit : Bool) (secret : Fin n → ZMod q)
    (table : Matrix (Fin (rows n)) (Fin p) (ZMod q)) (plaintext : ZMod q)
    (selector : Matrix (Fin p) (Fin (rows n * params.levels)) (ZMod q)) :
    GSWOperations.noise (key bit secret) (GSWGadget.gadget params (rows n))
      (encryptInputs params table plaintext selector) plaintext =
        vecMul (vecMul (key bit secret) table) selector := by
  simp only [GSWOperations.noise, encryptInputs, vecMul_add, vecMul_smul,
    vecMul_vecMul]
  abel

noncomputable section

variable {q n k : ℕ} [NeZero q]

noncomputable local instance : SampleableType (View (ZMod q) n k) :=
  instSampleableTypePiFintype
noncomputable local instance : SampleableType (Extra (ZMod q) n k) :=
  inferInstance

def randomSimulate (plan : Plan (ZMod q) n k) (raw : BatchTranscript (ZMod q) n k) :
    ProbComp (View (ZMod q) n k) := do
  let bit ← $ᵗ Bool
  let extra ← $ᵗ Extra (ZMod q) n k
  pure (simulate plan bit raw extra)

def realView (plan : Plan (ZMod q) n k) (errorSampler : ProbComp (ZMod q)) :
    ProbComp (View (ZMod q) n k) := do
  let mask ← $ᵗ Matrix (Fin n) (Fin k) (ZMod q)
  let secret ← $ᵗ (Fin n → ZMod q)
  let error ← ProbComp.sampleIID k errorSampler
  let bit ← $ᵗ Bool
  let extra ← $ᵗ Extra (ZMod q) n k
  pure (fresh plan bit secret mask error extra)

theorem real_eq_source (plan : Plan (ZMod q) n k) (errorSampler : ProbComp (ZMod q)) :
    realView plan errorSampler =
      LearningWithErrors.distr (zmodBatchProblem n k q errorSampler) >>= randomSimulate plan := by
  simp [realView, LearningWithErrors.distr, zmodBatchProblem, batchProblem,
    fresh, randomSimulate, monad_norm]

theorem fixed_uniform_evalDist (plan : Plan (ZMod q) n k) (bit : Bool) :
    𝒟[do
      let raw ← $ᵗ BatchTranscript (ZMod q) n k
      let extra ← $ᵗ Extra (ZMod q) n k
      pure (simulate plan bit raw extra)] =
      𝒟[$ᵗ View (ZMod q) n k] := by
  have hpair := FiniteProduct.evalDist_independent_uniform_product
    (first := BatchTranscript (ZMod q) n k) (second := Extra (ZMod q) n k)
  have hm := evalDist_map_eq_of_evalDist_eq hpair (tapeEquiv plan bit)
  have he := evalDist_map_bijective_uniform_cross
    (α := BatchTranscript (ZMod q) n k × Extra (ZMod q) n k)
    (β := View (ZMod q) n k) (tapeEquiv plan bit) (tapeEquiv plan bit).bijective
  simpa [monad_norm, tapeEquiv] using hm.trans he

theorem uniform_source_evalDist (plan : Plan (ZMod q) n k)
    (errorSampler : ProbComp (ZMod q)) :
    𝒟[LearningWithErrors.uniformDistr (zmodBatchProblem n k q errorSampler) >>=
      randomSimulate plan] = 𝒟[$ᵗ View (ZMod q) n k] := by
  have hsource : 𝒟[LearningWithErrors.uniformDistr (zmodBatchProblem n k q errorSampler)] =
      𝒟[$ᵗ BatchTranscript (ZMod q) n k] := by
    simpa only [LearningWithErrors.uniformDistr, zmodBatchProblem, batchProblem] using
      (FiniteProduct.evalDist_independent_uniform_product
        (first := Matrix (Fin n) (Fin k) (ZMod q)) (second := Fin k → ZMod q))
  have hswap := evalDist_bind_bind_swap ($ᵗ BatchTranscript (ZMod q) n k) ($ᵗ Bool)
    (fun raw bit ↦ do
      let extra ← $ᵗ Extra (ZMod q) n k
      pure (simulate plan bit raw extra))
  have hfixed := evalDist_bind_congr' ($ᵗ Bool)
    (fun bit ↦ fixed_uniform_evalDist plan bit)
  calc
    _ = 𝒟[($ᵗ BatchTranscript (ZMod q) n k) >>= randomSimulate plan] :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hsource _
    _ = 𝒟[do
        let bit ← $ᵗ Bool
        let raw ← $ᵗ BatchTranscript (ZMod q) n k
        let extra ← $ᵗ Extra (ZMod q) n k
        pure (simulate plan bit raw extra)] := by
      simpa [randomSimulate] using hswap
    _ = 𝒟[($ᵗ Bool) >>= fun _ ↦ ($ᵗ View (ZMod q) n k)] := hfixed
    _ = _ := by
      apply evalDist_ext
      intro view
      rw [probOutput_bind_const]
      simp

def reduction (plan : Plan (ZMod q) n k)
    (adversary : View (ZMod q) n k → ProbComp Bool) :
    BatchTranscript (ZMod q) n k → ProbComp Bool := fun raw ↦
  randomSimulate plan raw >>= adversary

/-- All zero-table columns and the complete one-anchor control matrix are
handled in one joint reduction. No hinted source is assumed. -/
theorem advantage_eq_ordinaryLWE (plan : Plan (ZMod q) n k)
    (errorSampler : ProbComp (ZMod q))
    (adversary : View (ZMod q) n k → ProbComp Bool) :
    (realView plan errorSampler >>= adversary).boolDistAdvantage
      (($ᵗ View (ZMod q) n k) >>= adversary) =
      LearningWithErrors.advantage (zmodBatchProblem n k q errorSampler)
        (reduction plan adversary) := by
  have hreal : (realView plan errorSampler >>= adversary) =
      LearningWithErrors.game0 (zmodBatchProblem n k q errorSampler)
        (reduction plan adversary) := by
    rw [real_eq_source]
    simp [LearningWithErrors.game0, reduction, monad_norm]
  have hideal : 𝒟[(($ᵗ View (ZMod q) n k) >>= adversary)] =
      𝒟[LearningWithErrors.game1 (zmodBatchProblem n k q errorSampler)
        (reduction plan adversary)] := by
    have hm := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
      (uniform_source_evalDist plan errorSampler) adversary
    simpa [LearningWithErrors.game1, reduction, monad_norm] using hm.symm
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage, hreal]
  unfold ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp hideal true]

/-- The concrete published public key and complete GSW b-control have a single
ordinary LWE bound; the number of source samples is exactly p+(2*n+2)*levels. -/
theorem published_advantage_eq_ordinaryLWE (params : Parameters q) (publicSamples : ℕ)
    (errorSampler : ProbComp (ZMod q))
    (adversary : Published (n := n) params publicSamples → ProbComp Bool) :
    ((publish params <$> realView (joinedPlan params publicSamples) errorSampler) >>=
      adversary).boolDistAdvantage
      ((publish params <$> ($ᵗ View (ZMod q) n (publicSamples + rows n * params.levels))) >>=
        adversary) =
      LearningWithErrors.advantage
        (zmodBatchProblem n (publicSamples + rows n * params.levels) q errorSampler)
        (reduction (joinedPlan params publicSamples) (fun view ↦ adversary (publish params view))) := by
  simpa [monad_norm] using advantage_eq_ordinaryLWE
    (joinedPlan params publicSamples) errorSampler (fun view ↦ adversary (publish params view))

abbrev MaskingView (params : Parameters q) (publicSamples : ℕ) :=
  GSWMasking.Table q (2 * n + 1) publicSamples × GSWGadget.Ciphertext params (rows n)

def tableEquiv {p : ℕ} : Matrix (Fin (rows n)) (Fin p) (ZMod q) ≃
    GSWMasking.Table q (2 * n + 1) p where
  toFun table := fun column row ↦ table row column
  invFun table := fun row column ↦ table column row
  left_inv _ := rfl
  right_inv _ := rfl

def maskingViewEquiv (params : Parameters q) (publicSamples : ℕ) :
    View (ZMod q) n (publicSamples + rows n * params.levels) ≃
      MaskingView (n := n) params publicSamples :=
  (publishEquiv params).trans (Equiv.prodCongr tableEquiv (Equiv.refl _))

def publicView (params : Parameters q) (publicSamples : ℕ)
    (errorSampler : ProbComp (ZMod q)) : ProbComp (MaskingView (n := n) params publicSamples) :=
  maskingViewEquiv params publicSamples <$> realView (joinedPlan params publicSamples) errorSampler

abbrev StoredView (params : Parameters q) (publicSamples : ℕ) :=
  GSWPublicKey.PublicKey q (2 * n + 1) publicSamples ×
    GSWAccumulator.StoredCiphertext params (rows n)

def storeView {p : ℕ} (params : Parameters q) (view : MaskingView (n := n) params p) :
    StoredView (n := n) params p :=
  (GSWMasking.storeTable view.1, GSWAccumulator.storeCiphertext params view.2)

def readStoredView {p : ℕ} (params : Parameters q) (view : StoredView (n := n) params p) :
    MaskingView (n := n) params p :=
  (GSWMasking.tableOfPublicKey view.1, GSWAccumulator.ciphertextView params view.2)

omit [NeZero q] in
theorem readStoredView_storeView {p : ℕ} (params : Parameters q)
    (view : MaskingView (n := n) params p) :
    readStoredView params (storeView params view) = view := by
  apply Prod.ext
  · exact GSWMasking.tableOfPublicKey_storeTable view.1
  · exact GSWAccumulator.ciphertextView_storeCiphertext params view.2

/-- Every public coefficient is eagerly stored before returning. The client
retains precisely its one original pair (b,u); no derived key is sampled. -/
def keygen (params : Parameters q) (publicSamples : ℕ) (errorSampler : ProbComp (ZMod q)) :
    ProbComp (StoredView (n := n) params publicSamples × (Bool × (Fin n → ZMod q))) := do
  let mask ← $ᵗ Matrix (Fin n) (Fin (publicSamples + rows n * params.levels)) (ZMod q)
  let secret ← $ᵗ (Fin n → ZMod q)
  let error ← ProbComp.sampleIID (publicSamples + rows n * params.levels) errorSampler
  let bit ← $ᵗ Bool
  let extra ← $ᵗ Extra (ZMod q) n (publicSamples + rows n * params.levels)
  let view := maskingViewEquiv params publicSamples
    (fresh (joinedPlan params publicSamples) bit secret mask error extra)
  pure (storeView params view, (bit, secret))

theorem keygen_public_eq (params : Parameters q) (publicSamples : ℕ)
    (errorSampler : ProbComp (ZMod q)) :
    Prod.fst <$> keygen (n := n) params publicSamples errorSampler =
      storeView params <$> publicView (n := n) params publicSamples errorSampler := by
  simp [keygen, publicView, realView, monad_norm]

abbrev Adversary (params : Parameters q) (publicSamples : ℕ) :=
  GSWMasking.Adversary (dimension := 2 * n + 1) (samples := publicSamples)
    params (GSWGadget.Ciphertext params (rows n))

def observe {p : ℕ} (params : Parameters q) (adversary : Adversary (n := n) params p)
    (view : MaskingView (n := n) params p) : ProbComp Bool := do
  let bit ← $ᵗ Bool
  let messages ← adversary.chooseMessages (GSWMasking.storeTable view.1, view.2)
  let ciphertext ← GSWMasking.encrypt params view.1 (if bit then messages.1 else messages.2.1)
  let guess ← adversary.distinguish messages.2.2 ciphertext
  pure (bit == guess)

theorem uniform_maskingView_fixedpoint (params : Parameters q) (publicSamples : ℕ) :
    𝒟[GSWMasking.uniformView ($ᵗ MaskingView (n := n) params publicSamples)] =
      𝒟[$ᵗ MaskingView (n := n) params publicSamples] := by
  let context := GSWGadget.Ciphertext params (rows n)
  let table := GSWMasking.Table q (2 * n + 1) publicSamples
  have hcontext : 𝒟[Prod.snd <$> ($ᵗ (table × context))] = 𝒟[$ᵗ context] := by
    have he := evalDist_map_bijective_uniform_cross
      (α := table × context) (β := context × table) (Equiv.prodComm _ _) (Equiv.prodComm _ _).bijective
    have hm := evalDist_map_eq_of_evalDist_eq he Prod.fst
    simpa only [Functor.map_map, Function.comp_def, Equiv.prodComm_apply, Prod.swap] using
      hm.trans (evalDist_map_fst_uniformSample_prod (α := context) (β := table))
  let finish := fun old : context ↦ do
    let freshTable ← $ᵗ table
    pure (freshTable, old)
  have hm := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hcontext finish
  have hswap := evalDist_bind_bind_swap ($ᵗ context) ($ᵗ table)
    (fun old freshTable ↦ pure (freshTable, old))
  have hpair := FiniteProduct.evalDist_independent_uniform_product (first := table) (second := context)
  calc
    _ = 𝒟[($ᵗ context) >>= finish] := by
      simpa [GSWMasking.uniformView, finish, context, table, monad_norm] using hm
    _ = 𝒟[$ᵗ MaskingView (n := n) params publicSamples] := by
      simpa only [finish, context, table] using hswap.trans hpair

theorem ideal_game_abs_advantage_le {p : ℕ} (params : Parameters q)
    (adversary : Adversary (n := n) params p) :
    |Pr[= true | GSWMasking.game params ($ᵗ MaskingView (n := n) params p) adversary].toReal - 1 / 2| ≤
      (rows n * params.levels) * (Real.sqrt ((q : ℝ) ^ rows n / (2 : ℝ) ^ p) / 2) := by
  have hmask := GSWMasking.uniform_game_abs_advantage_le params
    ($ᵗ MaskingView (n := n) params p) adversary
  have hm := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (uniform_maskingView_fixedpoint params p) (observe params adversary)
  have hgame : ∀ sampler : ProbComp (MaskingView (n := n) params p),
      GSWMasking.game params sampler adversary = sampler >>= observe params adversary := fun _ ↦ rfl
  rw [hgame, probOutput_congr (rfl : true = true) hm] at hmask
  change |Pr[= true | ($ᵗ MaskingView (n := n) params p) >>= observe params adversary].toReal - 1 / 2| ≤ _
  have hcount : 2 * n + 1 + 1 = rows n := by unfold rows; omega
  have hcoefficient : ((2 * n + 1 : ℕ) : ℝ) + 1 = (rows n : ℝ) := by
    push_cast
    unfold rows
    push_cast
    ring
  simpa only [hcount, hcoefficient] using hmask

/-- Public encryption IND-CPA bound with the entire anchor control retained,
including adaptive message choice after seeing the published view. -/
theorem public_game_abs_advantage_le {p : ℕ} (params : Parameters q)
    (errorSampler : ProbComp (ZMod q)) (adversary : Adversary (n := n) params p) :
    |Pr[= true | GSWMasking.game params (publicView params p errorSampler) adversary].toReal - 1 / 2| ≤
      LearningWithErrors.advantage (zmodBatchProblem n (p + rows n * params.levels) q errorSampler)
        (reduction (joinedPlan params p)
          (fun view ↦ observe params adversary (maskingViewEquiv params p view))) +
      (rows n * params.levels) * (Real.sqrt ((q : ℝ) ^ rows n / (2 : ℝ) ^ p) / 2) := by
  let downstream := fun view ↦ observe params adversary (maskingViewEquiv params p view)
  have hview := advantage_eq_ordinaryLWE (joinedPlan params p) errorSampler downstream
  have he := evalDist_map_bijective_uniform_cross
    (α := View (ZMod q) n (p + rows n * params.levels))
    (β := MaskingView (n := n) params p)
    (maskingViewEquiv params p) (maskingViewEquiv params p).bijective
  have hi := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    he (observe params adversary)
  have hreal : realView (joinedPlan params p) errorSampler >>= downstream =
      GSWMasking.game params (publicView params p errorSampler) adversary := by
    simp [GSWMasking.game, publicView, downstream, observe, monad_norm]
  have hideal : 𝒟[($ᵗ View (ZMod q) n (p + rows n * params.levels)) >>= downstream] =
      𝒟[GSWMasking.game params ($ᵗ MaskingView (n := n) params p) adversary] := by
    simpa [GSWMasking.game, downstream, observe, monad_norm] using hi
  unfold ProbComp.boolDistAdvantage at hview
  rw [hreal, probOutput_congr (rfl : true = true) hideal] at hview
  exact (abs_sub_le _ _ (1 / 2 : ℝ)).trans
    (add_le_add (le_of_eq hview) (ideal_game_abs_advantage_le params adversary))

end

end FormalProof4FHE.LWE.KDMStarGSW
