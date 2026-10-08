/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.AffineCircular
import FormalProof4FHE.LWE.BlockBinaryReduction
import FormalProof4FHE.LWE.NoiseFlooding
import FormalProof4FHE.TFHE.NoiseBounds

/-!
# Recursive-mask ciphertexts for fixed quadratic KDM batches

For a vector secret s, encrypt w using independent fresh masks A,a and errors e,f:
  T=A, c=sᵀA-a+e, b=sᵀa+w+f.
Decrypt by b+sᵀc-(sᵀT)·s. The error is f+sᵀe.

For w=sᵀM s+lᵀs+o, ordinary LWE rows (A',y),(a',z) give the
public simulation T=A'-M, c=y-a'+l, b=z+o. The private change of
variables A=A'-M, a=a'-sᵀM-l is used only to prove its distribution.
The actual reduction does not use s. A whole ordinary public-key batch is
retained, with the same secret as every recursive ciphertext.

This is a fixed, nonadaptive quadratic-KDM reduction for this fresh private
ciphertext law. It is not a GSW ciphertext, public encryption algorithm, or
repeatable bootstrapper. In particular its quadratic decryption features do
not supply the scalar GSW controls required by the existing accumulator.
-/

open Matrix OracleComp

namespace FormalProof4FHE.LWE.RecursiveQuadratic

noncomputable section

abbrev Column (dimension publicSamples messages : ℕ) :=
  Fin publicSamples ⊕ (Fin messages × Option (Fin dimension))

/-- An explicit public enumeration; one fresh LWE row per masked coordinate and body. -/
def columnsEquiv (n p k : ℕ) : Column n p k ≃ Fin (p + k * (n + 1)) :=
  (Equiv.sumCongr (Equiv.refl (Fin p))
    ((Equiv.prodCongr (Equiv.refl (Fin k)) (finSuccEquiv n).symm).trans
      finProdFinEquiv)).trans finSumFinEquiv
abbrev Raw (R : Type) (dimension publicSamples messages : ℕ) :=
  Matrix (Fin dimension) (Column dimension publicSamples messages) R ×
    (Column dimension publicSamples messages → R)
abbrev Ciphertext (R : Type) (dimension : ℕ) :=
  Matrix (Fin dimension) (Fin dimension) R × (Fin dimension → R) × R
abbrev View (R : Type) (dimension publicSamples messages : ℕ) :=
  BatchTranscript R dimension publicSamples × (Fin messages → Ciphertext R dimension)

structure Polynomial (R : Type) (dimension messages : ℕ) where
  quadratic : Fin messages → Matrix (Fin dimension) (Fin dimension) R
  linear : Fin messages → Fin dimension → R
  constant : Fin messages → R

def message {R : Type} [CommRing R] {n k : ℕ}
    (polynomial : Polynomial R n k) (secret : Fin n → R) (index : Fin k) : R :=
  dotProduct (vecMul secret (polynomial.quadratic index)) secret +
    dotProduct (polynomial.linear index) secret + polynomial.constant index

/-- Drop only the mask a; retain every public-key row and recursive ciphertext. -/
def project {R : Type} {n p k : ℕ} (raw : Raw R n p k) : View R n p k :=
  ((fun row column ↦ raw.1 row (.inl column), fun column ↦ raw.2 (.inl column)),
    fun index ↦ (fun row column ↦ raw.1 row (.inr (index, some column)),
      (fun row ↦ raw.2 (.inr (index, some row))), raw.2 (.inr (index, none))))

def publicShift {R : Type} [CommRing R] {n p k : ℕ}
    (polynomial : Polynomial R n k) (raw : Raw R n p k) : Raw R n p k :=
  (fun row column ↦ match column with
    | .inl _ => raw.1 row column
    | .inr (_, none) => raw.1 row column
    | .inr (index, some j) => raw.1 row column - polynomial.quadratic index row j,
   fun column ↦ match column with
    | .inl _ => raw.2 column
    | .inr (index, none) => raw.2 column + polynomial.constant index
    | .inr (index, some j) => raw.2 column - raw.1 j (.inr (index, none)) +
        polynomial.linear index j)

def publicUnshift {R : Type} [CommRing R] {n p k : ℕ}
    (polynomial : Polynomial R n k) (raw : Raw R n p k) : Raw R n p k :=
  (fun row column ↦ match column with
    | .inl _ => raw.1 row column
    | .inr (_, none) => raw.1 row column
    | .inr (index, some j) => raw.1 row column + polynomial.quadratic index row j,
   fun column ↦ match column with
    | .inl _ => raw.2 column
    | .inr (index, none) => raw.2 column - polynomial.constant index
    | .inr (index, some j) => raw.2 column + raw.1 j (.inr (index, none)) -
        polynomial.linear index j)

theorem publicShift_bijective {R : Type} [CommRing R] {n p k : ℕ}
    (polynomial : Polynomial R n k) :
    Function.Bijective (publicShift (p := p) polynomial) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨publicUnshift polynomial, ?_, ?_⟩ <;>
    intro raw <;> apply Prod.ext
  all_goals
    first
    | funext row column; cases column with
      | inl j => rfl
      | inr pair => rcases pair with ⟨index, j⟩; cases j <;>
          simp [publicShift, publicUnshift]
    | funext column; cases column with
      | inl j => rfl
      | inr pair =>
          rcases pair with ⟨index, j⟩
          cases j with
          | none => simp [publicShift, publicUnshift]
          | some j =>
              simp only [publicShift, publicUnshift]
              abel

def simulate {R : Type} [CommRing R] {n p k : ℕ}
    (polynomial : Polynomial R n k) (raw : Raw R n p k) : View R n p k :=
  project (publicShift polynomial raw)

def privateShift {R : Type} [CommRing R] {n p k : ℕ}
    (polynomial : Polynomial R n k) (secret : Fin n → R) :
    Matrix (Fin n) (Column n p k) R := fun row column ↦ match column with
  | .inl _ => 0
  | .inr (index, none) => vecMul secret (polynomial.quadratic index) row +
      polynomial.linear index row
  | .inr (index, some j) => polynomial.quadratic index row j

def fresh {R : Type} [CommRing R] {n p k : ℕ}
    (polynomial : Polynomial R n k) (secret : Fin n → R)
    (challenge : Matrix (Fin n) (Column n p k) R) (error : Column n p k → R) :
    View R n p k :=
  project (challenge, fun column ↦ match column with
    | .inl _ => vecMul secret challenge column + error column
    | .inr (index, none) => vecMul secret challenge column + error column +
        message polynomial secret index
    | .inr (index, some j) => vecMul secret challenge column + error column -
        challenge j (.inr (index, none)))

def decrypt {R : Type} [CommRing R] {n : ℕ}
    (secret : Fin n → R) (ciphertext : Ciphertext R n) : R :=
  ciphertext.2.2 + dotProduct ciphertext.2.1 secret -
    dotProduct (vecMul secret ciphertext.1) secret

theorem decrypt_fresh {R : Type} [CommRing R] {n p k : ℕ}
    (polynomial : Polynomial R n k) (secret : Fin n → R)
    (challenge : Matrix (Fin n) (Column n p k) R) (error : Column n p k → R)
    (index : Fin k) :
    decrypt secret ((fresh polynomial secret challenge error).2 index) =
      message polynomial secret index + error (.inr (index, none)) +
        dotProduct (fun row ↦ error (.inr (index, some row))) secret := by
  change (dotProduct secret (fun row ↦ challenge row (.inr (index, none))) +
      error (.inr (index, none)) + message polynomial secret index) +
    dotProduct
      ((vecMul secret (fun row column ↦ challenge row (.inr (index, some column))) +
        (fun row ↦ error (.inr (index, some row)))) -
          (fun row ↦ challenge row (.inr (index, none)))) secret -
    dotProduct (vecMul secret (fun row column ↦ challenge row (.inr (index, some column)))) secret = _
  rw [sub_dotProduct, add_dotProduct, dotProduct_comm secret]
  abel

/-- Exact deterministic error budget; the modulus/separation margin remains explicit. -/
theorem decrypt_fresh_error_bound {q n p k : ℕ} [NeZero q]
    (polynomial : Polynomial (ZMod q) n k) (secret : Fin n → ZMod q)
    (challenge : Matrix (Fin n) (Column n p k) (ZMod q))
    (error : Column n p k → ZMod q) (secretBound errorBound : ℕ)
    (hsecret : ∀ row, (LatticeCrypto.centeredRepr (secret row)).natAbs ≤ secretBound)
    (herror : ∀ column, (LatticeCrypto.centeredRepr (error column)).natAbs ≤ errorBound)
    (index : Fin k) :
    (LatticeCrypto.centeredRepr
      (decrypt secret ((fresh polynomial secret challenge error).2 index) -
        message polynomial secret index)).natAbs ≤ (n * secretBound + 1) * errorBound := by
  have hphase : decrypt secret ((fresh polynomial secret challenge error).2 index) -
      message polynomial secret index = error (.inr (index, none)) +
        dotProduct (fun row ↦ error (.inr (index, some row))) secret := by
    rw [decrypt_fresh]
    abel
  rw [hphase]
  calc
    _ ≤ (LatticeCrypto.centeredRepr (error (.inr (index, none)))).natAbs +
        (LatticeCrypto.centeredRepr
          (dotProduct (fun row ↦ error (.inr (index, some row))) secret)).natAbs :=
      TFHE.NoiseBounds.centeredRepr_add_natAbs_le _ _
    _ ≤ errorBound + ∑ _row : Fin n, errorBound * secretBound := by
      apply Nat.add_le_add (herror _)
      calc
        _ ≤ ∑ row : Fin n, (LatticeCrypto.centeredRepr
            (error (.inr (index, some row)) * secret row)).natAbs :=
          TFHE.NoiseBounds.centeredRepr_finset_sum_natAbs_le _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro row _
          exact (TFHE.NoiseBounds.centeredRepr_mul_natAbs_le _ _).trans
            (Nat.mul_le_mul (herror _) (hsecret row))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
      ring

theorem decrypt_fresh_binary_error_bound {q n p k : ℕ} [NeZero q]
    (polynomial : Polynomial (ZMod q) n k) (secret : Fin n → ZMod q)
    (challenge : Matrix (Fin n) (Column n p k) (ZMod q))
    (error : Column n p k → ZMod q) (errorBound : ℕ)
    (hsecret : ∀ row, secret row = 0 ∨ secret row = 1)
    (herror : ∀ column, (LatticeCrypto.centeredRepr (error column)).natAbs ≤ errorBound)
    (index : Fin k) :
    (LatticeCrypto.centeredRepr
      (decrypt secret ((fresh polynomial secret challenge error).2 index) -
        message polynomial secret index)).natAbs ≤ (n + 1) * errorBound := by
  have hs : ∀ row, (LatticeCrypto.centeredRepr (secret row)).natAbs ≤ 1 := by
    intro row
    rcases hsecret row with hzero | hone
    · rw [hzero]
      have hz : (LatticeCrypto.centeredRepr (0 : ZMod q)).natAbs ≤ 0 := by
        simpa using TFHE.NoiseBounds.centeredRepr_intCast_natAbs_le (q := q) (0 : ℤ)
      exact hz.trans (by decide : 0 ≤ 1)
    · rw [hone]
      simpa using TFHE.NoiseBounds.centeredRepr_intCast_natAbs_le (q := q) (1 : ℤ)
  simpa only [Nat.mul_one] using
    decrypt_fresh_error_bound polynomial secret challenge error 1 errorBound hs herror index

/-- Unlike the private variable change, this simulation consumes no secret. -/
theorem simulate_real {R : Type} [CommRing R] {n p k : ℕ}
    (polynomial : Polynomial R n k) (secret : Fin n → R)
    (challenge : Matrix (Fin n) (Column n p k) R) (error : Column n p k → R) :
    simulate polynomial (challenge, vecMul secret challenge + error) =
      fresh polynomial secret (challenge - privateShift polynomial secret) error := by
  apply Prod.ext
  · apply Prod.ext <;> funext i
    · funext j
      simp [simulate, publicShift, project, fresh, privateShift]
    · simp [simulate, publicShift, project, fresh, privateShift, vecMul, dotProduct]
  · funext index
    apply Prod.ext
    · funext row column
      simp [simulate, publicShift, project, fresh, privateShift]
    · apply Prod.ext
      · funext row
        simp only [simulate, publicShift, project, fresh, privateShift, vecMul,
          dotProduct, Pi.add_apply, Matrix.sub_apply]
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib]
        abel
      · simp only [simulate, publicShift, project, fresh, privateShift, vecMul,
          dotProduct, message, Pi.add_apply, Matrix.sub_apply]
        simp_rw [mul_sub, mul_add]
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
        simp_rw [mul_comm (secret _)]
        ring

def reindex {R : Type} {n p k samples : ℕ}
    (columns : Column n p k ≃ Fin samples) (transcript : BatchTranscript R n samples) :
    Raw R n p k :=
  (fun row column ↦ transcript.1 row (columns column), fun column ↦ transcript.2 (columns column))

theorem reindex_bijective {R : Type} {n p k samples : ℕ}
    (columns : Column n p k ≃ Fin samples) : Function.Bijective (reindex (R := R) columns) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨(fun raw ↦ (fun row column ↦ raw.1 row (columns.symm column),
      fun column ↦ raw.2 (columns.symm column))), ?_, ?_⟩ <;>
    intro raw <;> apply Prod.ext <;> simp [reindex]

variable {R Secret : Type} [CommRing R] [DecidableEq R] [SampleableType R]
  {n p k samples : ℕ}

local instance : SampleableType (Column n p k → R) := instSampleableTypePiFintype

local instance : SampleableType (Matrix (Fin n) (Column n p k) R) :=
  instSampleableTypeFinFunc

def freshView (columns : Column n p k ≃ Fin samples)
    (polynomial : Polynomial R n k) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin n → R) (errorSampler : ProbComp R) : ProbComp (View R n p k) := do
  let secret ← secretSampler
  let challenge ← $ᵗ Matrix (Fin n) (Column n p k) R
  let error ← ProbComp.sampleIID samples errorSampler
  pure (fresh polynomial (embed secret) challenge (fun column ↦ error (columns column)))

def idealView : ProbComp (View R n p k) := project <$> ($ᵗ Raw R n p k)

def reduction (columns : Column n p k ≃ Fin samples) (polynomial : Polynomial R n k)
    (adversary : View R n p k → ProbComp Bool) : BatchTranscript R n samples → ProbComp Bool :=
  fun transcript ↦ adversary (simulate polynomial (reindex columns transcript))

def shiftedChallenge (columns : Column n p k ≃ Fin samples)
    (polynomial : Polynomial R n k) (secret : Fin n → R)
    (challenge : Matrix (Fin n) (Fin samples) R) : Matrix (Fin n) (Column n p k) R :=
  fun row column ↦ challenge row (columns column) -
    privateShift (p := p) polynomial secret row column

omit [DecidableEq R] [SampleableType R] in
theorem shiftedChallenge_bijective (columns : Column n p k ≃ Fin samples)
    (polynomial : Polynomial R n k) (secret : Fin n → R) :
    Function.Bijective (shiftedChallenge columns polynomial secret) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨(fun (challenge : Matrix (Fin n) (Column n p k) R) row column ↦
      challenge row (columns.symm column) +
        privateShift (p := p) polynomial secret row (columns.symm column)), ?_, ?_⟩ <;>
    intro challenge <;> funext row column <;> simp [shiftedChallenge]

omit [DecidableEq R] [SampleableType R] in
theorem simulate_reindex_real (columns : Column n p k ≃ Fin samples)
    (polynomial : Polynomial R n k) (secret : Fin n → R)
    (challenge : Matrix (Fin n) (Fin samples) R) (error : Fin samples → R) :
    simulate polynomial (reindex columns (challenge, vecMul secret challenge + error)) =
      fresh polynomial secret (shiftedChallenge columns polynomial secret challenge)
        (fun column ↦ error (columns column)) := by
  exact simulate_real polynomial secret
    (fun row column ↦ challenge row (columns column)) (fun column ↦ error (columns column))

/-- Exact simulation of the complete fixed quadratic-message view, including PK. -/
theorem real_evalDist (columns : Column n p k ≃ Fin samples)
    (polynomial : Polynomial R n k) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin n → R) (errorSampler : ProbComp R) :
    𝒟[(fun transcript ↦ simulate polynomial (reindex columns transcript)) <$>
      LearningWithErrors.distr
        (AffineCircular.ordinaryProblem n samples secretSampler embed errorSampler)] =
      𝒟[freshView columns polynomial secretSampler embed errorSampler] := by
  let sourceChallenges : ProbComp (Matrix (Fin n) (Fin samples) R) := $ᵗ _
  let targetChallenges : ProbComp (Matrix (Fin n) (Column n p k) R) := $ᵗ _
  let finish := fun (secret : Secret) (challenge : Matrix (Fin n) (Column n p k) R) ↦ do
    let error ← ProbComp.sampleIID samples errorSampler
    pure (fresh polynomial (embed secret) challenge (fun column ↦ error (columns column)))
  have hleft :
      ((fun transcript ↦ simulate polynomial (reindex columns transcript)) <$>
        LearningWithErrors.distr
          (AffineCircular.ordinaryProblem n samples secretSampler embed errorSampler)) =
      (sourceChallenges >>= fun challenge ↦ secretSampler >>= fun secret ↦
        finish secret (shiftedChallenge columns polynomial (embed secret) challenge)) := by
    simp [LearningWithErrors.distr, AffineCircular.ordinaryProblem, embeddedBatchProblem,
      sourceChallenges, finish, simulate_reindex_real, monad_norm]
  have hright : freshView columns polynomial secretSampler embed errorSampler =
      (secretSampler >>= fun secret ↦ targetChallenges >>= finish secret) := rfl
  rw [hleft, hright]
  apply evalDist_ext
  intro view
  rw [probOutput_bind_bind_swap sourceChallenges secretSampler
    (fun challenge secret ↦ finish secret
      (shiftedChallenge columns polynomial (embed secret) challenge)) view]
  apply probOutput_bind_congr' secretSampler view
  intro secret
  exact probOutput_bind_bijective_uniform_cross
    (α := Matrix (Fin n) (Fin samples) R)
    (β := Matrix (Fin n) (Column n p k) R)
    (shiftedChallenge columns polynomial (embed secret))
    (shiftedChallenge_bijective columns polynomial (embed secret)) (finish secret) view

/-- The public transformation sends the uniform source to one message-independent ideal. -/
theorem uniform_evalDist (columns : Column n p k ≃ Fin samples)
    (polynomial : Polynomial R n k) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin n → R) (errorSampler : ProbComp R) :
    𝒟[(fun transcript ↦ simulate polynomial (reindex columns transcript)) <$>
      LearningWithErrors.uniformDistr
        (AffineCircular.ordinaryProblem n samples secretSampler embed errorSampler)] =
      𝒟[idealView (R := R) (n := n) (p := p) (k := k)] := by
  rw [AffineCircular.ordinary_uniformDistr_eq_uniformSample]
  have hreindex := evalDist_map_bijective_uniform_cross
    (α := BatchTranscript R n samples) (β := Raw R n p k)
    (reindex columns) (reindex_bijective columns)
  have hshift := evalDist_map_bijective_uniform_cross
    (α := Raw R n p k) (β := Raw R n p k)
    (publicShift polynomial) (publicShift_bijective polynomial)
  calc
    _ = 𝒟[project <$> (publicShift polynomial <$> (reindex columns <$> ($ᵗ BatchTranscript R n samples)))] := by
      simp [simulate]
    _ = 𝒟[project <$> (publicShift polynomial <$> ($ᵗ Raw R n p k))] := by
      simpa only [evalDist_map] using
        congrArg (fun distribution ↦ project <$> (publicShift polynomial <$> distribution)) hreindex
    _ = 𝒟[project <$> ($ᵗ Raw R n p k)] := by
      simpa only [evalDist_map] using congrArg (fun distribution ↦ project <$> distribution) hshift
    _ = _ := rfl

theorem real_game_evalDist (columns : Column n p k ≃ Fin samples)
    (polynomial : Polynomial R n k) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin n → R) (errorSampler : ProbComp R)
    (adversary : View R n p k → ProbComp Bool) :
    𝒟[freshView columns polynomial secretSampler embed errorSampler >>= adversary] =
      𝒟[LearningWithErrors.game0
        (AffineCircular.ordinaryProblem n samples secretSampler embed errorSampler)
        (reduction columns polynomial adversary)] := by
  unfold LearningWithErrors.game0
  rw [show (LearningWithErrors.distr
        (AffineCircular.ordinaryProblem n samples secretSampler embed errorSampler) >>=
      reduction columns polynomial adversary) =
    (((fun transcript ↦ simulate polynomial (reindex columns transcript)) <$>
        LearningWithErrors.distr
          (AffineCircular.ordinaryProblem n samples secretSampler embed errorSampler)) >>= adversary) by
      unfold reduction
      simp [monad_norm]]
  rw [evalDist_bind, evalDist_bind, real_evalDist]

theorem uniform_game_evalDist (columns : Column n p k ≃ Fin samples)
    (polynomial : Polynomial R n k) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin n → R) (errorSampler : ProbComp R)
    (adversary : View R n p k → ProbComp Bool) :
    𝒟[(idealView (R := R) (n := n) (p := p) (k := k)) >>= adversary] =
      𝒟[LearningWithErrors.game1
        (AffineCircular.ordinaryProblem n samples secretSampler embed errorSampler)
        (reduction columns polynomial adversary)] := by
  unfold LearningWithErrors.game1
  rw [show (LearningWithErrors.uniformDistr
        (AffineCircular.ordinaryProblem n samples secretSampler embed errorSampler) >>=
      reduction columns polynomial adversary) =
    (((fun transcript ↦ simulate polynomial (reindex columns transcript)) <$>
        LearningWithErrors.uniformDistr
          (AffineCircular.ordinaryProblem n samples secretSampler embed errorSampler)) >>= adversary) by
      unfold reduction
      simp [monad_norm]]
  rw [evalDist_bind, evalDist_bind, uniform_evalDist]

/-- A public, lossless LWE reduction, rather than a quadratic-KDM security premise. -/
theorem advantage_eq_lwe (columns : Column n p k ≃ Fin samples)
    (polynomial : Polynomial R n k) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin n → R) (errorSampler : ProbComp R)
    (adversary : View R n p k → ProbComp Bool) :
    (freshView columns polynomial secretSampler embed errorSampler >>= adversary).boolDistAdvantage
      ((idealView (R := R) (n := n) (p := p) (k := k)) >>= adversary) =
      LearningWithErrors.advantage
        (AffineCircular.ordinaryProblem n samples secretSampler embed errorSampler)
        (reduction columns polynomial adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
    (real_game_evalDist columns polynomial secretSampler embed errorSampler adversary) true,
    evalDist_ext_iff.mp
      (uniform_game_evalDist columns polynomial secretSampler embed errorSampler adversary) true]

/-- Fixed quadratic messages versus zero (or another fixed polynomial batch) have
two ordinary-LWE advantages as a bound, through the common ideal view. -/
theorem messages_advantage_le_lwe (columns : Column n p k ≃ Fin samples)
    (first second : Polynomial R n k) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin n → R) (errorSampler : ProbComp R)
    (adversary : View R n p k → ProbComp Bool) :
    (freshView columns first secretSampler embed errorSampler >>= adversary).boolDistAdvantage
      (freshView columns second secretSampler embed errorSampler >>= adversary) ≤
      LearningWithErrors.advantage
        (AffineCircular.ordinaryProblem n samples secretSampler embed errorSampler)
        (reduction columns first adversary) +
      LearningWithErrors.advantage
        (AffineCircular.ordinaryProblem n samples secretSampler embed errorSampler)
        (reduction columns second adversary) := by
  have h := ProbComp.boolDistAdvantage_triangle
    (freshView columns first secretSampler embed errorSampler >>= adversary)
    ((idealView (R := R) (n := n) (p := p) (k := k)) >>= adversary)
    (freshView columns second secretSampler embed errorSampler >>= adversary)
  rw [show ((idealView (R := R) (n := n) (p := p) (k := k)) >>= adversary).boolDistAdvantage
      (freshView columns second secretSampler embed errorSampler >>= adversary) =
    (freshView columns second secretSampler embed errorSampler >>= adversary).boolDistAdvantage
      ((idealView (R := R) (n := n) (p := p) (k := k)) >>= adversary) by
        unfold ProbComp.boolDistAdvantage
        exact abs_sub_comm _ _] at h
  simpa only [advantage_eq_lwe] using h

/-- The small-secret specialization reduces to ordinary uniform-secret LWE calls
and an explicit statistical gap, without assuming block-binary LWE separately.
Negligibility of the gap and a bootstrap-compatible parameter family are separate obligations. -/
theorem advantage_le_ordinary_for_blockSecrets [Fintype R]
    (blockLength blockCount extractedDimension : ℕ)
    (columns : Column (blockCount * blockLength) p k ≃ Fin samples)
    (polynomial : Polynomial R (blockCount * blockLength) k)
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : View R (blockCount * blockLength) p k → ProbComp Bool) :
    (freshView columns polynomial ($ᵗ FormalProof4FHE.BlockBinary.Key blockLength blockCount)
      (FormalProof4FHE.BlockBinary.expand R) wideErrorSampler >>= adversary).boolDistAdvantage
      ((idealView (R := R) (n := blockCount * blockLength) (p := p) (k := k)) >>= adversary) ≤
    2 * (∑ coordinate : Fin (blockCount * blockLength),
      LearningWithErrors.advantage
        (FormalProof4FHE.LWE.batchProblem extractedDimension samples
          ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler)
        (FormalProof4FHE.BlockBinary.rowHybridReduction (blockCount * blockLength)
          extractedDimension samples narrowErrorSampler coordinate
          (FormalProof4FHE.BlockBinary.combinedMaskReduction blockLength blockCount
            extractedDimension samples narrowErrorSampler wideErrorSampler
            (reduction columns polynomial adversary)))) +
      FormalProof4FHE.BlockBinary.jointStatisticalGap blockLength blockCount
        extractedDimension samples narrowErrorSampler wideErrorSampler +
      LearningWithErrors.advantage
        (FormalProof4FHE.LWE.batchProblem extractedDimension samples
          ($ᵗ (Fin extractedDimension → R)) wideErrorSampler)
        (FormalProof4FHE.BlockBinary.extractedLWReduction blockLength blockCount
          extractedDimension samples narrowErrorSampler wideErrorSampler
          (reduction columns polynomial adversary)) := by
  rw [advantage_eq_lwe]
  exact FormalProof4FHE.BlockBinary.advantage_le_combined_ordinaryLWE_add_jointGap
    blockLength blockCount extractedDimension samples narrowErrorSampler wideErrorSampler
    (reduction columns polynomial adversary)

end

/-- Concrete interval specialization: every computational term uses narrow-error
ordinary uniform-secret LWE; the two statistical losses are explicit. -/
theorem interval_advantage_le_narrowLWE {p k samples : ℕ}
    (q radius rounds blockLength blockCount extractedDimension : ℕ) [NeZero q]
    (columns : Column (blockCount * blockLength) p k ≃ Fin samples)
    (polynomial : Polynomial (ZMod q) (blockCount * blockLength) k)
    (narrow : ProbComp (ZMod q)) (hNarrow : Pr[⊥ | narrow] = 0)
    (adversary : View (ZMod q) (blockCount * blockLength) p k → ProbComp Bool) :
    let wide := UniformInterval.draw q radius
    let downstream := reduction columns polynomial adversary
    let maskReduction := FormalProof4FHE.BlockBinary.combinedMaskReduction blockLength blockCount
      extractedDimension samples narrow wide downstream
    let extractedReduction := FormalProof4FHE.BlockBinary.extractedLWReduction blockLength blockCount
      extractedDimension samples narrow wide downstream
    let moment := FormalProof4FHE.BlockBinary.scalarFirstMoment narrow
      (fun error ↦ ((LatticeCrypto.centeredRepr error).natAbs : ℝ))
    (freshView columns polynomial ($ᵗ FormalProof4FHE.BlockBinary.Key blockLength blockCount)
      (FormalProof4FHE.BlockBinary.expand (ZMod q)) wide >>= adversary).boolDistAdvantage
      ((idealView (R := ZMod q) (n := blockCount * blockLength) (p := p) (k := k)) >>=
        adversary) ≤
    2 * (∑ coordinate : Fin (blockCount * blockLength),
      LearningWithErrors.advantage (zmodBatchProblem extractedDimension samples q narrow)
        (FormalProof4FHE.BlockBinary.rowHybridReduction (blockCount * blockLength)
          extractedDimension samples narrow coordinate maskReduction)) +
    min 1 (((samples : ℝ) * (blockCount * blockLength : ℝ) / (blockLength + 1 : ℝ)) *
      (moment / (2 * radius + 1 : ℝ))) +
    Real.sqrt (((Fintype.card (ZMod q) : ℝ) ^ extractedDimension - 1) /
      (blockLength + 1 : ℝ) ^ blockCount) / 2 +
    LearningWithErrors.advantage (zmodBatchProblem extractedDimension samples q narrow)
      (NoiseFlooding.reduction (UniformInterval.sample q radius rounds) extractedReduction) +
    (samples : ℝ) * (moment / (2 * radius + 1 : ℝ) + (1 / 2 : ℝ) ^ rounds) := by
  dsimp only
  have hbase := advantage_le_ordinary_for_blockSecrets blockLength blockCount extractedDimension
    columns polynomial narrow (UniformInterval.draw q radius) adversary
  have hgap := FormalProof4FHE.BlockBinary.jointStatisticalGap_le_noise_add_leftover_tight
    blockLength blockCount extractedDimension samples narrow (UniformInterval.draw q radius)
  have habsorb := UniformInterval.noiseAbsorptionGap_le q radius blockLength blockCount
    extractedDimension samples narrow
    (FormalProof4FHE.BlockBinary.scalarFirstMoment narrow
      (fun error ↦ ((LatticeCrypto.centeredRepr error).natAbs : ℝ))) le_rfl
  have hflood := NoiseFlooding.interval_advantage_le extractedDimension samples q radius rounds
    narrow hNarrow
    (FormalProof4FHE.BlockBinary.extractedLWReduction blockLength blockCount
      extractedDimension samples narrow (UniformInterval.draw q radius)
      (reduction columns polynomial adversary))
  simp only [zmodBatchProblem] at hflood ⊢
  linarith

end FormalProof4FHE.LWE.RecursiveQuadratic
