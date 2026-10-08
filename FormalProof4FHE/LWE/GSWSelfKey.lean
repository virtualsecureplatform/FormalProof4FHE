/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.AffineCircular

/-!
# Fresh GSW sampling and the same-key quadratic target

Each GSW column is a fresh LWE column plus a gadget column.  `none` denotes the body
coordinate; `some j` denotes mask coordinate `j`.  This convention uses the decryption
vector `(1, -s)`, so the mask-column phase is `-weight * message * s_j`.

The change of masks is a permutation for each fixed secret.  Consequently the *complete*
freshly sampled view, including arbitrary auxiliary information sampled from that secret,
equals a direct quadratic-hint LWE view.  This is a distributional identity, not an
ordinary-LWE reduction: the change of masks depends on the unknown secret message.

The full self-key layout contains `dimension * (dimension + 1) * digits` LWE rows.  For
binary secrets the diagonal mask messages become affine; the off-diagonal messages remain
quadratic.  Neither the sampling identity nor the diagonal identity claims bootstrapping-key
security, a usable refresh algorithm, or a reduction of quadratic KDM to ordinary LWE.
-/

open Matrix OracleComp

namespace FormalProof4FHE.LWE.GSWSelfKey

/-- Public positions and coefficients of the gadget columns. -/
structure Layout (R : Type) (dimension samples : ℕ) where
  coordinate : Fin samples → Option (Fin dimension)
  weight : Fin samples → R

/-- Gadget added to the mask coordinates of the ciphertext. -/
def maskShift {R : Type} [Mul R] [Zero R] {dimension samples : ℕ}
    (layout : Layout R dimension samples) (message : Fin samples → R) :
    Matrix (Fin dimension) (Fin samples) R :=
  fun row column ↦ if layout.coordinate column = some row
    then message column * layout.weight column else 0

/-- Gadget added to the body coordinate of the ciphertext. -/
def bodyShift {R : Type} [Mul R] [Zero R] {dimension samples : ℕ}
    (layout : Layout R dimension samples) (message : Fin samples → R) : Fin samples → R :=
  fun column ↦ if layout.coordinate column = none
    then message column * layout.weight column else 0

/-- LWE message after absorbing the mask gadget into the fresh public challenge. -/
def phaseMessage {R : Type} [Ring R] {dimension samples : ℕ}
    (layout : Layout R dimension samples) (secret : Fin dimension → R)
    (message : Fin samples → R) : Fin samples → R :=
  fun column ↦ match layout.coordinate column with
    | none => message column * layout.weight column
    | some row => -(secret row * (message column * layout.weight column))

/-- Direct fresh-sampling GSW transcript, before any bit-decomposition encoding. -/
def freshTranscript {R : Type} [Ring R] {dimension samples : ℕ}
    (layout : Layout R dimension samples) (secret : Fin dimension → R)
    (message : Fin samples → R) (challenge : Matrix (Fin dimension) (Fin samples) R)
    (error : Fin samples → R) : BatchTranscript R dimension samples :=
  (challenge + maskShift layout message,
    (vecMul secret challenge + error) + bodyShift layout message)

/-- Direct LWE transcript with the corresponding gadget phase messages. -/
def normalizedTranscript {R : Type} [Ring R] {dimension samples : ℕ}
    (layout : Layout R dimension samples) (secret : Fin dimension → R)
    (message : Fin samples → R) (challenge : Matrix (Fin dimension) (Fin samples) R)
    (error : Fin samples → R) : BatchTranscript R dimension samples :=
  (challenge, (vecMul secret challenge + phaseMessage layout secret message) + error)

theorem vecMul_maskShift {R : Type} [Ring R] {dimension samples : ℕ}
    (layout : Layout R dimension samples) (secret : Fin dimension → R)
    (message : Fin samples → R) :
    vecMul secret (maskShift layout message) =
      bodyShift layout message - phaseMessage layout secret message := by
  classical
  funext column
  cases hcoordinate : layout.coordinate column with
  | none =>
    simp [vecMul, dotProduct, maskShift, bodyShift, phaseMessage, hcoordinate]
  | some row =>
    simp [vecMul, dotProduct, maskShift, bodyShift, phaseMessage, hcoordinate, mul_ite]

/-- Exact algebraic normalization of every column, simultaneously. -/
theorem freshTranscript_eq_normalized {R : Type} [Ring R] {dimension samples : ℕ}
    (layout : Layout R dimension samples) (secret : Fin dimension → R)
    (message : Fin samples → R) (challenge : Matrix (Fin dimension) (Fin samples) R)
    (error : Fin samples → R) :
    freshTranscript layout secret message challenge error =
      normalizedTranscript layout secret message
        (challenge + maskShift layout message) error := by
  apply Prod.ext
  · rfl
  · simp only [freshTranscript, normalizedTranscript, vecMul_add, vecMul_maskShift]
    abel

/-- The ciphertext phase has precisely the gadget message and the original error.
The sampling normalization does not enlarge or replace the encryption noise. -/
theorem freshTranscript_phase {R : Type} [Ring R] {dimension samples : ℕ}
    (layout : Layout R dimension samples) (secret : Fin dimension → R)
    (message : Fin samples → R) (challenge : Matrix (Fin dimension) (Fin samples) R)
    (error : Fin samples → R) :
    (freshTranscript layout secret message challenge error).2 -
        vecMul secret (freshTranscript layout secret message challenge error).1 =
      phaseMessage layout secret message + error := by
  simp only [freshTranscript, vecMul_add, vecMul_maskShift]
  abel

/-- For a fixed message, the challenge shift is a bijection.  Applying it in a security
reduction would require the message, which may depend on the unknown secret. -/
theorem addMaskShift_bijective {R : Type} [AddGroup R] [Mul R]
    {dimension samples : ℕ} (layout : Layout R dimension samples)
    (message : Fin samples → R) :
    Function.Bijective (fun challenge : Matrix (Fin dimension) (Fin samples) R ↦
      challenge + maskShift layout message) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨(fun challenge ↦ challenge - maskShift layout message), ?_, ?_⟩ <;>
    intro challenge <;> simp

/-- Full fresh view: auxiliary information and every GSW column share the sampled secret. -/
def freshView {R Secret Side : Type}
    [Ring R] [DecidableEq R] [SampleableType R] {dimension samples : ℕ}
    (layout : Layout R dimension samples) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin dimension → R) (messages : Secret → Fin samples → R)
    (auxiliary : Secret → ProbComp Side) (errorSampler : ProbComp (Fin samples → R)) :
    ProbComp (Side × BatchTranscript R dimension samples) := do
  let secret ← secretSampler
  let side ← auxiliary secret
  let challenge ← $ᵗ Matrix (Fin dimension) (Fin samples) R
  let error ← errorSampler
  return (side, freshTranscript layout (embed secret) (messages secret) challenge error)

/-- Full normalized view with the same auxiliary sampler and exact same error law. -/
def normalizedView {R Secret Side : Type}
    [Ring R] [DecidableEq R] [SampleableType R] {dimension samples : ℕ}
    (layout : Layout R dimension samples) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin dimension → R) (messages : Secret → Fin samples → R)
    (auxiliary : Secret → ProbComp Side) (errorSampler : ProbComp (Fin samples → R)) :
    ProbComp (Side × BatchTranscript R dimension samples) := do
  let secret ← secretSampler
  let side ← auxiliary secret
  let challenge ← $ᵗ Matrix (Fin dimension) (Fin samples) R
  let error ← errorSampler
  return (side, normalizedTranscript layout (embed secret) (messages secret) challenge error)

/-- The exact sampler equivalence retains all side information and all column correlations.
It needs no totality assumption and permits an arbitrary joint, independent-of-secret error law. -/
theorem freshView_evalDist {R Secret Side : Type}
    [Ring R] [DecidableEq R] [SampleableType R] {dimension samples : ℕ}
    (layout : Layout R dimension samples) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin dimension → R) (messages : Secret → Fin samples → R)
    (auxiliary : Secret → ProbComp Side) (errorSampler : ProbComp (Fin samples → R)) :
    evalDist (freshView layout secretSampler embed messages auxiliary errorSampler) =
      evalDist (normalizedView layout secretSampler embed messages auxiliary errorSampler) := by
  unfold freshView normalizedView
  refine evalDist_bind_congr' secretSampler fun secret ↦ ?_
  refine evalDist_bind_congr' (auxiliary secret) fun side ↦ ?_
  simp_rw [freshTranscript_eq_normalized]
  apply evalDist_ext
  intro output
  exact probOutput_bind_bijective_uniform_cross
    (α := Matrix (Fin dimension) (Fin samples) R)
    (β := Matrix (Fin dimension) (Fin samples) R)
    (fun challenge : Matrix (Fin dimension) (Fin samples) R ↦
      challenge + maskShift layout (messages secret))
    (addMaskShift_bijective layout (messages secret))
    (fun challenge ↦ errorSampler >>= fun error ↦
      pure (side, normalizedTranscript layout (embed secret) (messages secret) challenge error))
    output

/-- Binary secrets are represented explicitly rather than assumed for an arbitrary ring vector. -/
def binaryEmbed {R : Type} [Zero R] [One R] {dimension : ℕ}
    (secret : Fin dimension → Bool) : Fin dimension → R :=
  fun row ↦ if secret row then 1 else 0

theorem binaryEmbed_idempotent {R : Type} [Semiring R] {dimension : ℕ}
    (secret : Fin dimension → Bool) (row : Fin dimension) :
    binaryEmbed (R := R) secret row * binaryEmbed secret row = binaryEmbed secret row := by
  cases h : secret row <;> simp [binaryEmbed, h]

/-- Decode a full self-key column into its encrypted coordinate, gadget coordinate, and digit. -/
def selfKeyPosition (dimension digits : ℕ)
    (column : Fin (dimension * ((dimension + 1) * digits))) :
    Fin dimension × Fin (dimension + 1) × Fin digits :=
  let outer := finProdFinEquiv.symm column
  let inner := finProdFinEquiv.symm outer.2
  (outer.1, inner.1, inner.2)

/-- All columns of `dimension` GSW encryptions of the coordinates of that same secret. -/
def selfKeyLayout {R : Type} (dimension digits : ℕ) (gadget : Fin digits → R) :
    Layout R dimension (dimension * ((dimension + 1) * digits)) where
  coordinate column := Fin.cases none some (selfKeyPosition dimension digits column).2.1
  weight column := gadget (selfKeyPosition dimension digits column).2.2

/-- The plaintext for each full-key column is the coordinate encrypted by its GSW block. -/
def selfKeyMessages {R : Type} {dimension : ℕ} (digits : ℕ) (secret : Fin dimension → R) :
    Fin (dimension * ((dimension + 1) * digits)) → R :=
  fun column ↦ secret (selfKeyPosition dimension digits column).1

/-- Encode a particular column in the full self-key layout. -/
def selfKeyColumn {dimension digits : ℕ} (encrypted : Fin dimension)
    (coordinate : Fin (dimension + 1)) (digit : Fin digits) :
    Fin (dimension * ((dimension + 1) * digits)) :=
  finProdFinEquiv (encrypted, finProdFinEquiv (coordinate, digit))

@[simp]
theorem selfKeyPosition_selfKeyColumn {dimension digits : ℕ} (encrypted : Fin dimension)
    (coordinate : Fin (dimension + 1)) (digit : Fin digits) :
    selfKeyPosition dimension digits (selfKeyColumn encrypted coordinate digit) =
      (encrypted, coordinate, digit) := by
  simp [selfKeyPosition, selfKeyColumn]

/-- Body gadget rows encrypt an affine coordinate of the secret. -/
theorem selfKey_body_phase {R : Type} [Ring R] {dimension digits : ℕ}
    (gadget : Fin digits → R) (secret : Fin dimension → R)
    (encrypted : Fin dimension) (digit : Fin digits) :
    phaseMessage (selfKeyLayout dimension digits gadget) secret (selfKeyMessages digits secret)
      (selfKeyColumn encrypted 0 digit) = secret encrypted * gadget digit := by
  simp [phaseMessage, selfKeyLayout, selfKeyMessages]

/-- Mask gadget rows expose every quadratic coordinate product, with its actual gadget weight. -/
theorem selfKey_mask_phase {R : Type} [CommRing R] {dimension digits : ℕ}
    (gadget : Fin digits → R) (secret : Fin dimension → R)
    (encrypted row : Fin dimension) (digit : Fin digits) :
    phaseMessage (selfKeyLayout dimension digits gadget) secret (selfKeyMessages digits secret)
      (selfKeyColumn encrypted row.succ digit) =
        -(secret encrypted * secret row * gadget digit) := by
  simp [phaseMessage, selfKeyLayout, selfKeyMessages]
  ring

/-- For binary secrets precisely the diagonal mask products collapse to affine messages. -/
theorem binary_selfKey_diagonal_phase {R : Type} [CommRing R] {dimension digits : ℕ}
    (gadget : Fin digits → R) (secret : Fin dimension → Bool)
    (row : Fin dimension) (digit : Fin digits) :
    phaseMessage (selfKeyLayout dimension digits gadget) (binaryEmbed secret)
      (selfKeyMessages digits (binaryEmbed secret)) (selfKeyColumn row row.succ digit) =
        -(binaryEmbed secret row * gadget digit) := by
  rw [selfKey_mask_phase, binaryEmbed_idempotent]

/-- Exact binary products, considered as *unmasked* leakage rather than ciphertexts. -/
def quadraticBits {dimension : ℕ} (secret : Fin dimension → Bool) :
    Matrix (Fin dimension) (Fin dimension) Bool :=
  fun first second ↦ secret first && secret second

/-- Revealing the complete binary outer product reveals the entire secret via its diagonal.
Thus an entropy argument cannot safely grant these products as free exact auxiliary hints. -/
theorem quadraticBits_injective {dimension : ℕ} :
    Function.Injective (quadraticBits (dimension := dimension)) := by
  intro first second hequal
  funext row
  have hdiagonal := congrFun (congrFun hequal row) row
  simpa [quadraticBits] using hdiagonal

/-- Off-diagonal exact products also recover every bit whenever at least two bits are one. -/
theorem recover_from_offDiagonal {dimension : ℕ} (secret : Fin dimension → Bool)
    (htwo : ∃ first second, first ≠ second ∧ secret first = true ∧ secret second = true)
    (row : Fin dimension) :
    (∃ other, other ≠ row ∧ quadraticBits secret row other = true) ↔ secret row = true := by
  constructor
  · rintro ⟨other, _, hproduct⟩
    have hbits : secret row = true ∧ secret other = true := by
      simpa [quadraticBits] using hproduct
    exact hbits.1
  · intro hrow
    obtain ⟨first, second, hdistinct, hfirst, hsecond⟩ := htwo
    by_cases hsame : first = row
    · refine ⟨second, ?_, ?_⟩
      · simpa [hsame] using hdistinct.symm
      · simp [quadraticBits, hrow, hsecond]
    · exact ⟨first, hsame, by simp [quadraticBits, hrow, hfirst]⟩

/-- Off-diagonal binary products cannot be absorbed using fixed affine coefficients.
This rules out directly applying the existing affine coefficient-shift theorem to those rows. -/
theorem binaryProduct_not_affine {R : Type} [Ring R] [Nontrivial R] :
    ¬ ∃ first second offset : R, ∀ left right : Bool,
      (if left then (1 : R) else 0) * (if right then (1 : R) else 0) =
        first * (if left then (1 : R) else 0) +
        second * (if right then (1 : R) else 0) + offset := by
  rintro ⟨first, second, offset, hequal⟩
  have hoffset : offset = 0 := by
    simpa using (hequal false false).symm
  have hfirst : first = 0 := by
    simpa [hoffset] using (hequal true false).symm
  have hsecond : second = 0 := by
    simpa [hoffset] using (hequal false true).symm
  have hbad : (1 : R) = 0 := by
    simpa [hoffset, hfirst, hsecond] using hequal true true
  exact one_ne_zero hbad

end FormalProof4FHE.LWE.GSWSelfKey
