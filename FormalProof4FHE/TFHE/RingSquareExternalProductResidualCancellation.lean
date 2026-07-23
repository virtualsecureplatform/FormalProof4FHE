/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.InternalProduct
import FormalProof4FHE.TFHE.RingSquareRGSWSecurity
import FormalProof4FHE.TFHE.SharpRotationNoise

/-!
# External-Product Cancellation of the `RGSW_S(-S)` Compiler Residual

The public short-preimage compiler produces a square row whose phase contains

`S * phase(weightedSourceRow)`.

If a TGSW ciphertext encrypting `-S` is externally multiplied by that same weighted source row,
its phase contains the opposite term.  Adding the two public ciphertexts therefore cancels the
complete hidden source-error residual exactly.  The replacement residual is the standard weighted
TGSW row-error term of the external product.

This identity is algebraic and preserves narrow errors at the level of correctness bounds.  It is
not by itself a reduction from ordinary RLWE: the cancellation control is the circular
`RGSW_S(-S)` object whose security is at issue.  A computational proof must still remove that
self-auxiliary dependence or prove a suitable native rerandomization theorem.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler

namespace ExternalProductCancellation

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

/-! ## Public cancellation map -/

/-- Add the external product of a weighted source row with a caller-supplied TGSW control to the
square row produced by the short-preimage compiler.  Every operation is public. -/
def cancelResidual
    {R Index : Type} [CommRing R] [Fintype Index] {levels : ℕ}
    (weight : Index → R) (sourceRows : Index → TLWE.Ciphertext R 1)
    (targetRow : TLWE.Ciphertext R 1)
    (digits : Fin (1 + 1) → Fin levels → R)
    (control : TGSW.Ciphertext R 1 levels) : TLWE.Ciphertext R 1 :=
  TLWE.add
    (squareFromPreimage weight sourceRows targetRow)
    (TGSW.externalProduct digits control)

/-! ## Upper/lower external-product split -/

/-- The part of a rank-one external product using only the mask-block control rows. -/
def upperExternalProduct
    {R : Type} [Semiring R] {levels : ℕ}
    (digits : Fin (1 + 1) → Fin levels → R)
    (control : TGSW.Ciphertext R 1 levels) : TLWE.Ciphertext R 1 :=
  TLWE.linearCombination
    (digits (0 : Fin (1 + 1)))
    (fun level ↦ TLWE.entry control
      (finProdFinEquiv (Fin.castSucc (0 : Fin 1), level)))

/-- The part of a rank-one external product using only the final, body-block control rows. -/
def lowerExternalProductOfDigits
    {R : Type} [Semiring R] {levels : ℕ}
    (digits : Fin (1 + 1) → Fin levels → R)
    (control : TGSW.Ciphertext R 1 levels) : TLWE.Ciphertext R 1 :=
  TLWE.linearCombination
    (digits (1 : Fin (1 + 1)))
    (fun level ↦ TLWE.entry control
      (finProdFinEquiv (Fin.last 1, level)))

/-- Every rank-one external product splits exactly into its upper and lower control blocks. -/
theorem externalProduct_eq_upper_add_lower
    {R : Type} [CommSemiring R] {levels : ℕ}
    (digits : Fin (1 + 1) → Fin levels → R)
    (control : TGSW.Ciphertext R 1 levels) :
    TGSW.externalProduct digits control =
      TLWE.add (upperExternalProduct digits control)
        (lowerExternalProductOfDigits digits control) := by
  classical
  rw [TLWE.Ciphertext.mk.injEq]
  constructor
  · funext coordinate
    simp [TGSW.externalProduct, upperExternalProduct, lowerExternalProductOfDigits,
      TLWE.linearCombination, TLWE.add, Fintype.sum_prod_type,
      Fin.sum_univ_castSucc]
  · simp [TGSW.externalProduct, upperExternalProduct, lowerExternalProductOfDigits,
      TLWE.linearCombination, TLWE.add, Fintype.sum_prod_type,
      Fin.sum_univ_castSucc]

/-- The mask-block contribution to the standard external-product row error. -/
def upperExternalProductError
    {R : Type} [Ring R] {levels : ℕ}
    (secret : Fin 1 → R) (gadget : Fin levels → R) (message : R)
    (digits : Fin (1 + 1) → Fin levels → R)
    (control : TGSW.Ciphertext R 1 levels) : R :=
  ∑ level, digits (0 : Fin (1 + 1)) level *
    TGSW.rowError secret gadget message control
      (Fin.castSucc (0 : Fin 1), level)

/-- The final-block contribution to the standard external-product row error. -/
def lowerExternalProductError
    {R : Type} [Ring R] {levels : ℕ}
    (secret : Fin 1 → R) (gadget : Fin levels → R) (message : R)
    (digits : Fin (1 + 1) → Fin levels → R)
    (control : TGSW.Ciphertext R 1 levels) : R :=
  ∑ level, digits (1 : Fin (1 + 1)) level *
    TGSW.rowError secret gadget message control (Fin.last 1, level)

/-- The standard rank-one external-product error splits over the two control blocks. -/
theorem externalProductError_eq_upper_add_lower
    {R : Type} [CommRing R] {levels : ℕ}
    (secret : Fin 1 → R) (gadget : Fin levels → R) (message : R)
    (digits : Fin (1 + 1) → Fin levels → R)
    (control : TGSW.Ciphertext R 1 levels) :
    TGSW.externalProductError secret gadget message digits control =
      upperExternalProductError secret gadget message digits control +
        lowerExternalProductError secret gadget message digits control := by
  classical
  unfold TGSW.externalProductError upperExternalProductError
    lowerExternalProductError
  rw [Fintype.sum_prod_type, Fin.sum_univ_castSucc, Fin.sum_univ_one]
  rfl

/-! ## A target-level decomposition of the weighted source row -/

/-- Decompose the body of a rank-one row normally, but represent its known gadget-valued mask by
the one-hot digit at `targetLevel`.  The construction is useful exactly when a short-preimage
selector has made the row mask equal to that gadget element. -/
noncomputable def targetLevelDigits
    {q degree : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (targetLevel : Fin params.levels)
    (row : TLWE.Ciphertext (RLWE.Rq q (degree + 1)) 1) :
    Fin (1 + 1) → Fin params.levels → RLWE.Rq q (degree + 1) :=
  fun block ↦
    Fin.lastCases
      (Gadget.Base.ringDigit params row.body)
      (fun _ level ↦ if level = targetLevel then 1 else 0)
      block

@[simp]
theorem targetLevelDigits_castSucc
    {q degree : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (targetLevel : Fin params.levels)
    (row : TLWE.Ciphertext (RLWE.Rq q (degree + 1)) 1)
    (coordinate : Fin 1) (level : Fin params.levels) :
    targetLevelDigits params targetLevel row (Fin.castSucc coordinate) level =
      if level = targetLevel then 1 else 0 := by
  simp [targetLevelDigits]

@[simp]
theorem targetLevelDigits_last
    {q degree : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (targetLevel : Fin params.levels)
    (row : TLWE.Ciphertext (RLWE.Rq q (degree + 1)) 1)
    (level : Fin params.levels) :
    targetLevelDigits params targetLevel row (Fin.last 1) level =
      Gadget.Base.ringDigit params row.body level := by
  unfold targetLevelDigits
  rw [Fin.lastCases_last]

/-- A genuine public gadget preimage makes `targetLevelDigits` an exact decomposition of the
complete weighted source row. -/
theorem targetLevelDigits_decomposes_preimageCombination
    {q degree : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (targetLevel : Fin params.levels)
    {Index : Type} [Fintype Index]
    (weight : Index → RLWE.Rq q (degree + 1))
    (sourceRows : Index → TLWE.Ciphertext (RLWE.Rq q (degree + 1)) 1)
    (hPreimage : HasGadgetPreimage
      (Gadget.Base.ringGadget params targetLevel) weight sourceRows) :
    Gadget.Decomposes (Gadget.Base.ringGadget params)
      (preimageCombination weight sourceRows)
      (targetLevelDigits params targetLevel
        (preimageCombination weight sourceRows)) := by
  intro block
  refine Fin.lastCases ?_ (fun coordinate ↦ ?_) block
  · change Gadget.recompose (Gadget.Base.ringGadget params)
        (Gadget.Base.ringDigit params
          (preimageCombination weight sourceRows).body) =
      (preimageCombination weight sourceRows).body
    exact Gadget.Base.ring_recompose params
      (preimageCombination weight sourceRows).body
  · rw [Subsingleton.elim coordinate 0]
    change Gadget.recompose (Gadget.Base.ringGadget params)
        (fun level ↦ if level = targetLevel then 1 else 0) =
      (preimageCombination weight sourceRows).mask 0
    calc
      Gadget.recompose (Gadget.Base.ringGadget params)
          (fun level ↦ if level = targetLevel then 1 else 0) =
          Gadget.Base.ringGadget params targetLevel := by
            unfold Gadget.recompose
            rw [Finset.sum_eq_single targetLevel]
            · dsimp
              simp
            · intro level _ hne
              dsimp
              simp [hne]
            · simp
      _ = (preimageCombination weight sourceRows).mask 0 := by
        simpa [HasGadgetPreimage] using hPreimage.symm

/-- The contribution of the lower, linear-message control rows to the external-product error. -/
noncomputable def lowerRowErrorProduct
    {q degree : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (secret : Fin 1 → RLWE.Rq q (degree + 1))
    (row : TLWE.Ciphertext (RLWE.Rq q (degree + 1)) 1)
    (control : TGSW.Ciphertext
      (RLWE.Rq q (degree + 1)) 1 params.levels) :
    RLWE.Rq q (degree + 1) :=
  ∑ level,
    Gadget.Base.ringDigit params row.body level *
      TGSW.rowError (R := RLWE.Rq q (degree + 1)) secret
        (Gadget.Base.ringGadget params) (-secret 0) control
        (Fin.last 1, level)

/-- The one-hot mask digit forces the external-product error to retain the corresponding circular
upper-row error with coefficient one.  All remaining terms come only from the lower rows. -/
theorem externalProductError_targetLevelDigits_eq_upper_add_lower
    {q degree : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (secret : Fin 1 → RLWE.Rq q (degree + 1))
    (targetLevel : Fin params.levels)
    (row : TLWE.Ciphertext (RLWE.Rq q (degree + 1)) 1)
    (control : TGSW.Ciphertext
      (RLWE.Rq q (degree + 1)) 1 params.levels) :
    TGSW.externalProductError (R := RLWE.Rq q (degree + 1)) secret
        (Gadget.Base.ringGadget params) (-secret 0)
        (targetLevelDigits params targetLevel row) control =
      TGSW.rowError (R := RLWE.Rq q (degree + 1)) secret
          (Gadget.Base.ringGadget params) (-secret 0) control
          (Fin.castSucc (0 : Fin 1), targetLevel) +
        lowerRowErrorProduct params secret row control := by
  classical
  have hLastDigits :
      targetLevelDigits params targetLevel row (Fin.last 1) =
        Gadget.Base.ringDigit params row.body := by
    funext level
    exact targetLevelDigits_last params targetLevel row level
  unfold TGSW.externalProductError lowerRowErrorProduct
  rw [Fintype.sum_prod_type, Fin.sum_univ_castSucc, Fin.sum_univ_one]
  simp only
  rw [hLastDigits]
  simp only [targetLevelDigits_castSucc, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single targetLevel]
  · rw [if_pos rfl]
  · intro level _ hne
    rw [if_neg hne]
  · simp

/-- Adding one fixed public TLWE row is a permutation of the complete row carrier. -/
theorem addRight_bijective
    {R : Type} [AddCommGroup R] {dimension : ℕ}
    (offset : TLWE.Ciphertext R dimension) :
    Function.Bijective (fun row ↦ TLWE.add row offset) := by
  apply Function.bijective_iff_has_inverse.mpr
  refine ⟨fun row ↦ TLWE.sub row offset, ?_, ?_⟩
  · intro row
    rw [TLWE.Ciphertext.mk.injEq]
    constructor
    · funext coordinate
      simp [TLWE.add, TLWE.sub]
    · simp [TLWE.add, TLWE.sub]
  · intro row
    rw [TLWE.Ciphertext.mk.injEq]
    constructor
    · funext coordinate
      simp [TLWE.add, TLWE.sub]
    · simp [TLWE.add, TLWE.sub]

/-- For fixed source material, digits, and control, external-product cancellation remains a
permutation of the independent target row. -/
theorem cancelResidual_target_bijective
    {R Index : Type} [CommRing R] [Fintype Index] {levels : ℕ}
    (weight : Index → R) (sourceRows : Index → TLWE.Ciphertext R 1)
    (digits : Fin (1 + 1) → Fin levels → R)
    (control : TGSW.Ciphertext R 1 levels) :
    Function.Bijective
      (fun targetRow ↦ cancelResidual weight sourceRows targetRow digits control) := by
  have hTranslate := addRight_bijective (TGSW.externalProduct digits control)
  have hCompile := Row.subtractMask_bijective
    (gadgetApproximation weight sourceRows)
  simpa [cancelResidual, squareFromPreimage, squareFromApproximation,
    Function.comp_def] using
    hTranslate.comp hCompile

noncomputable local instance sampleableCiphertext
    {R : Type} [SampleableType R] {dimension : ℕ} :
    SampleableType (TLWE.Ciphertext R dimension) :=
  SampleableType.ofEquiv (TLWE.ciphertextEquiv R dimension)

/-- Thus an independent uniform target row remains exactly uniform after cancellation,
conditionally on arbitrary fixed source material and an arbitrary fixed control ciphertext. -/
theorem cancelResidual_uniform_target_evalDist
    {R Index : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Index] {levels : ℕ}
    (weight : Index → R) (sourceRows : Index → TLWE.Ciphertext R 1)
    (digits : Fin (1 + 1) → Fin levels → R)
    (control : TGSW.Ciphertext R 1 levels) :
    evalDist
        ((fun targetRow ↦
          cancelResidual weight sourceRows targetRow digits control) <$>
          ($ᵗ (TLWE.Ciphertext R 1))) =
      evalDist ($ᵗ (TLWE.Ciphertext R 1)) := by
  exact evalDist_map_bijective_uniform_cross
    (α := TLWE.Ciphertext R 1) (β := TLWE.Ciphertext R 1)
    (fun targetRow ↦
      cancelResidual weight sourceRows targetRow digits control)
    (cancelResidual_target_bijective weight sourceRows digits control)

/-- **Exact external-product cancellation identity.**  If the public weights recompose the target
gadget element and the supplied digits recompose the same weighted source row, then a control
whose intended message is `-S` cancels the compiler's complete `S * sourcePhase` term.  No
statistical approximation is used. -/
theorem phase_cancelResidual_eq_square_add_target_add_externalProductError
    {R Index : Type} [CommRing R] [Fintype Index] {levels : ℕ}
    (secret : Fin 1 → R)
    (controlGadget : Fin levels → R) (targetGadget : R)
    (weight : Index → R) (sourceRows : Index → TLWE.Ciphertext R 1)
    (targetRow : TLWE.Ciphertext R 1)
    (digits : Fin (1 + 1) → Fin levels → R)
    (control : TGSW.Ciphertext R 1 levels)
    (hPreimage : HasGadgetPreimage targetGadget weight sourceRows)
    (hDecomposes :
      Gadget.Decomposes controlGadget
        (preimageCombination weight sourceRows) digits) :
    TLWE.phase secret
        (cancelResidual weight sourceRows targetRow digits control) =
      secret 0 * secret 0 * targetGadget +
        TLWE.phase secret targetRow +
          TGSW.externalProductError secret controlGadget (-secret 0)
            digits control := by
  rw [cancelResidual, TLWE.phase_add]
  rw [phase_squareFromPreimage secret targetGadget weight sourceRows targetRow hPreimage]
  rw [TGSW.phase_externalProduct_eq_mul_add_error
    secret controlGadget (-secret 0)
    (preimageCombination weight sourceRows) digits control hDecomposes]
  ring

/-- When the target row is an ordinary zero-message RLWE sample with phase `targetError`, the
result is a square row with exactly that target error plus the external-product error. -/
theorem phase_cancelResidual_eq_square_add_errors
    {R Index : Type} [CommRing R] [Fintype Index] {levels : ℕ}
    (secret : Fin 1 → R)
    (controlGadget : Fin levels → R) (targetGadget targetError : R)
    (weight : Index → R) (sourceRows : Index → TLWE.Ciphertext R 1)
    (targetRow : TLWE.Ciphertext R 1)
    (digits : Fin (1 + 1) → Fin levels → R)
    (control : TGSW.Ciphertext R 1 levels)
    (hPreimage : HasGadgetPreimage targetGadget weight sourceRows)
    (hDecomposes :
      Gadget.Decomposes controlGadget
        (preimageCombination weight sourceRows) digits)
    (hTarget : TLWE.phase secret targetRow = targetError) :
    TLWE.phase secret
        (cancelResidual weight sourceRows targetRow digits control) =
      secret 0 * secret 0 * targetGadget + targetError +
        TGSW.externalProductError secret controlGadget (-secret 0)
          digits control := by
  rw [phase_cancelResidual_eq_square_add_target_add_externalProductError
    secret controlGadget targetGadget weight sourceRows targetRow digits control
      hPreimage hDecomposes]
  rw [hTarget]

/-- After subtracting the intended square phase, the compiler's source-error term has disappeared
completely; only the target-row phase and standard external-product error remain. -/
theorem residual_cancelResidual_eq_target_add_externalProductError
    {R Index : Type} [CommRing R] [Fintype Index] {levels : ℕ}
    (secret : Fin 1 → R)
    (controlGadget : Fin levels → R) (targetGadget : R)
    (weight : Index → R) (sourceRows : Index → TLWE.Ciphertext R 1)
    (targetRow : TLWE.Ciphertext R 1)
    (digits : Fin (1 + 1) → Fin levels → R)
    (control : TGSW.Ciphertext R 1 levels)
    (hPreimage : HasGadgetPreimage targetGadget weight sourceRows)
    (hDecomposes :
      Gadget.Decomposes controlGadget
        (preimageCombination weight sourceRows) digits) :
    TLWE.phase secret
          (cancelResidual weight sourceRows targetRow digits control) -
        secret 0 * secret 0 * targetGadget =
      TLWE.phase secret targetRow +
        TGSW.externalProductError secret controlGadget (-secret 0)
          digits control := by
  rw [phase_cancelResidual_eq_square_add_target_add_externalProductError
    secret controlGadget targetGadget weight sourceRows targetRow digits control
      hPreimage hDecomposes]
  ring

/-! ## Generic retained-square normal form -/

/-- Any exact decomposition of a row whose mask is the target gadget forces the upper part of a
control for `-S` to carry that same gadget-scaled square message.  This statement is independent
of how the mask digit is represented. -/
theorem phase_upperExternalProduct_eq_square_add_error
    {R : Type} [CommRing R] {levels : ℕ}
    (secret : Fin 1 → R) (gadget : Fin levels → R) (targetGadget : R)
    (row : TLWE.Ciphertext R 1)
    (digits : Fin (1 + 1) → Fin levels → R)
    (control : TGSW.Ciphertext R 1 levels)
    (hDecomposes : Gadget.Decomposes gadget row digits)
    (hMask : row.mask 0 = targetGadget) :
    TLWE.phase secret (upperExternalProduct digits control) =
      secret 0 * secret 0 * targetGadget +
        upperExternalProductError secret gadget (-secret 0) digits control := by
  classical
  have hRecompose :
      (∑ level, digits (0 : Fin (1 + 1)) level * gadget level) = targetGadget := by
    have h := hDecomposes (0 : Fin (1 + 1))
    change Gadget.recompose gadget (digits (0 : Fin (1 + 1))) = row.mask 0 at h
    exact (by simpa [Gadget.recompose] using h.trans hMask)
  have hIdeal :
      (∑ level, digits (0 : Fin (1 + 1)) level *
        TGSW.gadgetPhase secret gadget (-secret 0)
          (finProdFinEquiv (Fin.castSucc (0 : Fin 1), level))) =
        secret 0 * secret 0 * targetGadget := by
    simp_rw [TGSW.gadgetPhase_castSucc]
    calc
      _ = ∑ level, secret 0 * secret 0 *
          (digits (0 : Fin (1 + 1)) level * gadget level) := by
            apply Finset.sum_congr rfl
            intro level _
            ring
      _ = secret 0 * secret 0 *
          (∑ level, digits (0 : Fin (1 + 1)) level * gadget level) := by
            rw [Finset.mul_sum]
      _ = secret 0 * secret 0 * targetGadget := by rw [hRecompose]
  rw [upperExternalProduct, TLWE.phase_linearCombination]
  calc
    (∑ level, digits (0 : Fin (1 + 1)) level *
        TLWE.phase secret
          (TLWE.entry control
            (finProdFinEquiv (Fin.castSucc (0 : Fin 1), level)))) =
        (∑ level, digits (0 : Fin (1 + 1)) level *
          TGSW.gadgetPhase secret gadget (-secret 0)
            (finProdFinEquiv (Fin.castSucc (0 : Fin 1), level))) +
          ∑ level, digits (0 : Fin (1 + 1)) level *
            TGSW.rowError secret gadget (-secret 0) control
              (Fin.castSucc (0 : Fin 1), level) := by
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro level _
                unfold TGSW.rowError
                ring
    _ = secret 0 * secret 0 * targetGadget +
          upperExternalProductError secret gadget (-secret 0) digits control := by
            rw [hIdeal]
            rfl

/-- Remove the entire upper-block combination, rather than selecting any particular upper row. -/
def genericRerandomizationDifference
    {R Index : Type} [CommRing R] [Fintype Index] {levels : ℕ}
    (weight : Index → R) (sourceRows : Index → TLWE.Ciphertext R 1)
    (targetRow : TLWE.Ciphertext R 1)
    (digits : Fin (1 + 1) → Fin levels → R)
    (control : TGSW.Ciphertext R 1 levels) : TLWE.Ciphertext R 1 :=
  TLWE.sub (cancelResidual weight sourceRows targetRow digits control)
    (upperExternalProduct digits control)

/-- At ciphertext level, the generic remainder uses only the compiler output and lower control
rows.  No upper control entry occurs on the right-hand side. -/
theorem genericRerandomizationDifference_eq_square_add_lower
    {R Index : Type} [CommRing R] [Fintype Index] {levels : ℕ}
    (weight : Index → R) (sourceRows : Index → TLWE.Ciphertext R 1)
    (targetRow : TLWE.Ciphertext R 1)
    (digits : Fin (1 + 1) → Fin levels → R)
    (control : TGSW.Ciphertext R 1 levels) :
    genericRerandomizationDifference weight sourceRows targetRow digits control =
      TLWE.add (squareFromPreimage weight sourceRows targetRow)
        (lowerExternalProductOfDigits digits control) := by
  unfold genericRerandomizationDifference cancelResidual
  rw [externalProduct_eq_upper_add_lower]
  rw [TLWE.Ciphertext.mk.injEq]
  constructor
  · funext coordinate
    simp [TLWE.add, TLWE.sub]
    ring
  · simp [TLWE.add, TLWE.sub]
    ring

/-- For every exact digit decomposition, subtracting the upper control combination leaves a
zero-message row.  Its phase contains only the fresh target error and lower-block row errors. -/
theorem phase_genericRerandomizationDifference_eq_target_add_lowerError
    {R Index : Type} [CommRing R] [Fintype Index] {levels : ℕ}
    (secret : Fin 1 → R)
    (gadget : Fin levels → R) (targetGadget targetError : R)
    (weight : Index → R) (sourceRows : Index → TLWE.Ciphertext R 1)
    (targetRow : TLWE.Ciphertext R 1)
    (digits : Fin (1 + 1) → Fin levels → R)
    (control : TGSW.Ciphertext R 1 levels)
    (hPreimage : HasGadgetPreimage targetGadget weight sourceRows)
    (hDecomposes : Gadget.Decomposes gadget
      (preimageCombination weight sourceRows) digits)
    (hTarget : TLWE.phase secret targetRow = targetError) :
    TLWE.phase secret
        (genericRerandomizationDifference weight sourceRows targetRow digits control) =
      targetError +
        lowerExternalProductError secret gadget (-secret 0) digits control := by
  have hMask : (preimageCombination weight sourceRows).mask 0 = targetGadget := by
    simpa [HasGadgetPreimage] using hPreimage
  rw [genericRerandomizationDifference, TLWE.phase_sub]
  rw [phase_cancelResidual_eq_square_add_errors secret gadget targetGadget targetError
    weight sourceRows targetRow digits control hPreimage hDecomposes hTarget]
  rw [externalProductError_eq_upper_add_lower]
  rw [phase_upperExternalProduct_eq_square_add_error secret gadget targetGadget
    (preimageCombination weight sourceRows) digits control hDecomposes hMask]
  ring

/-- The self-assisted cancellation output is always the upper square-carrying control combination
plus its zero-message remainder. -/
theorem upperExternalProduct_add_genericRerandomizationDifference
    {R Index : Type} [CommRing R] [Fintype Index] {levels : ℕ}
    (weight : Index → R) (sourceRows : Index → TLWE.Ciphertext R 1)
    (targetRow : TLWE.Ciphertext R 1)
    (digits : Fin (1 + 1) → Fin levels → R)
    (control : TGSW.Ciphertext R 1 levels) :
    TLWE.add (upperExternalProduct digits control)
        (genericRerandomizationDifference weight sourceRows targetRow digits control) =
      cancelResidual weight sourceRows targetRow digits control := by
  rw [TLWE.Ciphertext.mk.injEq]
  constructor
  · funext coordinate
    simp [genericRerandomizationDifference, TLWE.add, TLWE.sub]
  · simp [genericRerandomizationDifference, TLWE.add, TLWE.sub]

/-! ## Retained-control normal form -/

/-- The self-assisted cancellation map instantiated with the exact target-level decomposition. -/
noncomputable def cancelResidualAtTargetLevel
    {q degree : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (targetLevel : Fin params.levels)
    {Index : Type} [Fintype Index]
    (weight : Index → RLWE.Rq q (degree + 1))
    (sourceRows : Index → TLWE.Ciphertext (RLWE.Rq q (degree + 1)) 1)
    (targetRow : TLWE.Ciphertext (RLWE.Rq q (degree + 1)) 1)
    (control : TGSW.Ciphertext
      (RLWE.Rq q (degree + 1)) 1 params.levels) :
    TLWE.Ciphertext (RLWE.Rq q (degree + 1)) 1 :=
  cancelResidual weight sourceRows targetRow
    (targetLevelDigits params targetLevel
      (preimageCombination weight sourceRows)) control

/-- The circular upper row selected by the one-hot mask digit. -/
def upperControlRow
    {R : Type} {levels : ℕ}
    (targetLevel : Fin levels) (control : TGSW.Ciphertext R 1 levels) :
    TLWE.Ciphertext R 1 :=
  TLWE.entry control
    (finProdFinEquiv (Fin.castSucc (0 : Fin 1), targetLevel))

/-- The external product formed only from the final (linear-message) control block. -/
noncomputable def lowerExternalProduct
    {q degree : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (row : TLWE.Ciphertext (RLWE.Rq q (degree + 1)) 1)
    (control : TGSW.Ciphertext
      (RLWE.Rq q (degree + 1)) 1 params.levels) :
    TLWE.Ciphertext (RLWE.Rq q (degree + 1)) 1 :=
  TLWE.linearCombination
    (Gadget.Base.ringDigit params row.body)
    (fun level ↦ TLWE.entry control (finProdFinEquiv (Fin.last 1, level)))

/-- With the exact target-level digits, the complete external product is literally the selected
upper control row plus a linear combination of lower control rows. -/
theorem externalProduct_targetLevelDigits_eq_upper_add_lower
    {q degree : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetLevel : Fin params.levels)
    (row : TLWE.Ciphertext (RLWE.Rq q (degree + 1)) 1)
    (control : TGSW.Ciphertext
      (RLWE.Rq q (degree + 1)) 1 params.levels) :
    TGSW.externalProduct (targetLevelDigits params targetLevel row) control =
      TLWE.add (upperControlRow targetLevel control)
        (lowerExternalProduct params row control) := by
  classical
  have hLastDigits :
      targetLevelDigits params targetLevel row (1 : Fin (1 + 1)) =
        Gadget.Base.ringDigit params row.body := by
    funext level
    exact targetLevelDigits_last params targetLevel row level
  rw [TLWE.Ciphertext.mk.injEq]
  constructor
  · funext coordinate
    simp [TGSW.externalProduct, TLWE.linearCombination, upperControlRow,
      lowerExternalProduct, TLWE.add, Fintype.sum_prod_type,
      Fin.sum_univ_castSucc]
    rw [hLastDigits]
  · simp [TGSW.externalProduct, TLWE.linearCombination, upperControlRow,
      lowerExternalProduct, TLWE.add, Fintype.sum_prod_type,
      Fin.sum_univ_castSucc]
    rw [hLastDigits]

/-- Subtract the retained circular upper row from the self-assisted output. -/
noncomputable def rerandomizationDifference
    {q degree : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (targetLevel : Fin params.levels)
    {Index : Type} [Fintype Index]
    (weight : Index → RLWE.Rq q (degree + 1))
    (sourceRows : Index → TLWE.Ciphertext (RLWE.Rq q (degree + 1)) 1)
    (targetRow : TLWE.Ciphertext (RLWE.Rq q (degree + 1)) 1)
    (control : TGSW.Ciphertext
      (RLWE.Rq q (degree + 1)) 1 params.levels) :
    TLWE.Ciphertext (RLWE.Rq q (degree + 1)) 1 :=
  TLWE.sub
    (cancelResidualAtTargetLevel params targetLevel weight sourceRows targetRow control)
    (upperControlRow targetLevel control)

/-- **The self-assisted output retains the selected circular row.**  Its phase is the phase of
that exact control row plus the target error and a term depending only on the lower control-row
errors. -/
theorem phase_cancelResidualAtTargetLevel_eq_upperControl_add_errors
    {q degree : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (secret : Fin 1 → RLWE.Rq q (degree + 1))
    (targetLevel : Fin params.levels)
    {Index : Type} [Fintype Index]
    (weight : Index → RLWE.Rq q (degree + 1))
    (sourceRows : Index → TLWE.Ciphertext (RLWE.Rq q (degree + 1)) 1)
    (targetRow : TLWE.Ciphertext (RLWE.Rq q (degree + 1)) 1)
    (targetError : RLWE.Rq q (degree + 1))
    (control : TGSW.Ciphertext
      (RLWE.Rq q (degree + 1)) 1 params.levels)
    (hPreimage : HasGadgetPreimage
      (Gadget.Base.ringGadget params targetLevel) weight sourceRows)
    (hTarget : TLWE.phase secret targetRow = targetError) :
    TLWE.phase secret
        (cancelResidualAtTargetLevel params targetLevel weight sourceRows
          targetRow control) =
      TLWE.phase secret (upperControlRow targetLevel control) + targetError +
        lowerRowErrorProduct params secret
          (preimageCombination weight sourceRows) control := by
  unfold cancelResidualAtTargetLevel
  rw [phase_cancelResidual_eq_square_add_errors
    secret (Gadget.Base.ringGadget params)
    (Gadget.Base.ringGadget params targetLevel) targetError
    weight sourceRows targetRow
    (targetLevelDigits params targetLevel
      (preimageCombination weight sourceRows)) control hPreimage
    (targetLevelDigits_decomposes_preimageCombination
      params targetLevel weight sourceRows hPreimage) hTarget]
  rw [externalProductError_targetLevelDigits_eq_upper_add_lower]
  unfold TGSW.rowError upperControlRow
  rw [TGSW.gadgetPhase_castSucc]
  ring

/-- Removing the retained upper row leaves a genuine zero-message rerandomizer: its phase contains
only the fresh target error and lower-control-row errors. -/
theorem phase_rerandomizationDifference_eq_target_add_lowerErrors
    {q degree : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (secret : Fin 1 → RLWE.Rq q (degree + 1))
    (targetLevel : Fin params.levels)
    {Index : Type} [Fintype Index]
    (weight : Index → RLWE.Rq q (degree + 1))
    (sourceRows : Index → TLWE.Ciphertext (RLWE.Rq q (degree + 1)) 1)
    (targetRow : TLWE.Ciphertext (RLWE.Rq q (degree + 1)) 1)
    (targetError : RLWE.Rq q (degree + 1))
    (control : TGSW.Ciphertext
      (RLWE.Rq q (degree + 1)) 1 params.levels)
    (hPreimage : HasGadgetPreimage
      (Gadget.Base.ringGadget params targetLevel) weight sourceRows)
    (hTarget : TLWE.phase secret targetRow = targetError) :
    TLWE.phase secret
        (rerandomizationDifference params targetLevel weight sourceRows targetRow control) =
      targetError +
        lowerRowErrorProduct params secret
          (preimageCombination weight sourceRows) control := by
  rw [rerandomizationDifference, TLWE.phase_sub]
  rw [phase_cancelResidualAtTargetLevel_eq_upperControl_add_errors
    params secret targetLevel weight sourceRows targetRow targetError control
      hPreimage hTarget]
  ring

/-- Componentwise addition recovers the self-assisted output from the retained circular row and
its zero-message rerandomization difference. -/
theorem upperControlRow_add_rerandomizationDifference
    {q degree : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (targetLevel : Fin params.levels)
    {Index : Type} [Fintype Index]
    (weight : Index → RLWE.Rq q (degree + 1))
    (sourceRows : Index → TLWE.Ciphertext (RLWE.Rq q (degree + 1)) 1)
    (targetRow : TLWE.Ciphertext (RLWE.Rq q (degree + 1)) 1)
    (control : TGSW.Ciphertext
      (RLWE.Rq q (degree + 1)) 1 params.levels) :
    TLWE.add (upperControlRow targetLevel control)
        (rerandomizationDifference params targetLevel weight sourceRows targetRow control) =
      cancelResidualAtTargetLevel params targetLevel weight sourceRows targetRow control := by
  rw [TLWE.Ciphertext.mk.injEq]
  constructor
  · funext coordinate
    simp [rerandomizationDifference, TLWE.add, TLWE.sub]
  · simp [rerandomizationDifference, TLWE.add, TLWE.sub]

/-- The rerandomization difference contains no selected upper control row at ciphertext level: it
is exactly the compiled square row plus the lower-block external product. -/
theorem rerandomizationDifference_eq_square_add_lowerExternalProduct
    {q degree : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (targetLevel : Fin params.levels)
    {Index : Type} [Fintype Index]
    (weight : Index → RLWE.Rq q (degree + 1))
    (sourceRows : Index → TLWE.Ciphertext (RLWE.Rq q (degree + 1)) 1)
    (targetRow : TLWE.Ciphertext (RLWE.Rq q (degree + 1)) 1)
    (control : TGSW.Ciphertext
      (RLWE.Rq q (degree + 1)) 1 params.levels) :
    rerandomizationDifference params targetLevel weight sourceRows targetRow control =
      TLWE.add (squareFromPreimage weight sourceRows targetRow)
        (lowerExternalProduct params (preimageCombination weight sourceRows) control) := by
  unfold rerandomizationDifference cancelResidualAtTargetLevel cancelResidual
  rw [externalProduct_targetLevelDigits_eq_upper_add_lower]
  rw [TLWE.Ciphertext.mk.injEq]
  constructor
  · funext coordinate
    simp [TLWE.add, TLWE.sub]
    ring
  · simp [TLWE.add, TLWE.sub]
    ring

/-! ## Checked native narrow-noise budget -/

/-- With executable base digits, the replacement residual remains in the conventional linear
external-product noise regime.  For rank one it costs two gadget blocks, rather than a product
with the selector-weighted source-error magnitude. -/
theorem cInfNorm_target_add_externalProductError_ringDigits_le
    {q degree : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (secret : Fin 1 → RLWE.Rq q (degree + 1))
    (targetError : RLWE.Rq q (degree + 1))
    (weightedSourceRow : TLWE.Ciphertext (RLWE.Rq q (degree + 1)) 1)
    (control : TGSW.Ciphertext
      (RLWE.Rq q (degree + 1)) 1 params.levels)
    (targetErrorBound controlRowErrorBound : ℕ)
    (hTarget : LatticeCrypto.cInfNorm targetError ≤ targetErrorBound)
    (hControl : ∀ index,
      LatticeCrypto.cInfNorm
        (TGSW.rowError (R := RLWE.Rq q (degree + 1)) secret
          (Gadget.Base.ringGadget params) (-secret 0) control index) ≤
        controlRowErrorBound) :
    LatticeCrypto.cInfNorm
        (targetError +
          TGSW.externalProductError (R := RLWE.Rq q (degree + 1)) secret
            (Gadget.Base.ringGadget params) (-secret 0)
            (Gadget.Base.ringExtendedDigits params weightedSourceRow) control) ≤
      targetErrorBound +
        ((1 + 1) * params.levels) *
          ((degree + 1) * ((params.base - 1) * controlRowErrorBound)) := by
  apply (NoiseBounds.cInfNorm_add_le _ _).trans
  exact Nat.add_le_add hTarget
    (SharpRotationNoise.cInfNorm_externalProductError_ringDigits_le_linear
      params secret (-secret 0) weightedSourceRow control controlRowErrorBound
        hControl)

end ExternalProductCancellation

end FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler
