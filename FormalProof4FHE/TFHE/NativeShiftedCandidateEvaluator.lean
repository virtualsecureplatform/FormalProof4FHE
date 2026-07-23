/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.GadgetDecomposition
import FormalProof4FHE.TFHE.InternalProduct
import FormalProof4FHE.TFHE.ScalarSecretRandomization
import FormalProof4FHE.Probability.FiniteProduct

/-!
# Native Shifted-Candidate Evaluation for TFHE

This file defines the construction-specific algebraic core of a scalar-coordinate candidate
evaluator.  Given a bootstrapping-key entry encrypting the hidden bit `s_i`, a public candidate
bit toggles that TGSW control to encrypt `s_i XOR candidate`.  The toggled entry then controls a
native TGSW CMux between a caller-supplied true branch and the original false branch.

The executable coefficientwise base decomposition is exact.  Every output row has an exact phase
normal form: the correct candidate selects the false branch, while the complementary candidate
selects the true branch.  All evaluation noise is exposed by `rowResidual`; the separate exact
decomposition theorem shows that its computed decomposition component carries no mathematical
decomposition loss.  An arbitrary public BRK is also decomposed canonically into its declared
binary gadget message plus a homogeneous remainder, yielding a correct-branch phase theorem for
the actual public ciphertext rather than only a syntactically generated one.  Explicit coherence
lemmas connect the executable and proof-facing `Rq` operation dictionaries, allowing the generic
complete-ciphertext CMux endpoints to lift to the actual digitizer, whole BRK, and named
homogeneous internal-product perturbation.

These algebraic identities deliberately do not assert fresh output masks.  The adaptive wrapper
uses the concrete computed residual and complete-ciphertext perturbation form; output-mask/error-
law freshness, perturbation smudging, and the wrong-branch distance are the remaining
distributional steps.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator

open FormalProof4FHE.TFHE

variable {q degree ringRank : ℕ}

/-- Addition from the coherent proof-facing `CommRing` dictionary for executable `Rq`. -/
noncomputable def proofAdd (left right : RLWE.Rq q degree) : RLWE.Rq q degree :=
  @HAdd.hAdd (RLWE.Rq q degree) (RLWE.Rq q degree) (RLWE.Rq q degree)
    (@instHAdd (RLWE.Rq q degree)
      (LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree).toAdd)
    left right

/-- Negation from the same coherent proof-facing `CommRing` dictionary. -/
noncomputable def proofNeg (value : RLWE.Rq q degree) : RLWE.Rq q degree :=
  @Neg.neg (RLWE.Rq q degree)
    (LatticeCrypto.vectorNegacyclicRing_instCommRing
      (ZMod q) degree).toAddCommGroup.toNeg value

/-- Zero from the semiring projection used inside the proof-facing native CMux. -/
noncomputable def proofZero : RLWE.Rq q degree :=
  @OfNat.ofNat (RLWE.Rq q degree) 0
    (@Zero.toOfNat0 (RLWE.Rq q degree)
      (@MulZeroClass.toZero (RLWE.Rq q degree)
        (@instMulZeroClassOfSemiring (RLWE.Rq q degree)
          (LatticeCrypto.vectorNegacyclicRing_instCommRing
            (ZMod q) degree).toSemiring)))

/-- One from the proof-facing `CommRing` dictionary used inside the native CMux. -/
noncomputable def proofOne : RLWE.Rq q degree :=
  @OfNat.ofNat (RLWE.Rq q degree) 1
    (@One.toOfNat1 (RLWE.Rq q degree)
      (LatticeCrypto.vectorNegacyclicRing_instCommRing
        (ZMod q) degree).toAddGroupWithOne.toOne)

/-- The proof-facing and executable zero polynomials are extensionally equal. -/
theorem proofZero_eq_zero : proofZero (q := q) (degree := degree) = 0 := by
  cases degree with
  | zero =>
      apply LatticeCrypto.NegacyclicRing.poly_ext
      intro index
      exact index.elim0
  | succ degree => rfl

/-- The proof-facing and executable one polynomials are extensionally equal. -/
theorem proofOne_eq_one : proofOne (q := q) (degree := degree) = 1 := by
  cases degree with
  | zero =>
    apply LatticeCrypto.NegacyclicRing.poly_ext
    intro index
    exact index.elim0
  | succ degree => rfl

/-- Proof-facing and executable coefficientwise negation agree on `Rq`. -/
theorem proofNeg_eq_neg (value : RLWE.Rq q degree) :
    proofNeg value = -value := by
  cases degree with
  | zero =>
      apply LatticeCrypto.NegacyclicRing.poly_ext
      intro index
      exact index.elim0
  | succ degree => rfl

/-- Proof-facing addition and executable coefficientwise addition agree on `Rq`. -/
theorem proofAdd_eq_add (left right : RLWE.Rq q degree) :
    proofAdd left right = left + right := by
  cases degree with
  | zero =>
      apply LatticeCrypto.NegacyclicRing.poly_ext
      intro index
      exact index.elim0
  | succ degree => rfl

/-- Proof-facing subtraction and executable coefficientwise subtraction agree on `Rq`. -/
theorem proofSub_eq_sub (left right : RLWE.Rq q degree) :
    @Sub.sub (RLWE.Rq q degree)
        (LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree).toSub
        left right =
      left - right := by
  cases degree with
  | zero =>
      apply LatticeCrypto.NegacyclicRing.poly_ext
      intro index
      exact index.elim0
  | succ degree => rfl

/-- Addition through the proof-facing ring dictionary is commutative, including for the
degree-zero executable carrier where the available operation dictionaries are only
extensionally equal. -/
theorem proofAdd_comm (left right : RLWE.Rq q degree) :
    proofAdd left right = proofAdd right left := by
  cases degree with
  | zero =>
      apply LatticeCrypto.NegacyclicRing.poly_ext
      intro index
      exact index.elim0
  | succ degree => exact add_comm _ _

/-- Proof-facing addition followed by executable subtraction cancels on the right. -/
theorem proofAdd_sub_cancel_right (left right : RLWE.Rq q degree) :
    proofAdd left right - right = left := by
  cases degree with
  | zero =>
      apply LatticeCrypto.NegacyclicRing.poly_ext
      intro index
      exact index.elim0
  | succ degree => exact add_sub_cancel_right _ _

/-- Executable subtraction followed by proof-facing addition cancels on the right. -/
theorem proofSub_add_cancel (left right : RLWE.Rq q degree) :
    proofAdd (left - right) right = left := by
  cases degree with
  | zero =>
      apply LatticeCrypto.NegacyclicRing.poly_ext
      intro index
      exact index.elim0
  | succ degree => exact sub_add_cancel _ _

/-- TGSW subtraction through the coherent proof-facing `CommRing` dictionary. -/
noncomputable def proofTGSWSub {levels : ℕ}
    (left right : RingGSWCiphertext q degree ringRank levels) :
    RingGSWCiphertext q degree ringRank levels :=
  @TGSW.sub (RLWE.Rq q degree)
    (LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree).toSub
    ringRank levels left right

/-- Proof-facing and executable TGSW subtraction are equal as complete ciphertexts. -/
theorem proofTGSWSub_eq_sub {levels : ℕ}
    (left right : RingGSWCiphertext q degree ringRank levels) :
    proofTGSWSub left right = TGSW.sub left right := by
  apply Prod.ext
  · funext coordinate row
    exact proofSub_eq_sub (left.1 coordinate row) (right.1 coordinate row)
  · funext row
    exact proofSub_eq_sub (left.2 row) (right.2 row)

/-- Adding a gadget message after removing the same message is the identity, over any
commutative ring. -/
theorem addGadget_neg_cancel {R : Type} [CommRing R]
    {dimension levels : ℕ} (gadget : Fin levels → R) (message : R)
    (ciphertext : TGSW.Ciphertext R dimension levels) :
    TGSW.addGadget gadget message
        (TGSW.addGadget gadget (-message) ciphertext) = ciphertext := by
  apply Prod.ext
  · funext component row
    simp only [TGSW.addGadget, TGSW.gadgetMaskShift, Matrix.add_apply]
    split_ifs <;> ring
  · funext row
    simp only [TGSW.addGadget, TGSW.gadgetBodyShift, Pi.add_apply]
    split_ifs <;> ring

/-- Exact gadget digits for every row of `ifTrue - ifFalse`. -/
def differenceDigits (params : Gadget.Base.Parameters q)
    (ifTrue ifFalse : RingGSWCiphertext q degree ringRank params.levels)
    (row : Fin (TGSW.rowCount ringRank params.levels)) :
    Fin (ringRank + 1) → Fin params.levels → RLWE.Rq q degree :=
  Gadget.Base.ringExtendedDigits params
    (TLWE.entry (TGSW.sub ifTrue ifFalse) row)

/-- The concrete row digitizer exactly decomposes every row difference. -/
theorem differenceDigits_decomposes [NeZero q] (params : Gadget.Base.Parameters q)
    (ifTrue ifFalse : RingGSWCiphertext q degree ringRank params.levels)
    (row : Fin (TGSW.rowCount ringRank params.levels)) :
    Gadget.Decomposes (Gadget.Base.ringGadget params)
      (TLWE.entry (TGSW.sub ifTrue ifFalse) row)
      (differenceDigits params ifTrue ifFalse row) := by
  exact Gadget.Base.ringExtendedDigits_decomposes params
    (TLWE.entry (TGSW.sub ifTrue ifFalse) row)

/-- Toggle a candidate control using the same native gadget as the CMux. -/
noncomputable def candidateControl (params : Gadget.Base.Parameters q) (candidate : Bool)
    (control : RingGSWCiphertext q degree ringRank params.levels) :
    RingGSWCiphertext q degree ringRank params.levels :=
  ScalarSecretRandomization.toggleTGSW
    (Gadget.Base.ringGadget params) candidate control

/-- A false candidate leaves the selected native control unchanged. -/
@[simp]
theorem candidateControl_false (params : Gadget.Base.Parameters q)
    (control : RingGSWCiphertext q degree ringRank params.levels) :
    candidateControl params false control = control := by
  simp [candidateControl, ScalarSecretRandomization.toggleTGSW]

/-- Execute the candidate-dependent native TGSW CMux. -/
noncomputable def select (params : Gadget.Base.Parameters q) (candidate : Bool)
    (control ifTrue ifFalse : RingGSWCiphertext q degree ringRank params.levels) :
    RingGSWCiphertext q degree ringRank params.levels :=
  TGSW.cmuxWithDigits (differenceDigits params ifTrue ifFalse)
    (candidateControl params candidate control) ifTrue ifFalse

/-- The single-row map induced by the native shifted CMux after the control and false row are
fixed.  This is the smallest explicit finite map whose bijectivity is needed by the exact
wrong-branch argument. -/
noncomputable def rowBranchTransform
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (control : RingGSWCiphertext q degree ringRank params.levels)
    (ifFalse : TLWE.Ciphertext (RLWE.Rq q degree) ringRank) :
    TLWE.Ciphertext (RLWE.Rq q degree) ringRank →
      TLWE.Ciphertext (RLWE.Rq q degree) ringRank :=
  fun ifTrue =>
    @TLWE.add (RLWE.Rq q degree)
      (LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree).toAdd
      ringRank ifFalse
      (@TGSW.externalProduct (RLWE.Rq q degree)
        (LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree).toSemiring
        ringRank params.levels
        (Gadget.Base.ringExtendedDigits params (TLWE.sub ifTrue ifFalse))
        (candidateControl params candidate control))

/-- The normalized row map seen after translating the true row by the false row.  It depends
only on the selected control and candidate; in particular it is shared by every output row of
the shifted evaluator. -/
noncomputable def controlBranchTransform
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (control : RingGSWCiphertext q degree ringRank params.levels) :
    TLWE.Ciphertext (RLWE.Rq q degree) ringRank →
      TLWE.Ciphertext (RLWE.Rq q degree) ringRank :=
  fun difference =>
    @TGSW.externalProduct (RLWE.Rq q degree)
      (LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree).toSemiring
      ringRank params.levels
      (Gadget.Base.ringExtendedDigits params difference)
      (candidateControl params candidate control)

/-- Once a candidate has been absorbed into the control, the normalized row map can be viewed
as the false-candidate map of that already-toggled control. -/
theorem controlBranchTransform_false_candidateControl
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (control : RingGSWCiphertext q degree ringRank params.levels) :
    controlBranchTransform params false (candidateControl params candidate control) =
      controlBranchTransform params candidate control := by
  funext difference
  simp [controlBranchTransform]

/-- Translation between a true row and its difference from one fixed false row.  The explicit
equivalence also records the coherence between the proof-facing addition and executable
subtraction dictionaries at degree zero. -/
noncomputable def rowTranslationEquiv
    (source : TLWE.Ciphertext (RLWE.Rq q degree) ringRank) :
    TLWE.Ciphertext (RLWE.Rq q degree) ringRank ≃
      TLWE.Ciphertext (RLWE.Rq q degree) ringRank where
  toFun := fun difference =>
    @TLWE.add (RLWE.Rq q degree)
      (LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree).toAdd
      ringRank difference source
  invFun := fun output => TLWE.sub output source
  left_inv := by
    intro difference
    rw [TLWE.Ciphertext.mk.injEq]
    constructor
    · funext coordinate
      exact proofAdd_sub_cancel_right
        (difference.mask coordinate) (source.mask coordinate)
    · exact proofAdd_sub_cancel_right difference.body source.body
  right_inv := by
    intro output
    rw [TLWE.Ciphertext.mk.injEq]
    constructor
    · funext coordinate
      exact proofSub_add_cancel
        (output.mask coordinate) (source.mask coordinate)
    · exact proofSub_add_cancel output.body source.body

/-- Every concrete row map is conjugate by translation to the same control-only normalized map.
Consequently, changing the false row cannot change its rank or bijectivity. -/
theorem rowBranchTransform_eq_conjugate
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (control : RingGSWCiphertext q degree ringRank params.levels)
    (ifFalse : TLWE.Ciphertext (RLWE.Rq q degree) ringRank) :
    rowBranchTransform params candidate control ifFalse =
      rowTranslationEquiv ifFalse ∘
        controlBranchTransform params candidate control ∘
          (rowTranslationEquiv ifFalse).symm := by
  funext ifTrue
  rw [TLWE.Ciphertext.mk.injEq]
  constructor
  · funext component
    exact proofAdd_comm _ _
  · exact proofAdd_comm _ _

/-- Control-level rank/freshness predicate shared by all data rows using the same shifted
candidate control. -/
def ControlBranchFresh
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (control : RingGSWCiphertext q degree ringRank params.levels) : Prop :=
  Function.Bijective (controlBranchTransform params candidate control)

/-- The corresponding map on one complete TGSW entry. -/
noncomputable def entryBranchTransform
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (control ifFalse : RingGSWCiphertext q degree ringRank params.levels) :
    RingGSWCiphertext q degree ringRank params.levels →
      RingGSWCiphertext q degree ringRank params.levels :=
  fun ifTrue => select params candidate control ifTrue ifFalse

/-- The complete TGSW entry map is rowwise, with no coupling between distinct data rows. -/
@[simp]
theorem entry_entryBranchTransform
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (control ifFalse ifTrue : RingGSWCiphertext q degree ringRank params.levels)
    (row : Fin (TGSW.rowCount ringRank params.levels)) :
    TLWE.entry (entryBranchTransform params candidate control ifFalse ifTrue) row =
      rowBranchTransform params candidate control (TLWE.entry ifFalse row)
        (TLWE.entry ifTrue row) := by
  simp only [entryBranchTransform, select, TGSW.cmuxWithDigits, TGSW.entry_add,
    TGSW.entry_internalProductWithDigits, differenceDigits, TGSW.entry_sub,
    rowBranchTransform]

/-- Equality of all represented TLWE rows determines a native TGSW ciphertext. -/
theorem tgsw_eq_of_entry_eq
    {levels : ℕ}
    {left right : RingGSWCiphertext q degree ringRank levels}
    (hentry : ∀ row, TLWE.entry left row = TLWE.entry right row) : left = right := by
  apply Prod.ext
  · funext coordinate row
    exact congrArg (fun ciphertext => ciphertext.mask coordinate) (hentry row)
  · funext row
    exact congrArg TLWE.Ciphertext.body (hentry row)

/-- Native TLWE rows are represented equivalently by their public mask and body. -/
def tlweCiphertextEquiv (R : Type) (dimension : ℕ) :
    ((Fin dimension → R) × R) ≃ TLWE.Ciphertext R dimension where
  toFun value := ⟨value.1, value.2⟩
  invFun ciphertext := (ciphertext.mask, ciphertext.body)
  left_inv value := by cases value; rfl
  right_inv ciphertext := by cases ciphertext; rfl

/-- Assembling the represented TLWE rows is a bijection onto native TGSW ciphertexts. -/
theorem tgswBatchOfRows_bijective
    (levels : ℕ) :
    Function.Bijective
      (@TLWE.batchOfRows (RLWE.Rq q degree) ringRank
        (TGSW.rowCount ringRank levels)) := by
  constructor
  · intro left right heq
    funext row
    simpa only [TLWE.entry_batchOfRows] using
      congrArg (fun ciphertext => TLWE.entry ciphertext row) heq
  · intro output
    refine ⟨fun row => TLWE.entry output row, ?_⟩
    apply tgsw_eq_of_entry_eq
    intro row
    rfl

/-- Applying the one-entry branch transform after row assembly is exactly rowwise assembly of the
single-row transforms. -/
theorem entryBranchTransform_batchOfRows
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (control ifFalse : RingGSWCiphertext q degree ringRank params.levels)
    (rows : Fin (TGSW.rowCount ringRank params.levels) →
      TLWE.Ciphertext (RLWE.Rq q degree) ringRank) :
    entryBranchTransform params candidate control ifFalse (TLWE.batchOfRows rows) =
      TLWE.batchOfRows fun row =>
        rowBranchTransform params candidate control (TLWE.entry ifFalse row) (rows row) := by
  apply tgsw_eq_of_entry_eq
  intro row
  simp only [entry_entryBranchTransform, TLWE.entry_batchOfRows]

/-- Exact row-level freshness condition for the shifted CMux. -/
def RowBranchFresh
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (control : RingGSWCiphertext q degree ringRank params.levels)
    (ifFalse : TLWE.Ciphertext (RLWE.Rq q degree) ringRank) : Prop :=
  Function.Bijective (rowBranchTransform params candidate control ifFalse)

/-- Row freshness is exactly the control-only freshness condition: the false row contributes
only an invertible translation on the input and output. -/
theorem rowBranchFresh_iff_controlBranchFresh
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (control : RingGSWCiphertext q degree ringRank params.levels)
    (ifFalse : TLWE.Ciphertext (RLWE.Rq q degree) ringRank) :
    RowBranchFresh params candidate control ifFalse ↔
      ControlBranchFresh params candidate control := by
  let translation := rowTranslationEquiv ifFalse
  constructor
  · intro hBranch
    have hConjugate : Function.Bijective
        (translation.symm ∘ rowBranchTransform params candidate control ifFalse ∘
          translation) :=
      translation.symm.bijective.comp (hBranch.comp translation.bijective)
    have heq :
        (translation.symm ∘ rowBranchTransform params candidate control ifFalse ∘
          translation) = controlBranchTransform params candidate control := by
      funext input
      rw [rowBranchTransform_eq_conjugate]
      simp only [Function.comp_apply, Equiv.symm_apply_apply, translation]
    rw [heq] at hConjugate
    exact hConjugate
  · intro hControl
    unfold RowBranchFresh
    rw [rowBranchTransform_eq_conjugate]
    exact (rowTranslationEquiv ifFalse).bijective.comp
      (hControl.comp (rowTranslationEquiv ifFalse).symm.bijective)

/-- Exact one-entry freshness condition for the shifted CMux. -/
def EntryBranchFresh
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (control ifFalse : RingGSWCiphertext q degree ringRank params.levels) : Prop :=
  Function.Bijective (entryBranchTransform params candidate control ifFalse)

/-- Bijectivity of every independent TLWE row map lifts to bijectivity of one complete TGSW
entry. -/
theorem entryBranchFresh_of_rowBranchFresh
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (control ifFalse : RingGSWCiphertext q degree ringRank params.levels)
    (hFresh : ∀ row, RowBranchFresh params candidate control (TLWE.entry ifFalse row)) :
    EntryBranchFresh params candidate control ifFalse := by
  classical
  constructor
  · intro left right heq
    apply tgsw_eq_of_entry_eq
    intro row
    apply (hFresh row).1
    simpa only [entry_entryBranchTransform] using
      congrArg (fun ciphertext => TLWE.entry ciphertext row) heq
  · intro output
    choose inputRow hinputRow using fun row =>
      (hFresh row).2 (TLWE.entry output row)
    refine ⟨TLWE.batchOfRows inputRow, ?_⟩
    apply tgsw_eq_of_entry_eq
    intro row
    simpa using hinputRow row

/-- Attach a gadget message through the same proof-facing semiring dictionary used by `select`.
This explicit wrapper prevents an accidental mix with the executable carrier's extensionally
equal but definitionally distinct operation dictionary. -/
noncomputable def proofAddGadget
    (params : Gadget.Base.Parameters q)
    (message : RLWE.Rq q degree)
    (homogeneous : RingGSWCiphertext q degree ringRank params.levels) :
    RingGSWCiphertext q degree ringRank params.levels :=
  @TGSW.addGadget (RLWE.Rq q degree)
    (LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree).toSemiring
    ringRank params.levels (Gadget.Base.ringGadget params) message homogeneous

/-- Add a homogeneous-control internal product to a chosen branch through the coherent
proof-facing operation dictionary.  This is the complete-ciphertext perturbation form used by
the native endpoint theorems below. -/
noncomputable def addInternalProduct
    (params : Gadget.Base.Parameters q)
    (base : RingGSWCiphertext q degree ringRank params.levels)
    (digits : Fin (TGSW.rowCount ringRank params.levels) →
      Fin (ringRank + 1) → Fin params.levels → RLWE.Rq q degree)
    (homogeneous : RingGSWCiphertext q degree ringRank params.levels) :
    RingGSWCiphertext q degree ringRank params.levels :=
  @TGSW.add (RLWE.Rq q degree)
    (LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree).toAdd
    ringRank params.levels base
    (@TGSW.internalProductWithDigits (RLWE.Rq q degree)
      (LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree).toSemiring
      ringRank params.levels digits homogeneous)

/-- Canonical homogeneous remainder of the actual candidate control relative to a declared
message.  Reattaching that message reconstructs the complete public control exactly. -/
noncomputable def candidateHomogeneousPart
    (params : Gadget.Base.Parameters q)
    (message : RLWE.Rq q degree) (candidate : Bool)
    (control : RingGSWCiphertext q degree ringRank params.levels) :
    RingGSWCiphertext q degree ringRank params.levels :=
  proofAddGadget params (proofNeg message) (candidateControl params candidate control)

/-- Reattaching a declared message to the candidate control's canonical homogeneous remainder
recovers the actual candidate control as a complete ciphertext. -/
theorem proofAddGadget_candidateHomogeneousPart
    (params : Gadget.Base.Parameters q)
    (message : RLWE.Rq q degree) (candidate : Bool)
    (control : RingGSWCiphertext q degree ringRank params.levels) :
    proofAddGadget params message
        (candidateHomogeneousPart params message candidate control) =
      candidateControl params candidate control := by
  simpa only [proofAddGadget, candidateHomogeneousPart, proofNeg] using
    (@addGadget_neg_cancel (RLWE.Rq q degree)
      (LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree)
      ringRank params.levels (Gadget.Base.ringGadget params) message
      (candidateControl params candidate control))

/-- Identity plus the digit-weighted homogeneous-control perturbation.  This is the fully
normalized nonlinear map whose bijectivity is the native complementary-branch rank event. -/
noncomputable def oneMessageRowTransform
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (control : RingGSWCiphertext q degree ringRank params.levels) :
    TLWE.Ciphertext (RLWE.Rq q degree) ringRank →
      TLWE.Ciphertext (RLWE.Rq q degree) ringRank :=
  fun input =>
    @TLWE.add (RLWE.Rq q degree)
      (LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree).toAdd
      ringRank input
      (@TGSW.externalProduct (RLWE.Rq q degree)
        (LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree).toSemiring
        ringRank params.levels
        (Gadget.Base.ringExtendedDigits params input)
        (candidateHomogeneousPart params proofOne candidate control))

/-- The control-only normalized map is exactly identity plus its canonical message-one
homogeneous perturbation.  Exact gadget recomposition supplies the identity term. -/
theorem controlBranchTransform_eq_oneMessageRowTransform [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (control : RingGSWCiphertext q degree ringRank params.levels) :
    controlBranchTransform params candidate control =
      oneMessageRowTransform params candidate control := by
  funext input
  unfold controlBranchTransform oneMessageRowTransform
  rw [← proofAddGadget_candidateHomogeneousPart params proofOne candidate control]
  simpa only [proofAddGadget, proofOne] using
    (@TGSW.externalProduct_addGadget_one (RLWE.Rq q degree)
      (LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree)
      ringRank params.levels (Gadget.Base.ringGadget params) input
      (Gadget.Base.ringExtendedDigits params input)
      (candidateHomogeneousPart params proofOne candidate control)
      (Gadget.Base.ringExtendedDigits_decomposes params input))

/-- Equivalent identity-plus-perturbation formulation of the control freshness event. -/
theorem controlBranchFresh_iff_oneMessageRowTransform_bijective [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (control : RingGSWCiphertext q degree ringRank params.levels) :
    ControlBranchFresh params candidate control ↔
      Function.Bijective (oneMessageRowTransform params candidate control) := by
  unfold ControlBranchFresh
  rw [controlBranchTransform_eq_oneMessageRowTransform]

/-- **Complete-ciphertext zero endpoint.**  Declaring the candidate control's message to be zero
identifies the native CMux output with the false branch plus one explicit homogeneous internal
product. -/
theorem select_zeroMessage_eq_addInternalProduct
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (control ifTrue ifFalse :
      RingGSWCiphertext q degree ringRank params.levels) :
    select params candidate control ifTrue ifFalse =
      addInternalProduct params ifFalse (differenceDigits params ifTrue ifFalse)
        (candidateHomogeneousPart params proofZero candidate control) := by
  unfold select
  rw [← proofAddGadget_candidateHomogeneousPart params proofZero candidate control]
  simpa only [proofAddGadget, addInternalProduct, proofZero] using
    (@TGSW.cmuxWithDigits_addGadget_zero (RLWE.Rq q degree)
      (LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree)
      ringRank params.levels (Gadget.Base.ringGadget params)
      (candidateHomogeneousPart params proofZero candidate control) ifTrue ifFalse
      (differenceDigits params ifTrue ifFalse))

/-- **Complete-ciphertext one endpoint.**  Exact executable gadget decomposition identifies the
native CMux output with the true branch plus one explicit homogeneous internal product. -/
theorem select_oneMessage_eq_addInternalProduct [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (control ifTrue ifFalse :
      RingGSWCiphertext q degree ringRank params.levels) :
    select params candidate control ifTrue ifFalse =
      addInternalProduct params ifTrue (differenceDigits params ifTrue ifFalse)
        (candidateHomogeneousPart params proofOne candidate control) := by
  unfold select
  rw [← proofAddGadget_candidateHomogeneousPart params proofOne candidate control]
  have hDecomposes : ∀ row,
      Gadget.Decomposes (Gadget.Base.ringGadget params)
        (TLWE.entry (proofTGSWSub ifTrue ifFalse) row)
        (differenceDigits params ifTrue ifFalse row) := by
    intro row
    rw [proofTGSWSub_eq_sub]
    exact differenceDigits_decomposes params ifTrue ifFalse row
  simpa only [proofAddGadget, addInternalProduct, proofOne] using
    (@TGSW.cmuxWithDigits_addGadget_one (RLWE.Rq q degree)
      (LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree)
      ringRank params.levels (Gadget.Base.ringGadget params)
      (candidateHomogeneousPart params proofOne candidate control) ifTrue ifFalse
      (differenceDigits params ifTrue ifFalse)
      (by simpa only [proofTGSWSub] using hDecomposes))

/-- Complete computed row residual of the executable shifted CMux. -/
noncomputable def rowResidual (params : Gadget.Base.Parameters q)
    (secret : Fin ringRank → RLWE.Rq q degree)
    (controlMessage trueMessage falseMessage : RLWE.Rq q degree)
    (candidate : Bool)
    (control ifTrue ifFalse : RingGSWCiphertext q degree ringRank params.levels)
    (index : Fin (ringRank + 1) × Fin params.levels) : RLWE.Rq q degree :=
  TGSW.computedCmuxRowResidual secret (Gadget.Base.ringGadget params)
    controlMessage trueMessage falseMessage
    (candidateControl params candidate control) ifTrue ifFalse
    (differenceDigits params ifTrue ifFalse) index

/-- Exact phase normal form for the executable candidate-dependent CMux. -/
theorem phase_entry_select_eq_gadgetPhase_add_rowResidual
    (params : Gadget.Base.Parameters q)
    (secret : Fin ringRank → RLWE.Rq q degree)
    (controlMessage trueMessage falseMessage : RLWE.Rq q degree)
    (candidate : Bool)
    (control ifTrue ifFalse : RingGSWCiphertext q degree ringRank params.levels)
    (index : Fin (ringRank + 1) × Fin params.levels) :
    TLWE.phase secret
        (TLWE.entry (select params candidate control ifTrue ifFalse)
          (finProdFinEquiv index)) =
      proofAdd
        (TGSW.gadgetPhase secret (Gadget.Base.ringGadget params)
          (TGSW.cmuxMessage controlMessage trueMessage falseMessage)
          (finProdFinEquiv index))
        (rowResidual params secret controlMessage trueMessage falseMessage
          candidate control ifTrue ifFalse index) := by
  simpa only [select, rowResidual, proofAdd] using
    TGSW.phase_entry_cmuxWithDigits_eq_gadgetPhase_add_computedResidual
      secret (Gadget.Base.ringGadget params)
      controlMessage trueMessage falseMessage
      (candidateControl params candidate control) ifTrue ifFalse
      (differenceDigits params ifTrue ifFalse)
      index

@[simp]
theorem maskedBit_self (bit : Bool) :
    LWE.MultiKeyAffine.maskedBit bit bit = false := by
  cases bit <;> rfl

@[simp]
theorem maskedBit_not_self (bit : Bool) :
    LWE.MultiKeyAffine.maskedBit bit (!bit) = true := by
  cases bit <;> rfl

/-! ## Abstract control-message endpoints -/

/-- Toggling a structured control by the hidden bit itself produces a zero-message control. -/
theorem toggleTGSW_correct {R : Type} [CommRing R] {dimension levels : ℕ}
    (gadget : Fin levels → R) (hidden : Bool)
    (homogeneous : TGSW.Ciphertext R dimension levels) :
    ScalarSecretRandomization.toggleTGSW gadget hidden
        (TGSW.addGadget gadget (embedBit hidden) homogeneous) =
      TGSW.addGadget gadget 0
        (if hidden then ScalarSecretRandomization.negateCiphertext homogeneous
        else homogeneous) := by
  simpa [maskedBit_self, embedBit] using
    ScalarSecretRandomization.toggleTGSW_addGadget
      gadget hidden hidden homogeneous

/-- Toggling a structured control by the complementary candidate produces a one-message
control. -/
theorem toggleTGSW_wrong {R : Type} [CommRing R] {dimension levels : ℕ}
    (gadget : Fin levels → R) (hidden : Bool)
    (homogeneous : TGSW.Ciphertext R dimension levels) :
    ScalarSecretRandomization.toggleTGSW gadget (!hidden)
        (TGSW.addGadget gadget (embedBit hidden) homogeneous) =
      TGSW.addGadget gadget 1
        (if !hidden then ScalarSecretRandomization.negateCiphertext homogeneous
        else homogeneous) := by
  simpa [maskedBit_not_self, embedBit] using
    ScalarSecretRandomization.toggleTGSW_addGadget
      gadget hidden (!hidden) homogeneous

/-- A correct candidate is evaluated with the zero CMux message.  The generic theorem
`TGSW.cmuxMessage_zero` identifies this message with `falseMessage`. -/
theorem phase_entry_select_correct
    (params : Gadget.Base.Parameters q)
    (secret : Fin ringRank → RLWE.Rq q degree)
    (hidden : Bool) (trueMessage falseMessage : RLWE.Rq q degree)
    (homogeneous ifTrue ifFalse :
      RingGSWCiphertext q degree ringRank params.levels)
    (index : Fin (ringRank + 1) × Fin params.levels) :
    TLWE.phase secret
        (TLWE.entry
          (select params hidden
            (TGSW.addGadget (Gadget.Base.ringGadget params)
              (embedBit hidden) homogeneous)
            ifTrue ifFalse)
          (finProdFinEquiv index)) =
      proofAdd
        (TGSW.gadgetPhase secret (Gadget.Base.ringGadget params)
          (TGSW.cmuxMessage 0 trueMessage falseMessage) (finProdFinEquiv index))
        (rowResidual params secret 0 trueMessage falseMessage hidden
          (TGSW.addGadget (Gadget.Base.ringGadget params)
            (embedBit hidden) homogeneous)
          ifTrue ifFalse index) := by
  exact phase_entry_select_eq_gadgetPhase_add_rowResidual params secret
    0 trueMessage falseMessage hidden
    (TGSW.addGadget (Gadget.Base.ringGadget params)
      (embedBit hidden) homogeneous)
    ifTrue ifFalse index

/-- The complementary candidate is evaluated with the one CMux message.  The generic theorem
`TGSW.cmuxMessage_one` identifies this message with `trueMessage`. -/
theorem phase_entry_select_wrong
    (params : Gadget.Base.Parameters q)
    (secret : Fin ringRank → RLWE.Rq q degree)
    (hidden : Bool) (trueMessage falseMessage : RLWE.Rq q degree)
    (homogeneous ifTrue ifFalse :
      RingGSWCiphertext q degree ringRank params.levels)
    (index : Fin (ringRank + 1) × Fin params.levels) :
    TLWE.phase secret
        (TLWE.entry
          (select params (!hidden)
            (TGSW.addGadget (Gadget.Base.ringGadget params)
              (embedBit hidden) homogeneous)
            ifTrue ifFalse)
          (finProdFinEquiv index)) =
      proofAdd
        (TGSW.gadgetPhase secret (Gadget.Base.ringGadget params)
          (TGSW.cmuxMessage 1 trueMessage falseMessage) (finProdFinEquiv index))
        (rowResidual params secret 1 trueMessage falseMessage (!hidden)
          (TGSW.addGadget (Gadget.Base.ringGadget params)
            (embedBit hidden) homogeneous)
          ifTrue ifFalse index) := by
  exact phase_entry_select_eq_gadgetPhase_add_rowResidual params secret
    1 trueMessage falseMessage (!hidden)
    (TGSW.addGadget (Gadget.Base.ringGadget params)
      (embedBit hidden) homogeneous)
    ifTrue ifFalse index

/-! ## Whole-bootstrapping-key evaluator -/

/-- Assemble a structurally encoded native BRK from its binary messages and homogeneous rows. -/
noncomputable def structuredBootstrappingKey {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q)
    (hidden : BinarySecret lweDimension)
    (homogeneous : BootstrappingKey q degree ringRank params.levels lweDimension) :
    BootstrappingKey q degree ringRank params.levels lweDimension :=
  fun coordinate =>
    TGSW.addGadget (Gadget.Base.ringGadget params)
      (embedBit (hidden coordinate)) (homogeneous coordinate)

/-- Remove the declared binary gadget message from an arbitrary public BRK.  This lets the phase
theorems below apply to the actual transported BRK without requiring a syntactic generation
witness: every ciphertext has a canonical homogeneous remainder relative to any declared binary
message vector. -/
noncomputable def homogeneousPart {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q)
    (hidden : BinarySecret lweDimension)
    (source : BootstrappingKey q degree ringRank params.levels lweDimension) :
    BootstrappingKey q degree ringRank params.levels lweDimension :=
  fun coordinate =>
    TGSW.addGadget (Gadget.Base.ringGadget params)
      (proofNeg (embedBit (hidden coordinate))) (source coordinate)

/-- Reattaching the removed gadget message recovers the original public BRK exactly. -/
@[simp]
theorem structuredBootstrappingKey_homogeneousPart {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q)
    (hidden : BinarySecret lweDimension)
    (source : BootstrappingKey q degree ringRank params.levels lweDimension) :
    structuredBootstrappingKey params hidden
        (homogeneousPart params hidden source) = source := by
  funext coordinate
  simpa only [structuredBootstrappingKey, homogeneousPart, proofNeg] using
    (addGadget_neg_cancel (Gadget.Base.ringGadget params)
      (embedBit (hidden coordinate)) (source coordinate))

/-- Apply one shifted candidate control to every BRK entry.  A supplied true branch can be sampled
uniformly by the outer probabilistic evaluator; the false branch is the original public BRK. -/
noncomputable def selectBootstrappingKey {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q) (coordinate : Fin lweDimension)
    (candidate : Bool)
    (source trueBranch :
      BootstrappingKey q degree ringRank params.levels lweDimension) :
    BootstrappingKey q degree ringRank params.levels lweDimension :=
  fun outputCoordinate =>
    select params candidate (source coordinate)
      (trueBranch outputCoordinate) (source outputCoordinate)

/-- **Whole-BRK complete-ciphertext correct endpoint.**  At every output coordinate, the correct
candidate's result is the original source entry plus the explicitly named homogeneous-control
internal-product perturbation. -/
theorem selectBootstrappingKey_correct_ciphertext {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q)
    (hidden : BinarySecret lweDimension) (coordinate outputCoordinate : Fin lweDimension)
    (source trueBranch :
      BootstrappingKey q degree ringRank params.levels lweDimension) :
    selectBootstrappingKey params coordinate (hidden coordinate)
        source trueBranch outputCoordinate =
      addInternalProduct params (source outputCoordinate)
        (differenceDigits params (trueBranch outputCoordinate) (source outputCoordinate))
        (candidateHomogeneousPart params proofZero
          (hidden coordinate) (source coordinate)) := by
  exact select_zeroMessage_eq_addInternalProduct params (hidden coordinate)
    (source coordinate) (trueBranch outputCoordinate) (source outputCoordinate)

/-- **Whole-BRK complete-ciphertext wrong endpoint.**  At every output coordinate, the
complementary candidate's result is the fresh true-branch entry plus the explicitly named
homogeneous-control internal-product perturbation. -/
theorem selectBootstrappingKey_wrong_ciphertext [NeZero q] {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q)
    (hidden : BinarySecret lweDimension) (coordinate outputCoordinate : Fin lweDimension)
    (source trueBranch :
      BootstrappingKey q degree ringRank params.levels lweDimension) :
    selectBootstrappingKey params coordinate (!hidden coordinate)
        source trueBranch outputCoordinate =
      addInternalProduct params (trueBranch outputCoordinate)
        (differenceDigits params (trueBranch outputCoordinate) (source outputCoordinate))
        (candidateHomogeneousPart params proofOne
          (!hidden coordinate) (source coordinate)) := by
  exact select_oneMessage_eq_addInternalProduct params (!hidden coordinate)
    (source coordinate) (trueBranch outputCoordinate) (source outputCoordinate)

/-- The exact public map from the evaluator's fresh true branch to its output BRK. -/
noncomputable def branchTransform {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q) (coordinate : Fin lweDimension)
    (candidate : Bool)
    (source : BootstrappingKey q degree ringRank params.levels lweDimension) :
    BootstrappingKey q degree ringRank params.levels lweDimension →
      BootstrappingKey q degree ringRank params.levels lweDimension :=
  fun trueBranch =>
    selectBootstrappingKey params coordinate candidate source trueBranch

/-- The whole-BRK branch map acts independently on each output coordinate. -/
@[simp]
theorem branchTransform_apply {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q) (coordinate : Fin lweDimension)
    (candidate : Bool)
    (source trueBranch :
      BootstrappingKey q degree ringRank params.levels lweDimension)
    (outputCoordinate : Fin lweDimension) :
    branchTransform params coordinate candidate source trueBranch outputCoordinate =
      entryBranchTransform params candidate (source coordinate)
        (source outputCoordinate) (trueBranch outputCoordinate) := by
  rfl

/-- Entrywise form of the native branch-freshness obligation. -/
def EntrywiseBranchFresh {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q) (coordinate : Fin lweDimension)
    (candidate : Bool)
    (source : BootstrappingKey q degree ringRank params.levels lweDimension) : Prop :=
  ∀ outputCoordinate,
    EntryBranchFresh params candidate (source coordinate) (source outputCoordinate)

/-- Rowwise form of the native branch-freshness obligation.  Each predicate is bijectivity of an
explicit map on one TLWE row rather than on a complete BRK. -/
def RowwiseBranchFresh {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q) (coordinate : Fin lweDimension)
    (candidate : Bool)
    (source : BootstrappingKey q degree ringRank params.levels lweDimension) : Prop :=
  ∀ outputCoordinate row,
    RowBranchFresh params candidate (source coordinate)
      (TLWE.entry (source outputCoordinate) row)

/-- Concrete rank/freshness predicate for the shifted evaluator.  It states that, after the public
source context and candidate are fixed, varying the fresh true branch permutes the full native BRK
space. -/
def BranchFresh {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q) (coordinate : Fin lweDimension)
    (candidate : Bool)
    (source : BootstrappingKey q degree ringRank params.levels lweDimension) : Prop :=
  Function.Bijective (branchTransform params coordinate candidate source)

/-- Rowwise freshness first lifts independently across the rows of every TGSW entry. -/
theorem entrywiseBranchFresh_of_rowwiseBranchFresh {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q) (coordinate : Fin lweDimension)
    (candidate : Bool)
    (source : BootstrappingKey q degree ringRank params.levels lweDimension)
    (hFresh : RowwiseBranchFresh params coordinate candidate source) :
    EntrywiseBranchFresh params coordinate candidate source := by
  intro outputCoordinate
  exact entryBranchFresh_of_rowBranchFresh params candidate (source coordinate)
    (source outputCoordinate) (hFresh outputCoordinate)

/-- Bijectivity of every independent TGSW-entry map lifts to bijectivity of the complete BRK map. -/
theorem branchFresh_of_entrywiseBranchFresh {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q) (coordinate : Fin lweDimension)
    (candidate : Bool)
    (source : BootstrappingKey q degree ringRank params.levels lweDimension)
    (hFresh : EntrywiseBranchFresh params coordinate candidate source) :
    BranchFresh params coordinate candidate source := by
  classical
  constructor
  · intro left right heq
    funext outputCoordinate
    apply (hFresh outputCoordinate).1
    simpa only [branchTransform_apply] using congrFun heq outputCoordinate
  · intro output
    choose input hinput using fun outputCoordinate =>
      (hFresh outputCoordinate).2 (output outputCoordinate)
    refine ⟨input, ?_⟩
    funext outputCoordinate
    simpa only [branchTransform_apply] using hinput outputCoordinate

/-- The full native branch-freshness premise is therefore discharged by the explicit family of
single-row bijectivity laws. -/
theorem branchFresh_of_rowwiseBranchFresh {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q) (coordinate : Fin lweDimension)
    (candidate : Bool)
    (source : BootstrappingKey q degree ringRank params.levels lweDimension)
    (hFresh : RowwiseBranchFresh params coordinate candidate source) :
    BranchFresh params coordinate candidate source :=
  branchFresh_of_entrywiseBranchFresh params coordinate candidate source
    (entrywiseBranchFresh_of_rowwiseBranchFresh params coordinate candidate source hFresh)

/-- Statistical defect of one explicit shifted-CMux TLWE-row map on a uniform input row. -/
noncomputable def rowBranchDistance [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (control : RingGSWCiphertext q degree ringRank params.levels)
    (ifFalse : TLWE.Ciphertext (RLWE.Rq q degree) ringRank) : ℝ :=
  letI : SampleableType (TLWE.Ciphertext (RLWE.Rq q degree) ringRank) :=
    SampleableType.ofEquiv
      (tlweCiphertextEquiv (RLWE.Rq q degree) ringRank)
  tvDist
    (rowBranchTransform params candidate control ifFalse <$>
      ($ᵗ TLWE.Ciphertext (RLWE.Rq q degree) ringRank))
    ($ᵗ TLWE.Ciphertext (RLWE.Rq q degree) ringRank)

/-- Statistical defect of the normalized control-only row map.  Unlike `rowBranchDistance`, this
quantity contains no false/data row. -/
noncomputable def controlBranchDistance [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (control : RingGSWCiphertext q degree ringRank params.levels) : ℝ :=
  letI : SampleableType (TLWE.Ciphertext (RLWE.Rq q degree) ringRank) :=
    SampleableType.ofEquiv
      (tlweCiphertextEquiv (RLWE.Rq q degree) ringRank)
  tvDist
    (controlBranchTransform params candidate control <$>
      ($ᵗ TLWE.Ciphertext (RLWE.Rq q degree) ringRank))
    ($ᵗ TLWE.Ciphertext (RLWE.Rq q degree) ringRank)

/-- Absorbing the candidate into the control also preserves the normalized one-row statistical
defect exactly. -/
theorem controlBranchDistance_false_candidateControl [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (control : RingGSWCiphertext q degree ringRank params.levels) :
    controlBranchDistance params false (candidateControl params candidate control) =
      controlBranchDistance params candidate control := by
  unfold controlBranchDistance
  rw [controlBranchTransform_false_candidateControl]

/-- Translation conjugacy removes the false row from the exact statistical defect as well as
from bijectivity.  Every data row governed by one control has the same TV distance. -/
theorem rowBranchDistance_eq_controlBranchDistance [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (control : RingGSWCiphertext q degree ringRank params.levels)
    (ifFalse : TLWE.Ciphertext (RLWE.Rq q degree) ringRank) :
    rowBranchDistance params candidate control ifFalse =
      controlBranchDistance params candidate control := by
  let Row := TLWE.Ciphertext (RLWE.Rq q degree) ringRank
  letI : SampleableType Row := SampleableType.ofEquiv
    (tlweCiphertextEquiv (RLWE.Rq q degree) ringRank)
  let Uniform : ProbComp Row := $ᵗ Row
  let translation := rowTranslationEquiv ifFalse
  let normalized := controlBranchTransform params candidate control
  have hpre :
      evalDist (translation.symm <$> Uniform) = evalDist Uniform :=
    evalDist_map_bijective_uniform_cross (α := Row) (β := Row)
      translation.symm translation.symm.bijective
  have hnormalized :
      evalDist (normalized <$> (translation.symm <$> Uniform)) =
        evalDist (normalized <$> Uniform) :=
    evalDist_map_eq_of_evalDist_eq hpre normalized
  have hleft :
      evalDist (rowBranchTransform params candidate control ifFalse <$> Uniform) =
        evalDist (translation <$> (normalized <$> Uniform)) := by
    calc
      _ = evalDist (translation <$>
          (normalized <$> (translation.symm <$> Uniform))) := by
        apply congrArg evalDist
        simp only [Functor.map_map]
        apply congrArg (fun transform => transform <$> Uniform)
        exact rowBranchTransform_eq_conjugate params candidate control ifFalse
      _ = _ := evalDist_map_eq_of_evalDist_eq hnormalized translation
  have huniform : evalDist (translation <$> Uniform) = evalDist Uniform :=
    evalDist_map_bijective_uniform_cross (α := Row) (β := Row)
      translation translation.bijective
  have htvMap (left right : ProbComp Row) :
      tvDist (translation <$> left) (translation <$> right) =
        tvDist left right := by
    apply le_antisymm
    · exact tvDist_map_le (m := ProbComp) translation left right
    · have h := tvDist_map_le (m := ProbComp) translation.symm
        (translation <$> left) (translation <$> right)
      have hleft : translation.symm <$> (translation <$> left) = left := by
        rw [Functor.map_map]
        simpa only [Equiv.symm_apply_apply] using (id_map' left)
      have hright : translation.symm <$> (translation <$> right) = right := by
        rw [Functor.map_map]
        simpa only [Equiv.symm_apply_apply] using (id_map' right)
      rw [hleft, hright] at h
      exact h
  unfold rowBranchDistance controlBranchDistance
  change tvDist
      (rowBranchTransform params candidate control ifFalse <$> Uniform) Uniform =
    tvDist (normalized <$> Uniform) Uniform
  calc
    _ = tvDist (translation <$> (normalized <$> Uniform))
        (translation <$> Uniform) := by
      unfold tvDist
      rw [hleft, huniform]
    _ = _ := htvMap (normalized <$> Uniform) Uniform

/-- Statistical defect of one complete shifted-CMux TGSW-entry map on a uniform input entry. -/
noncomputable def entryBranchDistance [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (control ifFalse : RingGSWCiphertext q degree ringRank params.levels) : ℝ :=
  tvDist
    (entryBranchTransform params candidate control ifFalse <$>
      ($ᵗ RingGSWCiphertext q degree ringRank params.levels))
    ($ᵗ RingGSWCiphertext q degree ringRank params.levels)

/-- Statistical defect of the whole native BRK branch map on a uniform true branch. -/
noncomputable def branchDistance [NeZero q] {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q) (coordinate : Fin lweDimension)
    (candidate : Bool)
    (source : BootstrappingKey q degree ringRank params.levels lweDimension) : ℝ :=
  tvDist
    (branchTransform params coordinate candidate source <$>
      ($ᵗ BootstrappingKey q degree ringRank params.levels lweDimension))
    ($ᵗ BootstrappingKey q degree ringRank params.levels lweDimension)

/-- The statistical defect of one TGSW-entry branch map is at most the sum of the independent
TLWE-row defects. -/
theorem entryBranchDistance_le_sum_rowBranchDistance [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (control ifFalse : RingGSWCiphertext q degree ringRank params.levels) :
    entryBranchDistance params candidate control ifFalse ≤
      ∑ row, rowBranchDistance params candidate control (TLWE.entry ifFalse row) := by
  let Row := TLWE.Ciphertext (RLWE.Rq q degree) ringRank
  letI : SampleableType Row := SampleableType.ofEquiv
    (tlweCiphertextEquiv (RLWE.Rq q degree) ringRank)
  let count := TGSW.rowCount ringRank params.levels
  let assemble : (Fin count → Row) →
      RingGSWCiphertext q degree ringRank params.levels := TLWE.batchOfRows
  let transform : Fin count → Row → Row := fun row =>
    rowBranchTransform params candidate control (TLWE.entry ifFalse row)
  let pointwise : (Fin count → Row) → Fin count → Row := fun rows row =>
    transform row (rows row)
  have hassemble :
      evalDist (assemble <$> ($ᵗ (Fin count → Row))) =
        evalDist ($ᵗ RingGSWCiphertext q degree ringRank params.levels) :=
    evalDist_map_bijective_uniform_cross assemble
      (α := Fin count → Row)
      (β := RingGSWCiphertext q degree ringRank params.levels)
      (tgswBatchOfRows_bijective (q := q) (degree := degree)
        (ringRank := ringRank) params.levels)
  have hmap :
      entryBranchTransform params candidate control ifFalse <$>
          (assemble <$> ($ᵗ (Fin count → Row))) =
        assemble <$> (pointwise <$> ($ᵗ (Fin count → Row))) := by
    simp only [Functor.map_map]
    apply congrArg (fun function => function <$> ($ᵗ (Fin count → Row)))
    funext rows
    exact entryBranchTransform_batchOfRows params candidate control ifFalse rows
  have hleft :
      evalDist
          (entryBranchTransform params candidate control ifFalse <$>
            ($ᵗ RingGSWCiphertext q degree ringRank params.levels)) =
        evalDist (assemble <$> (pointwise <$> ($ᵗ (Fin count → Row)))) := by
    calc
      _ = evalDist
          (entryBranchTransform params candidate control ifFalse <$>
            (assemble <$> ($ᵗ (Fin count → Row)))) :=
        evalDist_map_eq_of_evalDist_eq hassemble.symm
          (entryBranchTransform params candidate control ifFalse)
      _ = _ := congrArg evalDist hmap
  unfold entryBranchDistance tvDist
  rw [hleft, ← hassemble]
  change tvDist (assemble <$> (pointwise <$> ($ᵗ (Fin count → Row))))
      (assemble <$> ($ᵗ (Fin count → Row))) ≤ _
  calc
    _ ≤ tvDist (pointwise <$> ($ᵗ (Fin count → Row)))
        ($ᵗ (Fin count → Row)) :=
      tvDist_map_le assemble (pointwise <$> ($ᵗ (Fin count → Row)))
        ($ᵗ (Fin count → Row))
    _ ≤ ∑ row, tvDist (transform row <$> ($ᵗ Row)) ($ᵗ Row) :=
      FormalProof4FHE.FiniteProduct.tvDist_map_uniform_fun_le_sum count transform
    _ = ∑ row,
        rowBranchDistance params candidate control (TLWE.entry ifFalse row) := by
      rfl

/-- The whole-BRK branch defect is at most the sum of its independent TGSW-entry defects. -/
theorem branchDistance_le_sum_entryBranchDistance [NeZero q] {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q) (coordinate : Fin lweDimension)
    (candidate : Bool)
    (source : BootstrappingKey q degree ringRank params.levels lweDimension) :
    branchDistance params coordinate candidate source ≤
      ∑ outputCoordinate,
        entryBranchDistance params candidate (source coordinate)
          (source outputCoordinate) := by
  unfold branchDistance branchTransform selectBootstrappingKey
  simpa only [entryBranchDistance, entryBranchTransform] using
    (FormalProof4FHE.FiniteProduct.tvDist_map_uniform_fun_le_sum
      (alpha := RingGSWCiphertext q degree ringRank params.levels) lweDimension
      (fun outputCoordinate =>
        entryBranchTransform params candidate (source coordinate)
          (source outputCoordinate)))

/-- Combining the two exact product decompositions bounds the whole-BRK defect by the sum of all
explicit single-row defects. -/
theorem branchDistance_le_sum_rowBranchDistance [NeZero q] {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q) (coordinate : Fin lweDimension)
    (candidate : Bool)
    (source : BootstrappingKey q degree ringRank params.levels lweDimension) :
    branchDistance params coordinate candidate source ≤
      ∑ outputCoordinate, ∑ row,
        rowBranchDistance params candidate (source coordinate)
          (TLWE.entry (source outputCoordinate) row) := by
  exact (branchDistance_le_sum_entryBranchDistance params coordinate candidate source).trans
    (Finset.sum_le_sum fun outputCoordinate _ =>
      entryBranchDistance_le_sum_rowBranchDistance params candidate
        (source coordinate) (source outputCoordinate))

/-- Translation conjugacy collapses the complete row sum to one normalized control distance,
multiplied only by the number of independently transformed data rows.  This is the direct
statistical alternative when exact control-map bijectivity is too strong. -/
theorem branchDistance_le_card_mul_controlBranchDistance [NeZero q]
    {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q) (coordinate : Fin lweDimension)
    (candidate : Bool)
    (source : BootstrappingKey q degree ringRank params.levels lweDimension) :
    branchDistance params coordinate candidate source ≤
      (lweDimension * TGSW.rowCount ringRank params.levels : ℕ) *
        controlBranchDistance params candidate (source coordinate) := by
  calc
    _ ≤ ∑ outputCoordinate, ∑ row,
        rowBranchDistance params candidate (source coordinate)
          (TLWE.entry (source outputCoordinate) row) :=
      branchDistance_le_sum_rowBranchDistance params coordinate candidate source
    _ = ∑ _outputCoordinate : Fin lweDimension,
        ∑ _row : Fin (TGSW.rowCount ringRank params.levels),
          controlBranchDistance params candidate (source coordinate) := by
      apply Finset.sum_congr rfl
      intro outputCoordinate _
      apply Finset.sum_congr rfl
      intro row _
      exact rowBranchDistance_eq_controlBranchDistance params candidate
        (source coordinate) (TLWE.entry (source outputCoordinate) row)
    _ = _ := by
      simp [Nat.cast_mul]
      ring

/-- A fresh uniform true branch yields an exactly uniform output BRK whenever the concrete branch
map is fresh.  No distributional conclusion is hidden in `BranchFresh`: the remaining task is to
prove this explicit bijectivity or replace it by a quantified statistical bound. -/
theorem branchTransform_uniform_evalDist [NeZero q] {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q) (coordinate : Fin lweDimension)
    (candidate : Bool)
    (source : BootstrappingKey q degree ringRank params.levels lweDimension)
    (hFresh : BranchFresh params coordinate candidate source) :
    evalDist (branchTransform params coordinate candidate source <$>
        ($ᵗ BootstrappingKey q degree ringRank params.levels lweDimension)) =
      evalDist ($ᵗ BootstrappingKey q degree ringRank params.levels lweDimension) :=
  evalDist_map_bijective_uniform_cross
    (α := BootstrappingKey q degree ringRank params.levels lweDimension)
    (β := BootstrappingKey q degree ringRank params.levels lweDimension)
    (branchTransform params coordinate candidate source) hFresh

/-- Complete row residual for one entry of the whole-BRK shifted evaluator. -/
noncomputable def bootstrappingKeyRowResidual {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q)
    (secret : Fin ringRank → RLWE.Rq q degree)
    (controlMessage trueMessage falseMessage : RLWE.Rq q degree)
    (coordinate : Fin lweDimension) (candidate : Bool)
    (source trueBranch :
      BootstrappingKey q degree ringRank params.levels lweDimension)
    (outputCoordinate : Fin lweDimension)
    (index : Fin (ringRank + 1) × Fin params.levels) : RLWE.Rq q degree :=
  rowResidual params secret controlMessage trueMessage falseMessage candidate
    (source coordinate) (trueBranch outputCoordinate) (source outputCoordinate) index

/-- Complete coin-dependent residual of the correct branch for an arbitrary public source BRK.
The unused true-branch message is fixed to zero; any phase carried by that arbitrary uniform
ciphertext is accounted for inside the computed CMux residual. -/
noncomputable def correctBootstrappingResidual {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q)
    (secret : Fin ringRank → RLWE.Rq q degree)
    (hidden : BinarySecret lweDimension)
    (coordinate : Fin lweDimension)
    (source trueBranch :
      BootstrappingKey q degree ringRank params.levels lweDimension) :
    Fin lweDimension → Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q degree :=
  fun outputCoordinate row =>
    bootstrappingKeyRowResidual params secret 0 0
      (embedBit (hidden outputCoordinate)) coordinate (hidden coordinate)
      source trueBranch outputCoordinate (finProdFinEquiv.symm row)

/-- The concrete correct-branch residual has only two terms: the retained source-row error and
the executable digit-weighted row error of the zero-message candidate control.  In particular,
exact gadget decomposition contributes no residual term. -/
theorem correctBootstrappingResidual_eq_rowError_add_externalProductError
    {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q)
    (secret : Fin ringRank → RLWE.Rq q degree)
    (hidden : BinarySecret lweDimension)
    (coordinate outputCoordinate : Fin lweDimension)
    (source trueBranch :
      BootstrappingKey q degree ringRank params.levels lweDimension)
    (index : Fin (ringRank + 1) × Fin params.levels) :
    correctBootstrappingResidual params secret hidden coordinate source trueBranch
        outputCoordinate (finProdFinEquiv index) =
      proofAdd
        (TGSW.rowError secret (Gadget.Base.ringGadget params)
          (embedBit (hidden outputCoordinate)) (source outputCoordinate) index)
        (TGSW.externalProductError secret (Gadget.Base.ringGadget params)
          proofZero
          (differenceDigits params (trueBranch outputCoordinate)
            (source outputCoordinate) (finProdFinEquiv index))
          (candidateControl params (hidden coordinate) (source coordinate))) := by
  unfold correctBootstrappingResidual bootstrappingKeyRowResidual rowResidual
  rw [show (0 : RLWE.Rq q degree) = proofZero by
    exact proofZero_eq_zero.symm]
  simpa only [proofAdd, proofZero, Equiv.symm_apply_apply] using
    (TGSW.computedCmuxRowResidual_zero secret (Gadget.Base.ringGadget params)
      proofZero (embedBit (hidden outputCoordinate))
      (candidateControl params (hidden coordinate) (source coordinate))
      (trueBranch outputCoordinate) (source outputCoordinate)
      (differenceDigits params (trueBranch outputCoordinate) (source outputCoordinate))
      index)

/-- Correct-candidate row normal form for the executable whole-BRK evaluator. -/
theorem phase_entry_selectBootstrappingKey_correct {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q)
    (secret : Fin ringRank → RLWE.Rq q degree)
    (hidden : BinarySecret lweDimension)
    (trueMessage : Fin lweDimension → RLWE.Rq q degree)
    (homogeneous trueBranch :
      BootstrappingKey q degree ringRank params.levels lweDimension)
    (coordinate outputCoordinate : Fin lweDimension)
    (index : Fin (ringRank + 1) × Fin params.levels) :
    TLWE.phase secret
        (TLWE.entry
          (selectBootstrappingKey params coordinate (hidden coordinate)
            (structuredBootstrappingKey params hidden homogeneous) trueBranch
            outputCoordinate)
          (finProdFinEquiv index)) =
      proofAdd
        (TGSW.gadgetPhase secret (Gadget.Base.ringGadget params)
          (TGSW.cmuxMessage 0 (trueMessage outputCoordinate)
            (embedBit (hidden outputCoordinate)))
          (finProdFinEquiv index))
        (bootstrappingKeyRowResidual params secret 0
          (trueMessage outputCoordinate) (embedBit (hidden outputCoordinate))
          coordinate (hidden coordinate)
          (structuredBootstrappingKey params hidden homogeneous) trueBranch
          outputCoordinate index) := by
  simpa only [selectBootstrappingKey, structuredBootstrappingKey,
    bootstrappingKeyRowResidual] using
    phase_entry_select_correct params secret (hidden coordinate)
      (trueMessage outputCoordinate) (embedBit (hidden outputCoordinate))
      (homogeneous coordinate) (trueBranch outputCoordinate)
      (TGSW.addGadget (Gadget.Base.ringGadget params)
        (embedBit (hidden outputCoordinate)) (homogeneous outputCoordinate))
      index

/-- **Concrete whole-BRK correct residual law.**  For every arbitrary public source and
true-branch BRK, selecting with the declared hidden coordinate gives exactly the declared
binary gadget phase plus `correctBootstrappingResidual`, row by row.  Thus all remaining
correct-branch work is distributional mask freshness and quantitative residual size, not phase
algebra or a missing structural-generation premise. -/
theorem phase_entry_selectBootstrappingKey_correctResidual {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q)
    (secret : Fin ringRank → RLWE.Rq q degree)
    (hidden : BinarySecret lweDimension)
    (coordinate outputCoordinate : Fin lweDimension)
    (source trueBranch :
      BootstrappingKey q degree ringRank params.levels lweDimension)
    (row : Fin (TGSW.rowCount ringRank params.levels)) :
    TLWE.phase secret
        (TLWE.entry
          (selectBootstrappingKey params coordinate (hidden coordinate)
            source trueBranch outputCoordinate) row) =
      proofAdd
        (TGSW.gadgetPhase secret (Gadget.Base.ringGadget params)
          (TGSW.cmuxMessage 0 0 (embedBit (hidden outputCoordinate))) row)
        (correctBootstrappingResidual params secret hidden coordinate
          source trueBranch outputCoordinate row) := by
  obtain ⟨index, rfl⟩ := finProdFinEquiv.surjective row
  let homogeneous := homogeneousPart params hidden source
  have h := phase_entry_selectBootstrappingKey_correct params secret hidden
    (fun _ => 0) homogeneous trueBranch coordinate outputCoordinate
    index
  rw [structuredBootstrappingKey_homogeneousPart] at h
  simpa [correctBootstrappingResidual, homogeneous] using h

/-- Wrong-candidate row normal form for the executable whole-BRK evaluator. -/
theorem phase_entry_selectBootstrappingKey_wrong {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q)
    (secret : Fin ringRank → RLWE.Rq q degree)
    (hidden : BinarySecret lweDimension)
    (trueMessage : Fin lweDimension → RLWE.Rq q degree)
    (homogeneous trueBranch :
      BootstrappingKey q degree ringRank params.levels lweDimension)
    (coordinate outputCoordinate : Fin lweDimension)
    (index : Fin (ringRank + 1) × Fin params.levels) :
    TLWE.phase secret
        (TLWE.entry
          (selectBootstrappingKey params coordinate (!hidden coordinate)
            (structuredBootstrappingKey params hidden homogeneous) trueBranch
            outputCoordinate)
          (finProdFinEquiv index)) =
      proofAdd
        (TGSW.gadgetPhase secret (Gadget.Base.ringGadget params)
          (TGSW.cmuxMessage 1 (trueMessage outputCoordinate)
            (embedBit (hidden outputCoordinate)))
          (finProdFinEquiv index))
        (bootstrappingKeyRowResidual params secret 1
          (trueMessage outputCoordinate) (embedBit (hidden outputCoordinate))
          coordinate (!hidden coordinate)
          (structuredBootstrappingKey params hidden homogeneous) trueBranch
          outputCoordinate index) := by
  simpa only [selectBootstrappingKey, structuredBootstrappingKey,
    bootstrappingKeyRowResidual] using
    phase_entry_select_wrong params secret (hidden coordinate)
      (trueMessage outputCoordinate) (embedBit (hidden outputCoordinate))
      (homogeneous coordinate) (trueBranch outputCoordinate)
      (TGSW.addGadget (Gadget.Base.ringGadget params)
        (embedBit (hidden outputCoordinate)) (homogeneous outputCoordinate))
      index

end FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator
