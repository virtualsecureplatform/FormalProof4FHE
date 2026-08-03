/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeTRGSWAggregateProjectedLeakage
import FormalProof4FHE.SharedRandomness.Reduction

/-!
# Complete-view auxiliary zero-row source for native TRGSW

This module formalizes the valid finite claims in `sketch/completeview.md`.

The construction forwards the native key-switch key and every auxiliary object unchanged while
publicly translating a complete homogeneous BRK row block by a known plaintext.  The real-source
diagonal identity is valid for an arbitrary joint distribution of rows and side information.  The
uniform-source sign-erasure identity is stated with the necessary stronger condition: the uniform
row block is sampled independently of the jointly distributed KSK/auxiliary state.

The quantitative theorem is the projected match-and-square theorem specialized to the prefix
projection of a master key `(Prefix × Suffix)`.  Its concentration is exactly that of the prefix
marginal, so a uniform binary prefix contributes `2^t` and the suffix entropy disappears.  The
source bound remains an explicit auxiliary-input zero-row assumption; no reduction from ordinary
RLWE to that correlated complete-view source is asserted here.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.NativeTRGSWCompleteViewAuxiliarySource

noncomputable section

open NativeTRGSWAggregateSecurityAndComplexityLeveraging
open NativeTRGSWAggregateProjectedLeakage
open NativeTRGSWBarrierAndSpectralBoundary
open RGSWCoefficientCircularSecurity

/-! ## Complete views and public row translation -/

/-- A complete native source/public view.  The row carrier is separated from the KSK and
auxiliary fields only so that the public simulator can replace the rows while forwarding all side
information definitionally unchanged. -/
structure CompleteView (Rows KeySwitchKey Auxiliary : Type) where
  rows : Rows
  keySwitchKey : KeySwitchKey
  auxiliary : Auxiliary

namespace CompleteView

/-- Apply a public transformation only to the row carrier. -/
def mapRows {Rows TargetRows KeySwitchKey Auxiliary : Type}
    (transform : Rows → TargetRows)
    (view : CompleteView Rows KeySwitchKey Auxiliary) :
    CompleteView TargetRows KeySwitchKey Auxiliary :=
  ⟨transform view.rows, view.keySwitchKey, view.auxiliary⟩

@[simp]
theorem mapRows_rows {Rows TargetRows KeySwitchKey Auxiliary : Type}
    (transform : Rows → TargetRows)
    (view : CompleteView Rows KeySwitchKey Auxiliary) :
    (mapRows transform view).rows = transform view.rows := rfl

@[simp]
theorem mapRows_keySwitchKey {Rows TargetRows KeySwitchKey Auxiliary : Type}
    (transform : Rows → TargetRows)
    (view : CompleteView Rows KeySwitchKey Auxiliary) :
    (mapRows transform view).keySwitchKey = view.keySwitchKey := rfl

@[simp]
theorem mapRows_auxiliary {Rows TargetRows KeySwitchKey Auxiliary : Type}
    (transform : Rows → TargetRows)
    (view : CompleteView Rows KeySwitchKey Auxiliary) :
    (mapRows transform view).auxiliary = view.auxiliary := rfl

@[simp]
theorem mapRows_id {Rows KeySwitchKey Auxiliary : Type}
    (view : CompleteView Rows KeySwitchKey Auxiliary) :
    mapRows id view = view := by
  cases view
  rfl

@[simp]
theorem mapRows_comp
    {FirstRows SecondRows ThirdRows KeySwitchKey Auxiliary : Type}
    (second : SecondRows → ThirdRows) (first : FirstRows → SecondRows)
    (view : CompleteView FirstRows KeySwitchKey Auxiliary) :
    mapRows second (mapRows first view) = mapRows (second ∘ first) view := by
  cases view
  rfl

end CompleteView

/-- The complete-view simulator from the note.  A mask is sampled, converted with the fake prefix
to a known plaintext, and used only to translate the row carrier.  Neither the mask nor the fake
prefix is returned. -/
def simulator
    {Prefix Mask Message SourceRows TargetRows KeySwitchKey Auxiliary : Type}
    (translate : Message → SourceRows → TargetRows)
    (messageOf : Prefix → Mask → Message)
    (maskSampler : ProbComp Mask) (fakePrefix : Prefix)
    (source : CompleteView SourceRows KeySwitchKey Auxiliary) :
    ProbComp (CompleteView TargetRows KeySwitchKey Auxiliary) := do
  let mask ← maskSampler
  return source.mapRows (translate (messageOf fakePrefix mask))

/-- The target experiment associated with a caller-supplied honest translated-row function. -/
def targetView
    {Mask SourceRows TargetRows KeySwitchKey Auxiliary : Type}
    (targetRows : CompleteView SourceRows KeySwitchKey Auxiliary → Mask → TargetRows)
    (maskSampler : ProbComp Mask)
    (source : CompleteView SourceRows KeySwitchKey Auxiliary) :
    ProbComp (CompleteView TargetRows KeySwitchKey Auxiliary) := do
  let mask ← maskSampler
  return ⟨targetRows source mask, source.keySwitchKey, source.auxiliary⟩

/-- Exact diagonal simulation for one complete source view.  No independence among the source
rows, KSK, and auxiliary state is required: all correlations are retained by the deterministic
row-only map. -/
theorem simulator_evalDist_eq_targetView
    {Prefix Mask Message SourceRows TargetRows KeySwitchKey Auxiliary : Type}
    (translate : Message → SourceRows → TargetRows)
    (messageOf : Prefix → Mask → Message)
    (targetRows : CompleteView SourceRows KeySwitchKey Auxiliary → Mask → TargetRows)
    (maskSampler : ProbComp Mask) (prefixValue : Prefix)
    (source : CompleteView SourceRows KeySwitchKey Auxiliary)
    (hrows : ∀ mask,
      translate (messageOf prefixValue mask) source.rows = targetRows source mask) :
    evalDist (simulator translate messageOf maskSampler prefixValue source) =
      evalDist (targetView targetRows maskSampler source) := by
  unfold simulator targetView
  refine evalDist_bind_congr' maskSampler fun mask ↦ ?_
  simp [CompleteView.mapRows, hrows mask]

/-- The diagonal identity remains exact after sampling an arbitrary jointly correlated complete
source view. -/
theorem simulator_over_jointSource_evalDist_eq_targetView
    {Prefix Mask Message SourceRows TargetRows KeySwitchKey Auxiliary : Type}
    (translate : Message → SourceRows → TargetRows)
    (messageOf : Prefix → Mask → Message)
    (targetRows : CompleteView SourceRows KeySwitchKey Auxiliary → Mask → TargetRows)
    (maskSampler : ProbComp Mask) (prefixValue : Prefix)
    (sourceSampler : ProbComp (CompleteView SourceRows KeySwitchKey Auxiliary))
    (hrows : ∀ source mask,
      translate (messageOf prefixValue mask) source.rows = targetRows source mask) :
    evalDist (sourceSampler >>= simulator translate messageOf maskSampler prefixValue) =
      evalDist (sourceSampler >>= targetView targetRows maskSampler) := by
  refine evalDist_bind_congr' sourceSampler fun source ↦ ?_
  exact simulator_evalDist_eq_targetView
    translate messageOf targetRows maskSampler prefixValue source (hrows source)

/-! ## Independent uniform rows and exact sign erasure -/

/-- Assemble a complete view from a row sampler independent of a jointly sampled KSK/auxiliary
pair.  The KSK and auxiliary state may remain arbitrarily correlated with each other. -/
def independentViewSampler
    {Rows KeySwitchKey Auxiliary : Type}
    (rowSampler : ProbComp Rows)
    (sideSampler : ProbComp (KeySwitchKey × Auxiliary)) :
    ProbComp (CompleteView Rows KeySwitchKey Auxiliary) := do
  let rows ← rowSampler
  let side ← sideSampler
  return ⟨rows, side.1, side.2⟩

/-- One public source transcript for the match-and-square reduction.  The common master key is
latent; the reduction receives only the two conditionally independent local views. -/
structure TwoCopySourceView (View : Type) where
  first : View
  second : View

/-- Sample the two conditionally IID complete local views in equations (3) and (4).  Correlation
inside each local view is unrestricted; only the two calls to `localViewSampler key` are fresh. -/
def conditionalTwoCopySource
    {Key View : Type} (keySampler : ProbComp Key)
    (localViewSampler : Key → ProbComp View) :
    ProbComp (TwoCopySourceView View) := do
  let key ← keySampler
  let first ← localViewSampler key
  let second ← localViewSampler key
  return ⟨first, second⟩

/-- Advantage for the explicit complete-view auxiliary zero-row source.  In the uniform local
sampler, callers should use `independentViewSampler uniformRows (sideSampler key)` so that the
independence required by sign erasure is present in the experiment rather than inferred from its
marginals. -/
def auxiliaryInputZeroRowAdvantage
    {Key RealView UniformView : Type}
    (keySampler : ProbComp Key)
    (realLocalView : Key → ProbComp RealView)
    (uniformLocalView : Key → ProbComp UniformView)
    (realDistinguisher : TwoCopySourceView RealView → ProbComp Bool)
    (uniformDistinguisher : TwoCopySourceView UniformView → ProbComp Bool) : ℝ :=
  (conditionalTwoCopySource keySampler realLocalView >>= realDistinguisher).boolDistAdvantage
    (conditionalTwoCopySource keySampler uniformLocalView >>= uniformDistinguisher)

theorem auxiliaryInputZeroRowAdvantage_nonneg
    {Key RealView UniformView : Type}
    (keySampler : ProbComp Key)
    (realLocalView : Key → ProbComp RealView)
    (uniformLocalView : Key → ProbComp UniformView)
    (realDistinguisher : TwoCopySourceView RealView → ProbComp Bool)
    (uniformDistinguisher : TwoCopySourceView UniformView → ProbComp Bool) :
    0 ≤ auxiliaryInputZeroRowAdvantage keySampler realLocalView uniformLocalView
      realDistinguisher uniformDistinguisher := by
  exact abs_nonneg _

/-- Translate an independently sampled row block and forward the independent joint side state. -/
def translatedIndependentView
    {Message SourceRows TargetRows KeySwitchKey Auxiliary : Type}
    (translate : Message → SourceRows → TargetRows) (message : Message)
    (rowSampler : ProbComp SourceRows)
    (sideSampler : ProbComp (KeySwitchKey × Auxiliary)) :
    ProbComp (CompleteView TargetRows KeySwitchKey Auxiliary) :=
  independentViewSampler (translate message <$> rowSampler) sideSampler

/-- Forwarding independent side information preserves equality of translated row laws. -/
theorem translatedIndependentView_evalDist_eq
    {Message SourceRows TargetRows KeySwitchKey Auxiliary : Type}
    (translate : Message → SourceRows → TargetRows)
    (firstMessage secondMessage : Message)
    (rowSampler : ProbComp SourceRows)
    (sideSampler : ProbComp (KeySwitchKey × Auxiliary))
    (hrows : evalDist (translate firstMessage <$> rowSampler) =
      evalDist (translate secondMessage <$> rowSampler)) :
    evalDist (translatedIndependentView translate firstMessage rowSampler sideSampler) =
      evalDist (translatedIndependentView translate secondMessage rowSampler sideSampler) := by
  unfold translatedIndependentView independentViewSampler
  rw [evalDist_bind, evalDist_bind, hrows]

/-- Uniform-source simulator with a hidden mask. -/
def simulatedIndependentView
    {Prefix Mask Message SourceRows TargetRows KeySwitchKey Auxiliary : Type}
    (translate : Message → SourceRows → TargetRows)
    (messageOf : Prefix → Mask → Message)
    (maskSampler : ProbComp Mask) (fakePrefix : Prefix)
    (rowSampler : ProbComp SourceRows)
    (sideSampler : ProbComp (KeySwitchKey × Auxiliary)) :
    ProbComp (CompleteView TargetRows KeySwitchKey Auxiliary) := do
  let mask ← maskSampler
  translatedIndependentView translate (messageOf fakePrefix mask) rowSampler sideSampler

/-- If every fixed-message row translation has one common law, the complete output law is
independent of the hidden mask sampler.  This is the exact complete-view sign-erasure lemma. -/
theorem simulatedIndependentView_sign_erasure
    {Prefix Mask Message SourceRows TargetRows KeySwitchKey Auxiliary : Type}
    (translate : Message → SourceRows → TargetRows)
    (messageOf : Prefix → Mask → Message)
    (anchorMessage : Message)
    (positiveMaskSampler negativeMaskSampler : ProbComp Mask)
    (fakePrefix : Prefix) (rowSampler : ProbComp SourceRows)
    (sideSampler : ProbComp (KeySwitchKey × Auxiliary))
    (hrows : ∀ message,
      evalDist (translate message <$> rowSampler) =
        evalDist (translate anchorMessage <$> rowSampler)) :
    evalDist (simulatedIndependentView translate messageOf positiveMaskSampler
        fakePrefix rowSampler sideSampler) =
      evalDist (simulatedIndependentView translate messageOf negativeMaskSampler
        fakePrefix rowSampler sideSampler) := by
  let common := translatedIndependentView translate anchorMessage rowSampler sideSampler
  have hcommon (maskSampler : ProbComp Mask) :
      evalDist (simulatedIndependentView translate messageOf maskSampler
          fakePrefix rowSampler sideSampler) = evalDist common := by
    unfold simulatedIndependentView
    calc
      evalDist (maskSampler >>= fun mask ↦
          translatedIndependentView translate (messageOf fakePrefix mask)
            rowSampler sideSampler) =
          evalDist (maskSampler >>= fun _mask ↦ common) := by
        refine evalDist_bind_congr' maskSampler fun mask ↦ ?_
        exact translatedIndependentView_evalDist_eq
          translate (messageOf fakePrefix mask) anchorMessage rowSampler sideSampler
            (hrows (messageOf fakePrefix mask))
      _ = evalDist common := by
        exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
          maskSampler (by simp) common
  exact (hcommon positiveMaskSampler).trans (hcommon negativeMaskSampler).symm

/-! ## Native body/nonce rows -/

/-- Public gadget translation of an honest homogeneous native row block gives the exact native
known-message body/nonce representation while forwarding the KSK and auxiliary state unchanged. -/
theorem nativeKnownMessage_mapRows_exact
    {R KeySwitchKey Auxiliary : Type} [Ring R] {dimension levels : ℕ}
    (secret : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R)
    (error : Fin (TGSW.rowCount dimension levels) → R)
    (gadget : Fin levels → R) (message : R)
    (keySwitchKey : KeySwitchKey) (auxiliary : Auxiliary) :
    CompleteView.mapRows (TGSW.addGadget gadget message)
        (CompleteView.mk
          (challenge, Matrix.vecMul secret challenge + error)
          keySwitchKey auxiliary) =
      CompleteView.mk
        (TLWE.batchAssemble secret
          (TGSW.shiftChallenge (dimension := dimension) gadget message challenge)
          (TGSW.gadgetPhase secret gadget message) error)
        keySwitchKey auxiliary := by
  change CompleteView.mk
      (TGSW.addGadget gadget message
        (challenge, Matrix.vecMul secret challenge + error))
      keySwitchKey auxiliary = _
  rw [addKnownGadgetToZeroRows secret challenge error gadget message]

/-- Native known-message translations of independent uniform row carriers have one common
complete-view law even when an arbitrary joint KSK/auxiliary state is forwarded. -/
theorem nativeCompleteView_uniform_sign_erasure
    {R Prefix Mask KeySwitchKey Auxiliary : Type}
    [Ring R] [Fintype R] [SampleableType R] {levels : ℕ}
    (gadget : Fin levels → R) (messageOf : Prefix → Mask → R)
    (positiveMaskSampler negativeMaskSampler : ProbComp Mask)
    (fakePrefix : Prefix)
    (sideSampler : ProbComp (KeySwitchKey × Auxiliary)) :
    evalDist
        (simulatedIndependentView (TGSW.addGadget gadget) messageOf
          positiveMaskSampler fakePrefix ($ᵗ (RGSWChallenge R levels)) sideSampler) =
      evalDist
        (simulatedIndependentView (TGSW.addGadget gadget) messageOf
          negativeMaskSampler fakePrefix ($ᵗ (RGSWChallenge R levels)) sideSampler) := by
  apply simulatedIndependentView_sign_erasure
    (TGSW.addGadget gadget) messageOf 0 positiveMaskSampler negativeMaskSampler
      fakePrefix ($ᵗ (RGSWChallenge R levels)) sideSampler
  intro message
  exact knownMessageTranslations_uniform_evalDist_eq gadget message 0

/-- The uniform sign-erasure identity remains exact when the honest KSK/auxiliary law depends on
a latent master key.  The key is sampled once and not exposed; conditioning on it leaves the
uniform row block independent of the corresponding side sampler. -/
theorem nativeCompleteView_conditionalUniform_sign_erasure
    {Key R Prefix Mask KeySwitchKey Auxiliary : Type}
    [Ring R] [Fintype R] [SampleableType R] {levels : ℕ}
    (keySampler : ProbComp Key)
    (sideSampler : Key → ProbComp (KeySwitchKey × Auxiliary))
    (gadget : Fin levels → R) (messageOf : Prefix → Mask → R)
    (positiveMaskSampler negativeMaskSampler : ProbComp Mask)
    (fakePrefix : Prefix) :
    evalDist (do
        let key ← keySampler
        simulatedIndependentView (TGSW.addGadget gadget) messageOf
          positiveMaskSampler fakePrefix ($ᵗ (RGSWChallenge R levels)) (sideSampler key)) =
      evalDist (do
        let key ← keySampler
        simulatedIndependentView (TGSW.addGadget gadget) messageOf
          negativeMaskSampler fakePrefix ($ᵗ (RGSWChallenge R levels)) (sideSampler key)) := by
  refine evalDist_bind_congr' keySampler fun key ↦ ?_
  exact nativeCompleteView_uniform_sign_erasure
    gadget messageOf positiveMaskSampler negativeMaskSampler fakePrefix (sideSampler key)

/-! ## Prefix-only match-and-square loss -/

/-- Genuine aggregate advantage of the complete-view simulator.  Only the real prefix is used as
the deterministic diagonal leakage. -/
def completeViewAggregateAdvantage
    {Prefix Suffix : Type} (keySampler : ProbComp (Prefix × Suffix))
    (plus minus : Prefix → (Prefix × Suffix) → ProbComp Bool) : ℝ :=
  projectedAggregateAdvantage keySampler Prod.fst plus minus

/-- The four-call, two-copy reduction advantage to be bounded by auxiliary-input zero-row
security.  The name records the cryptographic premise; algebraically this is exactly the existing
projected leakage-removal game. -/
def completeViewZeroRowReductionAdvantage
    {Prefix Suffix : Type} (keySampler : ProbComp (Prefix × Suffix))
    (fakePrefixSampler : ProbComp Prefix)
    (plus minus : Prefix → (Prefix × Suffix) → ProbComp Bool) : ℝ :=
  projectedMatchSquareAdvantage keySampler fakePrefixSampler plus minus

/-- Exact two-copy identity from equation (21): the four-call reduction advantage is one half of
the conditional signed-gap second moment over the independently guessed prefix and genuine key. -/
theorem completeViewZeroRowReductionAdvantage_eq_half_guessedSecondMoment
    {Prefix Suffix : Type} [Fintype Prefix] [Fintype Suffix]
    (keySampler : ProbComp (Prefix × Suffix))
    (fakePrefixSampler : ProbComp Prefix)
    (plus minus : Prefix → (Prefix × Suffix) → ProbComp Bool) :
    completeViewZeroRowReductionAdvantage
        keySampler fakePrefixSampler plus minus =
      guessedSecondMoment keySampler fakePrefixSampler
        (conditionalGap plus minus) / 2 := by
  exact leakageRemovalAdvantage_eq_half_guessedSecondMoment
    keySampler fakePrefixSampler plus minus

/-- Renyi-half concentration of the actual prefix marginal. -/
def completeViewPrefixConcentration
    {Prefix Suffix : Type} [Fintype Prefix]
    (keySampler : ProbComp (Prefix × Suffix)) : ℝ :=
  projectedLeakageConcentration keySampler Prod.fst

theorem completeViewPrefixConcentration_eq_prefixMarginal
    {Prefix Suffix : Type} [Fintype Prefix]
    (keySampler : ProbComp (Prefix × Suffix)) :
    completeViewPrefixConcentration keySampler =
      halfRenyiConcentration (Prod.fst <$> keySampler) := by
  rfl

/-- The concentration depends only on the prefix marginal, even for a correlated master-key law. -/
theorem completeViewPrefixConcentration_eq_of_prefixMarginal_evalDist
    {Prefix Suffix : Type} [Fintype Prefix]
    (keySampler : ProbComp (Prefix × Suffix)) (prefixSampler : ProbComp Prefix)
    (hmarginal : evalDist (Prod.fst <$> keySampler) = evalDist prefixSampler) :
    completeViewPrefixConcentration keySampler =
      halfRenyiConcentration prefixSampler := by
  rw [completeViewPrefixConcentration_eq_prefixMarginal]
  exact halfRenyiConcentration_eq_of_evalDist_eq _ _ hmarginal

/-- For a uniform product master key, a uniform binary prefix has exact loss `2^prefixCount`,
independently of the suffix carrier size. -/
theorem completeViewPrefixConcentration_uniform_binary
    (prefixCount : ℕ) {Suffix : Type}
    [Fintype Suffix] [Nonempty Suffix] [SampleableType Suffix]
    [SampleableType ((Fin prefixCount → Bool) × Suffix)] :
    completeViewPrefixConcentration
        ($ᵗ ((Fin prefixCount → Bool) × Suffix)) =
      (2 : ℝ) ^ prefixCount := by
  rw [completeViewPrefixConcentration_eq_prefixMarginal,
    halfRenyiConcentration_eq_of_evalDist_eq
      (Prod.fst <$> ($ᵗ ((Fin prefixCount → Bool) × Suffix)))
      ($ᵗ (Fin prefixCount → Bool)) evalDist_map_fst_uniformSample_prod,
    halfRenyiConcentration_uniform_binaryTuple]

/-- Native complete-view aggregate theorem.  `hsource` is precisely the auxiliary-input CVZR
premise: it must bound the doubled reduction while the genuine KSK and auxiliary transcript are
available. -/
theorem nativeCompleteViewAggregateGap_le
    {Prefix Suffix : Type} [Fintype Prefix] [Fintype Suffix]
    (keySampler : ProbComp (Prefix × Suffix))
    (fakePrefixSampler : ProbComp Prefix)
    (plus minus : Prefix → (Prefix × Suffix) → ProbComp Bool)
    (nativeAggregateGap sigmaPlus sigmaMinus sourceBound : ℝ)
    (hdiagonal : nativeAggregateGap ≤ sigmaPlus + sigmaMinus +
      completeViewAggregateAdvantage keySampler plus minus)
    (hsource : completeViewZeroRowReductionAdvantage
      keySampler fakePrefixSampler plus minus ≤ sourceBound)
    (hcover : ∀ key, probabilityMass keySampler key ≠ 0 →
      probabilityMass fakePrefixSampler key.1 ≠ 0)
    (hoptimized : ∀ prefixValue,
      probabilityMass fakePrefixSampler prefixValue =
        Real.sqrt (probabilityMass (leakageLaw keySampler Prod.fst) prefixValue) /
          halfRenyiNormalizer keySampler Prod.fst) :
    nativeAggregateGap ≤ sigmaPlus + sigmaMinus +
      Real.sqrt (2 * completeViewPrefixConcentration keySampler * sourceBound) := by
  exact nativeProjectedAggregateGap_le_defects_add_sqrt
    keySampler fakePrefixSampler Prod.fst plus minus
    nativeAggregateGap sigmaPlus sigmaMinus sourceBound
    hdiagonal hsource hcover hoptimized

/-- Prefix-marginal form of the complete-view theorem.  This is equation (25) of the note. -/
theorem nativeCompleteViewAggregateGap_le_prefixMarginal
    {Prefix Suffix : Type} [Fintype Prefix] [Fintype Suffix]
    (keySampler : ProbComp (Prefix × Suffix))
    (prefixSampler fakePrefixSampler : ProbComp Prefix)
    (plus minus : Prefix → (Prefix × Suffix) → ProbComp Bool)
    (nativeAggregateGap sigmaPlus sigmaMinus sourceBound : ℝ)
    (hmarginal : evalDist (Prod.fst <$> keySampler) = evalDist prefixSampler)
    (hdiagonal : nativeAggregateGap ≤ sigmaPlus + sigmaMinus +
      completeViewAggregateAdvantage keySampler plus minus)
    (hsource : completeViewZeroRowReductionAdvantage
      keySampler fakePrefixSampler plus minus ≤ sourceBound)
    (hcover : ∀ key, probabilityMass keySampler key ≠ 0 →
      probabilityMass fakePrefixSampler key.1 ≠ 0)
    (hoptimized : ∀ prefixValue,
      probabilityMass fakePrefixSampler prefixValue =
        Real.sqrt (probabilityMass (leakageLaw keySampler Prod.fst) prefixValue) /
          halfRenyiNormalizer keySampler Prod.fst) :
    nativeAggregateGap ≤ sigmaPlus + sigmaMinus +
      Real.sqrt (2 * halfRenyiConcentration prefixSampler * sourceBound) := by
  have h := nativeCompleteViewAggregateGap_le
    keySampler fakePrefixSampler plus minus nativeAggregateGap sigmaPlus sigmaMinus
      sourceBound hdiagonal hsource hcover hoptimized
  rw [completeViewPrefixConcentration_eq_of_prefixMarginal_evalDist
    keySampler prefixSampler hmarginal] at h
  exact h

/-- Approximate uniform erasure with the prefix concentration.  The uniform defect appears once,
inside the second moment, as in equation (26). -/
theorem nativeCompleteViewAggregateGap_le_approximateErasure
    {Prefix : Type} [Fintype Prefix]
    (prefixSampler : ProbComp Prefix)
    (nativeAggregateGap sigmaPlus sigmaMinus realSecondMoment uniformSignedGap
      sourceAdvantage uniformGap : ℝ)
    (hdiagonal : nativeAggregateGap ≤ sigmaPlus + sigmaMinus +
      Real.sqrt (halfRenyiConcentration prefixSampler * realSecondMoment))
    (hsource : |realSecondMoment - uniformSignedGap ^ 2| ≤ 2 * sourceAdvantage)
    (herasure : |uniformSignedGap| ≤ uniformGap) :
    nativeAggregateGap ≤ sigmaPlus + sigmaMinus +
      Real.sqrt (halfRenyiConcentration prefixSampler *
        (2 * sourceAdvantage + uniformGap ^ 2)) := by
  apply nativeAggregateGap_le_of_approximateErasure
    nativeAggregateGap sigmaPlus sigmaMinus
      (halfRenyiConcentration prefixSampler) realSecondMoment uniformSignedGap
      sourceAdvantage uniformGap
  · exact sq_nonneg _
  · exact hdiagonal
  · exact hsource
  · exact herasure

/-! ## Integration with the exact native Fourier decomposition -/

/-- Complete-view prefix specialization of the final native Fourier theorem.  The low-support
term, aggregate normalization, construction defects, CVZR source bound, and independent endpoint
are each charged once. -/
theorem nativeCircularSecurity_with_completeViewPrefix
    {Index Prefix Suffix : Type}
    [Fintype Index] [DecidableEq Index]
    [Fintype Prefix] [Fintype Suffix]
    (response : BitVector Index → BitVector Index → ℝ)
    (degree : ℕ) (hdegree : degree < Fintype.card Index)
    (affineBound endpoint endpointBound sigmaPlus sigmaMinus sourceBound : ℝ)
    (keySampler : ProbComp (Prefix × Suffix))
    (prefixSampler fakePrefixSampler : ProbComp Prefix)
    (plus minus : Prefix → (Prefix × Suffix) → ProbComp Bool)
    (hmarginal : evalDist (Prod.fst <$> keySampler) = evalDist prefixSampler)
    (hlow : ∀ frequency ∈ lowFrequencies Index degree,
      |fourierCoefficient response frequency frequency| ≤
        Real.sqrt ((2 : ℝ) ^ (degree + 1) * affineBound))
    (hdiagonal :
      |aggregateAcceptance true response degree -
          aggregateAcceptance false response degree| ≤
        sigmaPlus + sigmaMinus +
          completeViewAggregateAdvantage keySampler plus minus)
    (hsource : completeViewZeroRowReductionAdvantage
      keySampler fakePrefixSampler plus minus ≤ sourceBound)
    (hendpoint : endpoint ≤ endpointBound)
    (hcover : ∀ key, probabilityMass keySampler key ≠ 0 →
      probabilityMass fakePrefixSampler key.1 ≠ 0)
    (hoptimized : ∀ prefixValue,
      probabilityMass fakePrefixSampler prefixValue =
        Real.sqrt (probabilityMass (leakageLaw keySampler Prod.fst) prefixValue) /
          halfRenyiNormalizer keySampler Prod.fst) :
    |diagonalMean response - independentMean response| + endpoint ≤
      lowFrequencyCount Index degree *
          Real.sqrt ((2 : ℝ) ^ (degree + 1) * affineBound) +
        aggregateNormalization Index degree *
          (sigmaPlus + sigmaMinus +
            Real.sqrt (2 * halfRenyiConcentration prefixSampler * sourceBound)) +
        endpointBound := by
  have haggregate := nativeCompleteViewAggregateGap_le_prefixMarginal
    keySampler prefixSampler fakePrefixSampler plus minus
    |aggregateAcceptance true response degree -
      aggregateAcceptance false response degree|
    sigmaPlus sigmaMinus sourceBound hmarginal hdiagonal hsource hcover hoptimized
  exact diagonalGap_add_endpoint_le response degree hdegree
    (Real.sqrt ((2 : ℝ) ^ (degree + 1) * affineBound))
    (sigmaPlus + sigmaMinus +
      Real.sqrt (2 * halfRenyiConcentration prefixSampler * sourceBound))
    endpoint endpointBound hlow haggregate hendpoint

/-! ## Extraction-based source obstruction -/

/-- Scalar form of the extraction attack.  If prefix extraction, suffix recovery from the native
KSK, and the real-row typicality test jointly give the stated lower acceptance bound, while a
uniform residual hits the typical set with mass `typicalRatio`, then the source advantage has the
lower bound from equation (32). -/
theorem extractionBasedSourceAdvantage_lowerBound
    (realAcceptance uniformAcceptance prefixFailure suffixFailure errorTail typicalRatio : ℝ)
    (hreal : 1 - prefixFailure - suffixFailure - errorTail ≤ realAcceptance)
    (huniform : uniformAcceptance = typicalRatio) :
    1 - prefixFailure - suffixFailure - errorTail - typicalRatio ≤
      |realAcceptance - uniformAcceptance| := by
  calc
    1 - prefixFailure - suffixFailure - errorTail - typicalRatio ≤
        realAcceptance - uniformAcceptance := by linarith
    _ ≤ |realAcceptance - uniformAcceptance| := le_abs_self _

end

end FormalProof4FHE.TFHE.NativeTRGSWCompleteViewAuxiliarySource
