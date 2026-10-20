/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.GSWBinaryRandomization

/-!
# Binary-key randomization with real controls and selected uniform bodies

The public-key-only hybrid retains the real quadratic controls. Its endpoint is
therefore a mixed transcript, rather than the fully uniform endpoint previously
checked in `GSWBinaryRandomization`. The same public bit-flip transformation
preserves this mixed endpoint exactly, under sign-invariance of the full error
tape. Masks, real rows and replaced rows are transported together.

This is an exact randomization ingredient. It does not construct the controls
from an ordinary-LWE challenge or establish hardness of the joint experiment.
-/

open Matrix OracleComp

namespace FormalProof4FHE.LWE.GSWMixedRandomization

open GSWBinaryRandomization

def mixedTranscript {R : Type} [CommRing R] {dimension samples : ℕ}
    (shape : Shape dimension samples) (weight : Fin samples → R)
    (replace : Fin samples → Bool) (secret : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin samples) R)
    (error uniform : Fin samples → R) : BatchTranscript R dimension samples :=
  (challenge, fun column ↦ if replace column then uniform column else
    (vecMul secret challenge + signal shape weight secret + error) column)

/-- Transport the independent uniform body tape, conditional on the old masks. -/
def transformUniform {R : Type} [CommRing R] {dimension samples : ℕ}
    (shape : Shape dimension samples) (weight : Fin samples → R)
    (mask : Fin dimension → Bool) (challenge : Matrix (Fin dimension) (Fin samples) R)
    (uniform : Fin samples → R) : Fin samples → R :=
  fun column ↦ rowSign (shape column) mask * uniform column +
    vecMul (maskEmbed mask) (transformChallenge shape weight mask challenge) column +
    signal shape weight (maskEmbed mask) column

def untransformUniform {R : Type} [CommRing R] {dimension samples : ℕ}
    (shape : Shape dimension samples) (weight : Fin samples → R)
    (mask : Fin dimension → Bool) (challenge : Matrix (Fin dimension) (Fin samples) R)
    (uniform : Fin samples → R) : Fin samples → R :=
  fun column ↦ rowSign (shape column) mask *
    (uniform column -
      vecMul (maskEmbed mask) (transformChallenge shape weight mask challenge) column -
      signal shape weight (maskEmbed mask) column)

theorem transformUniform_bijective {R : Type} [CommRing R] {dimension samples : ℕ}
    (shape : Shape dimension samples) (weight : Fin samples → R)
    (mask : Fin dimension → Bool) (challenge : Matrix (Fin dimension) (Fin samples) R) :
    Function.Bijective (transformUniform shape weight mask challenge) := by
  apply Function.bijective_iff_has_inverse.mpr
  refine ⟨untransformUniform shape weight mask challenge, ?_, ?_⟩
  · intro uniform
    funext column
    simp only [untransformUniform, transformUniform]
    have hsign := rowSign_sq (R := R) (shape column) mask
    linear_combination uniform column * hsign
  · intro uniform
    funext column
    simp only [untransformUniform, transformUniform]
    have hsign := rowSign_sq (R := R) (shape column) mask
    linear_combination
      (uniform column -
        vecMul (maskEmbed mask) (transformChallenge shape weight mask challenge) column -
        signal shape weight (maskEmbed mask) column) * hsign

/-- Pointwise transport keeps every selected real row and every uniform row. -/
theorem transformTranscript_mixed {R : Type} [CommRing R] {dimension samples : ℕ}
    (shape : Shape dimension samples) (weight : Fin samples → R)
    (replace : Fin samples → Bool) (mask : Fin dimension → Bool)
    (secret : Fin dimension → R) (challenge : Matrix (Fin dimension) (Fin samples) R)
    (error uniform : Fin samples → R) :
    transformTranscript shape weight mask
        (mixedTranscript shape weight replace secret challenge error uniform) =
      mixedTranscript shape weight replace (affineSecret mask secret)
        (transformChallenge shape weight mask challenge) (transformError shape mask error)
        (transformUniform shape weight mask challenge uniform) := by
  apply Prod.ext
  · rfl
  · funext column
    cases hreplace : replace column
    · have hreal := congrFun (congrArg Prod.snd
        (transformTranscript_real shape weight mask secret challenge error)) column
      simpa only [transformTranscript, mixedTranscript, hreplace, Bool.false_eq_true,
        ↓reduceIte] using hreal
    · simp [transformTranscript, mixedTranscript, transformUniform, hreplace]

def mixedView {R : Type} [CommRing R] [SampleableType R] {dimension samples : ℕ}
    (shape : Shape dimension samples) (weight : Fin samples → R)
    (replace : Fin samples → Bool) (errorSampler : ProbComp (Fin samples → R))
    (secret : Fin dimension → Bool) : ProbComp (BatchTranscript R dimension samples) := do
  let challenge ← $ᵗ Matrix (Fin dimension) (Fin samples) R
  let error ← errorSampler
  let uniform ← $ᵗ (Fin samples → R)
  return mixedTranscript shape weight replace (GSWSelfKey.binaryEmbed secret)
    challenge error uniform

/-- Exact mixed endpoint: the real rows share the flipped key, and replaced bodies
remain uniform jointly with all masks and real rows. -/
theorem transformTranscript_mixedView_evalDist {R : Type}
    [CommRing R] [Fintype R] [SampleableType R] {dimension samples : ℕ}
    (shape : Shape dimension samples) (weight : Fin samples → R)
    (replace : Fin samples → Bool) (mask : Fin dimension → Bool)
    (errorSampler : ProbComp (Fin samples → R)) (secret : Fin dimension → Bool)
    (symmetric : evalDist (transformError shape mask <$> errorSampler) = evalDist errorSampler) :
    evalDist (transformTranscript shape weight mask <$>
      mixedView shape weight replace errorSampler secret) =
      evalDist (mixedView shape weight replace errorSampler (flip mask secret)) := by
  let finish := fun challenge : Matrix (Fin dimension) (Fin samples) R ↦ do
    let error ← errorSampler
    let uniform ← $ᵗ (Fin samples → R)
    return mixedTranscript shape weight replace (GSWSelfKey.binaryEmbed (flip mask secret))
      challenge error uniform
  unfold mixedView
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  simp_rw [transformTranscript_mixed, ← binaryEmbed_flip]
  calc
    _ = evalDist (($ᵗ Matrix (Fin dimension) (Fin samples) R) >>= fun challenge ↦
        finish (transformChallenge shape weight mask challenge)) := by
      refine evalDist_bind_congr' ($ᵗ Matrix (Fin dimension) (Fin samples) R) fun challenge ↦ ?_
      let post := fun error : Fin samples → R ↦
        ($ᵗ (Fin samples → R)) >>= fun uniform ↦
        pure (mixedTranscript shape weight replace
          (GSWSelfKey.binaryEmbed (flip mask secret))
          (transformChallenge shape weight mask challenge) error uniform)
      calc
        _ = evalDist (errorSampler >>= fun error ↦ post (transformError shape mask error)) := by
          refine evalDist_bind_congr' errorSampler fun error ↦ ?_
          apply evalDist_ext
          intro output
          exact probOutput_bind_bijective_uniform_cross
            (α := Fin samples → R) (β := Fin samples → R)
            (transformUniform shape weight mask challenge)
            (transformUniform_bijective shape weight mask challenge)
            (fun uniform ↦ pure (mixedTranscript shape weight replace
              (GSWSelfKey.binaryEmbed (flip mask secret))
              (transformChallenge shape weight mask challenge)
              (transformError shape mask error) uniform)) output
        _ = evalDist ((transformError shape mask <$> errorSampler) >>= post) := by
          simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
        _ = _ := by
          change evalDist ((transformError shape mask <$> errorSampler) >>= post) =
            evalDist (errorSampler >>= post)
          simp only [evalDist_bind, symmetric]
    _ = _ := by
      apply evalDist_ext
      intro output
      exact probOutput_bind_bijective_uniform_cross
        (α := Matrix (Fin dimension) (Fin samples) R)
        (β := Matrix (Fin dimension) (Fin samples) R)
        (transformChallenge shape weight mask) (transformChallenge_bijective shape weight mask)
        finish output

/-- Ordinary public-key rows followed by every flattened self-key GSW column. -/
def jointShape (dimension digits publicSamples : ℕ) :
    Shape dimension (publicSamples + dimension * ((dimension + 1) * digits)) :=
  Fin.addCases (fun _ ↦ .zero) (selfKeyShape dimension digits)

def jointWeight {R : Type} [Zero R] [Neg R] (dimension digits publicSamples : ℕ)
    (gadget : Fin digits → R) :
    Fin (publicSamples + dimension * ((dimension + 1) * digits)) → R :=
  Fin.addCases (fun _ ↦ 0) (selfKeyWeight dimension digits gadget)

/-- Replace precisely the public-key bodies, retaining all real control columns. -/
def replacePublic (dimension digits publicSamples : ℕ) :
    Fin (publicSamples + dimension * ((dimension + 1) * digits)) → Bool :=
  Fin.addCases (fun _ ↦ true) (fun _ ↦ false)

theorem jointSignal_public {R : Type} [CommRing R] {dimension digits publicSamples : ℕ}
    (gadget : Fin digits → R) (secret : Fin dimension → R) (column : Fin publicSamples) :
    signal (jointShape dimension digits publicSamples)
      (jointWeight dimension digits publicSamples gadget) secret
      (Fin.castAdd (dimension * ((dimension + 1) * digits)) column) = 0 := by
  simp [signal, jointShape, jointWeight, monomialValue]

/-- Control phases are exactly the ordinary GSW self-key phases, including every weight. -/
theorem jointSignal_control {R : Type} [CommRing R] {dimension digits publicSamples : ℕ}
    (gadget : Fin digits → R) (secret : Fin dimension → R)
    (column : Fin (dimension * ((dimension + 1) * digits))) :
    signal (jointShape dimension digits publicSamples)
      (jointWeight dimension digits publicSamples gadget) secret (Fin.natAdd publicSamples column) =
      GSWSelfKey.phaseMessage (GSWSelfKey.selfKeyLayout dimension digits gadget) secret
        (GSWSelfKey.selfKeyMessages digits secret) column := by
  simpa [signal, jointShape, jointWeight] using
    congrFun (signal_selfKey_eq_phaseMessage gadget secret) column

theorem replacePublic_public (dimension digits publicSamples : ℕ) (column : Fin publicSamples) :
    replacePublic dimension digits publicSamples
      (Fin.castAdd (dimension * ((dimension + 1) * digits)) column) = true := by
  simp [replacePublic]

theorem replacePublic_control (dimension digits publicSamples : ℕ)
    (column : Fin (dimension * ((dimension + 1) * digits))) :
    replacePublic dimension digits publicSamples (Fin.natAdd publicSamples column) = false := by
  simp [replacePublic]

/-- The full real-control/uniform-public-key endpoint has exact public key-flip
randomization when scalar errors are symmetric and independently sampled. -/
theorem jointMixed_randomization_evalDist {R : Type}
    [CommRing R] [Fintype R] [SampleableType R] {dimension digits publicSamples : ℕ}
    (gadget : Fin digits → R) (errorSampler : ProbComp R)
    (symmetric : evalDist ((fun value : R ↦ -value) <$> errorSampler) = evalDist errorSampler)
    (mask secret : Fin dimension → Bool) :
    evalDist (transformTranscript (jointShape dimension digits publicSamples)
      (jointWeight dimension digits publicSamples gadget) mask <$>
      mixedView (jointShape dimension digits publicSamples)
        (jointWeight dimension digits publicSamples gadget)
        (replacePublic dimension digits publicSamples)
        (ProbComp.sampleIID (publicSamples + dimension * ((dimension + 1) * digits)) errorSampler)
        secret) =
      evalDist (mixedView (jointShape dimension digits publicSamples)
        (jointWeight dimension digits publicSamples gadget)
        (replacePublic dimension digits publicSamples)
        (ProbComp.sampleIID (publicSamples + dimension * ((dimension + 1) * digits)) errorSampler)
        (flip mask secret)) :=
  transformTranscript_mixedView_evalDist _ _ _ _ _ _
    (transformError_sampleIID_evalDist _ _ errorSampler symmetric)

end FormalProof4FHE.LWE.GSWMixedRandomization
