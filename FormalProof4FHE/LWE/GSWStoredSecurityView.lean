/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.GSWMixedRandomization
import FormalProof4FHE.LWE.GSWSampling
import FormalProof4FHE.LWE.GSWMasking

/-!
# Stored ordinary GSW keys and the complete normalized transcript

Reindex the actual public/control mask arrays into one transcript, and identify
its materialization with actual key generation. Normalization is a bijection of
private sampling coins; it is not a public ordinary-LWE challenge simulator.
-/

open Matrix OracleComp

namespace FormalProof4FHE.LWE.GSWStoredSecurityView

open GSWGadget GSWAccumulator GSWPublicKey GSWSampling

abbrev Challenge {q : ℕ} (params : Parameters q) (n p : ℕ) :=
  Matrix (Fin n) (Fin (errorCount params n p)) (ZMod q)
abbrev Seed {q : ℕ} (params : Parameters q) (n p : ℕ) :=
  (Fin n → Bool) × Challenge params n p
abbrev StoredView {q : ℕ} (params : Parameters q) (n p : ℕ) :=
  PublicKey q n p × Vector (StoredCiphertext params (n + 1)) n

def publicColumn {q : ℕ} (params : Parameters q) {n p : ℕ} (column : Fin p) :
    Fin (errorCount params n p) := Fin.castAdd (n * ((n + 1) * params.levels)) column

def controlColumn {q : ℕ} (params : Parameters q) {n p : ℕ} (index : Fin n)
    (column : Fin ((n + 1) * params.levels)) : Fin (errorCount params n p) :=
  Fin.natAdd p (finProdFinEquiv (index, column))

/-- Split/flatten masks by explicit index operations, without enumerating keys. -/
def maskEquiv {q : ℕ} (params : Parameters q) (n p : ℕ) : Challenge params n p ≃
    (Matrix (Fin n) (Fin p) (ZMod q) ×
      (Fin n → Matrix (Fin n) (Fin ((n + 1) * params.levels)) (ZMod q))) where
  toFun challenge :=
    (fun row column ↦ challenge row (publicColumn params column),
      fun index row column ↦ challenge row (controlColumn params index column))
  invFun pair := fun row ↦ Fin.addCases (pair.1 row)
    (fun column ↦ pair.2 (finProdFinEquiv.symm column).1 row (finProdFinEquiv.symm column).2)
  left_inv challenge := by
    funext row column
    refine Fin.addCases (fun index ↦ ?_) (fun index ↦ ?_) column
    · simp [publicColumn]
    · simp only [controlColumn, Fin.addCases_right]
      change challenge row (Fin.natAdd p (finProdFinEquiv (finProdFinEquiv.symm index))) = _
      rw [Equiv.apply_symm_apply]
  right_inv pair := by
    apply Prod.ext
    · funext row column
      simp [publicColumn]
    · funext index row column
      simp only [controlColumn, Fin.addCases_right]
      simp only [Equiv.symm_apply_apply]

def seedEquiv {q : ℕ} (params : Parameters q) (n p : ℕ) : KeySeed params n p ≃ Seed params n p :=
  Equiv.prodCongr (Equiv.refl _) (maskEquiv params n p).symm

def jointLayout {q : ℕ} [NeZero q] (params : Parameters q) (n p : ℕ) :
    GSWSelfKey.Layout (ZMod q) n (errorCount params n p) where
  coordinate := Fin.addCases (fun _ ↦ none)
    (GSWSelfKey.selfKeyLayout n params.levels (TFHE.Gadget.Base.gadget params)).coordinate
  weight := Fin.addCases (fun _ ↦ 0)
    (GSWSelfKey.selfKeyLayout n params.levels (TFHE.Gadget.Base.gadget params)).weight

def jointMessages {q : ℕ} (params : Parameters q) {n p : ℕ} (bits : Fin n → Bool) :
    Fin (errorCount params n p) → ZMod q :=
  Fin.addCases (fun _ ↦ 0) (GSWSelfKey.selfKeyMessages params.levels (GSWSelfKey.binaryEmbed bits))

def storeTranscript {q : ℕ} (params : Parameters q) {n p : ℕ}
    (transcript : BatchTranscript (ZMod q) n (errorCount params n p)) : StoredView params n p :=
  (storePublicKey (GSWOperations.ciphertextMatrix
    (fun row column ↦ transcript.1 row (publicColumn params column),
      fun column ↦ transcript.2 (publicColumn params column))),
    Vector.ofFn fun index ↦ storeCiphertext params (GSWOperations.ciphertextMatrix
      (fun row column ↦ transcript.1 row (controlColumn params index column),
        fun column ↦ transcript.2 (controlColumn params index column))))

def publicView {q : ℕ} {params : Parameters q} {n p : ℕ}
    (keys : KeyMaterial params n p) : StoredView params n p := (keys.publicKey, keys.controls)

set_option backward.isDefEq.respectTransparency false in
/-- Pointwise law of the actual materialized public key and every control. -/
theorem materialFromDraws_eq_storeFresh {q n p : ℕ} [NeZero q] (params : Parameters q)
    (draws : KeyDraws params n p) :
    publicView (materialFromDraws params draws) =
      storeTranscript params (GSWSelfKey.freshTranscript (jointLayout params n p)
        (GSWSelfKey.binaryEmbed draws.seed.1) (jointMessages params draws.seed.1)
        (seedEquiv params n p draws.seed).2 draws.errors) := by
  apply Prod.ext
  · simp only [publicView, materialFromDraws, freshPublicKey, storeTranscript]
    congr 1
    ext row column
    cases row using Fin.cases <;>
      simp [GSWOperations.ciphertextMatrix, GSWSelfKey.freshTranscript, Pi.add_apply,
        GSWSelfKey.maskShift, GSWSelfKey.bodyShift, jointLayout, jointMessages,
        publicColumn, seedEquiv, maskEquiv, publicErrors, vecMul, dotProduct]
  · simp only [publicView, materialFromDraws, storedFreshBootKey, storeTranscript]
    congr 1
    funext index
    congr 1
    ext row column
    cases row using Fin.cases <;>
      simp [-finProdFinEquiv_symm_apply, freshBootKey, GSWOperations.ciphertextMatrix,
        GSWSelfKey.freshTranscript, Pi.add_apply,
        GSWSelfKey.maskShift, GSWSelfKey.bodyShift, jointLayout, jointMessages,
        controlColumn, seedEquiv, maskEquiv, controlErrors, GSWSelfKey.selfKeyLayout,
        GSWSelfKey.selfKeyMessages, GSWSelfKey.selfKeyPosition, layout,
        GSWSelfKey.binaryEmbed, bitMessage, vecMul, dotProduct]

/-- A private-coin normalization, keeping the entire binary key and error law. -/
def normalizeSeedEquiv {q n p : ℕ} [NeZero q] (params : Parameters q) : Seed params n p ≃ Seed params n p where
  toFun seed := (seed.1, seed.2 + GSWSelfKey.maskShift (jointLayout params n p)
    (jointMessages params seed.1))
  invFun seed := (seed.1, seed.2 - GSWSelfKey.maskShift (jointLayout params n p)
    (jointMessages params seed.1))
  left_inv seed := by simp
  right_inv seed := by simp

def normalizedSeedEquiv {q n p : ℕ} [NeZero q] (params : Parameters q) :
    KeySeed params n p ≃ Seed params n p :=
  (seedEquiv params n p).trans (normalizeSeedEquiv params)

def normalizedKey {q n p : ℕ} [NeZero q] (params : Parameters q)
    (errors : Fin (errorCount params n p) → ZMod q) (seed : Seed params n p) :
    StoredView params n p × (Fin n → Bool) :=
  (storeTranscript params (GSWSelfKey.normalizedTranscript (jointLayout params n p)
    (GSWSelfKey.binaryEmbed seed.1) (jointMessages params seed.1) seed.2 errors), seed.1)

/-- Pointwise identity includes the retained private key, not only public marginals. -/
theorem materialFromDraws_eq_normalizedKey {q n p : ℕ} [NeZero q] (params : Parameters q)
    (draws : KeyDraws params n p) :
    (publicView (materialFromDraws params draws), (materialFromDraws params draws).secretBits) =
      normalizedKey params draws.errors (normalizedSeedEquiv params draws.seed) := by
  rw [materialFromDraws_eq_storeFresh, GSWSelfKey.freshTranscript_eq_normalized]
  rfl

def keygen {q n p : ℕ} [NeZero q] (params : Parameters q) (errorSampler : ProbComp (ZMod q)) :
    ProbComp (StoredView params n p × (Fin n → Bool)) :=
  (fun keys ↦ (publicView keys, keys.secretBits)) <$> generateKeys params n p errorSampler

def normalizedKeygen {q n p : ℕ} [NeZero q] (params : Parameters q)
    (errorSampler : ProbComp (ZMod q)) : ProbComp (StoredView params n p × (Fin n → Bool)) := do
  let errors ← ProbComp.sampleIID (errorCount params n p) errorSampler
  let seed ← $ᵗ Seed params n p
  return normalizedKey params errors seed

/-- Actual stored keygen equals the normalized sampler, with all shared-key correlations. -/
theorem keygen_normalized_evalDist {q n p : ℕ} [NeZero q] (params : Parameters q)
    (errorSampler : ProbComp (ZMod q)) :
    evalDist (keygen (n := n) (p := p) params errorSampler) =
      evalDist (normalizedKeygen (n := n) (p := p) params errorSampler) := by
  unfold keygen generateKeys sampleKeyDraws normalizedKeygen
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  refine evalDist_bind_congr' (ProbComp.sampleIID (errorCount params n p) errorSampler) fun errors ↦ ?_
  simp_rw [materialFromDraws_eq_normalizedKey]
  apply evalDist_ext
  intro output
  exact probOutput_bind_bijective_uniform_cross
    (α := KeySeed params n p) (β := Seed params n p)
    (normalizedSeedEquiv params) (normalizedSeedEquiv params).bijective
    (fun seed ↦ pure (normalizedKey params errors seed)) output

theorem jointPhase_eq_signal {q n p : ℕ} [NeZero q] (params : Parameters q)
    (bits : Fin n → Bool) :
    GSWSelfKey.phaseMessage (jointLayout params n p) (GSWSelfKey.binaryEmbed bits)
      (jointMessages params bits) =
      GSWBinaryRandomization.signal (GSWMixedRandomization.jointShape n params.levels p)
        (GSWMixedRandomization.jointWeight n params.levels p (TFHE.Gadget.Base.gadget params))
        (GSWSelfKey.binaryEmbed bits) := by
  funext column
  refine Fin.addCases (fun index ↦ ?_) (fun index ↦ ?_) column
  · simp [GSWSelfKey.phaseMessage, jointLayout, jointMessages,
      GSWBinaryRandomization.signal, GSWMixedRandomization.jointShape,
      GSWMixedRandomization.jointWeight, GSWBinaryRandomization.monomialValue]
  · rw [GSWMixedRandomization.jointSignal_control]
    simp only [GSWSelfKey.phaseMessage, jointLayout, jointMessages, Fin.addCases_right]

def fixedRealView {q n p : ℕ} [NeZero q] (params : Parameters q)
    (errorSampler : ProbComp (ZMod q)) (bits : Fin n → Bool) :
    ProbComp (BatchTranscript (ZMod q) n (errorCount params n p)) :=
  GSWBinaryRandomization.realView (GSWMixedRandomization.jointShape n params.levels p)
    (GSWMixedRandomization.jointWeight n params.levels p (TFHE.Gadget.Base.gadget params))
    (ProbComp.sampleIID (errorCount params n p) errorSampler) bits

/-- Actual stored keygen is exactly the complete quadratic real-view experiment,
including the retained secret and all scalar errors. -/
theorem keygen_realView_evalDist {q n p : ℕ} [NeZero q] (params : Parameters q)
    (errorSampler : ProbComp (ZMod q)) :
    evalDist (keygen (n := n) (p := p) params errorSampler) =
      evalDist (do
        let bits ← $ᵗ (Fin n → Bool)
        let transcript ← fixedRealView (n := n) (p := p) params errorSampler bits
        return (storeTranscript params transcript, bits)) := by
  rw [keygen_normalized_evalDist]
  let finish : (Fin (errorCount params n p) → ZMod q) → (Fin n → Bool) →
      Challenge params n p → ProbComp (StoredView params n p × (Fin n → Bool)) :=
    fun errors bits challenge ↦ pure (normalizedKey params errors (bits, challenge))
  have hproduct := FormalProof4FHE.FiniteProduct.evalDist_independent_uniform_product
    (first := Fin n → Bool) (second := Challenge params n p)
  calc
    _ = evalDist (do
        let errors ← ProbComp.sampleIID (errorCount params n p) errorSampler
        let bits ← $ᵗ (Fin n → Bool)
        let challenge ← $ᵗ Challenge params n p
        finish errors bits challenge) := by
      unfold normalizedKeygen
      refine evalDist_bind_congr' (ProbComp.sampleIID (errorCount params n p) errorSampler) fun errors ↦ ?_
      simpa [finish, monad_norm] using
        (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hproduct.symm
          (fun seed ↦ pure (normalizedKey params errors seed)))
    _ = evalDist (do
        let bits ← $ᵗ (Fin n → Bool)
        let errors ← ProbComp.sampleIID (errorCount params n p) errorSampler
        let challenge ← $ᵗ Challenge params n p
        finish errors bits challenge) :=
      evalDist_bind_bind_swap _ _ _
    _ = evalDist (do
        let bits ← $ᵗ (Fin n → Bool)
        let challenge ← $ᵗ Challenge params n p
        let errors ← ProbComp.sampleIID (errorCount params n p) errorSampler
        finish errors bits challenge) := by
      refine evalDist_bind_congr' ($ᵗ (Fin n → Bool)) fun bits ↦ ?_
      exact evalDist_bind_bind_swap _ _ _
    _ = _ := by
      simp only [finish, normalizedKey, GSWSelfKey.normalizedTranscript, jointPhase_eq_signal,
        fixedRealView, GSWBinaryRandomization.realView, bind_assoc, pure_bind]
      rfl

def maskingView {q n p : ℕ} (params : Parameters q) (view : StoredView params n p) :
    GSWMasking.Table q n p × Vector (StoredCiphertext params (n + 1)) n :=
  (GSWMasking.tableOfPublicKey view.1, view.2)

def normalizedView {q n p : ℕ} [NeZero q] (params : Parameters q)
    (errorSampler : ProbComp (ZMod q)) :
    ProbComp (GSWMasking.Table q n p × Vector (StoredCiphertext params (n + 1)) n) := do
  let bits ← $ᵗ (Fin n → Bool)
  let transcript ← fixedRealView (n := n) (p := p) params errorSampler bits
  return maskingView params (storeTranscript params transcript)

/-- The full adversary view, after forgetting only the client's private key. -/
theorem operationalView_normalized_evalDist {q n p : ℕ} [NeZero q] (params : Parameters q)
    (errorSampler : ProbComp (ZMod q)) :
    evalDist (GSWMasking.operationalView (dimension := n) (samples := p) params errorSampler) =
      evalDist (normalizedView (n := n) (p := p) params errorSampler) := by
  have h := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (keygen_realView_evalDist (n := n) (p := p) params errorSampler)
    (fun pair ↦ pure (maskingView params pair.1))
  simpa [GSWMasking.operationalView, keygen, publicView, normalizedView, maskingView,
    monad_norm] using h

/-- Both joint-hop endpoints agree, with the real control marginal retained. -/
theorem uniformView_normalized_evalDist {q n p : ℕ} [NeZero q] (params : Parameters q)
    (errorSampler : ProbComp (ZMod q)) :
    evalDist (GSWMasking.uniformView
      (GSWMasking.operationalView (dimension := n) (samples := p) params errorSampler)) =
      evalDist (GSWMasking.uniformView (normalizedView (n := n) (p := p) params errorSampler)) := by
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (operationalView_normalized_evalDist params errorSampler) _

def transcriptObserver {q n p : ℕ} [NeZero q] (params : Parameters q)
    (adversary : GSWMasking.Adversary (dimension := n) (samples := p) params
      (Vector (StoredCiphertext params (n + 1)) n))
    (transcript : BatchTranscript (ZMod q) n (errorCount params n p)) : ProbComp Bool :=
  GSWMasking.game params (pure (maskingView params (storeTranscript params transcript))) adversary

/-- The normalized observer runs exactly the operational encryptInputs challenge game. -/
theorem operationalGame_normalized_evalDist {q n p : ℕ} [NeZero q] (params : Parameters q)
    (errorSampler : ProbComp (ZMod q))
    (adversary : GSWMasking.Adversary (dimension := n) (samples := p) params
      (Vector (StoredCiphertext params (n + 1)) n)) :
    evalDist (GSWMasking.operationalGame params errorSampler adversary) =
      evalDist (do
        let bits ← $ᵗ (Fin n → Bool)
        let transcript ← fixedRealView (n := n) (p := p) params errorSampler bits
        transcriptObserver params adversary transcript) := by
  rw [GSWMasking.evalDist_operationalGame_eq_game]
  have h := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (operationalView_normalized_evalDist (n := n) (p := p) params errorSampler)
    (fun view ↦ GSWMasking.game params (pure view) adversary)
  simpa [normalizedView, transcriptObserver, GSWMasking.game, monad_norm] using h

/-- Exact computational-gap transport. This equality asserts no negligible bound. -/
theorem keyReplacementAdvantage_normalized {q n p : ℕ} [NeZero q] (params : Parameters q)
    (errorSampler : ProbComp (ZMod q))
    (adversary : GSWMasking.Adversary (dimension := n) (samples := p) params
      (Vector (StoredCiphertext params (n + 1)) n)) :
    GSWMasking.keyReplacementAdvantage params
      (GSWMasking.operationalView params errorSampler) adversary =
      GSWMasking.keyReplacementAdvantage params
        (normalizedView params errorSampler) adversary := by
  have hreal := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (operationalView_normalized_evalDist (n := n) (p := p) params errorSampler)
    (fun view ↦ GSWMasking.game params (pure view) adversary)
  have hideal := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (uniformView_normalized_evalDist (n := n) (p := p) params errorSampler)
    (fun view ↦ GSWMasking.game params (pure view) adversary)
  simp only [GSWMasking.game, pure_bind] at hreal hideal
  unfold GSWMasking.keyReplacementAdvantage GSWMasking.game
  rw [probOutput_congr (rfl : true = true) hreal,
    probOutput_congr (rfl : true = true) hideal]

end FormalProof4FHE.LWE.GSWStoredSecurityView
