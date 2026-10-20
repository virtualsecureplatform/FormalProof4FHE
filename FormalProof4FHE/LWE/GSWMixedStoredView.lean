/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.GSWStoredSecurityView

/-!
# The mixed quadratic endpoint is the actual public-key replacement endpoint

Uniform public masks and bodies split off from the real control masks. Explicit
index bijections establish the joint law; all control errors and the common key
are retained. This transport is not an ordinary-LWE hardness reduction.
-/

open Matrix OracleComp

namespace FormalProof4FHE.LWE.GSWMixedStoredView

open GSWGadget GSWAccumulator GSWPublicKey GSWSampling GSWStoredSecurityView

def shape {q : ℕ} (params : Parameters q) (n p : ℕ) :
    GSWBinaryRandomization.Shape n (errorCount params n p) :=
  GSWMixedRandomization.jointShape n params.levels p

def weight {q : ℕ} [NeZero q] (params : Parameters q) (n p : ℕ) :
    Fin (errorCount params n p) → ZMod q :=
  GSWMixedRandomization.jointWeight n params.levels p (TFHE.Gadget.Base.gadget params)

def replacement {q : ℕ} (params : Parameters q) (n p : ℕ) :
    Fin (errorCount params n p) → Bool :=
  GSWMixedRandomization.replacePublic n params.levels p

abbrev ControlMasks {q : ℕ} (params : Parameters q) (n : ℕ) :=
  Fin n → Matrix (Fin n) (Fin ((n + 1) * params.levels)) (ZMod q)
abbrev ControlBodies {q : ℕ} (params : Parameters q) (n : ℕ) :=
  Fin n → Fin ((n + 1) * params.levels) → ZMod q
abbrev Input {q : ℕ} (params : Parameters q) (n p : ℕ) :=
  (GSWMasking.Table q n p × ControlMasks params n) × ControlBodies params n

def mixedInputEquiv {q : ℕ} (params : Parameters q) (n p : ℕ) :
    (Challenge params n p × (Fin (errorCount params n p) → ZMod q)) ≃ Input params n p where
  toFun pair :=
    ((fun column ↦ Fin.cases (pair.2 (publicColumn params column))
      (fun row ↦ pair.1 row (publicColumn params column)),
      (maskEquiv params n p pair.1).2),
      fun index column ↦ pair.2 (controlColumn params index column))
  invFun input :=
    ((maskEquiv params n p).symm
      (fun row column ↦ input.1.1 column row.succ, input.1.2),
      Fin.addCases (fun column ↦ input.1.1 column 0)
        (fun column ↦ input.2 (finProdFinEquiv.symm column).1 (finProdFinEquiv.symm column).2))
  left_inv pair := by
    apply Prod.ext
    · change (maskEquiv params n p).symm (maskEquiv params n p pair.1) = pair.1
      exact (maskEquiv params n p).symm_apply_apply pair.1
    · funext column
      refine Fin.addCases (fun index ↦ ?_) (fun index ↦ ?_) column
      · simp [publicColumn]
      · simp only [Fin.addCases_right, controlColumn]
        change pair.2 (Fin.natAdd p (finProdFinEquiv (finProdFinEquiv.symm index))) = _
        rw [Equiv.apply_symm_apply]
  right_inv input := by
    apply Prod.ext
    · apply Prod.ext
      · funext column row
        cases row using Fin.cases <;> simp [maskEquiv, publicColumn]
      · change (maskEquiv params n p ((maskEquiv params n p).symm _)).2 = _
        rw [Equiv.apply_symm_apply]
    · funext index column
      simp only [controlColumn, Fin.addCases_right, Equiv.symm_apply_apply]

def mixedInputs {q n p : ℕ} [NeZero q] (params : Parameters q) :
    ProbComp (GSWMasking.Table q n p × ControlMasks params n) := do
  let challenge ← $ᵗ Challenge params n p
  let uniform ← $ᵗ (Fin (errorCount params n p) → ZMod q)
  return (mixedInputEquiv params n p (challenge, uniform)).1

/-- Public table and retained control masks are jointly independent uniform data. -/
theorem mixedInputs_uniform_evalDist {q n p : ℕ} [NeZero q] (params : Parameters q) :
    evalDist (mixedInputs (n := n) (p := p) params) =
      evalDist ($ᵗ (GSWMasking.Table q n p × ControlMasks params n)) := by
  have hproduct := FormalProof4FHE.FiniteProduct.evalDist_independent_uniform_product
    (first := Challenge params n p) (second := Fin (errorCount params n p) → ZMod q)
  have hmap := evalDist_map_bijective_uniform_cross
    (α := Challenge params n p × (Fin (errorCount params n p) → ZMod q))
    (β := Input params n p) (mixedInputEquiv params n p) (mixedInputEquiv params n p).bijective
  have h := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hproduct.symm
    (fun pair ↦ pure (mixedInputEquiv params n p pair).1)
  calc
    _ = evalDist (Prod.fst <$> (mixedInputEquiv params n p <$>
        ($ᵗ (Challenge params n p × (Fin (errorCount params n p) → ZMod q))))) := by
      simpa [mixedInputs, monad_norm] using h.symm
    _ = evalDist (Prod.fst <$> ($ᵗ Input params n p)) := by
      rw [evalDist_map, hmap, ← evalDist_map]
    _ = _ := evalDist_map_fst_uniformSample_prod

def idealInputs {q n p : ℕ} [NeZero q] (params : Parameters q) :
    ProbComp (GSWMasking.Table q n p × ControlMasks params n) := do
  let table ← $ᵗ GSWMasking.Table q n p
  let challenge ← $ᵗ Challenge params n p
  return (table, (maskEquiv params n p challenge).2)

theorem controlMasks_uniform_evalDist {q n p : ℕ} [NeZero q] (params : Parameters q) :
    evalDist ((fun challenge ↦ (maskEquiv params n p challenge).2) <$>
      ($ᵗ Challenge params n p)) = evalDist ($ᵗ ControlMasks params n) := by
  let equiv := (maskEquiv params n p).trans (Equiv.prodComm _ _)
  have h := evalDist_map_bijective_uniform_cross
    (α := Challenge params n p)
    (β := ControlMasks params n × Matrix (Fin n) (Fin p) (ZMod q)) equiv equiv.bijective
  calc
    _ = evalDist (Prod.fst <$> (equiv <$> ($ᵗ Challenge params n p))) := by
      simp [equiv, Functor.map_map]
    _ = evalDist (Prod.fst <$>
        ($ᵗ (ControlMasks params n × Matrix (Fin n) (Fin p) (ZMod q)))) := by
      rw [evalDist_map, h, ← evalDist_map]
    _ = _ := evalDist_map_fst_uniformSample_prod

theorem idealInputs_uniform_evalDist {q n p : ℕ} [NeZero q] (params : Parameters q) :
    evalDist (idealInputs (n := n) (p := p) params) =
      evalDist ($ᵗ (GSWMasking.Table q n p × ControlMasks params n)) := by
  have hproduct := FormalProof4FHE.FiniteProduct.evalDist_independent_uniform_product
    (first := GSWMasking.Table q n p) (second := ControlMasks params n)
  calc
    _ = evalDist (do
        let table ← $ᵗ GSWMasking.Table q n p
        let masks ← $ᵗ ControlMasks params n
        return (table, masks)) := by
      unfold idealInputs
      refine evalDist_bind_congr' ($ᵗ GSWMasking.Table q n p) fun table ↦ ?_
      simpa [monad_norm] using
        (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
          (controlMasks_uniform_evalDist (n := n) (p := p) params)
          (fun masks ↦ pure (table, masks)))
    _ = _ := hproduct

def finish {q n p : ℕ} [NeZero q] (params : Parameters q)
    (bits : Fin n → Bool) (errors : Fin (errorCount params n p) → ZMod q)
    (input : GSWMasking.Table q n p × ControlMasks params n) :
    GSWMasking.Table q n p × Vector (StoredCiphertext params (n + 1)) n :=
  (input.1, (normalizedKey params errors
    (bits, (maskEquiv params n p).symm (0, input.2))).1.2)

set_option backward.isDefEq.respectTransparency false in
/-- Control materialization depends on the retained control masks, never on public masks. -/
theorem realControls_eq_finish {q n p : ℕ} [NeZero q] (params : Parameters q)
    (bits : Fin n → Bool) (errors : Fin (errorCount params n p) → ZMod q)
    (challenge : Challenge params n p) (table : GSWMasking.Table q n p) :
    (storeTranscript params
      (challenge, vecMul (GSWSelfKey.binaryEmbed bits) challenge +
        GSWBinaryRandomization.signal (shape params n p)
          (weight params n p)
          (GSWSelfKey.binaryEmbed bits) + errors)).2 =
      (finish params bits errors (table, (maskEquiv params n p challenge).2)).2 := by
  simp only [finish, normalizedKey, GSWSelfKey.normalizedTranscript, jointPhase_eq_signal, shape, weight,
    storeTranscript]
  congr 1
  funext index
  congr 1
  ext row column
  cases row using Fin.cases <;>
    simp [-finProdFinEquiv_symm_apply, GSWOperations.ciphertextMatrix, maskEquiv,
      controlColumn, Pi.add_apply, vecMul, dotProduct]

set_option backward.isDefEq.respectTransparency false in
/-- The entire materialized mixed transcript factors through uniform public/control inputs. -/
theorem mixedTranscript_eq_finish {q n p : ℕ} [NeZero q] (params : Parameters q)
    (bits : Fin n → Bool) (errors uniform : Fin (errorCount params n p) → ZMod q)
    (challenge : Challenge params n p) :
    maskingView params (storeTranscript params
      (GSWMixedRandomization.mixedTranscript (shape params n p)
        (weight params n p)
        (replacement params n p)
        (GSWSelfKey.binaryEmbed bits) challenge errors uniform)) =
      finish params bits errors (mixedInputEquiv params n p (challenge, uniform)).1 := by
  apply Prod.ext
  · funext column row
    cases row using Fin.cases <;>
      simp [maskingView, storeTranscript, GSWMasking.tableOfPublicKey,
        GSWOperations.ciphertextMatrix, GSWMixedRandomization.mixedTranscript,
        publicColumn, replacement, GSWMixedRandomization.replacePublic, mixedInputEquiv, finish]
  · change _ = (finish params bits errors
      ((0 : GSWMasking.Table q n p), (maskEquiv params n p challenge).2)).2
    rw [← realControls_eq_finish params bits errors challenge (0 : GSWMasking.Table q n p)]
    simp only [maskingView, storeTranscript, GSWMixedRandomization.mixedTranscript]
    congr 1
    funext index
    congr 1
    ext row column
    cases row using Fin.cases <;>
      simp [GSWOperations.ciphertextMatrix, controlColumn, replacement, GSWMixedRandomization.replacePublic]

def fixedMixed {q n p : ℕ} [NeZero q] (params : Parameters q)
    (errorSampler : ProbComp (ZMod q)) (bits : Fin n → Bool) :
    ProbComp (GSWMasking.Table q n p × Vector (StoredCiphertext params (n + 1)) n) :=
  (fun transcript ↦ maskingView params (storeTranscript params transcript)) <$>
    GSWMixedRandomization.mixedView (shape params n p)
      (weight params n p)
      (replacement params n p)
      (ProbComp.sampleIID (errorCount params n p) errorSampler) bits

def fixedIdeal {q n p : ℕ} [NeZero q] (params : Parameters q)
    (errorSampler : ProbComp (ZMod q)) (bits : Fin n → Bool) :
    ProbComp (GSWMasking.Table q n p × Vector (StoredCiphertext params (n + 1)) n) :=
  GSWMasking.uniformView
    ((fun transcript ↦ maskingView params (storeTranscript params transcript)) <$>
      fixedRealView (n := n) (p := p) params errorSampler bits)

theorem fixedMixed_input_evalDist {q n p : ℕ} [NeZero q] (params : Parameters q)
    (errorSampler : ProbComp (ZMod q)) (bits : Fin n → Bool) :
    evalDist (fixedMixed (n := n) (p := p) params errorSampler bits) =
      evalDist (do
        let errors ← ProbComp.sampleIID (errorCount params n p) errorSampler
        let input ← mixedInputs (n := n) (p := p) params
        return finish params bits errors input) := by
  unfold fixedMixed GSWMixedRandomization.mixedView
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  simp_rw [mixedTranscript_eq_finish]
  simpa [mixedInputs, monad_norm] using
    (evalDist_bind_bind_swap ($ᵗ Challenge params n p)
      (ProbComp.sampleIID (errorCount params n p) errorSampler)
      (fun challenge errors ↦ do
        let uniform ← $ᵗ (Fin (errorCount params n p) → ZMod q)
        pure (finish params bits errors (mixedInputEquiv params n p (challenge, uniform)).1)))

set_option backward.isDefEq.respectTransparency false in
theorem fixedIdeal_input_evalDist {q n p : ℕ} [NeZero q] (params : Parameters q)
    (errorSampler : ProbComp (ZMod q)) (bits : Fin n → Bool) :
    evalDist (fixedIdeal (n := n) (p := p) params errorSampler bits) =
      evalDist (do
        let errors ← ProbComp.sampleIID (errorCount params n p) errorSampler
        let input ← idealInputs (n := n) (p := p) params
        return finish params bits errors input) := by
  unfold fixedIdeal GSWMasking.uniformView
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, maskingView]
  unfold fixedRealView GSWBinaryRandomization.realView
  simp only [bind_assoc, pure_bind]
  change evalDist (do
      let challenge ← $ᵗ Challenge params n p
      let errors ← ProbComp.sampleIID (errorCount params n p) errorSampler
      let table ← $ᵗ GSWMasking.Table q n p
      pure (table, (storeTranscript params
        (challenge, vecMul (GSWSelfKey.binaryEmbed bits) challenge +
          GSWBinaryRandomization.signal (shape params n p) (weight params n p)
            (GSWSelfKey.binaryEmbed bits) + errors)).2)) = _
  simp_rw [realControls_eq_finish params bits _ _ (0 : GSWMasking.Table q n p)]
  change evalDist (do
      let challenge ← $ᵗ Challenge params n p
      let errors ← ProbComp.sampleIID (errorCount params n p) errorSampler
      let table ← $ᵗ GSWMasking.Table q n p
      pure (finish params bits errors (table, (maskEquiv params n p challenge).2))) = _
  calc
    _ = evalDist (do
        let errors ← ProbComp.sampleIID (errorCount params n p) errorSampler
        let challenge ← $ᵗ Challenge params n p
        let table ← $ᵗ GSWMasking.Table q n p
        pure (finish params bits errors (table, (maskEquiv params n p challenge).2))) :=
      evalDist_bind_bind_swap _ _ _
    _ = _ := by
      refine evalDist_bind_congr' (ProbComp.sampleIID (errorCount params n p) errorSampler) fun errors ↦ ?_
      simpa [idealInputs, monad_norm] using
        (evalDist_bind_bind_swap ($ᵗ Challenge params n p) ($ᵗ GSWMasking.Table q n p)
          (fun challenge table ↦ pure (finish params bits errors (table, (maskEquiv params n p challenge).2))))

/-- Exact endpoint equality for each fixed key, hence for every shared-key context. -/
theorem fixedIdeal_mixed_evalDist {q n p : ℕ} [NeZero q] (params : Parameters q)
    (errorSampler : ProbComp (ZMod q)) (bits : Fin n → Bool) :
    evalDist (fixedIdeal (n := n) (p := p) params errorSampler bits) =
      evalDist (fixedMixed (n := n) (p := p) params errorSampler bits) := by
  rw [fixedIdeal_input_evalDist, fixedMixed_input_evalDist]
  refine evalDist_bind_congr' (ProbComp.sampleIID (errorCount params n p) errorSampler) fun errors ↦ ?_
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    ((idealInputs_uniform_evalDist params).trans (mixedInputs_uniform_evalDist params).symm) _

/-- The operational public-key-only replacement is the complete mixed quadratic sampler. -/
theorem operationalUniform_mixed_evalDist {q n p : ℕ} [NeZero q] (params : Parameters q)
    (errorSampler : ProbComp (ZMod q)) :
    evalDist (GSWMasking.uniformView
      (GSWMasking.operationalView (dimension := n) (samples := p) params errorSampler)) =
      evalDist (do
        let bits ← $ᵗ (Fin n → Bool)
        fixedMixed (n := n) (p := p) params errorSampler bits) := by
  rw [uniformView_normalized_evalDist]
  calc
    _ = evalDist (do
        let bits ← $ᵗ (Fin n → Bool)
        fixedIdeal (n := n) (p := p) params errorSampler bits) := by
      simp [GSWMasking.uniformView, normalizedView, fixedIdeal, monad_norm]
    _ = _ := evalDist_bind_congr' _ (fun bits ↦ fixedIdeal_mixed_evalDist params errorSampler bits)

/-- Read every public/control coefficient without receiving the secret or sampling coins. -/
def readView {q n p : ℕ} (params : Parameters q)
    (view : GSWMasking.Table q n p × Vector (StoredCiphertext params (n + 1)) n) :
    BatchTranscript (ZMod q) n (errorCount params n p) :=
  (fun row ↦ Fin.addCases (fun column ↦ view.1 column row.succ)
    (fun column ↦ ciphertextView params (view.2.get (finProdFinEquiv.symm column).1)
      row.succ (finProdFinEquiv.symm column).2),
    Fin.addCases (fun column ↦ view.1 column 0)
      (fun column ↦ ciphertextView params (view.2.get (finProdFinEquiv.symm column).1)
        0 (finProdFinEquiv.symm column).2))

/-- The reader recovers the whole transcript, including every retained control entry. -/
theorem readView_storeTranscript {q n p : ℕ} (params : Parameters q)
    (transcript : BatchTranscript (ZMod q) n (errorCount params n p)) :
    readView params (maskingView params (storeTranscript params transcript)) = transcript := by
  apply Prod.ext
  · funext row column
    refine Fin.addCases (fun index ↦ ?_) (fun index ↦ ?_) column
    · simp [readView, maskingView, storeTranscript, GSWMasking.tableOfPublicKey,
        GSWOperations.ciphertextMatrix, publicColumn]
    · simp [-finProdFinEquiv_symm_apply, readView, maskingView, storeTranscript,
        GSWOperations.ciphertextMatrix, controlColumn]
  · funext column
    refine Fin.addCases (fun index ↦ ?_) (fun index ↦ ?_) column
    · simp [readView, maskingView, storeTranscript, GSWMasking.tableOfPublicKey,
        GSWOperations.ciphertextMatrix, publicColumn]
    · simp [-finProdFinEquiv_symm_apply, readView, maskingView, storeTranscript,
        GSWOperations.ciphertextMatrix, controlColumn]

/-- A public transformation on the actual table and materialized control vector. -/
def storedFlip {q n p : ℕ} [NeZero q] (params : Parameters q) (mask : Fin n → Bool)
    (view : GSWMasking.Table q n p × Vector (StoredCiphertext params (n + 1)) n) :
    GSWMasking.Table q n p × Vector (StoredCiphertext params (n + 1)) n :=
  maskingView params (storeTranscript params
    (GSWBinaryRandomization.transformTranscript (shape params n p) (weight params n p)
      mask (readView params view)))

theorem storedFlip_storeTranscript {q n p : ℕ} [NeZero q] (params : Parameters q)
    (mask : Fin n → Bool) (transcript : BatchTranscript (ZMod q) n (errorCount params n p)) :
    storedFlip params mask (maskingView params (storeTranscript params transcript)) =
      maskingView params (storeTranscript params
        (GSWBinaryRandomization.transformTranscript (shape params n p) (weight params n p)
          mask transcript)) := by
  simp only [storedFlip, readView_storeTranscript]

/-- Exact stored mixed-endpoint retargeting, using only a public flip and the stored view. -/
theorem storedFlip_fixedMixed_evalDist {q n p : ℕ} [NeZero q] (params : Parameters q)
    (errorSampler : ProbComp (ZMod q))
    (symmetric : evalDist ((fun value : ZMod q ↦ -value) <$> errorSampler) = evalDist errorSampler)
    (mask bits : Fin n → Bool) :
    evalDist (storedFlip params mask <$> fixedMixed (n := n) (p := p) params errorSampler bits) =
      evalDist (fixedMixed params errorSampler (GSWBinaryRandomization.flip mask bits)) := by
  have h := GSWMixedRandomization.transformTranscript_mixedView_evalDist
    (shape params n p) (weight params n p) (replacement params n p) mask
    (ProbComp.sampleIID (errorCount params n p) errorSampler) bits
    (GSWBinaryRandomization.transformError_sampleIID_evalDist
      (shape params n p) mask errorSampler symmetric)
  have hpost := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq h
    (fun transcript ↦ pure (maskingView params (storeTranscript params transcript)))
  simpa [fixedMixed, monad_norm, storedFlip_storeTranscript] using hpost

/-- The same public map preserves the operational ideal endpoint for every fixed key. -/
theorem storedFlip_fixedIdeal_evalDist {q n p : ℕ} [NeZero q] (params : Parameters q)
    (errorSampler : ProbComp (ZMod q))
    (symmetric : evalDist ((fun value : ZMod q ↦ -value) <$> errorSampler) = evalDist errorSampler)
    (mask bits : Fin n → Bool) :
    evalDist (storedFlip params mask <$> fixedIdeal (n := n) (p := p) params errorSampler bits) =
      evalDist (fixedIdeal params errorSampler (GSWBinaryRandomization.flip mask bits)) := by
  calc
    _ = evalDist (storedFlip params mask <$> fixedMixed params errorSampler bits) := by
      rw [evalDist_map, fixedIdeal_mixed_evalDist, ← evalDist_map]
    _ = _ := (storedFlip_fixedMixed_evalDist params errorSampler symmetric mask bits).trans
      (fixedIdeal_mixed_evalDist params errorSampler (GSWBinaryRandomization.flip mask bits)).symm

/-- The public map retargets the actual materialized real view as well. -/
theorem storedFlip_fixedReal_evalDist {q n p : ℕ} [NeZero q] (params : Parameters q)
    (errorSampler : ProbComp (ZMod q))
    (symmetric : evalDist ((fun value : ZMod q ↦ -value) <$> errorSampler) = evalDist errorSampler)
    (mask bits : Fin n → Bool) :
    evalDist (storedFlip params mask <$>
      ((fun transcript ↦ maskingView params (storeTranscript params transcript)) <$>
        fixedRealView (n := n) (p := p) params errorSampler bits)) =
      evalDist ((fun transcript ↦ maskingView params (storeTranscript params transcript)) <$>
        fixedRealView params errorSampler (GSWBinaryRandomization.flip mask bits)) := by
  have h := GSWBinaryRandomization.transformTranscript_realView_evalDist
    (shape params n p) (weight params n p) mask
    (ProbComp.sampleIID (errorCount params n p) errorSampler) bits
    (GSWBinaryRandomization.transformError_sampleIID_evalDist
      (shape params n p) mask errorSampler symmetric)
  have hpost := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq h
    (fun transcript ↦ pure (maskingView params (storeTranscript params transcript)))
  simpa [fixedRealView, shape, weight, monad_norm, storedFlip_storeTranscript] using hpost

end FormalProof4FHE.LWE.GSWMixedStoredView
