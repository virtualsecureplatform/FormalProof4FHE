/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.FiniteProduct
import FormalProof4FHE.TFHE.AdaptiveEncryptionSecurity

/-!
# Statistical Replacement of TFHE Error Samplers

The native finite-modulus TFHE games use executable `ProbComp` error samplers.  This file makes
the modelling loss between two such samplers explicit.  Replacing a one-draw sampler at total
variation distance `δ` in an independent batch of `m` draws costs at most `m * δ`; deterministic
encryption assembly and arbitrary adversarial postprocessing cannot increase that distance.

The final theorem counts every error draw in a query-bounded adaptive TFHE execution:

* `lweDimension * TGSW.rowCount ringRank tgswLevels` ring errors in the bootstrapping key;
* `(ringRank * degree) * keySwitchLevels` scalar errors in the key-switch key; and
* `queryCount` scalar errors in the eager adaptive encryption tape.

This is a bridge between two finite executable samplers.  In particular, it does not identify an
ideal continuous-torus Gaussian with a finite sampler; a truncation/discretization construction
must separately establish the relevant one-draw total-variation bounds.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.SamplerReplacement

/-- Sequentially sample two independent components and combine them deterministically. -/
def independentPair {A B C : Type}
    (samplerA : ProbComp A) (samplerB : ProbComp B) (combine : A → B → C) :
    ProbComp C :=
  samplerA >>= fun a ↦ combine a <$> samplerB

/-- Independent replacement in two sequentially sampled components.  This small hybrid lemma is
used to account for the bootstrapping and key-switch parts of a cloud key separately. -/
theorem tvDist_independentPair_le {A B C : Type}
    (leftA rightA : ProbComp A) (leftB rightB : ProbComp B)
    (combine : A → B → C) :
    tvDist (independentPair leftA leftB combine)
        (independentPair rightA rightB combine) ≤
      tvDist leftA rightA + tvDist leftB rightB := by
  let middle : ProbComp C := independentPair rightA leftB combine
  calc
    tvDist (independentPair leftA leftB combine)
        (independentPair rightA rightB combine) ≤
      tvDist (independentPair leftA leftB combine) middle +
        tvDist middle (independentPair rightA rightB combine) :=
      tvDist_triangle _ _ _
    _ ≤ tvDist leftA rightA + tvDist leftB rightB := by
      apply add_le_add
      · unfold middle
        exact tvDist_bind_right_le (fun a ↦ combine a <$> leftB) leftA rightA
      · unfold middle
        exact tvDist_bind_left_le_const' (m := ProbComp) rightA
          (fun a ↦ combine a <$> leftB)
          (fun a ↦ combine a <$> rightB)
          (tvDist leftB rightB)
          (fun a ↦ tvDist_map_le (m := ProbComp) (combine a) leftB rightB)

/-- Replace a sampled input and then replace its continuation with a uniform per-input bound. -/
theorem tvDist_bind_le_add {A B : Type}
    (left right : ProbComp A) (leftCont rightCont : A → ProbComp B) (bound : ℝ)
    (hCont : ∀ value, tvDist (leftCont value) (rightCont value) ≤ bound) :
    tvDist (left >>= leftCont) (right >>= rightCont) ≤
      tvDist left right + bound := by
  calc
    tvDist (left >>= leftCont) (right >>= rightCont) ≤
        tvDist (left >>= leftCont) (right >>= leftCont) +
          tvDist (right >>= leftCont) (right >>= rightCont) :=
      tvDist_triangle _ _ _
    _ ≤ tvDist left right + bound :=
      add_le_add (tvDist_bind_right_le leftCont left right)
        (tvDist_bind_left_le_const' (m := ProbComp) right leftCont rightCont bound hCont)

/-- Replacing the sampler in `count` independent draws costs at most `count` times the one-draw
total-variation distance. -/
theorem tvDist_sampleIID_le {R : Type} [Finite R]
    (count : ℕ) (left right : ProbComp R) :
    tvDist (ProbComp.sampleIID count left) (ProbComp.sampleIID count right) ≤
      (count : ℝ) * tvDist left right := by
  simpa [ProbComp.sampleIID] using
    (FormalProof4FHE.FiniteProduct.tvDist_fin_mOfFn_le_sum count
      (fun _ ↦ left) (fun _ ↦ right))

/-- Fixed-message TLWE batch encryption inherits exactly the independent-error replacement
bound.  The shared public uniform challenge and deterministic assembly add no loss. -/
theorem tvDist_batchEncrypt_le {R : Type}
    [Semiring R] [Finite R] [DecidableEq R] [SampleableType R]
    (dimension samples : ℕ) (left right : ProbComp R)
    (secret : Fin dimension → R) (message : Fin samples → R) :
    tvDist
        (TLWE.batchEncrypt dimension samples left secret message)
        (TLWE.batchEncrypt dimension samples right secret message) ≤
      (samples : ℝ) * tvDist left right := by
  unfold TLWE.batchEncrypt
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using
    (tvDist_bind_left_le_const' (m := ProbComp)
      ($ᵗ Matrix (Fin dimension) (Fin samples) R)
      (fun challenge ↦
        (fun error ↦ TLWE.batchAssemble secret challenge message error) <$>
          ProbComp.sampleIID samples left)
      (fun challenge ↦
        (fun error ↦ TLWE.batchAssemble secret challenge message error) <$>
          ProbComp.sampleIID samples right)
      ((samples : ℝ) * tvDist left right)
      (fun challenge ↦
        (tvDist_map_le (m := ProbComp)
          (fun error ↦ TLWE.batchAssemble secret challenge message error)
          (ProbComp.sampleIID samples left)
          (ProbComp.sampleIID samples right)).trans
            (tvDist_sampleIID_le samples left right)))

/-- A native TGSW ciphertext uses `rowCount dimension levels` independent ring-error draws; the
deterministic gadget shift does not increase total variation. -/
theorem tvDist_tgswEncrypt_le {R : Type}
    [Semiring R] [Finite R] [DecidableEq R] [SampleableType R]
    (dimension levels : ℕ) (left right : ProbComp R)
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R) :
    tvDist
        (TGSW.encrypt dimension levels left secret gadget message)
        (TGSW.encrypt dimension levels right secret gadget message) ≤
      (TGSW.rowCount dimension levels : ℝ) * tvDist left right := by
  unfold TGSW.encrypt
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using
    ((tvDist_map_le (m := ProbComp) (TGSW.addGadget gadget message)
      (TLWE.batchEncrypt dimension (TGSW.rowCount dimension levels) left secret 0)
      (TLWE.batchEncrypt dimension (TGSW.rowCount dimension levels) right secret 0)).trans
        (tvDist_batchEncrypt_le dimension (TGSW.rowCount dimension levels)
          left right secret 0))

/-- Zero-message TGSW encryption has the same sampler-replacement cost. -/
theorem tvDist_tgswEncryptZero_le {R : Type}
    [Semiring R] [Finite R] [DecidableEq R] [SampleableType R]
    (dimension levels : ℕ) (left right : ProbComp R)
    (secret : Fin dimension → R) (gadget : Fin levels → R) :
    tvDist
        (TGSW.encryptZero dimension levels left secret gadget)
        (TGSW.encryptZero dimension levels right secret gadget) ≤
      (TGSW.rowCount dimension levels : ℝ) * tvDist left right := by
  exact tvDist_tgswEncrypt_le dimension levels left right secret gadget 0

/-! ## Native evaluation-key components -/

/-- Number of ring-error draws in a native bootstrapping key. -/
abbrev bootstrappingErrorCount
    (ringRank tgswLevels lweDimension : ℕ) : ℕ :=
  lweDimension * TGSW.rowCount ringRank tgswLevels

/-- Number of scalar-error draws in a native key-switch key. -/
abbrev keySwitchErrorCount
    (ringRank degree keySwitchLevels : ℕ) : ℕ :=
  (ringRank * degree) * keySwitchLevels

/-- Replacing the ring-error sampler in a real native bootstrapping key pays once for every
TGSW row in every scalar-secret coordinate. -/
theorem tvDist_generateBootstrappingKey_le
    (q degree ringRank tgswLevels lweDimension : ℕ) [NeZero q]
    (left right : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree) :
    tvDist
        (Native.generateBootstrappingKey q degree ringRank tgswLevels lweDimension
          left gadget lweSecret ringSecret)
        (Native.generateBootstrappingKey q degree ringRank tgswLevels lweDimension
          right gadget lweSecret ringSecret) ≤
      (bootstrappingErrorCount ringRank tgswLevels lweDimension : ℝ) *
        tvDist left right := by
  unfold Native.generateBootstrappingKey
  calc
    tvDist
        (Fin.mOfFn lweDimension fun coordinate ↦
          TGSW.encrypt ringRank tgswLevels left
            (embedRingSecret q ringSecret) gadget
            (embedConstantBit q degree (lweSecret coordinate)))
        (Fin.mOfFn lweDimension fun coordinate ↦
          TGSW.encrypt ringRank tgswLevels right
            (embedRingSecret q ringSecret) gadget
            (embedConstantBit q degree (lweSecret coordinate))) ≤
      ∑ coordinate,
        tvDist
          (TGSW.encrypt ringRank tgswLevels left
            (embedRingSecret q ringSecret) gadget
            (embedConstantBit q degree (lweSecret coordinate)))
          (TGSW.encrypt ringRank tgswLevels right
            (embedRingSecret q ringSecret) gadget
            (embedConstantBit q degree (lweSecret coordinate))) :=
      FormalProof4FHE.FiniteProduct.tvDist_fin_mOfFn_le_sum lweDimension _ _
    _ ≤ ∑ _ : Fin lweDimension,
        (TGSW.rowCount ringRank tgswLevels : ℝ) * tvDist left right := by
      exact Finset.sum_le_sum fun coordinate _ ↦
        tvDist_tgswEncrypt_le ringRank tgswLevels left right
          (embedRingSecret q ringSecret) gadget
          (embedConstantBit q degree (lweSecret coordinate))
    _ = (bootstrappingErrorCount ringRank tgswLevels lweDimension : ℝ) *
        tvDist left right := by
      simp [bootstrappingErrorCount, Nat.cast_mul, mul_assoc]

/-- The zero-message bootstrapping-key generator has the same replacement bound. -/
theorem tvDist_generateZeroBootstrappingKey_le
    (q degree ringRank tgswLevels lweDimension : ℕ) [NeZero q]
    (left right : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (ringSecret : RingBinarySecret ringRank degree) :
    tvDist
        (Native.generateZeroBootstrappingKey q degree ringRank tgswLevels lweDimension
          left gadget ringSecret)
        (Native.generateZeroBootstrappingKey q degree ringRank tgswLevels lweDimension
          right gadget ringSecret) ≤
      (bootstrappingErrorCount ringRank tgswLevels lweDimension : ℝ) *
        tvDist left right := by
  unfold Native.generateZeroBootstrappingKey
  calc
    tvDist
        (Fin.mOfFn lweDimension fun _ ↦
          TGSW.encryptZero ringRank tgswLevels left
            (embedRingSecret q ringSecret) gadget)
        (Fin.mOfFn lweDimension fun _ ↦
          TGSW.encryptZero ringRank tgswLevels right
            (embedRingSecret q ringSecret) gadget) ≤
      ∑ _ : Fin lweDimension,
        tvDist
          (TGSW.encryptZero ringRank tgswLevels left
            (embedRingSecret q ringSecret) gadget)
          (TGSW.encryptZero ringRank tgswLevels right
            (embedRingSecret q ringSecret) gadget) :=
      FormalProof4FHE.FiniteProduct.tvDist_fin_mOfFn_le_sum lweDimension _ _
    _ ≤ ∑ _ : Fin lweDimension,
        (TGSW.rowCount ringRank tgswLevels : ℝ) * tvDist left right := by
      exact Finset.sum_le_sum fun _ _ ↦
        tvDist_tgswEncryptZero_le ringRank tgswLevels left right
          (embedRingSecret q ringSecret) gadget
    _ = (bootstrappingErrorCount ringRank tgswLevels lweDimension : ℝ) *
        tvDist left right := by
      simp [bootstrappingErrorCount, Nat.cast_mul, mul_assoc]

/-- Replacing the scalar-error sampler in a native key-switch key pays once for each flattened
source-coordinate/gadget-level row. -/
theorem tvDist_generateKeySwitchKey_le
    (q targetDimension sourceDimension keySwitchLevels : ℕ) [NeZero q]
    (left right : ProbComp (ZMod q))
    (gadget : Fin keySwitchLevels → ZMod q)
    (sourceSecret : BinarySecret sourceDimension)
    (targetSecret : BinarySecret targetDimension) :
    tvDist
        (Native.generateKeySwitchKey q targetDimension sourceDimension keySwitchLevels
          left gadget sourceSecret targetSecret)
        (Native.generateKeySwitchKey q targetDimension sourceDimension keySwitchLevels
          right gadget sourceSecret targetSecret) ≤
      (sourceDimension * keySwitchLevels : ℕ) * tvDist left right := by
  exact tvDist_batchEncrypt_le targetDimension (sourceDimension * keySwitchLevels)
    left right (embedBinarySecret targetSecret)
    (Native.keySwitchMessages sourceDimension keySwitchLevels gadget sourceSecret)

/-- The zero-message key-switch-key generator has the same replacement bound. -/
theorem tvDist_generateZeroKeySwitchKey_le
    (q targetDimension sourceDimension keySwitchLevels : ℕ) [NeZero q]
    (left right : ProbComp (ZMod q))
    (targetSecret : BinarySecret targetDimension) :
    tvDist
        (Native.generateZeroKeySwitchKey q targetDimension sourceDimension keySwitchLevels
          left targetSecret)
        (Native.generateZeroKeySwitchKey q targetDimension sourceDimension keySwitchLevels
          right targetSecret) ≤
      (sourceDimension * keySwitchLevels : ℕ) * tvDist left right := by
  exact tvDist_batchEncrypt_le targetDimension (sourceDimension * keySwitchLevels)
    left right (embedBinarySecret targetSecret) 0

/-- Replacing both error samplers in a real native cloud key costs the sum of the two component
bounds.  The two key components are conditionally independent once the secrets are fixed. -/
theorem tvDist_generateCloudKey_le
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringLeft ringRight : ProbComp (RLWE.Rq q degree))
    (scalarLeft scalarRight : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree) :
    tvDist
        (Native.generateCloudKey q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringLeft scalarLeft tgswGadget keySwitchGadget lweSecret ringSecret)
        (Native.generateCloudKey q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringRight scalarRight tgswGadget keySwitchGadget lweSecret ringSecret) ≤
      (bootstrappingErrorCount ringRank tgswLevels lweDimension : ℝ) *
          tvDist ringLeft ringRight +
        (keySwitchErrorCount ringRank degree keySwitchLevels : ℝ) *
          tvDist scalarLeft scalarRight := by
  let leftBootstrap :=
    Native.generateBootstrappingKey q degree ringRank tgswLevels lweDimension
      ringLeft tgswGadget lweSecret ringSecret
  let rightBootstrap :=
    Native.generateBootstrappingKey q degree ringRank tgswLevels lweDimension
      ringRight tgswGadget lweSecret ringSecret
  let leftSwitch :=
    Native.generateKeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels
      scalarLeft keySwitchGadget (keyExtract ringSecret) lweSecret
  let rightSwitch :=
    Native.generateKeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels
      scalarRight keySwitchGadget (keyExtract ringSecret) lweSecret
  let combine := fun bootstrapKey switchKey ↦
    (Native.CloudKey.mk bootstrapKey switchKey :
      Native.CloudKey q degree ringRank tgswLevels lweDimension keySwitchLevels)
  have hPair := tvDist_independentPair_le
    leftBootstrap rightBootstrap leftSwitch rightSwitch combine
  have hBootstrap : tvDist leftBootstrap rightBootstrap ≤
      (bootstrappingErrorCount ringRank tgswLevels lweDimension : ℝ) *
        tvDist ringLeft ringRight := by
    exact tvDist_generateBootstrappingKey_le q degree ringRank tgswLevels lweDimension
      ringLeft ringRight tgswGadget lweSecret ringSecret
  have hSwitch : tvDist leftSwitch rightSwitch ≤
      (keySwitchErrorCount ringRank degree keySwitchLevels : ℝ) *
        tvDist scalarLeft scalarRight := by
    simpa [leftSwitch, rightSwitch, keySwitchErrorCount] using
      (tvDist_generateKeySwitchKey_le q lweDimension (ringRank * degree) keySwitchLevels
        scalarLeft scalarRight keySwitchGadget (keyExtract ringSecret) lweSecret)
  simpa only [Native.generateCloudKey, independentPair, leftBootstrap, rightBootstrap,
    leftSwitch, rightSwitch, combine, map_eq_bind_pure_comp, Function.comp_def] using
      hPair.trans (add_le_add hBootstrap hSwitch)

/-- The all-zero-message cloud-key generator obeys the same two-sampler replacement bound. -/
theorem tvDist_generateZeroCloudKey_le
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringLeft ringRight : ProbComp (RLWE.Rq q degree))
    (scalarLeft scalarRight : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree) :
    tvDist
        (Native.generateZeroCloudKey q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringLeft scalarLeft tgswGadget lweSecret ringSecret)
        (Native.generateZeroCloudKey q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringRight scalarRight tgswGadget lweSecret ringSecret) ≤
      (bootstrappingErrorCount ringRank tgswLevels lweDimension : ℝ) *
          tvDist ringLeft ringRight +
        (keySwitchErrorCount ringRank degree keySwitchLevels : ℝ) *
          tvDist scalarLeft scalarRight := by
  let leftBootstrap :=
    Native.generateZeroBootstrappingKey q degree ringRank tgswLevels lweDimension
      ringLeft tgswGadget ringSecret
  let rightBootstrap :=
    Native.generateZeroBootstrappingKey q degree ringRank tgswLevels lweDimension
      ringRight tgswGadget ringSecret
  let leftSwitch :=
    Native.generateZeroKeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels
      scalarLeft lweSecret
  let rightSwitch :=
    Native.generateZeroKeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels
      scalarRight lweSecret
  let combine := fun bootstrapKey switchKey ↦
    (Native.CloudKey.mk bootstrapKey switchKey :
      Native.CloudKey q degree ringRank tgswLevels lweDimension keySwitchLevels)
  have hPair := tvDist_independentPair_le
    leftBootstrap rightBootstrap leftSwitch rightSwitch combine
  have hBootstrap : tvDist leftBootstrap rightBootstrap ≤
      (bootstrappingErrorCount ringRank tgswLevels lweDimension : ℝ) *
        tvDist ringLeft ringRight := by
    exact tvDist_generateZeroBootstrappingKey_le q degree ringRank tgswLevels lweDimension
      ringLeft ringRight tgswGadget ringSecret
  have hSwitch : tvDist leftSwitch rightSwitch ≤
      (keySwitchErrorCount ringRank degree keySwitchLevels : ℝ) *
        tvDist scalarLeft scalarRight := by
    simpa [leftSwitch, rightSwitch, keySwitchErrorCount] using
      (tvDist_generateZeroKeySwitchKey_le q lweDimension (ringRank * degree) keySwitchLevels
        scalarLeft scalarRight lweSecret)
  simpa only [Native.generateZeroCloudKey, independentPair, leftBootstrap, rightBootstrap,
    leftSwitch, rightSwitch, combine, map_eq_bind_pure_comp, Function.comp_def] using
      hPair.trans (add_le_add hBootstrap hSwitch)

/-! ## Query-bounded adaptive encryption tape -/

/-- Replacing the input-error sampler in the eager adaptive tape costs exactly the query budget
times the one-draw distance, regardless of the downstream adversary. -/
theorem tvDist_adaptiveContinuation_le
    {Message : Type}
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (queryCount : ℕ) (left right : ProbComp (ZMod q))
    (encode : Message → ZMod q)
    (adversary : Encryption.Adaptive.NativeAdversary Message q degree ringRank
      tgswLevels lweDimension keySwitchLevels)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree)
    (bootstrapKey : Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
    (keySwitchKey : Native.KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) :
    tvDist
        (Encryption.Adaptive.continuation queryCount left encode adversary
          lweSecret ringSecret bootstrapKey keySwitchKey)
        (Encryption.Adaptive.continuation queryCount right encode adversary
          lweSecret ringSecret bootstrapKey keySwitchKey) ≤
      (queryCount : ℝ) * tvDist left right := by
  unfold Encryption.Adaptive.continuation
  exact (tvDist_bind_right_le _
    (TLWE.batchEncrypt lweDimension queryCount left (embedBinarySecret lweSecret) 0)
    (TLWE.batchEncrypt lweDimension queryCount right (embedBinarySecret lweSecret) 0)).trans
      (tvDist_batchEncrypt_le lweDimension queryCount left right
        (embedBinarySecret lweSecret) 0)

/-- Explicit adaptive native game factored through the combined cloud-key sampler.  This form is
convenient for statistical replacement; `adaptiveGameViaCloudKey_eq_realGame` proves that it is
the existing security game, not a new experiment. -/
noncomputable def adaptiveGameViaCloudKey
    {Message : Type}
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.Adaptive.NativeAdversary Message q degree ringRank
      tgswLevels lweDimension keySwitchLevels) : ProbComp Bool := do
  let lweSecret ← Native.sampleLweSecret lweDimension
  let ringSecret ← Native.sampleRingSecret ringRank degree
  let cloudKey ← Native.generateCloudKey q degree ringRank tgswLevels lweDimension
    keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
    lweSecret ringSecret
  Encryption.Adaptive.continuation queryCount inputErrorSampler encode adversary
    lweSecret ringSecret cloudKey.bootstrappingKey cloudKey.keySwitchKey

/-- Factoring native evaluation-key generation through `Native.generateCloudKey` preserves the
adaptive real game exactly. -/
theorem adaptiveGameViaCloudKey_eq_realGame
    {Message : Type}
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.Adaptive.NativeAdversary Message q degree ringRank
      tgswLevels lweDimension keySwitchLevels) :
    adaptiveGameViaCloudKey q degree ringRank tgswLevels lweDimension keySwitchLevels
        queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget
        keySwitchGadget encode adversary =
      Encryption.Adaptive.realGame queryCount ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget encode adversary := by
  simp [adaptiveGameViaCloudKey, Encryption.Adaptive.realGame,
    Circular.realContinuationGame, Native.nativeCycleSpec, Native.generateCloudKey, monad_norm]

/-- Total statistical cost of replacing all three error samplers in one query-bounded adaptive
native TFHE execution. -/
noncomputable def adaptiveReplacementCost
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ)
    (ringLeft ringRight : ProbComp (RLWE.Rq q degree))
    (keySwitchLeft keySwitchRight inputLeft inputRight : ProbComp (ZMod q)) : ℝ :=
  ((bootstrappingErrorCount ringRank tgswLevels lweDimension : ℝ) *
      tvDist ringLeft ringRight +
    (keySwitchErrorCount ringRank degree keySwitchLevels : ℝ) *
      tvDist keySwitchLeft keySwitchRight) +
    (queryCount : ℝ) * tvDist inputLeft inputRight

/-- One-draw approximation bounds lift to the draw-count-weighted adaptive replacement cost. -/
theorem adaptiveReplacementCost_le
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ)
    (ringLeft ringRight : ProbComp (RLWE.Rq q degree))
    (keySwitchLeft keySwitchRight inputLeft inputRight : ProbComp (ZMod q))
    (ringBound keySwitchBound inputBound : ℝ)
    (hRing : tvDist ringLeft ringRight ≤ ringBound)
    (hKeySwitch : tvDist keySwitchLeft keySwitchRight ≤ keySwitchBound)
    (hInput : tvDist inputLeft inputRight ≤ inputBound) :
    adaptiveReplacementCost q degree ringRank tgswLevels lweDimension keySwitchLevels
        queryCount ringLeft ringRight keySwitchLeft keySwitchRight inputLeft inputRight ≤
      ((bootstrappingErrorCount ringRank tgswLevels lweDimension : ℝ) * ringBound +
        (keySwitchErrorCount ringRank degree keySwitchLevels : ℝ) * keySwitchBound) +
        (queryCount : ℝ) * inputBound := by
  unfold adaptiveReplacementCost
  exact add_le_add
    (add_le_add
      (mul_le_mul_of_nonneg_left hRing (Nat.cast_nonneg _))
      (mul_le_mul_of_nonneg_left hKeySwitch (Nat.cast_nonneg _)))
    (mul_le_mul_of_nonneg_left hInput (Nat.cast_nonneg _))

/-- Identical implementation and reference samplers have zero replacement cost. -/
@[simp]
theorem adaptiveReplacementCost_self
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ)
    (ringSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchSampler inputSampler : ProbComp (ZMod q)) :
    adaptiveReplacementCost q degree ringRank tgswLevels lweDimension keySwitchLevels
      queryCount ringSampler ringSampler keySwitchSampler keySwitchSampler
      inputSampler inputSampler = 0 := by
  simp [adaptiveReplacementCost, tvDist_self]

/-- End-to-end total-variation bound for replacing the BRK, KSK, and adaptive-input error
samplers in the factored native game. -/
theorem tvDist_adaptiveGameViaCloudKey_le
    {Message : Type}
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ) [NeZero q]
    (ringLeft ringRight : ProbComp (RLWE.Rq q degree))
    (keySwitchLeft keySwitchRight inputLeft inputRight : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.Adaptive.NativeAdversary Message q degree ringRank
      tgswLevels lweDimension keySwitchLevels) :
    tvDist
        (adaptiveGameViaCloudKey q degree ringRank tgswLevels lweDimension keySwitchLevels
          queryCount ringLeft keySwitchLeft inputLeft tgswGadget keySwitchGadget
          encode adversary)
        (adaptiveGameViaCloudKey q degree ringRank tgswLevels lweDimension keySwitchLevels
          queryCount ringRight keySwitchRight inputRight tgswGadget keySwitchGadget
          encode adversary) ≤
      adaptiveReplacementCost q degree ringRank tgswLevels lweDimension keySwitchLevels
        queryCount ringLeft ringRight keySwitchLeft keySwitchRight inputLeft inputRight := by
  unfold adaptiveGameViaCloudKey
  refine tvDist_bind_left_le_const' (m := ProbComp)
    (Native.sampleLweSecret lweDimension) _ _
    (adaptiveReplacementCost q degree ringRank tgswLevels lweDimension keySwitchLevels
      queryCount ringLeft ringRight keySwitchLeft keySwitchRight inputLeft inputRight) ?_
  intro lweSecret
  refine tvDist_bind_left_le_const' (m := ProbComp)
    (Native.sampleRingSecret ringRank degree) _ _
    (adaptiveReplacementCost q degree ringRank tgswLevels lweDimension keySwitchLevels
      queryCount ringLeft ringRight keySwitchLeft keySwitchRight inputLeft inputRight) ?_
  intro ringSecret
  let cloudLeft :=
    Native.generateCloudKey q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringLeft keySwitchLeft tgswGadget keySwitchGadget lweSecret ringSecret
  let cloudRight :=
    Native.generateCloudKey q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringRight keySwitchRight tgswGadget keySwitchGadget lweSecret ringSecret
  let leftCont := fun
      (cloudKey : Native.CloudKey q degree ringRank tgswLevels lweDimension keySwitchLevels) ↦
    Encryption.Adaptive.continuation queryCount inputLeft encode adversary
      lweSecret ringSecret cloudKey.bootstrappingKey cloudKey.keySwitchKey
  let rightCont := fun
      (cloudKey : Native.CloudKey q degree ringRank tgswLevels lweDimension keySwitchLevels) ↦
    Encryption.Adaptive.continuation queryCount inputRight encode adversary
      lweSecret ringSecret cloudKey.bootstrappingKey cloudKey.keySwitchKey
  change tvDist (cloudLeft >>= leftCont) (cloudRight >>= rightCont) ≤
    adaptiveReplacementCost q degree ringRank tgswLevels lweDimension keySwitchLevels
      queryCount ringLeft ringRight keySwitchLeft keySwitchRight inputLeft inputRight
  calc
    tvDist (cloudLeft >>= leftCont) (cloudRight >>= rightCont) ≤
        tvDist cloudLeft cloudRight +
          (queryCount : ℝ) * tvDist inputLeft inputRight :=
      tvDist_bind_le_add cloudLeft cloudRight leftCont rightCont
        ((queryCount : ℝ) * tvDist inputLeft inputRight)
        (fun cloudKey ↦
          tvDist_adaptiveContinuation_le queryCount inputLeft inputRight encode adversary
            lweSecret ringSecret cloudKey.bootstrappingKey cloudKey.keySwitchKey)
    _ ≤
        ((bootstrappingErrorCount ringRank tgswLevels lweDimension : ℝ) *
            tvDist ringLeft ringRight +
          (keySwitchErrorCount ringRank degree keySwitchLevels : ℝ) *
            tvDist keySwitchLeft keySwitchRight) +
          (queryCount : ℝ) * tvDist inputLeft inputRight := by
      exact add_le_add
        (tvDist_generateCloudKey_le q degree ringRank tgswLevels lweDimension
          keySwitchLevels ringLeft ringRight keySwitchLeft keySwitchRight tgswGadget
          keySwitchGadget lweSecret ringSecret)
        le_rfl
    _ = adaptiveReplacementCost q degree ringRank tgswLevels lweDimension keySwitchLevels
        queryCount ringLeft ringRight keySwitchLeft keySwitchRight inputLeft inputRight := rfl

/-- End-to-end sampler replacement for the existing adaptive real game. -/
theorem tvDist_adaptiveRealGame_le
    {Message : Type}
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ) [NeZero q]
    (ringLeft ringRight : ProbComp (RLWE.Rq q degree))
    (keySwitchLeft keySwitchRight inputLeft inputRight : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.Adaptive.NativeAdversary Message q degree ringRank
      tgswLevels lweDimension keySwitchLevels) :
    tvDist
        (Encryption.Adaptive.realGame queryCount ringLeft keySwitchLeft inputLeft
          tgswGadget keySwitchGadget encode adversary)
        (Encryption.Adaptive.realGame queryCount ringRight keySwitchRight inputRight
          tgswGadget keySwitchGadget encode adversary) ≤
      adaptiveReplacementCost q degree ringRank tgswLevels lweDimension keySwitchLevels
        queryCount ringLeft ringRight keySwitchLeft keySwitchRight inputLeft inputRight := by
  rw [← adaptiveGameViaCloudKey_eq_realGame q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount ringLeft keySwitchLeft inputLeft tgswGadget
      keySwitchGadget encode adversary,
    ← adaptiveGameViaCloudKey_eq_realGame q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount ringRight keySwitchRight inputRight tgswGadget
      keySwitchGadget encode adversary]
  exact tvDist_adaptiveGameViaCloudKey_le q degree ringRank tgswLevels lweDimension
    keySwitchLevels queryCount ringLeft ringRight keySwitchLeft keySwitchRight inputLeft
    inputRight tgswGadget keySwitchGadget encode adversary

/-- The signed winning advantage is 1-Lipschitz in total variation. -/
theorem abs_signedAdvantage_sub_le_tvDist (left right : ProbComp Bool) :
    |Encryption.signedAdvantage left - Encryption.signedAdvantage right| ≤
      tvDist left right := by
  simpa [Encryption.signedAdvantage] using
    (abs_probOutput_toReal_sub_le_tvDist left right)

/-- The signed advantages of adaptive TFHE games using two sampler triples differ by at most the
explicit replacement cost. -/
theorem abs_signedAdvantage_adaptiveReal_sub_le
    {Message : Type}
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ) [NeZero q]
    (ringLeft ringRight : ProbComp (RLWE.Rq q degree))
    (keySwitchLeft keySwitchRight inputLeft inputRight : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.Adaptive.NativeAdversary Message q degree ringRank
      tgswLevels lweDimension keySwitchLevels) :
    |Encryption.signedAdvantage
        (Encryption.Adaptive.realGame queryCount ringLeft keySwitchLeft inputLeft
          tgswGadget keySwitchGadget encode adversary) -
      Encryption.signedAdvantage
        (Encryption.Adaptive.realGame queryCount ringRight keySwitchRight inputRight
          tgswGadget keySwitchGadget encode adversary)| ≤
      adaptiveReplacementCost q degree ringRank tgswLevels lweDimension keySwitchLevels
        queryCount ringLeft ringRight keySwitchLeft keySwitchRight inputLeft inputRight := by
  exact (abs_signedAdvantage_sub_le_tvDist _ _).trans
    (tvDist_adaptiveRealGame_le q degree ringRank tgswLevels lweDimension keySwitchLevels
      queryCount ringLeft ringRight keySwitchLeft keySwitchRight inputLeft inputRight
      tgswGadget keySwitchGadget encode adversary)

/-- Absolute advantage under implementation samplers is bounded by the reference-sampler
advantage plus the exact sampler-replacement cost. -/
theorem abs_signedAdvantage_adaptiveReal_le_reference_add
    {Message : Type}
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ) [NeZero q]
    (ringImplementation ringReference : ProbComp (RLWE.Rq q degree))
    (keySwitchImplementation keySwitchReference inputImplementation inputReference :
      ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.Adaptive.NativeAdversary Message q degree ringRank
      tgswLevels lweDimension keySwitchLevels) :
    |Encryption.signedAdvantage
      (Encryption.Adaptive.realGame queryCount ringImplementation keySwitchImplementation
        inputImplementation tgswGadget keySwitchGadget encode adversary)| ≤
      |Encryption.signedAdvantage
        (Encryption.Adaptive.realGame queryCount ringReference keySwitchReference
          inputReference tgswGadget keySwitchGadget encode adversary)| +
        adaptiveReplacementCost q degree ringRank tgswLevels lweDimension keySwitchLevels
          queryCount ringImplementation ringReference keySwitchImplementation
          keySwitchReference inputImplementation inputReference := by
  let implementationAdvantage := Encryption.signedAdvantage
    (Encryption.Adaptive.realGame queryCount ringImplementation keySwitchImplementation
      inputImplementation tgswGadget keySwitchGadget encode adversary)
  let referenceAdvantage := Encryption.signedAdvantage
    (Encryption.Adaptive.realGame queryCount ringReference keySwitchReference
      inputReference tgswGadget keySwitchGadget encode adversary)
  have hDistance : |implementationAdvantage - referenceAdvantage| ≤
      adaptiveReplacementCost q degree ringRank tgswLevels lweDimension keySwitchLevels
        queryCount ringImplementation ringReference keySwitchImplementation
        keySwitchReference inputImplementation inputReference := by
    exact abs_signedAdvantage_adaptiveReal_sub_le q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount ringImplementation ringReference
      keySwitchImplementation keySwitchReference inputImplementation inputReference
      tgswGadget keySwitchGadget encode adversary
  calc
    |implementationAdvantage| = |(implementationAdvantage - referenceAdvantage) +
        referenceAdvantage| := by ring_nf
    _ ≤ |implementationAdvantage - referenceAdvantage| + |referenceAdvantage| :=
      abs_add_le _ _
    _ = |referenceAdvantage| + |implementationAdvantage - referenceAdvantage| :=
      add_comm _ _
    _ ≤ |referenceAdvantage| +
        adaptiveReplacementCost q degree ringRank tgswLevels lweDimension keySwitchLevels
          queryCount ringImplementation ringReference keySwitchImplementation
          keySwitchReference inputImplementation inputReference :=
      add_le_add_right hDistance _

/-- Adversary-class security transfers from reference samplers to implementation samplers by
adding any proved upper bound on `adaptiveReplacementCost`. -/
theorem adaptiveHardAgainst_implementation_of_reference
    {Message : Type}
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ) [NeZero q]
    (ringImplementation ringReference : ProbComp (RLWE.Rq q degree))
    (keySwitchImplementation keySwitchReference inputImplementation inputReference :
      ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (allowed : Encryption.Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels → Prop)
    (referenceBound replacementBound : ℝ)
    (hReference : Encryption.Adaptive.HardAgainst queryCount ringReference
      keySwitchReference inputReference tgswGadget keySwitchGadget encode
      allowed referenceBound)
    (hReplacement : adaptiveReplacementCost q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount ringImplementation ringReference keySwitchImplementation
      keySwitchReference inputImplementation inputReference ≤ replacementBound) :
    Encryption.Adaptive.HardAgainst queryCount ringImplementation keySwitchImplementation
      inputImplementation tgswGadget keySwitchGadget encode allowed
      (referenceBound + replacementBound) := by
  intro adversary hadversary hbound
  calc
    |Encryption.signedAdvantage
      (Encryption.Adaptive.realGame queryCount ringImplementation keySwitchImplementation
        inputImplementation tgswGadget keySwitchGadget encode adversary)| ≤
      |Encryption.signedAdvantage
        (Encryption.Adaptive.realGame queryCount ringReference keySwitchReference
          inputReference tgswGadget keySwitchGadget encode adversary)| +
        adaptiveReplacementCost q degree ringRank tgswLevels lweDimension keySwitchLevels
          queryCount ringImplementation ringReference keySwitchImplementation
          keySwitchReference inputImplementation inputReference :=
      abs_signedAdvantage_adaptiveReal_le_reference_add q degree ringRank tgswLevels
        lweDimension keySwitchLevels queryCount ringImplementation ringReference
        keySwitchImplementation keySwitchReference inputImplementation inputReference
        tgswGadget keySwitchGadget encode adversary
    _ ≤ referenceBound + replacementBound :=
      add_le_add (hReference adversary hadversary hbound) hReplacement

/-! ## Composition with the computational TFHE security theorem -/

/-- Security of a reference sampler triple transfers to an implementation sampler triple with
the explicit statistical loss.  The reference game is then bounded by one native circular BRK
replacement and one exact joint-LWE problem. -/
theorem abs_signedAdvantage_implementation_le_bootstrap_add_jointLwe_add_replacement
    {Message : Type}
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ) [NeZero q]
    (ringImplementation ringReference : ProbComp (RLWE.Rq q degree))
    (keySwitchImplementation keySwitchReference inputImplementation inputReference :
      ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.Adaptive.NativeAdversary Message q degree ringRank
      tgswLevels lweDimension keySwitchLevels)
    (hbound : Encryption.Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (Encryption.Adaptive.realGame queryCount ringImplementation keySwitchImplementation
        inputImplementation tgswGadget keySwitchGadget encode adversary)| ≤
      Encryption.Adaptive.bootstrapReplacementAdvantage queryCount ringReference
          keySwitchReference inputReference tgswGadget keySwitchGadget encode adversary +
        LearningWithErrors.advantage
          (Encryption.Adaptive.jointLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
            keySwitchReference inputReference)
          (Encryption.Adaptive.keySwitchMessageReduction ringReference keySwitchReference
            inputReference tgswGadget
            (Encryption.Adaptive.nativeKeySwitchMessage keySwitchGadget) encode adversary) +
        adaptiveReplacementCost q degree ringRank tgswLevels lweDimension keySwitchLevels
          queryCount ringImplementation ringReference keySwitchImplementation
          keySwitchReference inputImplementation inputReference := by
  calc
    |Encryption.signedAdvantage
      (Encryption.Adaptive.realGame queryCount ringImplementation keySwitchImplementation
        inputImplementation tgswGadget keySwitchGadget encode adversary)| ≤
      |Encryption.signedAdvantage
        (Encryption.Adaptive.realGame queryCount ringReference keySwitchReference
          inputReference tgswGadget keySwitchGadget encode adversary)| +
        adaptiveReplacementCost q degree ringRank tgswLevels lweDimension keySwitchLevels
          queryCount ringImplementation ringReference keySwitchImplementation
          keySwitchReference inputImplementation inputReference :=
      abs_signedAdvantage_adaptiveReal_le_reference_add q degree ringRank tgswLevels
        lweDimension keySwitchLevels queryCount ringImplementation ringReference
        keySwitchImplementation keySwitchReference inputImplementation inputReference
        tgswGadget keySwitchGadget encode adversary
    _ ≤
      (Encryption.Adaptive.bootstrapReplacementAdvantage queryCount ringReference
          keySwitchReference inputReference tgswGadget keySwitchGadget encode adversary +
        LearningWithErrors.advantage
          (Encryption.Adaptive.jointLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
            keySwitchReference inputReference)
          (Encryption.Adaptive.keySwitchMessageReduction ringReference keySwitchReference
            inputReference tgswGadget
            (Encryption.Adaptive.nativeKeySwitchMessage keySwitchGadget) encode adversary)) +
        adaptiveReplacementCost q degree ringRank tgswLevels lweDimension keySwitchLevels
          queryCount ringImplementation ringReference keySwitchImplementation
          keySwitchReference inputImplementation inputReference := by
      exact add_le_add_left
        (Encryption.Adaptive.abs_signedAdvantage_real_le_bootstrap_add_jointLwe
          queryCount ringReference keySwitchReference inputReference tgswGadget
          keySwitchGadget encode adversary hbound) _

/-- The previous theorem with the circular term exposed as the exact native direct-bilinear KDM
advantage of the complete adaptive continuation. -/
theorem abs_signedAdvantage_implementation_le_directBilinear_add_jointLwe_add_replacement
    {Message : Type}
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ) [NeZero q]
    (ringImplementation ringReference : ProbComp (RLWE.Rq q degree))
    (keySwitchImplementation keySwitchReference inputImplementation inputReference :
      ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.Adaptive.NativeAdversary Message q degree ringRank
      tgswLevels lweDimension keySwitchLevels)
    (hbound : Encryption.Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (Encryption.Adaptive.realGame queryCount ringImplementation keySwitchImplementation
        inputImplementation tgswGadget keySwitchGadget encode adversary)| ≤
      Native.BootstrapSecurity.directBilinearAdvantage ringReference keySwitchReference
          tgswGadget keySwitchGadget
          (Encryption.Adaptive.continuation queryCount inputReference encode adversary) +
        LearningWithErrors.advantage
          (Encryption.Adaptive.jointLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
            keySwitchReference inputReference)
          (Encryption.Adaptive.keySwitchMessageReduction ringReference keySwitchReference
            inputReference tgswGadget
            (Encryption.Adaptive.nativeKeySwitchMessage keySwitchGadget) encode adversary) +
        adaptiveReplacementCost q degree ringRank tgswLevels lweDimension keySwitchLevels
          queryCount ringImplementation ringReference keySwitchImplementation
          keySwitchReference inputImplementation inputReference := by
  rw [← Encryption.Adaptive.bootstrapReplacementAdvantage_eq_directBilinear
    queryCount ringReference keySwitchReference inputReference tgswGadget keySwitchGadget
    encode adversary]
  exact abs_signedAdvantage_implementation_le_bootstrap_add_jointLwe_add_replacement
    q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount
    ringImplementation ringReference keySwitchImplementation keySwitchReference
    inputImplementation inputReference tgswGadget keySwitchGadget encode adversary hbound

/-- Equal reference scalar noise flattens the KSK and adaptive-query rows to one ordinary
binary-secret batch-LWE problem.  This is the end-to-end finite-sampler theorem: native
direct-bilinear circular/KDM security, ordinary LWE, and the explicit sampler approximation loss
are the only three terms. -/
theorem abs_signedAdvantage_implementation_le_directBilinear_add_batchLwe_add_replacement
    {Message : Type}
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ) [NeZero q]
    (ringImplementation ringReference : ProbComp (RLWE.Rq q degree))
    (keySwitchImplementation inputImplementation referenceError : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.Adaptive.NativeAdversary Message q degree ringRank
      tgswLevels lweDimension keySwitchLevels)
    (hbound : Encryption.Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (Encryption.Adaptive.realGame queryCount ringImplementation keySwitchImplementation
        inputImplementation tgswGadget keySwitchGadget encode adversary)| ≤
      Native.BootstrapSecurity.directBilinearAdvantage ringReference referenceError
          tgswGadget keySwitchGadget
          (Encryption.Adaptive.continuation queryCount referenceError encode adversary) +
        LearningWithErrors.advantage
          (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels + queryCount)
            referenceError)
          (FormalProof4FHE.LWE.TwoBlock.reduction
            (Encryption.Adaptive.keySwitchMessageReduction ringReference referenceError
              referenceError tgswGadget
              (Encryption.Adaptive.nativeKeySwitchMessage keySwitchGadget) encode adversary)) +
        adaptiveReplacementCost q degree ringRank tgswLevels lweDimension keySwitchLevels
          queryCount ringImplementation ringReference keySwitchImplementation referenceError
          inputImplementation referenceError := by
  calc
    |Encryption.signedAdvantage
      (Encryption.Adaptive.realGame queryCount ringImplementation keySwitchImplementation
        inputImplementation tgswGadget keySwitchGadget encode adversary)| ≤
      |Encryption.signedAdvantage
        (Encryption.Adaptive.realGame queryCount ringReference referenceError referenceError
          tgswGadget keySwitchGadget encode adversary)| +
        adaptiveReplacementCost q degree ringRank tgswLevels lweDimension keySwitchLevels
          queryCount ringImplementation ringReference keySwitchImplementation referenceError
          inputImplementation referenceError :=
      abs_signedAdvantage_adaptiveReal_le_reference_add q degree ringRank tgswLevels
        lweDimension keySwitchLevels queryCount ringImplementation ringReference
        keySwitchImplementation referenceError inputImplementation referenceError
        tgswGadget keySwitchGadget encode adversary
    _ ≤
      (Encryption.Adaptive.bootstrapReplacementAdvantage queryCount ringReference
          referenceError referenceError tgswGadget keySwitchGadget encode adversary +
        LearningWithErrors.advantage
          (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels + queryCount)
            referenceError)
          (FormalProof4FHE.LWE.TwoBlock.reduction
            (Encryption.Adaptive.keySwitchMessageReduction ringReference referenceError
              referenceError tgswGadget
              (Encryption.Adaptive.nativeKeySwitchMessage keySwitchGadget) encode adversary))) +
        adaptiveReplacementCost q degree ringRank tgswLevels lweDimension keySwitchLevels
          queryCount ringImplementation ringReference keySwitchImplementation referenceError
          inputImplementation referenceError := by
      exact add_le_add_left
        (Encryption.Adaptive.abs_signedAdvantage_real_le_bootstrap_add_batchLwe_of_same_noise
          queryCount ringReference referenceError tgswGadget keySwitchGadget encode
          adversary hbound) _
    _ =
      Native.BootstrapSecurity.directBilinearAdvantage ringReference referenceError
          tgswGadget keySwitchGadget
          (Encryption.Adaptive.continuation queryCount referenceError encode adversary) +
        LearningWithErrors.advantage
          (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels + queryCount)
            referenceError)
          (FormalProof4FHE.LWE.TwoBlock.reduction
            (Encryption.Adaptive.keySwitchMessageReduction ringReference referenceError
              referenceError tgswGadget
              (Encryption.Adaptive.nativeKeySwitchMessage keySwitchGadget) encode adversary)) +
        adaptiveReplacementCost q degree ringRank tgswLevels lweDimension keySwitchLevels
          queryCount ringImplementation ringReference keySwitchImplementation referenceError
          inputImplementation referenceError := by
      rw [Encryption.Adaptive.bootstrapReplacementAdvantage_eq_directBilinear]

end FormalProof4FHE.TFHE.SamplerReplacement
