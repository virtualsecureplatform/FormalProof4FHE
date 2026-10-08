/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.GSWPublicKey
import FormalProof4FHE.LWE.NoisyBinaryGadget

/-!
# Receiver-readable tensor linking hints

A masked tensor hint has n rows and n*n*levels columns. If a public link Z
cancels its subset mask in the receiver's phase, a participant knowing that
receiver key can read noisy gadget multiples of every sender-key coordinate.
For a power-of-two modulus the explicit binary decoder recovers the entire
sender residue vector under a checked noise-separation margin.

This audits the public P,Z equations of WHT26 under a receiver-owned key.
It does not attack a one-key specialization against an adversary knowing no
secret key, and it does not formalize the paper's complete security game.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.LWE.GSWLinkedDisclosure

open GSWGadget TFHE.BootstrappingCorrectness

abbrev Columns (rows levels : ℕ) := Fin rows × Fin rows × Fin levels
abbrev Hint {q : ℕ} (params : Parameters q) (rows : ℕ) :=
  Matrix (Fin rows) (Columns rows params.levels) (ZMod q)

/-- Canonical public flattening of the two tensor coordinates and gadget level. -/
def columnEquiv (rows levels : ℕ) : Columns rows levels ≃ Fin (rows * (rows * levels)) :=
  (Equiv.prodCongr (Equiv.refl (Fin rows))
    (finProdFinEquiv : Fin rows × Fin levels ≃ Fin (rows * levels))).trans finProdFinEquiv

abbrev StoredHint {q : ℕ} (params : Parameters q) (rows : ℕ) :=
  Vector (Vector (ZMod q) (rows * (rows * params.levels))) rows

/-- Materialize public coefficients before exposing them to the attacker. -/
def storeHint {q rows : ℕ} (params : Parameters q) (hint : Hint params rows) :
    StoredHint params rows :=
  Vector.ofFn fun row ↦ Vector.ofFn fun column ↦
    hint row ((columnEquiv rows params.levels).symm column)

def hintView {q rows : ℕ} (params : Parameters q) (hint : StoredHint params rows) :
    Hint params rows :=
  fun row column ↦ (hint.get row).get (columnEquiv rows params.levels column)

@[simp]
theorem hintView_storeHint {q rows : ℕ} (params : Parameters q) (hint : Hint params rows) :
    hintView params (storeHint params hint) = hint := by
  ext row column
  simp [hintView, storeHint]

/-- Public tensor offset I_n ⊗ sender ⊗ g, using explicit product indices. -/
def tensorHint {q rows : ℕ} [NeZero q] (params : Parameters q)
    (sender : Fin rows → ZMod q) : Hint params rows :=
  fun row column ↦ if row = column.1 then
    sender column.2.1 * TFHE.Gadget.Base.gadget params column.2.2 else 0

/-- The exact tensor phase, before introducing or canceling an independent mask. -/
theorem phase_tensorHint {q rows : ℕ} [NeZero q] (params : Parameters q)
    (sender receiver : Fin rows → ZMod q) (column : Columns rows params.levels) :
    vecMul receiver (tensorHint params sender) column =
      receiver column.1 * sender column.2.1 * TFHE.Gadget.Base.gadget params column.2.2 := by
  simp [vecMul, dotProduct, tensorHint, mul_ite, mul_assoc]

/-- Public cancellation C=P-Z. -/
def linked {q rows : ℕ} [NeZero q] (params : Parameters q)
    (maskedHint publicLink : Hint params rows) : Hint params rows := maskedHint - publicLink

/-- The exactly measurable phase discrepancy of the link from the subset mask. -/
def linkNoise {q rows : ℕ} [NeZero q] (params : Parameters q)
    (receiver : Fin rows → ZMod q) (mask publicLink : Hint params rows) :
    Columns rows params.levels → ZMod q :=
  vecMul receiver publicLink - vecMul receiver mask

/-- Binary subset mask D R on the full tensor-hint column layout. -/
def subsetMask {q rows pads : ℕ} [NeZero q] (params : Parameters q)
    (seed : Matrix (Fin rows) (Fin pads) (ZMod q))
    (bits : Fin pads → Columns rows params.levels → Bool) : Hint params rows :=
  seed * Matrix.of (fun pad column ↦ (bitMessage (bits pad column) : ZMod q))

/-- A repeated seed column lets the checked GSW decomposition expose exactly
one column of the sparse matrices used by Modified LinkAlgo. -/
def repeatedColumn {q rows : ℕ} (params : Parameters q) (mask : Fin rows → ZMod q) :
    Ciphertext params rows := fun row _column ↦ mask row

def anchor {q rows : ℕ} (params : Parameters q) (column : Columns rows params.levels) :
    Fin (rows * params.levels) := finProdFinEquiv (column.1, column.2.2)

/-- Exact public linking computation, with one encrypted pad per output column.
Each sparse L_{u,v} contributes only in output column v. -/
def sourceLink {q rows pads : ℕ} [NeZero q] (params : Parameters q)
    (seed : Matrix (Fin rows) (Fin pads) (ZMod q))
    (encryptedPads : Fin pads → Columns rows params.levels → Ciphertext params rows) :
    Hint params rows :=
  fun row column ↦ ∑ pad,
    multiply params (encryptedPads pad column) (repeatedColumn params (fun r ↦ seed r pad))
      row (anchor params column)

def sourceError {q rows pads : ℕ} [NeZero q] (params : Parameters q)
    (receiver : Fin rows → ZMod q) (seed : Matrix (Fin rows) (Fin pads) (ZMod q))
    (bits : Fin pads → Columns rows params.levels → Bool)
    (encryptedPads : Fin pads → Columns rows params.levels → Ciphertext params rows) :
    Columns rows params.levels → ZMod q :=
  fun column ↦ ∑ pad, vecMul
    (GSWOperations.noise receiver (gadget params rows)
      (encryptedPads pad column) (bitMessage (bits pad column)))
    (digitMatrix params (repeatedColumn params (fun row ↦ seed row pad)))
    (anchor params column)

/-- The linking phase follows from concrete decomposition, without trusting a
separate claimed tensor-link correctness axiom. -/
theorem phase_sourceLink {q rows pads : ℕ} [NeZero q] (params : Parameters q)
    (receiver : Fin rows → ZMod q) (seed : Matrix (Fin rows) (Fin pads) (ZMod q))
    (bits : Fin pads → Columns rows params.levels → Bool)
    (encryptedPads : Fin pads → Columns rows params.levels → Ciphertext params rows)
    (column : Columns rows params.levels) :
    vecMul receiver (sourceLink params seed encryptedPads) column =
      vecMul receiver (subsetMask params seed bits) column +
        sourceError params receiver seed bits encryptedPads column := by
  have hsingle (pad : Fin pads) :
      vecMul receiver (multiply params (encryptedPads pad column)
          (repeatedColumn params (fun row ↦ seed row pad))) (anchor params column) =
        vecMul (GSWOperations.noise receiver (gadget params rows)
          (encryptedPads pad column) (bitMessage (bits pad column)))
          (digitMatrix params (repeatedColumn params (fun row ↦ seed row pad))) (anchor params column) +
            bitMessage (bits pad column) *
              vecMul receiver (repeatedColumn params (fun row ↦ seed row pad)) (anchor params column) := by
    simp only [multiply, GSWOperations.noise, sub_vecMul, smul_vecMul, vecMul_vecMul,
      gadget_mul_digitMatrix, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hsum : vecMul receiver (sourceLink params seed encryptedPads) column =
      ∑ pad, vecMul receiver (multiply params (encryptedPads pad column)
        (repeatedColumn params (fun row ↦ seed row pad))) (anchor params column) := by
    change (∑ row, receiver row * (∑ pad, _)) = _
    simp only [Finset.mul_sum]
    exact Finset.sum_comm
  have hmask : (∑ pad, bitMessage (bits pad column) *
      vecMul receiver (repeatedColumn params (fun row ↦ seed row pad)) (anchor params column)) =
        vecMul receiver (subsetMask params seed bits) column := by
    rw [subsetMask, ← vecMul_vecMul]
    apply Finset.sum_congr rfl
    intro pad _
    simp only [repeatedColumn, vecMul, dotProduct, Matrix.of_apply]
    ring
  rw [hsum]
  simp_rw [hsingle]
  rw [Finset.sum_add_distrib, hmask]
  simp only [sourceError]
  ring

theorem linkNoise_sourceLink {q rows pads : ℕ} [NeZero q] (params : Parameters q)
    (receiver : Fin rows → ZMod q) (seed : Matrix (Fin rows) (Fin pads) (ZMod q))
    (bits : Fin pads → Columns rows params.levels → Bool)
    (encryptedPads : Fin pads → Columns rows params.levels → Ciphertext params rows) :
    linkNoise params receiver (subsetMask params seed bits) (sourceLink params seed encryptedPads) =
      sourceError params receiver seed bits encryptedPads := by
  funext column
  simp only [linkNoise, Pi.sub_apply]
  rw [phase_sourceLink params receiver seed bits encryptedPads column]
  simp

/-- Sparsity leaves only `pads` nonzero contributions per output column. -/
theorem sourceLink_noise_bound {q rows pads : ℕ} [NeZero q] (params : Parameters q)
    (receiver : Fin rows → ZMod q) (seed : Matrix (Fin rows) (Fin pads) (ZMod q))
    (bits : Fin pads → Columns rows params.levels → Bool)
    (encryptedPads : Fin pads → Columns rows params.levels → Ciphertext params rows) (bound : ℕ)
    (hpad : ∀ pad column, NoiseBound params receiver (encryptedPads pad column)
      (bitMessage (bits pad column)) bound) (column : Columns rows params.levels) :
    (LatticeCrypto.centeredRepr (linkNoise params receiver
      (subsetMask params seed bits) (sourceLink params seed encryptedPads) column)).natAbs ≤
        pads * growth params rows * bound := by
  rw [linkNoise_sourceLink]
  unfold sourceError
  calc
    _ ≤ ∑ pad, (LatticeCrypto.centeredRepr (vecMul
        (GSWOperations.noise receiver (gadget params rows)
          (encryptedPads pad column) (bitMessage (bits pad column)))
        (digitMatrix params (repeatedColumn params (fun row ↦ seed row pad)))
        (anchor params column))).natAbs :=
      TFHE.NoiseBounds.centeredRepr_finset_sum_natAbs_le _ _
    _ ≤ ∑ _pad : Fin pads, growth params rows * bound := by
      apply Finset.sum_le_sum
      intro pad _
      exact vecMul_error_bound params _ _ bound (hpad pad column) (anchor params column)
    _ = _ := by simp [mul_assoc]

/-- No probabilistic premise: independent masking disappears from the phase. -/
theorem phase_linked {q rows : ℕ} [NeZero q] (params : Parameters q)
    (sender receiver : Fin rows → ZMod q) (mask publicLink : Hint params rows)
    (column : Columns rows params.levels) :
    vecMul receiver (linked params (mask + tensorHint params sender) publicLink) column =
      receiver column.1 * sender column.2.1 * TFHE.Gadget.Base.gadget params column.2.2 -
        linkNoise params receiver mask publicLink column := by
  simp only [linked, linkNoise, vecMul_sub, vecMul_add, Pi.sub_apply, Pi.add_apply,
    phase_tensorHint]
  ring

/-- Only the receiver-owned key and the two public hint/link matrices are inputs. -/
def observations {q rows : ℕ} [NeZero q] (params : Parameters q)
    (receiver : Fin rows → ZMod q) (knownUnit coordinate : Fin rows)
    (maskedHint publicLink : Hint params rows) : ℕ → ZMod q :=
  fun level ↦ if h : level < params.levels then
    vecMul receiver (linked params maskedHint publicLink) (knownUnit, coordinate, ⟨level, h⟩)
  else 0

def recoverSender {q rows : ℕ} [NeZero q] (params : Parameters q)
    (receiver : Fin rows → ZMod q) (knownUnit : Fin rows)
    (maskedHint publicLink : Hint params rows) : Fin rows → ZMod q :=
  fun coordinate ↦ NoisyBinaryGadget.recover params.levels
    (observations params receiver knownUnit coordinate maskedHint publicLink)

/-- Eager key recovery from public finite data, without sender-dependent closures. -/
def recoverStoredSender {q rows : ℕ} [NeZero q] (params : Parameters q)
    (receiver : Fin rows → ZMod q) (knownUnit : Fin rows)
    (maskedHint publicLink : StoredHint params rows) : Vector (ZMod q) rows :=
  Vector.ofFn fun coordinate ↦ recoverSender params receiver knownUnit
    (hintView params maskedHint) (hintView params publicLink) coordinate

@[simp]
theorem recoverStoredSender_get {q rows : ℕ} [NeZero q] (params : Parameters q)
    (receiver : Fin rows → ZMod q) (knownUnit : Fin rows)
    (maskedHint publicLink : StoredHint params rows) (coordinate : Fin rows) :
    (recoverStoredSender params receiver knownUnit maskedHint publicLink).get coordinate =
      recoverSender params receiver knownUnit
        (hintView params maskedHint) (hintView params publicLink) coordinate := by
  simp [recoverStoredSender]

/-- Any key holder with a known unit component can recover every sender residue,
provided the link phase has the indicated small error. -/
theorem recoverSender_eq {q rows : ℕ} [NeZero q] (params : Parameters q)
    (hbase : params.base = 2) (hq : q = 2 ^ params.levels)
    (sender receiver : Fin rows → ZMod q) (knownUnit : Fin rows)
    (hunit : receiver knownUnit = 1) (mask publicLink : Hint params rows) (bound : ℕ)
    (hnoise : ∀ column, (LatticeCrypto.centeredRepr
      (linkNoise params receiver mask publicLink column)).natAbs ≤ bound)
    (hmargin : 2 * bound < centeredDistance 0 ((2 ^ (params.levels - 1) : ℕ) : ZMod q)) :
    recoverSender params receiver knownUnit (mask + tensorHint params sender) publicLink = sender := by
  funext coordinate
  apply NoisyBinaryGadget.recover_eq hq _ _ bound _ hmargin
  intro level hlevel
  simp only [observations, dif_pos hlevel]
  rw [phase_linked]
  simp only [hunit, one_mul, TFHE.Gadget.Base.gadget, hbase, Nat.cast_pow]
  simpa only [centeredDistance, sub_sub_cancel_left,
    LatticeCrypto.centeredRepr_natAbs_neg] using
    hnoise (knownUnit, coordinate, ⟨level, hlevel⟩)


/-- Full sender recovery from the actual encrypted-pad source link. The receiver
key is the attacker's existing key; the sender key is not an attack input. -/
theorem recoverSender_sourceLink {q rows pads : ℕ} [NeZero q] (params : Parameters q)
    (hbase : params.base = 2) (hlevels : 0 < params.levels) (hq : q = 2 ^ params.levels)
    (sender receiver : Fin rows → ZMod q) (knownUnit : Fin rows) (hunit : receiver knownUnit = 1)
    (seed : Matrix (Fin rows) (Fin pads) (ZMod q))
    (bits : Fin pads → Columns rows params.levels → Bool)
    (encryptedPads : Fin pads → Columns rows params.levels → Ciphertext params rows) (bound : ℕ)
    (hpad : ∀ pad column, NoiseBound params receiver (encryptedPads pad column)
      (bitMessage (bits pad column)) bound)
    (hmargin : 4 * (pads * growth params rows * bound) < q) :
    recoverSender params receiver knownUnit
      (subsetMask params seed bits + tensorHint params sender)
      (sourceLink params seed encryptedPads) = sender := by
  apply recoverSender_eq params hbase hq sender receiver knownUnit hunit _ _
    (pads * growth params rows * bound)
    (sourceLink_noise_bound params receiver seed bits encryptedPads bound hpad)
  rw [NoisyBinaryGadget.half_code_distance hlevels hq]
  have hpow : q = 2 * 2 ^ (params.levels - 1) := by
    calc
      q = 2 ^ params.levels := hq
      _ = 2 * 2 ^ (params.levels - 1) := by
        rw [← pow_succ']
        congr 1
        omega
  omega


/-- Instantiate the recovery attack with the project's actual public GSW pad
sampler. It needs neither the sender key nor the pad bits as attack inputs. -/
theorem recoverSender_publicSourceLink {q dimension pads samples : ℕ} [NeZero q]
    (params : Parameters q) (hbase : params.base = 2) (hlevels : 0 < params.levels)
    (hq : q = 2 ^ params.levels) (sender : Fin (dimension + 1) → ZMod q)
    (receiverSecret : Fin dimension → ZMod q)
    (key : GSWPublicKey.PublicKey q dimension samples)
    (seed : Matrix (Fin (dimension + 1)) (Fin pads) (ZMod q))
    (bits : Fin pads → Columns (dimension + 1) params.levels → Bool)
    (coins : Fin pads → Columns (dimension + 1) params.levels →
      GSWPublicKey.SelectorCoins samples ((dimension + 1) * params.levels)) (bound : ℕ)
    (hkey : ∀ sample, (LatticeCrypto.centeredRepr
      (vecMul (GSWOperations.extendedSecret receiverSecret)
        (GSWPublicKey.publicKeyView key) sample)).natAbs ≤ bound)
    (hmargin : 4 * (pads * growth params (dimension + 1) * (samples * bound)) < q) :
    recoverSender params (GSWOperations.extendedSecret receiverSecret) 0
      (subsetMask params seed bits + tensorHint params sender)
      (sourceLink params seed (fun pad column ↦
        GSWPublicKey.encryptMatrix params key (coins pad column) (bits pad column))) = sender := by
  apply recoverSender_sourceLink params hbase hlevels hq sender
    (GSWOperations.extendedSecret receiverSecret) 0
    (by simp [GSWOperations.extendedSecret]) seed bits _ (samples * bound) _ hmargin
  intro pad column
  simpa only [GSWPublicKey.encryptStored, GSWAccumulator.ciphertextView_storeCiphertext] using
    GSWPublicKey.noiseBound_encryptStored params receiverSecret key
      (coins pad column) (bits pad column) bound hkey


/-- Apply the recovered sender vector to a challenge body-gadget column. -/
def decodeChallenge {q rows : ℕ} [NeZero q] (params : Parameters q)
    (receiver : Fin rows → ZMod q) (knownUnit : Fin rows)
    (maskedHint publicLink : Hint params rows) (ciphertext : Ciphertext params rows)
    (level : Fin params.levels) : Bool :=
  decodeNearest 0 (TFHE.Gadget.Base.gadget params level)
    (vecMul (recoverSender params receiver knownUnit maskedHint publicLink) ciphertext
      (finProdFinEquiv (knownUnit, level)))

/-- The operational attacker uses only stored public hints, a stored challenge,
and its own receiver key. -/
def decodeStoredChallenge {q rows : ℕ} [NeZero q] (params : Parameters q)
    (receiver : Fin rows → ZMod q) (knownUnit : Fin rows)
    (maskedHint publicLink : StoredHint params rows)
    (ciphertext : GSWAccumulator.StoredCiphertext params rows) (level : Fin params.levels) : Bool :=
  let recovered := recoverStoredSender params receiver knownUnit maskedHint publicLink
  decodeNearest 0 (TFHE.Gadget.Base.gadget params level)
    (vecMul (fun row ↦ recovered.get row) (GSWAccumulator.ciphertextView params ciphertext)
      (finProdFinEquiv (knownUnit, level)))

theorem decodeStoredChallenge_eq {q rows : ℕ} [NeZero q] (params : Parameters q)
    (receiver : Fin rows → ZMod q) (knownUnit : Fin rows)
    (maskedHint publicLink : StoredHint params rows)
    (ciphertext : GSWAccumulator.StoredCiphertext params rows) (level : Fin params.levels) :
    decodeStoredChallenge params receiver knownUnit maskedHint publicLink ciphertext level =
      decodeChallenge params receiver knownUnit (hintView params maskedHint)
        (hintView params publicLink) (GSWAccumulator.ciphertextView params ciphertext) level := by
  simp only [decodeStoredChallenge, recoverStoredSender_get, decodeChallenge]

/-- The recovered key decrypts actual fresh public GSW challenges of either bit. -/
theorem decodeChallenge_publicSourceLink {q dimension pads receiverSamples senderSamples : ℕ}
    [NeZero q] (params : Parameters q) (hbase : params.base = 2)
    (hlevels : 0 < params.levels) (hq : q = 2 ^ params.levels)
    (senderSecret receiverSecret : Fin dimension → ZMod q)
    (receiverKey : GSWPublicKey.PublicKey q dimension receiverSamples)
    (senderKey : GSWPublicKey.PublicKey q dimension senderSamples)
    (seed : Matrix (Fin (dimension + 1)) (Fin pads) (ZMod q))
    (bits : Fin pads → Columns (dimension + 1) params.levels → Bool)
    (padCoins : Fin pads → Columns (dimension + 1) params.levels →
      GSWPublicKey.SelectorCoins receiverSamples ((dimension + 1) * params.levels))
    (challengeCoins : GSWPublicKey.SelectorCoins senderSamples ((dimension + 1) * params.levels))
    (message : Bool) (receiverBound senderBound : ℕ)
    (hreceiver : ∀ sample, (LatticeCrypto.centeredRepr
      (vecMul (GSWOperations.extendedSecret receiverSecret)
        (GSWPublicKey.publicKeyView receiverKey) sample)).natAbs ≤ receiverBound)
    (hsender : ∀ sample, (LatticeCrypto.centeredRepr
      (vecMul (GSWOperations.extendedSecret senderSecret)
        (GSWPublicKey.publicKeyView senderKey) sample)).natAbs ≤ senderBound)
    (hlink : 4 * (pads * growth params (dimension + 1) * (receiverSamples * receiverBound)) < q)
    (level : Fin params.levels)
    (hchallenge : 2 * (senderSamples * senderBound) <
      centeredDistance 0 (TFHE.Gadget.Base.gadget params level)) :
    decodeChallenge params (GSWOperations.extendedSecret receiverSecret) 0
      (subsetMask params seed bits + tensorHint params (GSWOperations.extendedSecret senderSecret))
      (sourceLink params seed (fun pad column ↦
        GSWPublicKey.encryptMatrix params receiverKey (padCoins pad column) (bits pad column)))
      (GSWAccumulator.ciphertextView params
        (GSWPublicKey.encryptStored params senderKey challengeCoins message)) level = message := by
  unfold decodeChallenge
  rw [recoverSender_publicSourceLink params hbase hlevels hq
    (GSWOperations.extendedSecret senderSecret) receiverSecret receiverKey seed bits padCoins
    receiverBound hreceiver hlink]
  change decrypt params senderSecret _ level = message
  exact decrypt_eq_bit params senderSecret _ message (senderSamples * senderBound) level
    (GSWPublicKey.noiseBound_encryptStored params senderSecret senderKey challengeCoins message
      senderBound hsender) hchallenge

end FormalProof4FHE.LWE.GSWLinkedDisclosure
