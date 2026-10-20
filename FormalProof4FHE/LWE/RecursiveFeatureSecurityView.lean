/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.RecursiveFeatureBootstrap
import FormalProof4FHE.LWE.RecursiveFeaturePublicKey

/-!
# The actual complete public-key and original-bit control security experiment

One sampled binary secret generates every recursive zero public-key column and
every original-bit refresh control. Their masks and scalar errors are sampled in
one joint experiment. All controls and public columns are materialized before
publication. Public product controls and circuit evaluation are deterministic
postprocessing of this view.

The standard one-time IND-CPA experiment is bounded by one explicit joint-view
replacement advantage plus the existing statistical subset-masking loss. The
replacement retains the actual marginal control law and resamples only the public
table. This module does NOT assume this advantage negligible or reduce it to
ordinary LWE. That reduction, including the cubic control messages, remains the
central security requirement; the bound is not a completed FHE security theorem.
-/

open Matrix OracleComp AsymmEncAlg

namespace FormalProof4FHE.LWE.RecursiveFeatureSecurityView

open RecursiveMultiplication RecursiveFeatureGSW RecursiveFeatureBootstrap

abbrev Dimension (n : ℕ) := RecursiveFeaturePublicKey.Dimension n
abbrev Table (q n p : ℕ) := RecursiveFeaturePublicKey.Table q n p
abbrev View {q : ℕ} (params : Parameters q) (n p : ℕ) := Table q n p × StoredOriginal params n
abbrev StoredView {q : ℕ} (params : Parameters q) (n p : ℕ) :=
  GSWPublicKey.PublicKey q (Dimension n) p × StoredOriginal params n

def scalarColumns {q : ℕ} (params : Parameters q) (n p : ℕ) : ℕ := p + n * (rows n * params.levels)
def errorCount {q : ℕ} (params : Parameters q) (n p : ℕ) : ℕ := scalarColumns params n p * (n + 1)

def errorColumnsEquiv {q : ℕ} (params : Parameters q) (n p : ℕ) :
    RecursiveQuadratic.Column n 0 (scalarColumns params n p) ≃ Fin (errorCount params n p) :=
  (RecursiveQuadratic.columnsEquiv n 0 (scalarColumns params n p)).trans
    (finCongr (by simp only [errorCount, zero_add]))

abbrev RawColumn {q : ℕ} (params : Parameters q) (n p : ℕ) :=
  RecursiveQuadratic.Column n 0 (scalarColumns params n p)
abbrev Challenge {q : ℕ} (params : Parameters q) (n p : ℕ) := Matrix (Fin n) (RawColumn params n p) (ZMod q)
abbrev Errors {q : ℕ} (params : Parameters q) (n p : ℕ) := RawColumn params n p → ZMod q
abbrev Draws {q : ℕ} (params : Parameters q) (n p : ℕ) :=
  (Fin n → Bool) × Challenge params n p × Errors params n p

noncomputable local instance {q : ℕ} [NeZero q] (params : Parameters q) (n p : ℕ) :
    SampleableType (Challenge params n p) := instSampleableTypeFinFunc

def publicColumn {q : ℕ} (params : Parameters q) {n p : ℕ} (index : Fin p) : Fin (scalarColumns params n p) :=
  finSumFinEquiv (.inl index)

def controlColumn {q : ℕ} (params : Parameters q) {n p : ℕ}
    (index : Fin n) (column : Fin (rows n * params.levels)) : Fin (scalarColumns params n p) :=
  finSumFinEquiv (.inr (finProdFinEquiv (index, column)))

def maskAt {q : ℕ} (params : Parameters q) {n p : ℕ} (challenge : Challenge params n p)
    (column : Fin (scalarColumns params n p)) : Matrix (Fin n) (Fin n) (ZMod q) :=
  fun row index ↦ challenge row (.inr (column, some index))

def innerAt {q : ℕ} (params : Parameters q) {n p : ℕ} (challenge : Challenge params n p)
    (column : Fin (scalarColumns params n p)) : Fin n → ZMod q :=
  fun row ↦ challenge row (.inr (column, none))

def errorsAt {q : ℕ} (params : Parameters q) {n p : ℕ} (errors : Errors params n p)
    (column : Fin (scalarColumns params n p)) : Fin n → ZMod q :=
  fun row ↦ errors (.inr (column, some row))

def bodyErrorAt {q : ℕ} (params : Parameters q) {n p : ℕ} (errors : Errors params n p)
    (column : Fin (scalarColumns params n p)) : ZMod q := errors (.inr (column, none))

/-- Masks and errors for zero columns and controls share exactly this sampled secret. -/
noncomputable def sampleDraws {q n p : ℕ} [NeZero q] (params : Parameters q)
    (secretSampler : ProbComp (Fin n → Bool)) (errorSampler : ProbComp (ZMod q)) : ProbComp (Draws params n p) := do
  let bits ← secretSampler
  let challenge ← $ᵗ Challenge params n p
  let errors ← ProbComp.sampleIID (errorCount params n p) errorSampler
  pure (bits, challenge, fun column ↦ errors (errorColumnsEquiv params n p column))

def publicTable {q n p : ℕ} [NeZero q] (params : Parameters q) (draws : Draws params n p) : Table q n p :=
  fun index ↦ flatten (freshCiphertext (GSWSelfKey.binaryEmbed draws.1) 0
    (maskAt params draws.2.1 (publicColumn params index))
    (innerAt params draws.2.1 (publicColumn params index))
    (errorsAt params draws.2.2 (publicColumn params index))
    (bodyErrorAt params draws.2.2 (publicColumn params index)))

def controls {q n p : ℕ} [NeZero q] (params : Parameters q) (draws : Draws params n p) : StoredOriginal params n :=
  freshOriginalStored params draws.1
    (fun index column ↦ maskAt params draws.2.1 (controlColumn params index column))
    (fun index column ↦ innerAt params draws.2.1 (controlColumn params index column))
    (fun index column ↦ errorsAt params draws.2.2 (controlColumn params index column))
    (fun index column ↦ bodyErrorAt params draws.2.2 (controlColumn params index column))

theorem public_column_phase {q n p : ℕ} [NeZero q] (params : Parameters q)
    (draws : Draws params n p) (index : Fin p) :
    RecursiveQuadratic.decrypt (GSWSelfKey.binaryEmbed draws.1)
      (unflatten (publicTable params draws index)) =
      bodyErrorAt params draws.2.2 (publicColumn params index) +
        dotProduct (errorsAt params draws.2.2 (publicColumn params index))
          (GSWSelfKey.binaryEmbed draws.1) := by
  simp only [publicTable, unflatten_flatten, decrypt_freshCiphertext, zero_add]

theorem controls_view {q n p : ℕ} [NeZero q] (params : Parameters q) (draws : Draws params n p) :
    originalView params (controls params draws) = freshOriginal params draws.1
      (fun index column ↦ maskAt params draws.2.1 (controlColumn params index column))
      (fun index column ↦ innerAt params draws.2.1 (controlColumn params index column))
      (fun index column ↦ errorsAt params draws.2.2 (controlColumn params index column))
      (fun index column ↦ bodyErrorAt params draws.2.2 (controlColumn params index column)) :=
  originalView_freshOriginalStored params _ _ _ _ _

/-- The exact original-bit control plaintext includes cubic gadget features. -/
theorem controls_phase {q n p : ℕ} [NeZero q] (params : Parameters q) (draws : Draws params n p)
    (index : Fin n) (column : Fin (rows n * params.levels)) :
    phase params (GSWSelfKey.binaryEmbed draws.1) (originalView params (controls params draws) index) column =
      GSWGadget.bitMessage (draws.1 index) *
          phase params (GSWSelfKey.binaryEmbed draws.1) (gadgetBatch params) column +
        bodyErrorAt params draws.2.2 (controlColumn params index column) +
        dotProduct (errorsAt params draws.2.2 (controlColumn params index column))
          (GSWSelfKey.binaryEmbed draws.1) := by
  rw [controls_view]
  exact decrypt_freshCiphertext _ _ _ _ _ _

def publicView {q n p : ℕ} [NeZero q] (params : Parameters q) (draws : Draws params n p) : View params n p :=
  (publicTable params draws, controls params draws)

def storeView {q n p : ℕ} {params : Parameters q} (view : View params n p) : StoredView params n p :=
  (GSWMasking.storeTable view.1, view.2)

noncomputable def keyView {q n p : ℕ} [NeZero q] (params : Parameters q)
    (secretSampler : ProbComp (Fin n → Bool)) (errorSampler : ProbComp (ZMod q)) : ProbComp (View params n p) :=
  publicView params <$> sampleDraws params secretSampler errorSampler

/-- Key generation retains only the binary secret privately and returns completed public data. -/
noncomputable def keygen {q n p : ℕ} [NeZero q] (params : Parameters q)
    (secretSampler : ProbComp (Fin n → Bool)) (errorSampler : ProbComp (ZMod q)) :
    ProbComp (StoredView params n p × (Fin n → Bool)) :=
  (fun draws ↦ (storeView (publicView params draws), draws.1)) <$> sampleDraws params secretSampler errorSampler

theorem keygen_public_evalDist {q n p : ℕ} [NeZero q] (params : Parameters q)
    (secretSampler : ProbComp (Fin n → Bool)) (errorSampler : ProbComp (ZMod q)) :
    𝒟[Prod.fst <$> keygen (p := p) params secretSampler errorSampler] =
      𝒟[storeView <$> keyView (p := p) params secretSampler errorSampler] := by
  simp [keygen, keyView, Functor.map_map]

noncomputable def scheme {q n p : ℕ} [NeZero q] (params : Parameters q) (level : Fin params.levels)
    (secretSampler : ProbComp (Fin n → Bool)) (errorSampler : ProbComp (ZMod q)) :
    AsymmEncAlg ProbComp Bool (StoredView params n p) (Fin n → Bool)
      (GSWAccumulator.StoredCiphertext params (Dimension n + 1)) where
  keygen := keygen params secretSampler errorSampler
  encrypt := fun view bit ↦ GSWMasking.encrypt params (GSWMasking.tableOfPublicKey view.1) bit
  decrypt := fun bits ciphertext ↦ pure (some (decode params (GSWSelfKey.binaryEmbed bits)
    (ofMatrix params (GSWAccumulator.ciphertextView params ciphertext)) level))

def fromINDCPA {q n p : ℕ} [NeZero q] (params : Parameters q) (level : Fin params.levels)
    (secretSampler : ProbComp (Fin n → Bool)) (errorSampler : ProbComp (ZMod q))
    (adversary : IND_CPA_Adv (scheme (p := p) params level secretSampler errorSampler)) :
    GSWMasking.Adversary (dimension := Dimension n) (samples := p) params (StoredOriginal params n) where
  State := adversary.State
  chooseMessages := adversary.chooseMessages
  distinguish := adversary.distinguish

theorem oneTime_game_evalDist {q n p : ℕ} [NeZero q] (params : Parameters q) (level : Fin params.levels)
    (secretSampler : ProbComp (Fin n → Bool)) (errorSampler : ProbComp (ZMod q))
    (adversary : IND_CPA_Adv (scheme (p := p) params level secretSampler errorSampler)) :
    𝒟[IND_CPA_OneTime_Game_ProbComp adversary] =
      𝒟[GSWMasking.game params (keyView params secretSampler errorSampler)
        (fromINDCPA params level secretSampler errorSampler adversary)] := by
  let observer := fun view : StoredView params n p ↦ do
    let bit ← $ᵗ Bool
    let messages ← adversary.chooseMessages view
    let ciphertext ← GSWMasking.encrypt params (GSWMasking.tableOfPublicKey view.1)
      (if bit then messages.1 else messages.2.1)
    let guess ← adversary.distinguish messages.2.2 ciphertext
    pure (bit == guess)
  have hswap := evalDist_bind_bind_swap ($ᵗ Bool) (keygen (p := p) params secretSampler errorSampler)
    (fun bit pair ↦ do
      let messages ← adversary.chooseMessages pair.1
      let ciphertext ← GSWMasking.encrypt params (GSWMasking.tableOfPublicKey pair.1.1)
        (if bit then messages.1 else messages.2.1)
      let guess ← adversary.distinguish messages.2.2 ciphertext
      pure (bit == guess))
  have hforget := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (keygen_public_evalDist (p := p) params secretSampler errorSampler) observer
  simpa [IND_CPA_OneTime_Game_ProbComp, scheme, GSWMasking.game,
    fromINDCPA, observer, storeView, monad_norm] using hswap.trans (by
      simpa [bind_map_left, observer, storeView, fromINDCPA, monad_norm] using hforget)

/-- Exactly the unresolved complete joint-view hop; no hardness property is assumed. -/
noncomputable def jointReplacementAdvantage {q n p : ℕ} [NeZero q] (params : Parameters q)
    (level : Fin params.levels) (secretSampler : ProbComp (Fin n → Bool)) (errorSampler : ProbComp (ZMod q))
    (adversary : IND_CPA_Adv (scheme (p := p) params level secretSampler errorSampler)) : ℝ :=
  GSWMasking.keyReplacementAdvantage params (keyView params secretSampler errorSampler)
    (fromINDCPA params level secretSampler errorSampler adversary)

theorem oneTime_abs_signedAdvantage_le {q n p : ℕ} [NeZero q] (params : Parameters q)
    (level : Fin params.levels) (secretSampler : ProbComp (Fin n → Bool)) (errorSampler : ProbComp (ZMod q))
    (adversary : IND_CPA_Adv (scheme (p := p) params level secretSampler errorSampler)) :
    |IND_CPA_OneTime_signedAdvantageReal (scheme params level secretSampler errorSampler) adversary| ≤
      jointReplacementAdvantage params level secretSampler errorSampler adversary +
        ((Dimension n + 1) * params.levels) * (Real.sqrt ((q : ℝ) ^ (Dimension n + 1) / (2 : ℝ) ^ p) / 2) := by
  have hgame := oneTime_game_evalDist params level secretSampler errorSampler adversary
  have hbound := GSWMasking.game_abs_advantage_le_keyReplacement_add_masking params
    (keyView params secretSampler errorSampler) (fromINDCPA params level secretSampler errorSampler adversary)
  unfold IND_CPA_OneTime_signedAdvantageReal
  rw [probOutput_congr (rfl : true = true) hgame]
  exact hbound

end FormalProof4FHE.LWE.RecursiveFeatureSecurityView
