/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.RecursiveFeatureGSW
import FormalProof4FHE.LWE.GSWMasking
import FormalProof4FHE.TFHE.KeySwitchRecovery

/-!
# Full-coordinate public masks for recursive-feature GSW

The public mask table consists of fresh recursive encryptions of zero, covering
all quadratic, linear and body coefficients. The retained view includes the
original linear public key and the remaining fixed quadratic hint batch.
Its whole-view replacement uses the existing ordinary-LWE reduction. In the
ideal branch an explicit raw-tape equivalence proves that every retained
ciphertext coordinate is uniform, and a second equivalence publishes the
flattened public mask table without losing the context.

This module does not justify cubic refresh controls or reusable bootstrapping.
-/

open Matrix OracleComp AsymmEncAlg
open scoped BigOperators ENNReal

namespace FormalProof4FHE.LWE.RecursiveFeaturePublicKey

open RecursiveMultiplication

abbrev Dimension (n : ℕ) := n * n + n
abbrev Table (q n p : ℕ) := GSWMasking.Table q (Dimension n) p
abbrev Context (q n r k : ℕ) := RecursivePublicKey.PublicKey q n r × RecursivePublicKey.Context q n k
abbrev View (q n r p k : ℕ) := Table q n p × Context q n r k

noncomputable local instance (q n k : ℕ) [NeZero q] :
    SampleableType ((Fin k × Option (Fin n)) → ZMod q) := instSampleableTypePiFintype
noncomputable local instance (q n k : ℕ) [NeZero q] :
    SampleableType (Matrix (Fin n) (Fin k × Option (Fin n)) (ZMod q)) := instSampleableTypeFinFunc
noncomputable local instance (q n r k : ℕ) [NeZero q] :
    SampleableType (RecursiveQuadratic.Column n r k → ZMod q) := instSampleableTypePiFintype
noncomputable local instance (q n r k : ℕ) [NeZero q] :
    SampleableType (Matrix (Fin n) (RecursiveQuadratic.Column n r k) (ZMod q)) := instSampleableTypeFinFunc

/-- Every raw hint coordinate is either retained or explicitly accounted for as unused mask data. -/
def splitHints {q n k : ℕ} : RecursivePublicKey.HintRaw q n k ≃
    RecursivePublicKey.Context q n k × Matrix (Fin n) (Fin k) (ZMod q) where
  toFun raw := (RecursivePublicKey.hintContext raw, fun row index ↦ raw.1 row (index, none))
  invFun pair :=
    (fun row column ↦ column.2.elim (pair.2 row column.1) (fun j ↦ (pair.1 column.1).1 row j),
      fun column ↦ column.2.elim (pair.1 column.1).2.2 (fun j ↦ (pair.1 column.1).2.1 j))
  left_inv raw := by
    apply Prod.ext
    · funext row column
      rcases column with ⟨index, column⟩
      cases column <;> rfl
    · funext column
      rcases column with ⟨index, column⟩
      cases column <;> rfl
  right_inv pair := by rfl

/-- Reassociation keeps the complete original view in the first component. -/
def rawViewEquiv {q n r k : ℕ} : RecursiveQuadratic.Raw (ZMod q) n r k ≃
    RecursiveQuadratic.View (ZMod q) n r k × Matrix (Fin n) (Fin k) (ZMod q) :=
  RecursivePublicKey.splitRaw.trans
    ((Equiv.prodCongr (Equiv.refl _) splitHints).trans (Equiv.prodAssoc _ _ _).symm)

theorem rawViewEquiv_fst {q n r k : ℕ} (raw : RecursiveQuadratic.Raw (ZMod q) n r k) :
    (rawViewEquiv raw).1 = RecursiveQuadratic.project raw := rfl

/-- This uniform law is asserted only for the justified ideal branch. -/
theorem idealView_uniform (q n r k : ℕ) [NeZero q] :
    𝒟[RecursiveQuadratic.idealView (R := ZMod q) (n := n) (p := r) (k := k)] =
      𝒟[$ᵗ RecursiveQuadratic.View (ZMod q) n r k] := by
  have hequiv := evalDist_map_bijective_uniform_cross
    (α := RecursiveQuadratic.Raw (ZMod q) n r k)
    (β := RecursiveQuadratic.View (ZMod q) n r k × Matrix (Fin n) (Fin k) (ZMod q))
    rawViewEquiv rawViewEquiv.bijective
  have hmap := evalDist_map_eq_of_evalDist_eq hequiv Prod.fst
  have hfst := evalDist_map_fst_uniformSample_prod
    (α := RecursiveQuadratic.View (ZMod q) n r k) (β := Matrix (Fin n) (Fin k) (ZMod q))
  simpa only [RecursiveQuadratic.idealView, Functor.map_map, Function.comp_def,
    rawViewEquiv_fst] using hmap.trans hfst

def tableEquiv {q n p : ℕ} : RecursivePublicKey.Context q n p ≃ Table q n p where
  toFun columns := fun sample ↦ RecursiveFeatureGSW.flatten (columns sample)
  invFun table := fun sample ↦ RecursiveFeatureGSW.unflatten (table sample)
  left_inv columns := by
    funext sample
    exact RecursiveFeatureGSW.unflatten_flatten (columns sample)
  right_inv table := by
    funext sample
    exact RecursiveFeatureGSW.flatten_unflatten (table sample)

def splitColumns {q n p k : ℕ} : RecursivePublicKey.Context q n (p + k) ≃
    RecursivePublicKey.Context q n p × RecursivePublicKey.Context q n k :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl _)).trans
    (Equiv.sumArrowEquivProdArrow (Fin p) (Fin k) (Ciphertext (ZMod q) n))

/-- Publish full recursive zero columns and retain all other public information. -/
def publish {q n r p k : ℕ} (original : RecursiveQuadratic.View (ZMod q) n r (p + k)) :
    View q n r p k :=
  (tableEquiv (splitColumns original.2).1, (original.1, (splitColumns original.2).2))

def publishEquiv {q n r p k : ℕ} : RecursiveQuadratic.View (ZMod q) n r (p + k) ≃ View q n r p k where
  toFun := publish
  invFun view := (view.2.1, splitColumns.symm (tableEquiv.symm view.1, view.2.2))
  left_inv original := by
    apply Prod.ext
    · rfl
    · simp only [publish, Equiv.symm_apply_apply]
      exact splitColumns.symm_apply_apply original.2
  right_inv view := by
    apply Prod.ext
    · simp only [publish, Equiv.apply_symm_apply]
    · apply Prod.ext
      · rfl
      · simp only [publish, Equiv.apply_symm_apply]

noncomputable def idealView (q n r p k : ℕ) [NeZero q] : ProbComp (View q n r p k) :=
  publish <$> (RecursiveQuadratic.idealView (R := ZMod q) (n := n) (p := r) (k := p + k))

theorem idealView_uniform_published (q n r p k : ℕ) [NeZero q] :
    𝒟[idealView q n r p k] = 𝒟[$ᵗ View q n r p k] := by
  have hmap := evalDist_map_eq_of_evalDist_eq (idealView_uniform q n r (p + k)) publish
  have hequiv := evalDist_map_bijective_uniform_cross
    (α := RecursiveQuadratic.View (ZMod q) n r (p + k)) (β := View q n r p k)
    publishEquiv publishEquiv.bijective
  exact hmap.trans hequiv

/-- The first p messages are zero; the retained tail has the fixed quadratic message law. -/
def joinedPolynomial {q n p k : ℕ} (tail : RecursiveQuadratic.Polynomial (ZMod q) n k) :
    RecursiveQuadratic.Polynomial (ZMod q) n (p + k) where
  quadratic index := Sum.elim (fun _ : Fin p ↦ 0) tail.quadratic (finSumFinEquiv.symm index)
  linear index := Sum.elim (fun _ : Fin p ↦ 0) tail.linear (finSumFinEquiv.symm index)
  constant index := Sum.elim (fun _ : Fin p ↦ 0) tail.constant (finSumFinEquiv.symm index)

theorem joinedPolynomial_zero_message {q n p k : ℕ}
    (tail : RecursiveQuadratic.Polynomial (ZMod q) n k) (secret : Fin n → ZMod q) (index : Fin p) :
    RecursiveQuadratic.message (joinedPolynomial tail) secret (finSumFinEquiv (.inl index)) = 0 := by
  simp [RecursiveQuadratic.message, joinedPolynomial]

theorem published_column_fresh_phase {q n r p k : ℕ}
    (tail : RecursiveQuadratic.Polynomial (ZMod q) n k) (secret : Fin n → ZMod q)
    (challenge : Matrix (Fin n) (RecursiveQuadratic.Column n r (p + k)) (ZMod q))
    (errors : RecursiveQuadratic.Column n r (p + k) → ZMod q) (index : Fin p) :
    dotProduct (RecursiveFeatureGSW.featureSecret secret)
      ((publish (RecursiveQuadratic.fresh (joinedPolynomial tail) secret challenge errors)).1 index) =
        errors (.inr (finSumFinEquiv (.inl index), none)) +
        dotProduct (fun row ↦ errors (.inr (finSumFinEquiv (.inl index), some row))) secret := by
  change dotProduct (RecursiveFeatureGSW.featureSecret secret)
    (RecursiveFeatureGSW.flatten ((RecursiveQuadratic.fresh (joinedPolynomial tail) secret challenge errors).2
      (finSumFinEquiv (.inl index)))) = _
  rw [← RecursiveFeatureGSW.decrypt_eq_dotProduct, RecursiveQuadratic.decrypt_fresh,
    joinedPolynomial_zero_message, zero_add]

theorem uniform_context_evalDist (q n r p k : ℕ) [NeZero q] :
    𝒟[Prod.snd <$> ($ᵗ View q n r p k)] = 𝒟[$ᵗ Context q n r k] := by
  have hequiv := evalDist_map_bijective_uniform_cross
    (α := View q n r p k) (β := Context q n r k × Table q n p)
    (Equiv.prodComm _ _) (Equiv.prodComm _ _).bijective
  have hmap := evalDist_map_eq_of_evalDist_eq hequiv Prod.fst
  have hfst := evalDist_map_fst_uniformSample_prod (α := Context q n r k) (β := Table q n p)
  simpa [Functor.map_map, Equiv.prodComm_apply] using hmap.trans hfst

/-- Uniform publication is already independent in every retained coordinate. -/
theorem uniformView_fixedpoint (q n r p k : ℕ) [NeZero q] :
    𝒟[GSWMasking.uniformView ($ᵗ View q n r p k)] = 𝒟[$ᵗ View q n r p k] := by
  let next := fun context : Context q n r k ↦ do
    let table ← $ᵗ Table q n p
    pure (table, context)
  have hm := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (uniform_context_evalDist q n r p k) next
  have hleft : 𝒟[GSWMasking.uniformView ($ᵗ View q n r p k)] =
      𝒟[($ᵗ Context q n r k) >>= next] := by
    simpa [GSWMasking.uniformView, next, monad_norm] using hm
  have hswap := evalDist_bind_bind_swap ($ᵗ Context q n r k) ($ᵗ Table q n p)
    (fun context table ↦ pure (table, context))
  have hpair := FiniteProduct.evalDist_independent_uniform_product
    (first := Table q n p) (second := Context q n r k)
  exact hleft.trans (by simpa only [next] using hswap.trans hpair)

abbrev Adversary {q n r p k : ℕ} [NeZero q] (params : Parameters q) :=
  GSWMasking.Adversary (dimension := Dimension n) (samples := p) params (Context q n r k)

def observe {q n r p k : ℕ} [NeZero q] (params : Parameters q)
    (adversary : Adversary (n := n) (r := r) (p := p) (k := k) params) (view : View q n r p k) :
    ProbComp Bool := do
  let bit ← $ᵗ Bool
  let messages ← adversary.chooseMessages (GSWMasking.storeTable view.1, view.2)
  let ciphertext ← GSWMasking.encrypt params view.1 (if bit then messages.1 else messages.2.1)
  let guess ← adversary.distinguish messages.2.2 ciphertext
  pure (bit == guess)

theorem game_eq_bind {q n r p k : ℕ} [NeZero q] (params : Parameters q)
    (viewSampler : ProbComp (View q n r p k))
    (adversary : Adversary (n := n) (r := r) (p := p) (k := k) params) :
    GSWMasking.game params viewSampler adversary = viewSampler >>= observe params adversary := rfl

theorem ideal_game_abs_advantage_le {q n r p k : ℕ} [NeZero q] (params : Parameters q)
    (adversary : Adversary (n := n) (r := r) (p := p) (k := k) params) :
    |Pr[= true | GSWMasking.game params (idealView q n r p k) adversary].toReal - 1 / 2| ≤
      ((Dimension n + 1) * params.levels) *
        (Real.sqrt ((q : ℝ) ^ (Dimension n + 1) / (2 : ℝ) ^ p) / 2) := by
  have hbound := GSWMasking.uniform_game_abs_advantage_le params ($ᵗ View q n r p k) adversary
  have hfixed := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (uniformView_fixedpoint q n r p k) (observe params adversary)
  have hideal := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (idealView_uniform_published q n r p k) (observe params adversary)
  rw [game_eq_bind, probOutput_congr (rfl : true = true) hfixed] at hbound
  simpa only [game_eq_bind, probOutput_congr (rfl : true = true) hideal] using hbound

noncomputable def freshView {q n r p k samples : ℕ} [NeZero q]
    (columns : RecursiveQuadratic.Column n r (p + k) ≃ Fin samples)
    (tail : RecursiveQuadratic.Polynomial (ZMod q) n k)
    (secretSampler : ProbComp (Fin n → ZMod q)) (errorSampler : ProbComp (ZMod q)) :
    ProbComp (View q n r p k) :=
  publish <$> RecursiveQuadratic.freshView columns (joinedPolynomial tail) secretSampler id errorSampler

/-- The complete published GSW view reduces to the existing ordinary-LWE observer.
The retained tail here is quadratic; this is not a cubic refresh-control security claim. -/
theorem sampled_game_abs_advantage_le {r p k samples : ℕ} (parameter : ℕ)
    (params : Parameters (RecursiveQuadraticParameters.modulus parameter))
    (columns : RecursiveQuadratic.Column (RecursiveQuadraticParameters.binaryDimension parameter * 1)
      r (p + k) ≃ Fin samples)
    (tail : RecursiveQuadratic.Polynomial (ZMod (RecursiveQuadraticParameters.modulus parameter))
      (RecursiveQuadraticParameters.binaryDimension parameter * 1) k)
    (adversary : Adversary (n := RecursiveQuadraticParameters.binaryDimension parameter * 1)
      (r := r) (p := p) (k := k) params) :
    |Pr[= true | GSWMasking.game params
      (freshView columns tail
        (FormalProof4FHE.BlockBinary.expand (ZMod (RecursiveQuadraticParameters.modulus parameter)) <$>
          ($ᵗ FormalProof4FHE.BlockBinary.Key 1 (RecursiveQuadraticParameters.binaryDimension parameter)))
        (UniformInterval.sample (RecursiveQuadraticParameters.modulus parameter)
          (RecursiveQuadraticParameters.radius parameter) (RecursiveQuadraticParameters.retries parameter)))
        adversary].toReal - 1 / 2| ≤
      RecursiveQuadraticParameters.ordinaryReductionLoss parameter columns (joinedPolynomial tail)
        (fun original ↦ observe params adversary (publish original)) +
      RecursiveQuadraticParameters.implementationLoss samples parameter +
      ((Dimension (RecursiveQuadraticParameters.binaryDimension parameter * 1) + 1) * params.levels) *
        (Real.sqrt ((RecursiveQuadraticParameters.modulus parameter : ℝ) ^
          (Dimension (RecursiveQuadraticParameters.binaryDimension parameter * 1) + 1) / (2 : ℝ) ^ p) / 2) := by
  have hview := RecursiveQuadraticParameters.sampled_advantage_le_narrowLWE parameter columns
    (joinedPolynomial tail) (fun original ↦ observe params adversary (publish original))
  have hmask := ideal_game_abs_advantage_le params adversary
  have hreal : GSWMasking.game params
      (freshView columns tail
        (FormalProof4FHE.BlockBinary.expand (ZMod (RecursiveQuadraticParameters.modulus parameter)) <$>
          ($ᵗ FormalProof4FHE.BlockBinary.Key 1 (RecursiveQuadraticParameters.binaryDimension parameter)))
        (UniformInterval.sample (RecursiveQuadraticParameters.modulus parameter)
          (RecursiveQuadraticParameters.radius parameter) (RecursiveQuadraticParameters.retries parameter))) adversary =
      RecursiveQuadratic.freshView columns (joinedPolynomial tail)
        ($ᵗ FormalProof4FHE.BlockBinary.Key 1 (RecursiveQuadraticParameters.binaryDimension parameter))
        (FormalProof4FHE.BlockBinary.expand (ZMod (RecursiveQuadraticParameters.modulus parameter)))
        (UniformInterval.sample (RecursiveQuadraticParameters.modulus parameter)
          (RecursiveQuadraticParameters.radius parameter) (RecursiveQuadraticParameters.retries parameter)) >>=
        fun original ↦ observe params adversary (publish original) := by
    simp [game_eq_bind, freshView, RecursiveQuadratic.freshView, monad_norm]
  have hideal : GSWMasking.game params
      (idealView (RecursiveQuadraticParameters.modulus parameter)
        (RecursiveQuadraticParameters.binaryDimension parameter * 1) r p k) adversary =
      RecursiveQuadratic.idealView >>= fun original ↦ observe params adversary (publish original) := by
    simp [game_eq_bind, idealView, monad_norm]
  unfold ProbComp.boolDistAdvantage at hview
  rw [← hreal, ← hideal] at hview
  exact (abs_sub_le _ _ (1 / 2 : ℝ)).trans (add_le_add hview hmask)

abbrev StoredView (q n r p k : ℕ) :=
  GSWPublicKey.PublicKey q (Dimension n) p × Context q n r k

def storeView {q n r p k : ℕ} (view : View q n r p k) : StoredView q n r p k :=
  (GSWMasking.storeTable view.1, view.2)

/-- Materialize the public table and keep only the original secret as the decryption key. -/
noncomputable def keygen {q n r p k samples : ℕ} [NeZero q]
    (columns : RecursiveQuadratic.Column n r (p + k) ≃ Fin samples)
    (tail : RecursiveQuadratic.Polynomial (ZMod q) n k)
    (secretSampler : ProbComp (Fin n → ZMod q)) (errorSampler : ProbComp (ZMod q)) :
    ProbComp (StoredView q n r p k × (Fin n → ZMod q)) := do
  let original ← RecursivePublicKey.keygen columns (joinedPolynomial tail) secretSampler errorSampler
  pure (storeView (publish original.1), original.2)

theorem keygen_public_evalDist {q n r p k samples : ℕ} [NeZero q]
    (columns : RecursiveQuadratic.Column n r (p + k) ≃ Fin samples)
    (tail : RecursiveQuadratic.Polynomial (ZMod q) n k)
    (secretSampler : ProbComp (Fin n → ZMod q)) (errorSampler : ProbComp (ZMod q)) :
    𝒟[Prod.fst <$> keygen columns tail secretSampler errorSampler] =
      𝒟[storeView <$> freshView columns tail secretSampler errorSampler] := by
  have h := evalDist_map_eq_of_evalDist_eq
    (RecursivePublicKey.keygen_public_evalDist columns (joinedPolynomial tail) secretSampler errorSampler)
    (fun original ↦ storeView (publish original))
  simpa [keygen, freshView, monad_norm] using h

def ofStored {q n : ℕ} (params : Parameters q)
    (ciphertext : GSWAccumulator.StoredCiphertext params (Dimension n + 1)) : RecursiveFeatureGSW.Batch params n :=
  RecursiveFeatureGSW.ofMatrix params (GSWAccumulator.ciphertextView params ciphertext)

noncomputable def scheme {q n r p k samples : ℕ} [NeZero q]
    (params : Parameters q) (level : Fin params.levels)
    (columns : RecursiveQuadratic.Column n r (p + k) ≃ Fin samples)
    (tail : RecursiveQuadratic.Polynomial (ZMod q) n k)
    (secretSampler : ProbComp (Fin n → ZMod q)) (errorSampler : ProbComp (ZMod q)) :
    AsymmEncAlg ProbComp Bool (StoredView q n r p k) (Fin n → ZMod q)
      (GSWAccumulator.StoredCiphertext params (Dimension n + 1)) where
  keygen := keygen columns tail secretSampler errorSampler
  encrypt := fun view bit ↦ GSWMasking.encrypt params (GSWMasking.tableOfPublicKey view.1) bit
  decrypt := fun secret ciphertext ↦
    pure (some (RecursiveFeatureGSW.decode params secret (ofStored params ciphertext) level))

def fromINDCPA {q n r p k samples : ℕ} [NeZero q]
    (params : Parameters q) (level : Fin params.levels)
    (columns : RecursiveQuadratic.Column n r (p + k) ≃ Fin samples)
    (tail : RecursiveQuadratic.Polynomial (ZMod q) n k)
    (secretSampler : ProbComp (Fin n → ZMod q)) (errorSampler : ProbComp (ZMod q))
    (adversary : IND_CPA_Adv (scheme params level columns tail secretSampler errorSampler)) :
    Adversary (n := n) (r := r) (p := p) (k := k) params where
  State := adversary.State
  chooseMessages := adversary.chooseMessages
  distinguish := adversary.distinguish

/-- The standard one-time experiment retains exactly the same published view. -/
theorem oneTime_game_evalDist {q n r p k samples : ℕ} [NeZero q]
    (params : Parameters q) (level : Fin params.levels)
    (columns : RecursiveQuadratic.Column n r (p + k) ≃ Fin samples)
    (tail : RecursiveQuadratic.Polynomial (ZMod q) n k)
    (secretSampler : ProbComp (Fin n → ZMod q)) (errorSampler : ProbComp (ZMod q))
    (adversary : IND_CPA_Adv (scheme params level columns tail secretSampler errorSampler)) :
    𝒟[IND_CPA_OneTime_Game_ProbComp adversary] =
      𝒟[GSWMasking.game params (freshView columns tail secretSampler errorSampler)
        (fromINDCPA params level columns tail secretSampler errorSampler adversary)] := by
  let observer := fun view : StoredView q n r p k ↦ do
    let bit ← $ᵗ Bool
    let messages ← adversary.chooseMessages view
    let ciphertext ← GSWMasking.encrypt params (GSWMasking.tableOfPublicKey view.1)
      (if bit then messages.1 else messages.2.1)
    let guess ← adversary.distinguish messages.2.2 ciphertext
    pure (bit == guess)
  have hswap := evalDist_bind_bind_swap ($ᵗ Bool) (keygen columns tail secretSampler errorSampler)
    (fun bit pair ↦ do
      let messages ← adversary.chooseMessages pair.1
      let ciphertext ← GSWMasking.encrypt params (GSWMasking.tableOfPublicKey pair.1.1)
        (if bit then messages.1 else messages.2.1)
      let guess ← adversary.distinguish messages.2.2 ciphertext
      pure (bit == guess))
  have hforget := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (keygen_public_evalDist columns tail secretSampler errorSampler) observer
  simpa [IND_CPA_OneTime_Game_ProbComp, scheme, game_eq_bind, fromINDCPA,
    observer, observe, storeView, monad_norm] using hswap.trans (by
      simpa [bind_map_left, observer, storeView, fromINDCPA, observe, monad_norm] using hforget)

abbrev Coins {q : ℕ} (params : Parameters q) (n p : ℕ) :=
  GSWMasking.Coins p ((Dimension n + 1) * params.levels)

def encryptWithCoins {q n p : ℕ} [NeZero q] (params : Parameters q)
    (table : Table q n p) (coins : Coins params n p) (bit : Bool) :
    GSWAccumulator.StoredCiphertext params (Dimension n + 1) :=
  GSWPublicKey.encryptStored params (GSWMasking.storeTable table) (GSWMasking.storeCoins coins) bit

theorem encrypt_eq_uniformCoins {q n p : ℕ} [NeZero q] (params : Parameters q)
    (table : Table q n p) (bit : Bool) :
    GSWMasking.encrypt params table bit =
      (fun coins ↦ encryptWithCoins params table coins bit) <$> ($ᵗ Coins params n p) := rfl

theorem published_column_fresh_bound {q n r p k : ℕ} [NeZero q]
    (tail : RecursiveQuadratic.Polynomial (ZMod q) n k) (secret : Fin n → ZMod q)
    (challenge : Matrix (Fin n) (RecursiveQuadratic.Column n r (p + k)) (ZMod q))
    (errors : RecursiveQuadratic.Column n r (p + k) → ZMod q) (bound : ℕ)
    (hsecret : ∀ row, secret row = 0 ∨ secret row = 1)
    (herrors : ∀ column, (LatticeCrypto.centeredRepr (errors column)).natAbs ≤ bound) (index : Fin p) :
    (LatticeCrypto.centeredRepr (dotProduct (RecursiveFeatureGSW.featureSecret secret)
      ((publish (RecursiveQuadratic.fresh (joinedPolynomial tail) secret challenge errors)).1 index))).natAbs ≤
        (n + 1) * bound := by
  change (LatticeCrypto.centeredRepr (dotProduct (RecursiveFeatureGSW.featureSecret secret)
    (RecursiveFeatureGSW.flatten ((RecursiveQuadratic.fresh (joinedPolynomial tail) secret challenge errors).2
      (finSumFinEquiv (.inl index)))))).natAbs ≤ _
  rw [← RecursiveFeatureGSW.decrypt_eq_dotProduct]
  have h := RecursiveQuadratic.decrypt_fresh_binary_error_bound (joinedPolynomial tail) secret challenge errors
    bound hsecret herrors (finSumFinEquiv (.inl index))
  simpa only [joinedPolynomial_zero_message, sub_zero] using h

/-- Gadget addition cancels; no assumption about a uniform derived secret is used. -/
theorem noise_encryptWithCoins {q n p : ℕ} [NeZero q] (params : Parameters q)
    (secret : Fin n → ZMod q) (table : Table q n p) (coins : Coins params n p) (bit : Bool) :
    RecursiveFeatureGSW.noise params secret (ofStored params (encryptWithCoins params table coins bit))
      (GSWGadget.bitMessage bit) =
        vecMul (fun sample ↦ dotProduct (RecursiveFeatureGSW.featureSecret secret) (table sample))
          (GSWPublicKey.selectors (GSWMasking.storeCoins coins)) := by
  rw [RecursiveFeatureGSW.noise_eq_gswNoise]
  simp only [ofStored, RecursiveFeatureGSW.matrix_ofMatrix, encryptWithCoins,
    GSWPublicKey.encryptStored]
  unfold RecursiveFeatureGSW.rows
  rw [GSWAccumulator.ciphertextView_storeCiphertext]
  simp only [GSWPublicKey.encryptMatrix, GSWOperations.noise, vecMul_add, vecMul_smul,
    ← vecMul_vecMul, GSWMasking.storeTable, GSWPublicKey.publicKeyView_storePublicKey]
  change _ = vecMul (vecMul (RecursiveFeatureGSW.featureSecret secret)
    (fun row sample ↦ table sample row)) (GSWPublicKey.selectors (GSWMasking.storeCoins coins))
  abel

theorem noiseBound_encryptWithCoins {q n p : ℕ} [NeZero q] (params : Parameters q)
    (secret : Fin n → ZMod q) (table : Table q n p) (coins : Coins params n p) (bit : Bool) (bound : ℕ)
    (hkey : ∀ sample, (LatticeCrypto.centeredRepr
      (dotProduct (RecursiveFeatureGSW.featureSecret secret) (table sample))).natAbs ≤ bound) :
    RecursiveFeatureGSW.NoiseBound params secret (ofStored params (encryptWithCoins params table coins bit))
      (GSWGadget.bitMessage bit) (p * bound) := by
  intro column
  rw [noise_encryptWithCoins]
  change (LatticeCrypto.centeredRepr (∑ sample, dotProduct (RecursiveFeatureGSW.featureSecret secret) (table sample) *
    GSWPublicKey.selectors (GSWMasking.storeCoins coins) sample column)).natAbs ≤ _
  have hsum := centered_sum_bound
    (fun sample : Fin p ↦ dotProduct (RecursiveFeatureGSW.featureSecret secret) (table sample) *
      GSWPublicKey.selectors (GSWMasking.storeCoins coins) sample column) bound
  simp only [Fintype.card_fin] at hsum
  apply hsum
  intro sample
  have h := (TFHE.NoiseBounds.centeredRepr_mul_natAbs_le _ _).trans
    (Nat.mul_le_mul (hkey sample) (GSWPublicKey.selectors_bound (GSWMasking.storeCoins coins) sample column))
  simpa only [Nat.mul_one] using h

theorem decode_encryptWithCoins {q n p : ℕ} [NeZero q] (params : Parameters q)
    (secret : Fin n → ZMod q) (table : Table q n p) (coins : Coins params n p)
    (bit : Bool) (bound : ℕ) (level : Fin params.levels)
    (hkey : ∀ sample, (LatticeCrypto.centeredRepr
      (dotProduct (RecursiveFeatureGSW.featureSecret secret) (table sample))).natAbs ≤ bound)
    (hmargin : 2 * (p * bound) < TFHE.BootstrappingCorrectness.centeredDistance
      0 (TFHE.Gadget.Base.gadget params level)) :
    RecursiveFeatureGSW.decode params secret (ofStored params (encryptWithCoins params table coins bit)) level = bit :=
  RecursiveFeatureGSW.decode_eq_bit params secret _ bit _ level
    (noiseBound_encryptWithCoins params secret table coins bit bound hkey) hmargin

/-- Supported key-generation and encryption outcomes satisfy the standard correctness experiment. -/
theorem correctExp_supported {q n r p k samples : ℕ} [NeZero q]
    (params : Parameters q) (level : Fin params.levels)
    (columns : RecursiveQuadratic.Column n r (p + k) ≃ Fin samples)
    (tail : RecursiveQuadratic.Polynomial (ZMod q) n k)
    (secretSampler : ProbComp (Fin n → ZMod q)) (errorSampler : ProbComp (ZMod q)) (bound : ℕ)
    (hsecret : ∀ secret ∈ support secretSampler, ∀ row, secret row = 0 ∨ secret row = 1)
    (herror : ∀ error ∈ support errorSampler, (LatticeCrypto.centeredRepr error).natAbs ≤ bound)
    (hmargin : 2 * (p * ((n + 1) * bound)) < TFHE.BootstrappingCorrectness.centeredDistance
      0 (TFHE.Gadget.Base.gadget params level))
    (bit result : Bool)
    (hresult : result ∈ support ((scheme params level columns tail secretSampler errorSampler).CorrectExp bit)) :
    result = true := by
  simp only [scheme, CorrectExp, mem_support_bind_iff] at hresult
  obtain ⟨pair, hpair, ciphertext, hciphertext, output, houtput, hresult⟩ := hresult
  simp only [keygen, RecursivePublicKey.keygen, mem_support_bind_iff] at hpair
  obtain ⟨original, horiginal, hpair⟩ := hpair
  obtain ⟨secret, hsecretSupport, challenge, _, errors, herrors, horiginal⟩ := horiginal
  simp only [support_pure, Set.mem_singleton_iff] at horiginal hpair
  subst original
  subst pair
  simp only [storeView, GSWMasking.tableOfPublicKey_storeTable] at hciphertext
  rw [encrypt_eq_uniformCoins] at hciphertext
  obtain ⟨coins, _, hcoins⟩ := mem_support_map_peel _ _ hciphertext
  subst ciphertext
  have heach : ∀ column, (LatticeCrypto.centeredRepr (errors (columns column))).natAbs ≤ bound := by
    intro column
    exact herror _ (TFHE.Native.KeySwitchRecovery.mem_support_mOfFn_apply _ _ errors herrors _)
  have hdecode := decode_encryptWithCoins params secret
    (publish (RecursiveQuadratic.fresh (joinedPolynomial tail) secret challenge
      (fun column ↦ errors (columns column)))).1 coins bit ((n + 1) * bound) level
    (published_column_fresh_bound tail secret challenge _ bound (hsecret secret hsecretSupport) heach) hmargin
  simp only [support_pure, Set.mem_singleton_iff] at houtput hresult
  subst output
  rw [hdecode] at hresult
  simpa only [decide_true] using hresult

theorem correctExp_probability_one {q n r p k samples : ℕ} [NeZero q]
    (params : Parameters q) (level : Fin params.levels)
    (columns : RecursiveQuadratic.Column n r (p + k) ≃ Fin samples)
    (tail : RecursiveQuadratic.Polynomial (ZMod q) n k)
    (secretSampler : ProbComp (Fin n → ZMod q)) (errorSampler : ProbComp (ZMod q)) (bound : ℕ)
    (hsecret : ∀ secret ∈ support secretSampler, ∀ row, secret row = 0 ∨ secret row = 1)
    (herror : ∀ error ∈ support errorSampler, (LatticeCrypto.centeredRepr error).natAbs ≤ bound)
    (hmargin : 2 * (p * ((n + 1) * bound)) < TFHE.BootstrappingCorrectness.centeredDistance
      0 (TFHE.Gadget.Base.gadget params level)) (bit : Bool) :
    Pr[= true | (scheme params level columns tail secretSampler errorSampler).CorrectExp bit] = 1 := by
  apply (probOutput_eq_one_iff_forall _ _).mpr
  exact ⟨by simp, fun result hresult ↦ correctExp_supported params level columns tail
    secretSampler errorSampler bound hsecret herror hmargin bit result hresult⟩

end FormalProof4FHE.LWE.RecursiveFeaturePublicKey
