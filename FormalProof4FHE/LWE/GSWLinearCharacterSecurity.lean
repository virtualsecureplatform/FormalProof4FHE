/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/
import FormalProof4FHE.LWE.GSWLinearCharacterCompiler
import FormalProof4FHE.LWE.RecursiveFeaturePublicKey

/-!
# Complete-view security of publicly compiled cubic controls

One retained ordinary-LWE batch supplies every character compiler. Each
correction is added to a fresh recursive zero ciphertext from the SAME source
key as the public encryption table. The complete retained context is transformed
publicly, including every control simultaneously. This is a reversible
translation conditional on the retained source, even for nonlinear builders.

The sampled plaintext game inherits the existing uniform-secret ordinary-LWE
bound. No independence between controls or table and controls is assumed.
Supported correctness is proved for the actual joint source draw below.
Efficient asymptotic coefficient shortness and polynomial-time closure are
still unproved; this is not a completed FHE security theorem.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.LWE.GSWLinearCharacterSecurity

open GSWLinearCharacterCompiler

variable {q n m p k : ℕ} {P : Type} [Fintype P]

abbrev Builder (q n m k : ℕ) (P : Type) :=
  Matrix (Fin n) (Fin m) (ZMod q) → Fin k → Matrix P (Fin m) (ZMod q)

def zeroPolynomial (q n k : ℕ) : RecursiveQuadratic.Polynomial (ZMod q) n k where
  quadratic := fun _ ↦ 0
  linear := fun _ ↦ 0
  constant := fun _ ↦ 0

def correction (first second : P → Fin n) (builder : Builder q n m k P)
    (source : BatchTranscript (ZMod q) n m) (index : Fin k) :
    RecursiveQuadratic.Ciphertext (ZMod q) n :=
  compileCanonical first second source.1 (builder source.1 index) source.2

/-- The retained source is common to ALL controls. No secret is an input. -/
def context (first second : P → Fin n) (builder : Builder q n m k P)
    (original : RecursiveFeaturePublicKey.Context q n m k) :
    RecursiveFeaturePublicKey.Context q n m k :=
  (original.1, fun index ↦ addZero (original.2 index)
    (correction first second builder original.1 index))

def uncontext (first second : P → Fin n) (builder : Builder q n m k P)
    (compiled : RecursiveFeaturePublicKey.Context q n m k) :
    RecursiveFeaturePublicKey.Context q n m k :=
  (compiled.1, fun index ↦ compiled.2 index - correction first second builder compiled.1 index)

theorem context_left_inverse (first second : P → Fin n) (builder : Builder q n m k P) :
    Function.LeftInverse (uncontext first second builder) (context first second builder) := by
  intro original
  apply Prod.ext
  · rfl
  · funext index
    simp only [context, uncontext, addZero]
    apply Prod.ext
    · exact add_sub_cancel_right _ _
    · apply Prod.ext <;> exact add_sub_cancel_right _ _

theorem context_right_inverse (first second : P → Fin n) (builder : Builder q n m k P) :
    Function.RightInverse (uncontext first second builder) (context first second builder) := by
  intro compiled
  apply Prod.ext
  · rfl
  · funext index
    simp only [context, uncontext, addZero, Prod.fst_sub, Prod.snd_sub]
    apply Prod.ext
    · exact sub_add_cancel _ _
    · apply Prod.ext <;> exact sub_add_cancel _ _

def contextEquiv (first second : P → Fin n) (builder : Builder q n m k P) :
    RecursiveFeaturePublicKey.Context q n m k ≃ RecursiveFeaturePublicKey.Context q n m k where
  toFun := context first second builder
  invFun := uncontext first second builder
  left_inv := context_left_inverse first second builder
  right_inv := context_right_inverse first second builder

def materialize (first second : P → Fin n) (builder : Builder q n m k P)
    (original : RecursiveFeaturePublicKey.View q n m p k) :
    RecursiveFeaturePublicKey.View q n m p k :=
  (original.1, context first second builder original.2)

def viewEquiv (first second : P → Fin n) (builder : Builder q n m k P) :
    RecursiveFeaturePublicKey.View q n m p k ≃ RecursiveFeaturePublicKey.View q n m p k :=
  Equiv.prodCongr (Equiv.refl _) (contextEquiv first second builder)

theorem viewEquiv_apply (first second : P → Fin n) (builder : Builder q n m k P)
    (original : RecursiveFeaturePublicKey.View q n m p k) :
    viewEquiv first second builder original = materialize first second builder original := rfl

variable [NeZero q]

noncomputable local instance :
    SampleableType (Matrix (Fin n) (RecursiveQuadratic.Column n m (p + k)) (ZMod q)) :=
  instSampleableTypeFinFunc

/-- Uniformity is for the entire retained view, not just separate marginals. -/
theorem materialize_uniform (first second : P → Fin n) (builder : Builder q n m k P) :
    𝒟[materialize (p := p) first second builder <$>
      ($ᵗ RecursiveFeaturePublicKey.View q n m p k)] =
        𝒟[$ᵗ RecursiveFeaturePublicKey.View q n m p k] := by
  exact evalDist_map_bijective_uniform_cross
    (α := RecursiveFeaturePublicKey.View q n m p k)
    (β := RecursiveFeaturePublicKey.View q n m p k)
    (viewEquiv (p := p) first second builder) (viewEquiv first second builder).bijective

def liftAdversary (params : GSWGadget.Parameters q)
    (first second : P → Fin n) (builder : Builder q n m k P)
    (adversary : RecursiveFeaturePublicKey.Adversary (n := n) (r := m) (p := p) (k := k) params) :
    RecursiveFeaturePublicKey.Adversary (n := n) (r := m) (p := p) (k := k) params where
  State := adversary.State
  chooseMessages view := adversary.chooseMessages (view.1, context first second builder view.2)
  distinguish := adversary.distinguish

/-- Exact equality for adaptive messages and the complete ciphertext continuation. -/
theorem game_materialize (params : GSWGadget.Parameters q)
    (first second : P → Fin n) (builder : Builder q n m k P)
    (sampler : ProbComp (RecursiveFeaturePublicKey.View q n m p k))
    (adversary : RecursiveFeaturePublicKey.Adversary (n := n) (r := m) (p := p) (k := k) params) :
    GSWMasking.game params (materialize first second builder <$> sampler) adversary =
      GSWMasking.game params sampler (liftAdversary params first second builder adversary) := by
  simp [GSWMasking.game, materialize, liftAdversary, monad_norm]

/-- This sampler materializes all controls jointly after one same-key source draw. -/
noncomputable def freshView {samples : ℕ}
    (first second : P → Fin n) (builder : Builder q n m k P)
    (columns : RecursiveQuadratic.Column n m (p + k) ≃ Fin samples)
    (secretSampler : ProbComp (Fin n → ZMod q)) (errorSampler : ProbComp (ZMod q)) :
    ProbComp (RecursiveFeaturePublicKey.View q n m p k) :=
  materialize first second builder <$>
    RecursiveFeaturePublicKey.freshView columns (zeroPolynomial q n k) secretSampler errorSampler

/-- The complete public simulator consumes one ordinary source and no key. -/
def sourceSimulator {samples : ℕ}
    (first second : P → Fin n) (builder : Builder q n m k P)
    (columns : RecursiveQuadratic.Column n m (p + k) ≃ Fin samples)
    (raw : BatchTranscript (ZMod q) n samples) : RecursiveFeaturePublicKey.View q n m p k :=
  materialize first second builder (RecursiveFeaturePublicKey.publish
    (RecursiveQuadratic.simulate
      (RecursiveFeaturePublicKey.joinedPolynomial (zeroPolynomial q n k))
      (RecursiveQuadratic.reindex columns raw)))

theorem sourceSimulator_real {samples : ℕ}
    (first second : P → Fin n) (builder : Builder q n m k P)
    (columns : RecursiveQuadratic.Column n m (p + k) ≃ Fin samples)
    (secretSampler : ProbComp (Fin n → ZMod q)) (errorSampler : ProbComp (ZMod q)) :
    𝒟[sourceSimulator first second builder columns <$>
      LearningWithErrors.distr (AffineCircular.ordinaryProblem n samples secretSampler id errorSampler)] =
        𝒟[freshView first second builder columns secretSampler errorSampler] := by
  have h := evalDist_map_eq_of_evalDist_eq
    (RecursiveQuadratic.real_evalDist columns
      (RecursiveFeaturePublicKey.joinedPolynomial (zeroPolynomial q n k)) secretSampler id errorSampler)
    (fun original ↦ materialize first second builder (RecursiveFeaturePublicKey.publish original))
  simpa [sourceSimulator, freshView, RecursiveFeaturePublicKey.freshView,
    RecursiveQuadratic.freshView, monad_norm] using h

/-- One full-view ideal, including the common retained source and all cubic
controls. This is stronger than separate ciphertext-marginal statements. -/
theorem sourceSimulator_uniform {samples : ℕ}
    (first second : P → Fin n) (builder : Builder q n m k P)
    (columns : RecursiveQuadratic.Column n m (p + k) ≃ Fin samples)
    (secretSampler : ProbComp (Fin n → ZMod q)) (errorSampler : ProbComp (ZMod q)) :
    𝒟[sourceSimulator first second builder columns <$>
      LearningWithErrors.uniformDistr (AffineCircular.ordinaryProblem n samples secretSampler id errorSampler)] =
        𝒟[$ᵗ RecursiveFeaturePublicKey.View q n m p k] := by
  have h := evalDist_map_eq_of_evalDist_eq
    (RecursiveQuadratic.uniform_evalDist columns
      (RecursiveFeaturePublicKey.joinedPolynomial (zeroPolynomial q n k)) secretSampler id errorSampler)
    (fun original ↦ materialize first second builder (RecursiveFeaturePublicKey.publish original))
  have hi := evalDist_map_eq_of_evalDist_eq
    (RecursiveFeaturePublicKey.idealView_uniform_published q n m p k)
    (materialize first second builder)
  calc
    _ = 𝒟[materialize first second builder <$>
        RecursiveFeaturePublicKey.idealView q n m p k] := by
      change 𝒟[(fun raw ↦ materialize first second builder (RecursiveFeaturePublicKey.publish
        (RecursiveQuadratic.simulate (RecursiveFeaturePublicKey.joinedPolynomial (zeroPolynomial q n k))
          (RecursiveQuadratic.reindex columns raw)))) <$>
        LearningWithErrors.uniformDistr (AffineCircular.ordinaryProblem n samples secretSampler id errorSampler)] = _
      simpa only [RecursiveFeaturePublicKey.idealView, Functor.map_map, Function.comp_def] using h
    _ = _ := hi.trans (materialize_uniform first second builder)

/-- One complete source draw, with its original key kept private. -/
def freshDraw (first second : P → Fin n) (builder : Builder q n m k P)
    (secret : Fin n → ZMod q)
    (masks : Matrix (Fin n) (RecursiveQuadratic.Column n m (p + k)) (ZMod q))
    (errors : RecursiveQuadratic.Column n m (p + k) → ZMod q) :
    RecursiveFeaturePublicKey.View q n m p k :=
  materialize first second builder (RecursiveFeaturePublicKey.publish
    (RecursiveQuadratic.fresh (RecursiveFeaturePublicKey.joinedPolynomial (zeroPolynomial q n k))
      secret masks errors))

/-- This is the very draw used by the security sampler, including the retained
base, full public table and every control. -/
theorem freshView_eq_draw {samples : ℕ}
    (first second : P → Fin n) (builder : Builder q n m k P)
    (columns : RecursiveQuadratic.Column n m (p + k) ≃ Fin samples)
    (secretSampler : ProbComp (Fin n → ZMod q)) (errorSampler : ProbComp (ZMod q)) :
    freshView first second builder columns secretSampler errorSampler = (do
      let secret ← secretSampler
      let masks ← $ᵗ Matrix (Fin n) (RecursiveQuadratic.Column n m (p + k)) (ZMod q)
      let errors ← ProbComp.sampleIID samples errorSampler
      pure (freshDraw first second builder secret masks (fun column ↦ errors (columns column)))) := by
  simp [freshView, freshDraw, RecursiveFeaturePublicKey.freshView,
    RecursiveQuadratic.freshView, monad_norm]

/-- Uniform in all masks, every binary key and ALL supported errors of the ONE
shared source. Thus no independent-source or per-slot correctness premise is used. -/
theorem freshDraw_control_error_bound
    (first second : P → Fin n) (hpair : ∀ pair, first pair ≠ second pair)
    (builder : Builder q n m k P) (bits : Fin n → Bool)
    (masks : Matrix (Fin n) (RecursiveQuadratic.Column n m (p + k)) (ZMod q))
    (errors : RecursiveQuadratic.Column n m (p + k) → ZMod q) (E : ℕ)
    (herror : ∀ column, (LatticeCrypto.centeredRepr (errors column)).natAbs ≤ E)
    (index : Fin k) :
    let a : Matrix (Fin n) (Fin m) (ZMod q) := fun row column ↦ masks row (.inl column)
    (LatticeCrypto.centeredRepr
      (RecursiveQuadratic.decrypt (GSWSelfKey.binaryEmbed bits)
        ((freshDraw first second builder (GSWSelfKey.binaryEmbed bits) masks errors).2.2 index) -
          cubicPhase first second a (builder a index) (GSWSelfKey.binaryEmbed bits))).natAbs ≤
      (n + 1) * E + (∑ pair, ∑ column,
        (LatticeCrypto.centeredRepr (builder a index pair column)).natAbs) * E := by
  let poly := RecursiveFeaturePublicKey.joinedPolynomial (p := p) (zeroPolynomial q n k)
  let original := RecursiveQuadratic.fresh poly (GSWSelfKey.binaryEmbed bits) masks errors
  let source : BatchTranscript (ZMod q) n m := original.1
  let control : Fin (p + k) := finSumFinEquiv (.inr index)
  have hmessage : RecursiveQuadratic.message poly (GSWSelfKey.binaryEmbed bits) control = 0 := by
    simp [poly, control, RecursiveQuadratic.message, RecursiveFeaturePublicKey.joinedPolynomial,
      zeroPolynomial]
  have hs : ∀ row, GSWSelfKey.binaryEmbed (R := ZMod q) bits row = 0 ∨
      GSWSelfKey.binaryEmbed (R := ZMod q) bits row = 1 := by
    intro row
    cases hb : bits row <;> simp [GSWSelfKey.binaryEmbed, hb]
  have hz := RecursiveQuadratic.decrypt_fresh_binary_error_bound poly
    (GSWSelfKey.binaryEmbed bits) masks errors E hs herror control
  rw [hmessage, sub_zero] at hz
  have hzero : (LatticeCrypto.centeredRepr (RecursiveQuadratic.decrypt
      (GSWSelfKey.binaryEmbed bits)
      ((RecursiveFeaturePublicKey.splitColumns original.2).2 index))).natAbs ≤ (n + 1) * E := by
    exact hz
  exact phase_error_bound_with_zero first second hpair source.1 (builder source.1 index)
    bits (fun column ↦ errors (.inl column)) E ((n + 1) * E) (fun column ↦ herror (.inl column))
    _ hzero

def storeMaterialize (first second : P → Fin n) (builder : Builder q n m k P)
    (view : RecursiveFeaturePublicKey.StoredView q n m p k) :
    RecursiveFeaturePublicKey.StoredView q n m p k :=
  (view.1, context first second builder view.2)

/-- The only private key is the original source secret. Controls are eagerly
materialized; evaluation never invokes the private key generator. -/
noncomputable def keygen {samples : ℕ}
    (first second : P → Fin n) (builder : Builder q n m k P)
    (columns : RecursiveQuadratic.Column n m (p + k) ≃ Fin samples)
    (secretSampler : ProbComp (Fin n → ZMod q)) (errorSampler : ProbComp (ZMod q)) :
    ProbComp (RecursiveFeaturePublicKey.StoredView q n m p k × (Fin n → ZMod q)) :=
  (fun keys ↦ (storeMaterialize first second builder keys.1, keys.2)) <$>
    RecursiveFeaturePublicKey.keygen columns (zeroPolynomial q n k) secretSampler errorSampler

theorem keygen_public_evalDist {samples : ℕ}
    (first second : P → Fin n) (builder : Builder q n m k P)
    (columns : RecursiveQuadratic.Column n m (p + k) ≃ Fin samples)
    (secretSampler : ProbComp (Fin n → ZMod q)) (errorSampler : ProbComp (ZMod q)) :
    𝒟[Prod.fst <$> keygen first second builder columns secretSampler errorSampler] =
      𝒟[RecursiveFeaturePublicKey.storeView <$>
        freshView first second builder columns secretSampler errorSampler] := by
  have h := evalDist_map_eq_of_evalDist_eq
    (RecursiveFeaturePublicKey.keygen_public_evalDist columns (zeroPolynomial q n k)
      secretSampler errorSampler) (storeMaterialize first second builder)
  simpa [keygen, freshView, storeMaterialize, materialize,
    RecursiveFeaturePublicKey.storeView, monad_norm] using h

noncomputable def scheme {samples : ℕ} (params : GSWGadget.Parameters q)
    (level : Fin params.levels) (first second : P → Fin n) (builder : Builder q n m k P)
    (columns : RecursiveQuadratic.Column n m (p + k) ≃ Fin samples)
    (secretSampler : ProbComp (Fin n → ZMod q)) (errorSampler : ProbComp (ZMod q)) :
    AsymmEncAlg ProbComp Bool (RecursiveFeaturePublicKey.StoredView q n m p k)
      (Fin n → ZMod q)
      (GSWAccumulator.StoredCiphertext params (RecursiveFeaturePublicKey.Dimension n + 1)) where
  keygen := keygen first second builder columns secretSampler errorSampler
  encrypt := fun view bit ↦ GSWMasking.encrypt params (GSWMasking.tableOfPublicKey view.1) bit
  decrypt := fun secret ciphertext ↦ pure (some (RecursiveFeatureGSW.decode params secret
    (RecursiveFeaturePublicKey.ofStored params ciphertext) level))

def fromINDCPA {samples : ℕ} (params : GSWGadget.Parameters q)
    (level : Fin params.levels) (first second : P → Fin n) (builder : Builder q n m k P)
    (columns : RecursiveQuadratic.Column n m (p + k) ≃ Fin samples)
    (secretSampler : ProbComp (Fin n → ZMod q)) (errorSampler : ProbComp (ZMod q))
    (adversary : AsymmEncAlg.IND_CPA_Adv
      (scheme params level first second builder columns secretSampler errorSampler)) :
    RecursiveFeaturePublicKey.Adversary (n := n) (r := m) (p := p) (k := k) params where
  State := adversary.State
  chooseMessages := adversary.chooseMessages
  distinguish := adversary.distinguish

/-- The standard IND-CPA experiment receives exactly the materialized same-key
view appearing in the ordinary-source security bound. -/
theorem oneTime_game_evalDist {samples : ℕ} (params : GSWGadget.Parameters q)
    (level : Fin params.levels) (first second : P → Fin n) (builder : Builder q n m k P)
    (columns : RecursiveQuadratic.Column n m (p + k) ≃ Fin samples)
    (secretSampler : ProbComp (Fin n → ZMod q)) (errorSampler : ProbComp (ZMod q))
    (adversary : AsymmEncAlg.IND_CPA_Adv
      (scheme params level first second builder columns secretSampler errorSampler)) :
    𝒟[AsymmEncAlg.IND_CPA_OneTime_Game_ProbComp adversary] =
      𝒟[GSWMasking.game params (freshView first second builder columns secretSampler errorSampler)
        (fromINDCPA params level first second builder columns secretSampler errorSampler adversary)] := by
  let observer := fun view : RecursiveFeaturePublicKey.StoredView q n m p k ↦ do
    let bit ← $ᵗ Bool
    let messages ← adversary.chooseMessages view
    let ciphertext ← GSWMasking.encrypt params (GSWMasking.tableOfPublicKey view.1)
      (if bit then messages.1 else messages.2.1)
    let guess ← adversary.distinguish messages.2.2 ciphertext
    pure (bit == guess)
  have hswap := evalDist_bind_bind_swap ($ᵗ Bool)
    (keygen first second builder columns secretSampler errorSampler)
    (fun bit keys ↦ do
      let messages ← adversary.chooseMessages keys.1
      let ciphertext ← GSWMasking.encrypt params (GSWMasking.tableOfPublicKey keys.1.1)
        (if bit then messages.1 else messages.2.1)
      let guess ← adversary.distinguish messages.2.2 ciphertext
      pure (bit == guess))
  have hforget := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (keygen_public_evalDist first second builder columns secretSampler errorSampler) observer
  simpa [AsymmEncAlg.IND_CPA_OneTime_Game_ProbComp, scheme, GSWMasking.game,
    RecursiveFeaturePublicKey.observe, fromINDCPA, observer,
    RecursiveFeaturePublicKey.storeView, monad_norm] using hswap.trans (by
      simpa [bind_map_left, observer, RecursiveFeaturePublicKey.storeView,
        RecursiveFeaturePublicKey.observe, fromINDCPA, monad_norm] using hforget)

/-- The actual materialized cubic-control game has only existing ordinary-LWE
advantages and statistical losses. Coefficient correctness/shortness is not
needed for this computational bound, but is still needed for bootstrapping. -/
theorem sampled_game_abs_advantage_le {m p k samples : ℕ} (parameter : ℕ)
    (params : GSWGadget.Parameters (RecursiveQuadraticParameters.modulus parameter))
    (first second : P → Fin (RecursiveQuadraticParameters.binaryDimension parameter * 1))
    (builder : Builder (RecursiveQuadraticParameters.modulus parameter)
      (RecursiveQuadraticParameters.binaryDimension parameter * 1) m k P)
    (columns : RecursiveQuadratic.Column (RecursiveQuadraticParameters.binaryDimension parameter * 1)
      m (p + k) ≃ Fin samples)
    (adversary : RecursiveFeaturePublicKey.Adversary
      (n := RecursiveQuadraticParameters.binaryDimension parameter * 1)
      (r := m) (p := p) (k := k) params) :
    |Pr[= true | GSWMasking.game params
      (freshView first second builder columns
        (FormalProof4FHE.BlockBinary.expand (ZMod (RecursiveQuadraticParameters.modulus parameter)) <$>
          ($ᵗ FormalProof4FHE.BlockBinary.Key 1 (RecursiveQuadraticParameters.binaryDimension parameter)))
        (UniformInterval.sample (RecursiveQuadraticParameters.modulus parameter)
          (RecursiveQuadraticParameters.radius parameter) (RecursiveQuadraticParameters.retries parameter)))
      adversary].toReal - 1 / 2| ≤
      RecursiveQuadraticParameters.ordinaryReductionLoss parameter columns
        (RecursiveFeaturePublicKey.joinedPolynomial
          (zeroPolynomial (RecursiveQuadraticParameters.modulus parameter)
            (RecursiveQuadraticParameters.binaryDimension parameter * 1) k))
        (fun original ↦ RecursiveFeaturePublicKey.observe params
          (liftAdversary params first second builder adversary) (RecursiveFeaturePublicKey.publish original)) +
      RecursiveQuadraticParameters.implementationLoss samples parameter +
      ((RecursiveFeaturePublicKey.Dimension (RecursiveQuadraticParameters.binaryDimension parameter * 1) + 1) * params.levels) *
        (Real.sqrt ((RecursiveQuadraticParameters.modulus parameter : ℝ) ^
          (RecursiveFeaturePublicKey.Dimension (RecursiveQuadraticParameters.binaryDimension parameter * 1) + 1) /
            (2 : ℝ) ^ p) / 2) := by
  unfold freshView
  rw [game_materialize]
  exact RecursiveFeaturePublicKey.sampled_game_abs_advantage_le parameter params columns
    (zeroPolynomial _ _ _) (liftAdversary params first second builder adversary)

/-- Standard one-time IND-CPA, for the materialized same-key scheme itself.
The right side names only existing ordinary-LWE reductions and statistical
losses; no cubic-control or circular-security advantage is left as a premise.
Negligibility still needs an efficient builder and reduction-class closure. -/
theorem oneTime_abs_signedAdvantage_le {m p k samples : ℕ} (parameter : ℕ)
    (params : GSWGadget.Parameters (RecursiveQuadraticParameters.modulus parameter))
    (level : Fin params.levels)
    (first second : P → Fin (RecursiveQuadraticParameters.binaryDimension parameter * 1))
    (builder : Builder (RecursiveQuadraticParameters.modulus parameter)
      (RecursiveQuadraticParameters.binaryDimension parameter * 1) m k P)
    (columns : RecursiveQuadratic.Column (RecursiveQuadraticParameters.binaryDimension parameter * 1)
      m (p + k) ≃ Fin samples)
    (adversary : AsymmEncAlg.IND_CPA_Adv (scheme params level first second builder columns
      (FormalProof4FHE.BlockBinary.expand (ZMod (RecursiveQuadraticParameters.modulus parameter)) <$>
        ($ᵗ FormalProof4FHE.BlockBinary.Key 1 (RecursiveQuadraticParameters.binaryDimension parameter)))
      (UniformInterval.sample (RecursiveQuadraticParameters.modulus parameter)
        (RecursiveQuadraticParameters.radius parameter) (RecursiveQuadraticParameters.retries parameter)))) :
    let secretSampler := FormalProof4FHE.BlockBinary.expand (ZMod (RecursiveQuadraticParameters.modulus parameter)) <$>
      ($ᵗ FormalProof4FHE.BlockBinary.Key 1 (RecursiveQuadraticParameters.binaryDimension parameter))
    let errorSampler := UniformInterval.sample (RecursiveQuadraticParameters.modulus parameter)
      (RecursiveQuadraticParameters.radius parameter) (RecursiveQuadraticParameters.retries parameter)
    let reduced := liftAdversary params first second builder
      (fromINDCPA params level first second builder columns secretSampler errorSampler adversary)
    |AsymmEncAlg.IND_CPA_OneTime_signedAdvantageReal
      (scheme params level first second builder columns secretSampler errorSampler) adversary| ≤
      RecursiveQuadraticParameters.ordinaryReductionLoss parameter columns
        (RecursiveFeaturePublicKey.joinedPolynomial
          (zeroPolynomial (RecursiveQuadraticParameters.modulus parameter)
            (RecursiveQuadraticParameters.binaryDimension parameter * 1) k))
        (fun original ↦ RecursiveFeaturePublicKey.observe params reduced (RecursiveFeaturePublicKey.publish original)) +
      RecursiveQuadraticParameters.implementationLoss samples parameter +
      ((RecursiveFeaturePublicKey.Dimension (RecursiveQuadraticParameters.binaryDimension parameter * 1) + 1) * params.levels) *
        (Real.sqrt ((RecursiveQuadraticParameters.modulus parameter : ℝ) ^
          (RecursiveFeaturePublicKey.Dimension (RecursiveQuadraticParameters.binaryDimension parameter * 1) + 1) /
            (2 : ℝ) ^ p) / 2) := by
  dsimp only
  unfold AsymmEncAlg.IND_CPA_OneTime_signedAdvantageReal
  rw [probOutput_congr (rfl : true = true) (oneTime_game_evalDist params level first second builder
    columns _ _ adversary)]
  exact sampled_game_abs_advantage_le parameter params first second builder columns
    (fromINDCPA params level first second builder columns _ _ adversary)

end FormalProof4FHE.LWE.GSWLinearCharacterSecurity
