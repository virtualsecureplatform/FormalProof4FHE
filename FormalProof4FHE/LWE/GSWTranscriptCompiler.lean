/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/
import FormalProof4FHE.LWE.GSWQuadraticPreimageGSW

/-!
# Public corrections computed from the complete retained LWE transcript

Unlike the A-only quadratic builder, a compiler sees both A and y and can
compute arbitrary nonlinear mask/body corrections. Its full-tape inverse,
real phase, derived binary-source bound and native adaptive plaintext-game
bound are explicit. No correctness, efficiency or negligible-failure claim
for a useful compiler is assumed or established by these source identities.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.LWE.GSWTranscriptCompiler

open GSWQuadraticPreimage FormalProof4FHE.BlockBinary

abbrev Compiler (R : Type) (n m k : ℕ) :=
  BatchTranscript R n m → BatchTranscript R n k

def simulate {R : Type} [CommRing R] {n m k : ℕ}
    (compiler : Compiler R n m k) (raw : View R n m k) : View R n m k :=
  (raw.1, (raw.2.1 - (compiler raw.1).1, raw.2.2 + (compiler raw.1).2))

def unsimulate {R : Type} [CommRing R] {n m k : ℕ}
    (compiler : Compiler R n m k) (view : View R n m k) : View R n m k :=
  (view.1, (view.2.1 + (compiler view.1).1, view.2.2 - (compiler view.1).2))

def tapeEquiv {R : Type} [CommRing R] {n m k : ℕ}
    (compiler : Compiler R n m k) : View R n m k ≃ View R n m k where
  toFun := simulate compiler
  invFun := unsimulate compiler
  left_inv raw := by
    rcases raw with ⟨base, mask, body⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> simp only [simulate, unsimulate] <;> abel
  right_inv view := by
    rcases view with ⟨base, mask, body⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> simp only [simulate, unsimulate] <;> abel

def sourceEquiv {R : Type} [CommRing R] {n m k : ℕ}
    (compiler : Compiler R n m k) : BatchTranscript R n (m + k) ≃ View R n m k :=
  (splitEquiv R n m k).trans (tapeEquiv compiler)

theorem phase_simulate {R : Type} [CommRing R] {n m k : ℕ}
    (compiler : Compiler R n m k) (raw : View R n m k) (secret : Fin n → R)
    (column : Fin k) :
    phase secret (simulate compiler raw).2 column =
      phase secret raw.2 column + (compiler raw.1).2 column +
        vecMul secret (compiler raw.1).1 column := by
  change (raw.2.2 column + (compiler raw.1).2 column) -
    dotProduct secret ((fun row ↦ raw.2.1 row column) -
      (fun row ↦ (compiler raw.1).1 row column)) = _
  rw [dotProduct_sub]
  change _ = (raw.2.2 column - dotProduct secret (fun row ↦ raw.2.1 row column)) +
    (compiler raw.1).2 column + dotProduct secret (fun row ↦ (compiler raw.1).1 row column)
  ring

theorem phase_real {R : Type} [CommRing R] {n m k : ℕ}
    (compiler : Compiler R n m k) (base : BatchTranscript R n m)
    (secret : Fin n → R) (mask : Matrix (Fin n) (Fin k) R) (error : Fin k → R)
    (column : Fin k) :
    phase secret (simulate compiler (base, mask, vecMul secret mask + error)).2 column =
      error column + (compiler base).2 column + vecMul secret (compiler base).1 column := by
  rw [phase_simulate]
  simp [phase, vecMul, dotProduct]

/-- The earlier A-only interface is a special case of this compiler. -/
def ofBuilder {R : Type} [CommRing R] {n m k : ℕ}
    (builder : Builder R n m k) (linear : Matrix (Fin n) (Fin k) R)
    (offset : Fin k → R) : Compiler R n m k :=
  fun base ↦ (linear + correction builder base, offset)

theorem simulate_ofBuilder {R : Type} [CommRing R] {n m k : ℕ}
    (builder : Builder R n m k) (linear : Matrix (Fin n) (Fin k) R)
    (offset : Fin k → R) (raw : View R n m k) :
    simulate (ofBuilder builder linear offset) raw =
      GSWQuadraticPreimage.simulate builder linear offset raw := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · simp only [simulate, ofBuilder, GSWQuadraticPreimage.simulate]
      abel
    · rfl

noncomputable section
variable {q b n m k : ℕ} [NeZero q]

noncomputable local instance : SampleableType (View (ZMod q) (n * b) m k) := inferInstance

def realView (compiler : Compiler (ZMod q) (n * b) m k)
    (errorSampler : ProbComp (ZMod q)) : ProbComp (View (ZMod q) (n * b) m k) :=
  sourceEquiv compiler <$> LearningWithErrors.distr (problem b n (m + k) errorSampler)

theorem uniform_source_evalDist (compiler : Compiler (ZMod q) (n * b) m k)
    (errorSampler : ProbComp (ZMod q)) :
    𝒟[sourceEquiv compiler <$>
      LearningWithErrors.uniformDistr (problem b n (m + k) errorSampler)] =
        𝒟[$ᵗ View (ZMod q) (n * b) m k] := by
  have hsource : 𝒟[LearningWithErrors.uniformDistr (problem b n (m + k) errorSampler)] =
      𝒟[$ᵗ BatchTranscript (ZMod q) (n * b) (m + k)] := by
    simpa only [LearningWithErrors.uniformDistr, problem] using
      (FiniteProduct.evalDist_independent_uniform_product
        (first := Matrix (Fin (n * b)) (Fin (m + k)) (ZMod q))
        (second := Fin (m + k) → ZMod q))
  exact (evalDist_map_eq_of_evalDist_eq hsource (sourceEquiv compiler)).trans
    (evalDist_map_bijective_uniform_cross
      (BatchTranscript (ZMod q) (n * b) (m + k)) (sourceEquiv compiler)
      (sourceEquiv compiler).bijective)

def reduction (compiler : Compiler (ZMod q) (n * b) m k)
    (adversary : View (ZMod q) (n * b) m k → ProbComp Bool) :
    BatchTranscript (ZMod q) (n * b) (m + k) → ProbComp Bool :=
  fun raw ↦ adversary (sourceEquiv compiler raw)

theorem advantage_eq_blockBinary (compiler : Compiler (ZMod q) (n * b) m k)
    (errorSampler : ProbComp (ZMod q))
    (adversary : View (ZMod q) (n * b) m k → ProbComp Bool) :
    (realView compiler errorSampler >>= adversary).boolDistAdvantage
      (($ᵗ View (ZMod q) (n * b) m k) >>= adversary) =
      LearningWithErrors.advantage (problem b n (m + k) errorSampler)
        (reduction compiler adversary) := by
  have hreal : realView compiler errorSampler >>= adversary =
      LearningWithErrors.game0 (problem b n (m + k) errorSampler)
        (reduction compiler adversary) := by
    simp [realView, reduction, LearningWithErrors.game0, monad_norm]
  have hideal := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (uniform_source_evalDist compiler errorSampler) adversary
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage, hreal]
  unfold ProbComp.boolDistAdvantage
  have hideal' : 𝒟[LearningWithErrors.game1 (problem b n (m + k) errorSampler)
      (reduction compiler adversary)] =
      𝒟[($ᵗ View (ZMod q) (n * b) m k) >>= adversary] := by
    simpa [LearningWithErrors.game1, reduction, monad_norm] using hideal
  rw [evalDist_ext_iff.mp hideal' true]

def ordinaryLoss (compiler : Compiler (ZMod q) (n * b) m k)
    (d : ℕ) (narrow wide : ProbComp (ZMod q))
    (adversary : View (ZMod q) (n * b) m k → ProbComp Bool) : ℝ :=
  let red := reduction compiler adversary
  (∑ coordinate : Fin (n * b), LearningWithErrors.advantage
    (batchProblem d (m + k) ($ᵗ (Fin d → ZMod q)) narrow)
    (rowHybridReduction (n * b) d (m + k) narrow coordinate
      (realMaskReduction b n d (m + k) narrow wide red))) +
    noiseAbsorptionGap b n d (m + k) narrow wide +
    Real.sqrt ((q : ℝ) ^ d / (b + 1 : ℝ) ^ n) / 2 +
    LearningWithErrors.advantage
      (batchProblem d (m + k) ($ᵗ (Fin d → ZMod q)) wide)
      (extractedLWReduction b n d (m + k) narrow wide red) +
    (∑ coordinate : Fin (n * b), LearningWithErrors.advantage
      (batchProblem d (m + k) ($ᵗ (Fin d → ZMod q)) narrow)
      (rowHybridReduction (n * b) d (m + k) narrow coordinate
        (uniformMaskReduction b n d (m + k) narrow wide red)))

theorem advantage_le_ordinaryLWE (compiler : Compiler (ZMod q) (n * b) m k)
    (d : ℕ) (narrow wide : ProbComp (ZMod q))
    (adversary : View (ZMod q) (n * b) m k → ProbComp Bool) :
    (realView compiler wide >>= adversary).boolDistAdvantage
      (($ᵗ View (ZMod q) (n * b) m k) >>= adversary) ≤
      ordinaryLoss compiler d narrow wide adversary := by
  rw [advantage_eq_blockBinary]
  simpa only [ordinaryLoss, ZMod.card] using
    (advantage_le_ordinaryLWE_add_gaps b n d (m + k) narrow wide
      (reduction compiler adversary))

open GSWQuadraticPreimageGSW GSWGadget
variable {p : ℕ}

def publicView (params : Parameters q)
    (compiler : Compiler (ZMod q) (n * b) p (columns params (n * b)))
    (errorSampler : ProbComp (ZMod q)) : ProbComp (MaskingView params (n * b) p) :=
  viewEquiv params (n * b) p <$> realView compiler errorSampler

/-- Native adaptive plaintext security for the whole public view. This does
not supply a compiler whose controls implement the claimed key bits. -/
theorem public_game_abs_advantage_le (params : Parameters q)
    (compiler : Compiler (ZMod q) (n * b) p (columns params (n * b)))
    (d : ℕ) (narrow wide : ProbComp (ZMod q)) (adversary : Adversary params (n * b) p) :
    |Pr[= true | GSWMasking.game params (publicView params compiler wide) adversary].toReal - 1 / 2| ≤
      ordinaryLoss compiler d narrow wide
        (fun view ↦ observe params adversary (viewEquiv params (n * b) p view)) +
      ((n * b + 1) * params.levels) *
        (Real.sqrt ((q : ℝ) ^ (n * b + 1) / (2 : ℝ) ^ p) / 2) := by
  let downstream := fun view ↦ observe params adversary (viewEquiv params (n * b) p view)
  have hview := advantage_le_ordinaryLWE compiler d narrow wide downstream
  have he := evalDist_map_bijective_uniform_cross
    (α := View (ZMod q) (n * b) p (columns params (n * b)))
    (β := MaskingView params (n * b) p)
    (viewEquiv params (n * b) p) (viewEquiv params (n * b) p).bijective
  have hi := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    he (observe params adversary)
  have hreal : realView compiler wide >>= downstream =
      GSWMasking.game params (publicView params compiler wide) adversary := by
    simp [GSWMasking.game, publicView, downstream, observe, monad_norm]
  have hideal : 𝒟[($ᵗ View (ZMod q) (n * b) p (columns params (n * b))) >>= downstream] =
      𝒟[GSWMasking.game params ($ᵗ MaskingView params (n * b) p) adversary] := by
    simpa [GSWMasking.game, downstream, observe, monad_norm] using hi
  unfold ProbComp.boolDistAdvantage at hview
  rw [hreal, probOutput_congr (rfl : true = true) hideal] at hview
  exact (abs_sub_le _ _ (1 / 2 : ℝ)).trans
    (add_le_add hview (by simpa only [Nat.cast_mul] using
      ideal_game_abs_advantage_le params adversary))

def privateView (params : Parameters q)
    (compiler : Compiler (ZMod q) (n * b) p (columns params (n * b)))
    (secret : Fin (n * b) → ZMod q)
    (challenge : Matrix (Fin (n * b)) (Fin (p + columns params (n * b))) (ZMod q))
    (errors : Fin (p + columns params (n * b)) → ZMod q) : MaskingView params (n * b) p :=
  viewEquiv params (n * b) p (sourceEquiv compiler (challenge, vecMul secret challenge + errors))

/-- All public coefficients are stored eagerly; the one original key stays private. -/
def keygen (params : Parameters q)
    (compiler : Compiler (ZMod q) (n * b) p (columns params (n * b)))
    (errorSampler : ProbComp (ZMod q)) :
    ProbComp (FormalProof4FHE.BlockBinary.Key b n ×
      (GSWPublicKey.PublicKey q (n * b) p ×
        Vector (GSWAccumulator.StoredCiphertext params (n * b + 1)) (n * b))) := do
  let challenge ← $ᵗ Matrix (Fin (n * b)) (Fin (p + columns params (n * b))) (ZMod q)
  let secret ← $ᵗ FormalProof4FHE.BlockBinary.Key b n
  let errors ← ProbComp.sampleIID (p + columns params (n * b)) errorSampler
  pure (secret, storeView params (privateView params compiler
    (FormalProof4FHE.BlockBinary.expand (ZMod q) secret) challenge errors))

theorem keygen_public_eq (params : Parameters q)
    (compiler : Compiler (ZMod q) (n * b) p (columns params (n * b)))
    (errorSampler : ProbComp (ZMod q)) :
    Prod.snd <$> keygen params compiler errorSampler =
      storeView params <$> publicView params compiler errorSampler := by
  simp [keygen, publicView, realView, privateView,
    LearningWithErrors.distr, FormalProof4FHE.BlockBinary.problem, monad_norm]

/-- The challenge game actually receives the materialized key-generator output. -/
def storedGame (params : Parameters q)
    (compiler : Compiler (ZMod q) (n * b) p (columns params (n * b)))
    (errorSampler : ProbComp (ZMod q)) (adversary : StoredAdversary params (n * b) p) : ProbComp Bool :=
  GSWMasking.game params ((fun keys ↦ (GSWMasking.tableOfPublicKey keys.2.1, keys.2.2)) <$>
    keygen params compiler errorSampler) adversary

theorem storedGame_eq (params : Parameters q)
    (compiler : Compiler (ZMod q) (n * b) p (columns params (n * b)))
    (errorSampler : ProbComp (ZMod q)) (adversary : StoredAdversary params (n * b) p) :
    storedGame params compiler errorSampler adversary =
      GSWMasking.game params (publicView params compiler errorSampler) (liftStoredAdversary params adversary) := by
  have hmap : ((fun keys ↦ (GSWMasking.tableOfPublicKey keys.2.1, keys.2.2)) <$>
      keygen params compiler errorSampler) =
      (fun view ↦ (view.1, Vector.ofFn fun index ↦ GSWAccumulator.storeCiphertext params (view.2 index))) <$>
        publicView params compiler errorSampler := by
    have hh := congrArg (fun sampler ↦ (fun stored ↦
      (GSWMasking.tableOfPublicKey stored.1, stored.2)) <$> sampler)
      (keygen_public_eq params compiler errorSampler)
    simpa [storeView, monad_norm] using hh
  simp [storedGame, hmap, GSWMasking.game, liftStoredAdversary, monad_norm]

theorem stored_game_abs_advantage_le (params : Parameters q)
    (compiler : Compiler (ZMod q) (n * b) p (columns params (n * b)))
    (d : ℕ) (narrow wide : ProbComp (ZMod q)) (adversary : StoredAdversary params (n * b) p) :
    |Pr[= true | storedGame params compiler wide adversary].toReal - 1 / 2| ≤
      ordinaryLoss compiler d narrow wide
        (fun view ↦ observe params (liftStoredAdversary params adversary) (viewEquiv params (n * b) p view)) +
      ((n * b + 1) * params.levels) *
        (Real.sqrt ((q : ℝ) ^ (n * b + 1) / (2 : ℝ) ^ p) / 2) := by
  rw [storedGame_eq]
  exact public_game_abs_advantage_le params compiler d narrow wide (liftStoredAdversary params adversary)


end

open GSWQuadraticPreimageGSW GSWGadget

/-- The sampled discrepancy is measured against the actual native self-key phase. -/
def discrepancy {q n p : ℕ} [NeZero q] (params : Parameters q)
    (compiler : Compiler (ZMod q) n p (columns params n)) (secret : Fin n → ZMod q)
    (base : BatchTranscript (ZMod q) n p) : Fin (columns params n) → ZMod q :=
  fun column ↦ (compiler base).2 column + vecMul secret (compiler base).1 column -
    GSWSelfKey.phaseMessage (fullLayout params n) secret
      (GSWSelfKey.selfKeyMessages params.levels secret) column

theorem control_noise {q n p : ℕ} [NeZero q] (params : Parameters q)
    (compiler : Compiler (ZMod q) n p (columns params n)) (secret : Fin n → ZMod q)
    (base : BatchTranscript (ZMod q) n p)
    (mask : Matrix (Fin n) (Fin (columns params n)) (ZMod q))
    (error : Fin (columns params n) → ZMod q) (index : Fin n) :
    GSWOperations.noise (GSWOperations.extendedSecret secret) (gadget params (n + 1))
      (controlsEquiv params n (simulate compiler (base, mask, vecMul secret mask + error)).2 index)
      (secret index) =
      fun column ↦ error (finProdFinEquiv (index, column)) +
        discrepancy params compiler secret base (finProdFinEquiv (index, column)) := by
  ext column
  rw [GSWOperations.noise, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    control_phase, control_gadget_phase, phase_real]
  simp only [discrepancy]
  ring

/-- Same-key reusable refresh only needs bounds on the actual joint discrepancy.
This premise remains a construction obligation, not a new hardness assumption. -/
theorem noiseBound_bootstrap {factor lookup n p : ℕ} [NeZero factor] [NeZero lookup]
    (params : Parameters (factor * lookup))
    (compiler : Compiler (ZMod (factor * lookup)) n p (columns params n))
    (bits : Fin n → Bool) (base : BatchTranscript (ZMod (factor * lookup)) n p)
    (mask : Matrix (Fin n) (Fin (columns params n)) (ZMod (factor * lookup)))
    (error : Fin (columns params n) → ZMod (factor * lookup))
    (ciphertext : Ciphertext params (n + 1)) (level : Fin params.levels) (oneCode : ZMod lookup)
    (bit : Bool) (inputBound keyBound : ℕ)
    (hcode : TFHE.Gadget.Base.gadget params level = GSWModulusSwitch.up factor lookup oneCode)
    (hinput : NoiseBound params (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits))
      ciphertext (bitMessage bit) inputBound)
    (herror : ∀ column, (LatticeCrypto.centeredRepr (error column +
      discrepancy params compiler (GSWSelfKey.binaryEmbed bits) base column)).natAbs ≤ keyBound)
    (hround : 2 * (inputBound + (n + 1) * (factor - 1)) <
      factor * TFHE.BootstrappingCorrectness.centeredDistance 0 oneCode) :
    let controls := controlsEquiv params n (simulate compiler
      (base, mask, vecMul (GSWSelfKey.binaryEmbed bits) mask + error)).2
    NoiseBound params (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits))
      (GSWBootstrap.bootstrap params controls ciphertext level oneCode) (bitMessage bit)
      (lookup * n * growth params (n + 1) * keyBound) := by
  apply GSWBootstrap.noiseBound_bootstrap params bits _ ciphertext level oneCode bit inputBound keyBound
    hcode hinput _ hround
  intro index column
  change (LatticeCrypto.centeredRepr (GSWOperations.noise _ _ _
    (GSWSelfKey.binaryEmbed bits index) column)).natAbs ≤ keyBound
  rw [control_noise]
  exact herror _

end FormalProof4FHE.LWE.GSWTranscriptCompiler
