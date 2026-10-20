/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.GSWQuadraticPreimageBinary
import FormalProof4FHE.LWE.GSWMasking
import FormalProof4FHE.LWE.GSWBootstrap

/-!
# Native stored GSW materialization of the correlated-control candidate

All original secret coordinates have a full native GSW control. The public
sampler uses one block-binary secret and one ordinary source tape, followed by
the public triangular shear. This is a modified key-generation law, with
shared residual errors, not an assertion about the stock independent controls.
Binary diagonal products are affine: their quadratic target is zero, so only
off-diagonal mask columns require nonzero quadratic preimages.

The public IND-CPA bound reduces the COMPLETE stored view to ordinary LWE and
explicit statistical losses, including adaptive message choice. It holds for
any public builder. Correctness additionally requires its actual sampled
matrix to satisfy the stated alternating certificates and residual bounds.
No short builder, negligible failure theorem or compatible asymptotic
shortness guarantee is supplied or assumed as a security hypothesis.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.LWE.GSWQuadraticPreimageGSW

open GSWGadget GSWQuadraticPreimage

abbrev columns {q : ℕ} (params : Parameters q) (n : ℕ) :=
  n * ((n + 1) * params.levels)

def fullLayout {q : ℕ} [NeZero q] (params : Parameters q) (n : ℕ) :=
  GSWSelfKey.selfKeyLayout n params.levels (TFHE.Gadget.Base.gadget params)

def encryptedIndex {q : ℕ} (params : Parameters q) {n : ℕ}
    (column : Fin (columns params n)) : Fin n :=
  (GSWSelfKey.selfKeyPosition n params.levels column).1

def linear {q : ℕ} [NeZero q] (params : Parameters q) (n : ℕ) :
    Matrix (Fin n) (Fin (columns params n)) (ZMod q) :=
  fun row column ↦ match (fullLayout params n).coordinate column with
    | none => if row = encryptedIndex params column then (fullLayout params n).weight column else 0
    | some maskRow => if maskRow = encryptedIndex params column then
        if row = encryptedIndex params column then -(fullLayout params n).weight column else 0 else 0

def quadratic {q : ℕ} [NeZero q] (params : Parameters q) (n : ℕ)
    (column : Fin (columns params n)) : Matrix (Fin n) (Fin n) (ZMod q) :=
  fun row other ↦ match (fullLayout params n).coordinate column with
    | none => 0
    | some maskRow => if maskRow = encryptedIndex params column then 0 else
        if row = encryptedIndex params column then
          if other = maskRow then -(fullLayout params n).weight column else 0 else 0

theorem quadratic_eq_zero_of_body {q n : ℕ} [NeZero q] (params : Parameters q)
    (column : Fin (columns params n))
    (h : (fullLayout params n).coordinate column = none) :
    quadratic params n column = 0 := by
  ext row other
  simp [quadratic, h]

theorem quadratic_eq_zero_of_diagonal {q n : ℕ} [NeZero q] (params : Parameters q)
    (column : Fin (columns params n))
    (h : (fullLayout params n).coordinate column = some (encryptedIndex params column)) :
    quadratic params n column = 0 := by
  ext row other
  simp [quadratic, h]

theorem target_eq_phaseMessage {q n : ℕ} [NeZero q] (params : Parameters q)
    (secret : Fin n → ZMod q) (hidempotent : ∀ row, secret row * secret row = secret row)
    (column : Fin (columns params n)) :
    vecMul secret (linear params n) column +
      dotProduct secret ((quadratic params n column).mulVec secret) =
    GSWSelfKey.phaseMessage (fullLayout params n) secret
      (GSWSelfKey.selfKeyMessages params.levels secret) column := by
  cases hc : (fullLayout params n).coordinate column with
  | none =>
    simp [linear, quadratic, vecMul, dotProduct, mulVec, hc, mul_ite,
      GSWSelfKey.phaseMessage, GSWSelfKey.selfKeyMessages, encryptedIndex]
  | some row =>
    by_cases hd : row = encryptedIndex params column
    · subst row
      simp [linear, quadratic, vecMul, dotProduct, mulVec, hc, mul_ite,
        GSWSelfKey.phaseMessage, GSWSelfKey.selfKeyMessages, encryptedIndex]
      have hh := hidempotent (encryptedIndex params column)
      dsimp [encryptedIndex] at hh
      linear_combination -(fullLayout params n).weight column * hh
    · dsimp [encryptedIndex] at hd
      simp [linear, quadratic, vecMul, dotProduct, mulVec, hc, hd, mul_ite,
        GSWSelfKey.phaseMessage, GSWSelfKey.selfKeyMessages, encryptedIndex]
      ring

/-- Body-first serialization is an equivalence, without inspecting any secret. -/
def matrixEquiv (R : Type) (n k : ℕ) :
    BatchTranscript R n k ≃ Matrix (Fin (n + 1)) (Fin k) R where
  toFun := GSWOperations.ciphertextMatrix
  invFun matrix := (fun row column ↦ matrix row.succ column, fun column ↦ matrix 0 column)
  left_inv _ := rfl
  right_inv matrix := by
    ext row column
    cases row using Fin.cases <;> rfl

def tableEquiv (R : Type) (n p : ℕ) :
    BatchTranscript R n p ≃ (Fin p → Fin (n + 1) → R) :=
  (matrixEquiv R n p).trans
    { toFun := fun matrix column row ↦ matrix row column
      invFun := fun table row column ↦ table column row
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

def controlsEquiv {q : ℕ} (params : Parameters q) (n : ℕ) :
    BatchTranscript (ZMod q) n (columns params n) ≃
      (Fin n → Ciphertext params (n + 1)) :=
  (matrixEquiv (ZMod q) n (columns params n)).trans
    { toFun := fun matrix index row column ↦ matrix row (finProdFinEquiv (index, column))
      invFun := fun controls row column ↦
        controls (finProdFinEquiv.symm column).1 row (finProdFinEquiv.symm column).2
      left_inv := by
        intro matrix
        ext row column
        change matrix row (finProdFinEquiv (finProdFinEquiv.symm column)) = _
        rw [Equiv.apply_symm_apply]
      right_inv := by
        intro controls
        ext index row column
        simp }

abbrev MaskingView {q : ℕ} (params : Parameters q) (n p : ℕ) :=
  GSWMasking.Table q n p × (Fin n → Ciphertext params (n + 1))

def viewEquiv {q : ℕ} (params : Parameters q) (n p : ℕ) :
    View (ZMod q) n p (columns params n) ≃ MaskingView params n p :=
  Equiv.prodCongr (tableEquiv (ZMod q) n p) (controlsEquiv params n)

def storeView {q : ℕ} (params : Parameters q) {n p : ℕ} (view : MaskingView params n p) :
    GSWPublicKey.PublicKey q n p × Vector (GSWAccumulator.StoredCiphertext params (n + 1)) n :=
  (GSWMasking.storeTable view.1,
    Vector.ofFn fun index ↦ GSWAccumulator.storeCiphertext params (view.2 index))

def readStoredView {q : ℕ} (params : Parameters q) {n p : ℕ}
    (stored : GSWPublicKey.PublicKey q n p ×
      Vector (GSWAccumulator.StoredCiphertext params (n + 1)) n) : MaskingView params n p :=
  (GSWMasking.tableOfPublicKey stored.1,
    fun index ↦ GSWAccumulator.ciphertextView params (stored.2.get index))

theorem readStoredView_storeView {q n p : ℕ} (params : Parameters q)
    (view : MaskingView params n p) : readStoredView params (storeView params view) = view := by
  apply Prod.ext
  · simp [readStoredView, storeView]
  · ext index row column
    simp [readStoredView, storeView]

def privateView {q n p : ℕ} [NeZero q] (params : Parameters q)
    (builder : Builder (ZMod q) n p (columns params n)) (secret : Fin n → ZMod q)
    (challenge : Matrix (Fin n) (Fin (p + columns params n)) (ZMod q))
    (errors : Fin (p + columns params n) → ZMod q) : MaskingView params n p :=
  viewEquiv params n p (sourceEquiv builder (linear params n) 0
    (challenge, vecMul secret challenge + errors))

/-- Actual shared residual, including dependence on the retained source errors. -/
def residual {q n p : ℕ} [NeZero q] (params : Parameters q)
    (builder : Builder (ZMod q) n p (columns params n)) (secret : Fin n → ZMod q)
    (base : BatchTranscript (ZMod q) n p) (controlError : Fin (columns params n) → ZMod q) :
    Fin (columns params n) → ZMod q :=
  fun column ↦ controlError column + dotProduct secret
    ((builder base.1 column).mulVec (base.2 - vecMul secret base.1))

theorem control_phase {q n : ℕ} (params : Parameters q)
    (secret : Fin n → ZMod q) (transcript : BatchTranscript (ZMod q) n (columns params n))
    (index : Fin n) (column : Fin ((n + 1) * params.levels)) :
    vecMul (GSWOperations.extendedSecret secret) (controlsEquiv params n transcript index) column =
      phase secret transcript (finProdFinEquiv (index, column)) := by
  simp [phase, controlsEquiv, matrixEquiv, GSWOperations.ciphertextMatrix,
    vecMul, dotProduct, GSWOperations.extendedSecret, Fin.sum_univ_succ, sub_eq_add_neg]

theorem control_gadget_phase {q n : ℕ} [NeZero q] (params : Parameters q)
    (secret : Fin n → ZMod q) (index : Fin n) (column : Fin ((n + 1) * params.levels)) :
    secret index * vecMul (GSWOperations.extendedSecret secret) (gadget params (n + 1)) column =
      GSWSelfKey.phaseMessage (fullLayout params n) secret
        (GSWSelfKey.selfKeyMessages params.levels secret) (finProdFinEquiv (index, column)) := by
  obtain ⟨⟨row, level⟩, rfl⟩ := finProdFinEquiv.surjective column
  rw [vecMul_gadget_column]
  cases row using Fin.cases with
  | zero =>
    change secret index * (GSWOperations.extendedSecret secret 0 * _) =
      GSWSelfKey.phaseMessage
        (GSWSelfKey.selfKeyLayout n params.levels (TFHE.Gadget.Base.gadget params)) secret
        (GSWSelfKey.selfKeyMessages params.levels secret) (GSWSelfKey.selfKeyColumn index 0 level)
    rw [GSWSelfKey.selfKey_body_phase]
    simp [GSWOperations.extendedSecret]
  | succ row =>
    change secret index * (GSWOperations.extendedSecret secret row.succ * _) =
      GSWSelfKey.phaseMessage
        (GSWSelfKey.selfKeyLayout n params.levels (TFHE.Gadget.Base.gadget params)) secret
        (GSWSelfKey.selfKeyMessages params.levels secret) (GSWSelfKey.selfKeyColumn index row.succ level)
    rw [GSWSelfKey.selfKey_mask_phase]
    simp [GSWOperations.extendedSecret]
    ring

theorem control_noise {q n p : ℕ} [NeZero q] (params : Parameters q)
    (builder : Builder (ZMod q) n p (columns params n)) (secret : Fin n → ZMod q)
    (hidempotent : ∀ row, secret row * secret row = secret row)
    (baseMask : Matrix (Fin n) (Fin p) (ZMod q)) (baseError : Fin p → ZMod q)
    (controlMask : Matrix (Fin n) (Fin (columns params n)) (ZMod q))
    (controlError : Fin (columns params n) → ZMod q)
    (witness : Fin (columns params n) → Matrix (Fin n) (Fin n) (ZMod q))
    (hcertificate : ∀ column, builder baseMask column * baseMask.transpose =
      quadratic params n column + witness column - (witness column).transpose)
    (index : Fin n) :
    GSWOperations.noise (GSWOperations.extendedSecret secret) (gadget params (n + 1))
      (controlsEquiv params n (simulate builder (linear params n) 0
        ((baseMask, vecMul secret baseMask + baseError),
          (controlMask, vecMul secret controlMask + controlError))).2 index)
      (secret index) =
    fun column ↦ controlError (finProdFinEquiv (index, column)) +
      dotProduct secret ((builder baseMask (finProdFinEquiv (index, column))).mulVec baseError) := by
  ext column
  let joint := finProdFinEquiv (index, column)
  have hphase := phase_real builder (linear params n) 0 secret baseMask baseError
    controlMask controlError joint
  rw [quadratic_eq_of_certificate baseMask (builder baseMask joint)
    (quadratic params n joint) (witness joint) (hcertificate joint) secret] at hphase
  have htarget := target_eq_phaseMessage params secret hidempotent joint
  have hnoise : GSWOperations.noise (GSWOperations.extendedSecret secret)
      (gadget params (n + 1))
      (controlsEquiv params n (simulate builder (linear params n) 0
        ((baseMask, vecMul secret baseMask + baseError),
          (controlMask, vecMul secret controlMask + controlError))).2 index)
      (secret index) column =
    phase secret (simulate builder (linear params n) 0
        ((baseMask, vecMul secret baseMask + baseError),
          (controlMask, vecMul secret controlMask + controlError))).2 joint -
      GSWSelfKey.phaseMessage (fullLayout params n) secret
        (GSWSelfKey.selfKeyMessages params.levels secret) joint := by
    rw [GSWOperations.noise, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      control_phase, control_gadget_phase]
  rw [hnoise, hphase]
  simp only [Pi.zero_apply, add_zero]
  rw [← htarget]
  ring

theorem control_noiseBound {q n p : ℕ} [NeZero q] (params : Parameters q)
    (builder : Builder (ZMod q) n p (columns params n)) (secret : Fin n → ZMod q)
    (hidempotent : ∀ row, secret row * secret row = secret row)
    (baseMask : Matrix (Fin n) (Fin p) (ZMod q)) (baseError : Fin p → ZMod q)
    (controlMask : Matrix (Fin n) (Fin (columns params n)) (ZMod q))
    (controlError : Fin (columns params n) → ZMod q)
    (witness : Fin (columns params n) → Matrix (Fin n) (Fin n) (ZMod q))
    (hcertificate : ∀ column, builder baseMask column * baseMask.transpose =
      quadratic params n column + witness column - (witness column).transpose)
    (bound : ℕ) (herror : ∀ column, (LatticeCrypto.centeredRepr
      (controlError column + dotProduct secret ((builder baseMask column).mulVec baseError))).natAbs ≤ bound)
    (index : Fin n) :
    NoiseBound params (GSWOperations.extendedSecret secret)
      (controlsEquiv params n (simulate builder (linear params n) 0
        ((baseMask, vecMul secret baseMask + baseError),
          (controlMask, vecMul secret controlMask + controlError))).2 index)
      (secret index) bound := by
  intro column
  rw [control_noise params builder secret hidempotent baseMask baseError controlMask controlError witness hcertificate]
  exact herror _

/-- Existing reusable same-key refresh applies to these correlated controls;
neither independence nor the stock fresh-control law is needed for correctness. -/
theorem noiseBound_bootstrap {factor lookup n p : ℕ} [NeZero factor] [NeZero lookup]
    (params : Parameters (factor * lookup))
    (builder : Builder (ZMod (factor * lookup)) n p (columns params n)) (bits : Fin n → Bool)
    (baseMask : Matrix (Fin n) (Fin p) (ZMod (factor * lookup)))
    (baseError : Fin p → ZMod (factor * lookup))
    (controlMask : Matrix (Fin n) (Fin (columns params n)) (ZMod (factor * lookup)))
    (controlError : Fin (columns params n) → ZMod (factor * lookup))
    (witness : Fin (columns params n) → Matrix (Fin n) (Fin n) (ZMod (factor * lookup)))
    (hcertificate : ∀ column, builder baseMask column * baseMask.transpose =
      quadratic params n column + witness column - (witness column).transpose)
    (ciphertext : Ciphertext params (n + 1)) (level : Fin params.levels) (oneCode : ZMod lookup)
    (bit : Bool) (inputBound keyBound : ℕ)
    (hcode : TFHE.Gadget.Base.gadget params level = GSWModulusSwitch.up factor lookup oneCode)
    (hinput : NoiseBound params (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits))
      ciphertext (bitMessage bit) inputBound)
    (herror : ∀ column, (LatticeCrypto.centeredRepr (controlError column +
      dotProduct (GSWSelfKey.binaryEmbed bits) ((builder baseMask column).mulVec baseError))).natAbs ≤ keyBound)
    (hround : 2 * (inputBound + (n + 1) * (factor - 1)) <
      factor * TFHE.BootstrappingCorrectness.centeredDistance 0 oneCode) :
    let controls := controlsEquiv params n (simulate builder (linear params n) 0
      ((baseMask, vecMul (GSWSelfKey.binaryEmbed bits) baseMask + baseError),
        (controlMask, vecMul (GSWSelfKey.binaryEmbed bits) controlMask + controlError))).2
    NoiseBound params (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits))
      (GSWBootstrap.bootstrap params controls ciphertext level oneCode) (bitMessage bit)
      (lookup * n * growth params (n + 1) * keyBound) := by
  apply GSWBootstrap.noiseBound_bootstrap params bits _ ciphertext level oneCode bit inputBound keyBound
    hcode hinput _ hround
  intro index
  simpa only [bitMessage, GSWSelfKey.binaryEmbed] using
    control_noiseBound params builder (GSWSelfKey.binaryEmbed bits) (GSWSelfKey.binaryEmbed_idempotent bits) baseMask baseError
      controlMask controlError witness hcertificate keyBound herror index

noncomputable section

variable {q b n p : ℕ} [NeZero q]

noncomputable local instance (params : Parameters q) : SampleableType (MaskingView params (n * b) p) :=
  inferInstance

def publicView (params : Parameters q)
    (builder : Builder (ZMod q) (n * b) p (columns params (n * b)))
    (errorSampler : ProbComp (ZMod q)) : ProbComp (MaskingView params (n * b) p) :=
  viewEquiv params (n * b) p <$>
    GSWQuadraticPreimageBinary.realView builder (linear params (n * b)) 0 errorSampler

/-- All public coefficients are stored eagerly; the one original key stays private. -/
def keygen (params : Parameters q)
    (builder : Builder (ZMod q) (n * b) p (columns params (n * b)))
    (errorSampler : ProbComp (ZMod q)) :
    ProbComp (FormalProof4FHE.BlockBinary.Key b n ×
      (GSWPublicKey.PublicKey q (n * b) p ×
        Vector (GSWAccumulator.StoredCiphertext params (n * b + 1)) (n * b))) := do
  let challenge ← $ᵗ Matrix (Fin (n * b)) (Fin (p + columns params (n * b))) (ZMod q)
  let secret ← $ᵗ FormalProof4FHE.BlockBinary.Key b n
  let errors ← ProbComp.sampleIID (p + columns params (n * b)) errorSampler
  pure (secret, storeView params (privateView params builder
    (FormalProof4FHE.BlockBinary.expand (ZMod q) secret) challenge errors))

theorem keygen_public_eq (params : Parameters q)
    (builder : Builder (ZMod q) (n * b) p (columns params (n * b)))
    (errorSampler : ProbComp (ZMod q)) :
    Prod.snd <$> keygen params builder errorSampler =
      storeView params <$> publicView params builder errorSampler := by
  simp [keygen, publicView, GSWQuadraticPreimageBinary.realView, privateView,
    LearningWithErrors.distr, FormalProof4FHE.BlockBinary.problem, monad_norm]

abbrev Adversary (params : Parameters q) (n p : ℕ) :=
  GSWMasking.Adversary (dimension := n) (samples := p)
    params (Fin n → Ciphertext params (n + 1))

def observe {N : ℕ} (params : Parameters q) (adversary : Adversary params N p)
    (view : MaskingView params N p) : ProbComp Bool := do
  let bit ← $ᵗ Bool
  let messages ← adversary.chooseMessages (GSWMasking.storeTable view.1, view.2)
  let ciphertext ← GSWMasking.encrypt params view.1 (if bit then messages.1 else messages.2.1)
  let guess ← adversary.distinguish messages.2.2 ciphertext
  pure (bit == guess)

theorem uniform_maskingView_fixedpoint {N : ℕ} (params : Parameters q) :
    𝒟[GSWMasking.uniformView ($ᵗ MaskingView params N p)] =
      𝒟[$ᵗ MaskingView params N p] := by
  let context := Fin N → Ciphertext params (N + 1)
  let table := GSWMasking.Table q N p
  have hcontext : 𝒟[Prod.snd <$> ($ᵗ (table × context))] = 𝒟[$ᵗ context] := by
    have he := evalDist_map_bijective_uniform_cross
      (α := table × context) (β := context × table) (Equiv.prodComm _ _) (Equiv.prodComm _ _).bijective
    have hm := evalDist_map_eq_of_evalDist_eq he Prod.fst
    simpa only [Functor.map_map, Function.comp_def, Equiv.prodComm_apply, Prod.swap] using
      hm.trans (evalDist_map_fst_uniformSample_prod (α := context) (β := table))
  let finish := fun old : context ↦ do
    let freshTable ← $ᵗ table
    pure (freshTable, old)
  have hm := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hcontext finish
  have hswap := evalDist_bind_bind_swap ($ᵗ context) ($ᵗ table)
    (fun old freshTable ↦ pure (freshTable, old))
  have hpair := FiniteProduct.evalDist_independent_uniform_product (first := table) (second := context)
  calc
    _ = 𝒟[($ᵗ context) >>= finish] := by
      simpa [GSWMasking.uniformView, finish, context, table, monad_norm] using hm
    _ = 𝒟[$ᵗ MaskingView params N p] := by
      simpa only [finish, context, table] using hswap.trans hpair

theorem ideal_game_abs_advantage_le {N : ℕ} (params : Parameters q)
    (adversary : Adversary params N p) :
    |Pr[= true | GSWMasking.game params ($ᵗ MaskingView params N p) adversary].toReal - 1 / 2| ≤
      ((N + 1) * params.levels) * (Real.sqrt ((q : ℝ) ^ (N + 1) / (2 : ℝ) ^ p) / 2) := by
  have hmask := GSWMasking.uniform_game_abs_advantage_le params
    ($ᵗ MaskingView params N p) adversary
  have hm := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (uniform_maskingView_fixedpoint params) (observe params adversary)
  have hgame : ∀ sampler : ProbComp (MaskingView params N p),
      GSWMasking.game params sampler adversary = sampler >>= observe params adversary := fun _ ↦ rfl
  rw [hgame, probOutput_congr (rfl : true = true) hm] at hmask
  change |Pr[= true | ($ᵗ MaskingView params N p) >>= observe params adversary].toReal - 1 / 2| ≤ _
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hmask

/-- Full native public encryption game, with every self-key control retained.
There is no circular-security premise. The builder's usefulness is a separate
correctness question; its public simulation gives the computational bound. -/
theorem public_game_abs_advantage_le (params : Parameters q)
    (builder : Builder (ZMod q) (n * b) p (columns params (n * b)))
    (d : ℕ) (narrow wide : ProbComp (ZMod q)) (adversary : Adversary params (n * b) p) :
    |Pr[= true | GSWMasking.game params (publicView params builder wide) adversary].toReal - 1 / 2| ≤
      GSWQuadraticPreimageBinary.ordinaryLoss builder (linear params (n * b)) 0 d narrow wide
        (fun view ↦ observe params adversary (viewEquiv params (n * b) p view)) +
      ((n * b + 1) * params.levels) *
        (Real.sqrt ((q : ℝ) ^ (n * b + 1) / (2 : ℝ) ^ p) / 2) := by
  let downstream := fun view ↦ observe params adversary (viewEquiv params (n * b) p view)
  have hview := GSWQuadraticPreimageBinary.advantage_le_ordinaryLWE builder
    (linear params (n * b)) 0 d narrow wide downstream
  have he := evalDist_map_bijective_uniform_cross
    (α := View (ZMod q) (n * b) p (columns params (n * b)))
    (β := MaskingView params (n * b) p)
    (viewEquiv params (n * b) p) (viewEquiv params (n * b) p).bijective
  have hi := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    he (observe params adversary)
  have hreal : GSWQuadraticPreimageBinary.realView builder (linear params (n * b)) 0 wide >>=
      downstream = GSWMasking.game params (publicView params builder wide) adversary := by
    simp [GSWMasking.game, publicView, downstream, observe, monad_norm]
  have hideal : 𝒟[($ᵗ View (ZMod q) (n * b) p (columns params (n * b))) >>= downstream] =
      𝒟[GSWMasking.game params ($ᵗ MaskingView params (n * b) p) adversary] := by
    simpa [GSWMasking.game, downstream, observe, monad_norm] using hi
  unfold ProbComp.boolDistAdvantage at hview
  rw [hreal, probOutput_congr (rfl : true = true) hideal] at hview
  exact (abs_sub_le _ _ (1 / 2 : ℝ)).trans
    (add_le_add hview (by simpa only [Nat.cast_mul] using
      ideal_game_abs_advantage_le params adversary))

abbrev StoredAdversary (params : Parameters q) (N p : ℕ) :=
  GSWMasking.Adversary (dimension := N) (samples := p) params
    (Vector (GSWAccumulator.StoredCiphertext params (N + 1)) N)

def liftStoredAdversary {N : ℕ} (params : Parameters q)
    (adversary : StoredAdversary params N p) : Adversary params N p where
  State := adversary.State
  chooseMessages view := adversary.chooseMessages
    (view.1, Vector.ofFn fun index ↦ GSWAccumulator.storeCiphertext params (view.2 index))
  distinguish := adversary.distinguish

/-- The challenge game actually receives the materialized key-generator output. -/
def storedGame (params : Parameters q)
    (builder : Builder (ZMod q) (n * b) p (columns params (n * b)))
    (errorSampler : ProbComp (ZMod q)) (adversary : StoredAdversary params (n * b) p) : ProbComp Bool :=
  GSWMasking.game params ((fun keys ↦ (GSWMasking.tableOfPublicKey keys.2.1, keys.2.2)) <$>
    keygen params builder errorSampler) adversary

theorem storedGame_eq (params : Parameters q)
    (builder : Builder (ZMod q) (n * b) p (columns params (n * b)))
    (errorSampler : ProbComp (ZMod q)) (adversary : StoredAdversary params (n * b) p) :
    storedGame params builder errorSampler adversary =
      GSWMasking.game params (publicView params builder errorSampler) (liftStoredAdversary params adversary) := by
  have hmap : ((fun keys ↦ (GSWMasking.tableOfPublicKey keys.2.1, keys.2.2)) <$>
      keygen params builder errorSampler) =
      (fun view ↦ (view.1, Vector.ofFn fun index ↦ GSWAccumulator.storeCiphertext params (view.2 index))) <$>
        publicView params builder errorSampler := by
    have hh := congrArg (fun sampler ↦ (fun stored ↦
      (GSWMasking.tableOfPublicKey stored.1, stored.2)) <$> sampler)
      (keygen_public_eq params builder errorSampler)
    simpa [storeView, monad_norm] using hh
  simp [storedGame, hmap, GSWMasking.game, liftStoredAdversary, monad_norm]

theorem stored_game_abs_advantage_le (params : Parameters q)
    (builder : Builder (ZMod q) (n * b) p (columns params (n * b)))
    (d : ℕ) (narrow wide : ProbComp (ZMod q)) (adversary : StoredAdversary params (n * b) p) :
    |Pr[= true | storedGame params builder wide adversary].toReal - 1 / 2| ≤
      GSWQuadraticPreimageBinary.ordinaryLoss builder (linear params (n * b)) 0 d narrow wide
        (fun view ↦ observe params (liftStoredAdversary params adversary) (viewEquiv params (n * b) p view)) +
      ((n * b + 1) * params.levels) *
        (Real.sqrt ((q : ℝ) ^ (n * b + 1) / (2 : ℝ) ^ p) / 2) := by
  rw [storedGame_eq]
  exact public_game_abs_advantage_le params builder d narrow wide (liftStoredAdversary params adversary)

end

end FormalProof4FHE.LWE.GSWQuadraticPreimageGSW
