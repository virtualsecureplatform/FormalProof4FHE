/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/
import FormalProof4FHE.LWE.GSWLinearCharacterPolynomial
import FormalProof4FHE.LWE.GSWLinearCharacterSecurity
import FormalProof4FHE.LWE.RecursiveFeatureControlPolynomial
import FormalProof4FHE.LWE.RecursiveFeatureFHECorrectness

/-!
# Complete original-bit controls from one public character-compiler source

The existing quadratic control polynomial supplies all constant, linear and
repeated-index gadget targets. A public sparse-polynomial discrepancy accounts
for every genuine cubic slot, including low gadget levels. No cancellation or
shortness premise is used to define the actual bound. The completed matrices
are materialized in the original bootstrapper's StoredOriginal format.

This connects the new candidate's source draw to reusable refresh correctness;
it does not prove an efficient builder with sufficiently small bounds.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.LWE.GSWLinearCharacterBootstrap

open RecursiveMultiplication RecursiveFeatureGSW RecursiveFeatureBootstrap
open RecursiveFeatureControlHybrid RecursiveFeatureControlPolynomial
open GSWLinearCharacterCompiler GSWLinearCharacterPolynomial

variable {q n m p : ℕ} [NeZero q] {P : Type} [Fintype P]

abbrev Builder (params : Parameters q) (n m : ℕ) (P : Type) :=
  GSWLinearCharacterSecurity.Builder q n m (controlCount params n) P

abbrev Context (params : Parameters q) (n m : ℕ) :=
  RecursiveFeaturePublicKey.Context q n m (controlCount params n)

def polynomialCipher {k : ℕ} (polynomial : RecursiveQuadratic.Polynomial (ZMod q) n k)
    (index : Fin k) : RecursiveQuadratic.Ciphertext (ZMod q) n :=
  (-polynomial.quadratic index, polynomial.linear index, polynomial.constant index)

omit [NeZero q] in
theorem decrypt_polynomialCipher {k : ℕ}
    (polynomial : RecursiveQuadratic.Polynomial (ZMod q) n k)
    (index : Fin k) (secret : Fin n → ZMod q) :
    RecursiveQuadratic.decrypt secret (polynomialCipher polynomial index) =
      RecursiveQuadratic.message polynomial secret index := by
  simp only [RecursiveQuadratic.decrypt, polynomialCipher, RecursiveQuadratic.message,
    vecMul, dotProduct, Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib]
  ring

noncomputable def targetPolynomial (params : Parameters q) (index : Fin n)
    (coordinate : Feature n) (level : Fin params.levels) : MvPolynomial (Fin n) (ZMod q) :=
  match coordinate with
  | some (.inr (first, second)) =>
      if genuineCubic index coordinate then
        MvPolynomial.C (TFHE.Gadget.Base.gadget params level) * MvPolynomial.X index *
          MvPolynomial.X first * MvPolynomial.X second
      else 0
  | _ => 0

theorem eval_targetPolynomial (params : Parameters q) (index : Fin n)
    (coordinate : Feature n) (level : Fin params.levels) (secret : Fin n → ZMod q) :
    MvPolynomial.eval secret (targetPolynomial params index coordinate level) =
      if genuineCubic index coordinate then controlMessage params secret index coordinate level else 0 := by
  cases coordinate with
  | none => simp [targetPolynomial, genuineCubic]
  | some coordinate => cases coordinate with
    | inl row => simp [targetPolynomial, genuineCubic]
    | inr pair =>
        rcases pair with ⟨first, second⟩
        by_cases h : genuineCubic index (some (.inr (first, second))) = true
        · simp [targetPolynomial, h, controlMessage_quadratic]
        · simp [targetPolynomial, h]

omit [NeZero q] in
theorem targetPolynomial_eq_zero (params : Parameters q) (index : Fin n)
    (coordinate : Feature n) (level : Fin params.levels)
    (h : genuineCubic index coordinate = false) :
    targetPolynomial params index coordinate level = 0 := by
  cases coordinate with
  | none => rfl
  | some coordinate => cases coordinate with
    | inl row => rfl
    | inr pair => simp [targetPolynomial, h]

/-- In particular, omitting the two lowest cubic gadget weights has bounded
discrepancy; it does not require division by four or assumed zero noise. -/
theorem targetPolynomial_bound (params : Parameters q) (index : Fin n)
    (coordinate : Feature n) (level : Fin params.levels) :
    coefficientBound (targetPolynomial params index coordinate level) ≤ params.base ^ level.val := by
  cases coordinate with
  | none => simp [targetPolynomial]
  | some coordinate => cases coordinate with
    | inl row => simp [targetPolynomial]
    | inr pair =>
        rcases pair with ⟨first, second⟩
        unfold targetPolynomial
        split_ifs
        · rw [coefficientBound_cubicMonomial]
          simpa only [TFHE.Gadget.Base.gadget, Nat.cast_pow] using
            TFHE.NoiseBounds.centeredRepr_natCast_natAbs_le (q := q) (params.base ^ level.val)
        · simp

/-- Exact target decomposition, including every repeated-index Boolean identity. -/
theorem controlMessage_split (params : Parameters q) (bits : Fin n → Bool) (index : Fin n)
    (coordinate : Feature n) (level : Fin params.levels) :
    RecursiveQuadratic.message (controlPolynomial params) (GSWSelfKey.binaryEmbed bits)
        (finProdFinEquiv (index, finProdFinEquiv (featureEquiv n coordinate, level))) +
      MvPolynomial.eval (GSWSelfKey.binaryEmbed bits) (targetPolynomial params index coordinate level) =
        controlMessage params (GSWSelfKey.binaryEmbed bits) index coordinate level := by
  rw [controlPolynomial_message_at, eval_targetPolynomial]
  split_ifs <;> simp

/-- Public addition of the lower-degree correction, followed by eager storage
of every complete GSW matrix. The input is the new security sampler's context. -/
def completeOriginal (params : Parameters q) (original : Context params n m) : StoredOriginal params n :=
  storeOriginal params (fun index column ↦
    addZero (polynomialCipher (controlPolynomial params) (finProdFinEquiv (index, column)))
      (original.2 (finProdFinEquiv (index, column))))

theorem completeOriginal_view (params : Parameters q) (original : Context params n m) :
    originalView params (completeOriginal params original) = fun index column ↦
      addZero (polynomialCipher (controlPolynomial params) (finProdFinEquiv (index, column)))
        (original.2 (finProdFinEquiv (index, column))) :=
  originalView_storeOriginal params _

noncomputable def columnBound (params : Parameters q) (first second : P → Fin n)
    (builder : Builder params n m P) (a : Matrix (Fin n) (Fin m) (ZMod q))
    (E : ℕ) (slot : Fin (controlCount params n)) : ℕ :=
  let coords := coordinates params n slot
  (∑ pair, ∑ column, (LatticeCrypto.centeredRepr (builder a slot pair column)).natAbs) * E +
    coefficientBound (cubicPolynomial first second a (builder a slot) -
      targetPolynomial params coords.1 coords.2.1 coords.2.2)

noncomputable def compilerBound (params : Parameters q) (first second : P → Fin n)
    (builder : Builder params n m P) (a : Matrix (Fin n) (Fin m) (ZMod q)) (E : ℕ) : ℕ :=
  Finset.univ.sup (columnBound params first second builder a E)

noncomputable def controlBound (params : Parameters q) (first second : P → Fin n)
    (builder : Builder params n m P) (a : Matrix (Fin n) (Fin m) (ZMod q)) (E : ℕ) : ℕ :=
  (n + 1) * E + compilerBound params first second builder a E

theorem columnBound_zero (params : Parameters q) (first second : P → Fin n)
    (builder : Builder params n m P) (a : Matrix (Fin n) (Fin m) (ZMod q)) (E : ℕ)
    (slot : Fin (controlCount params n)) (hu : builder a slot = 0) :
    columnBound params first second builder a E slot =
      coefficientBound (targetPolynomial params (coordinates params n slot).1
        (coordinates params n slot).2.1 (coordinates params n slot).2.2) := by
  simp [columnBound, hu, cubicPolynomial_zero, LatticeCrypto.centeredRepr_eq_valMinAbs]

theorem columnBound_le (params : Parameters q) (first second : P → Fin n)
    (builder : Builder params n m P) (a : Matrix (Fin n) (Fin m) (ZMod q))
    (E : ℕ) (slot : Fin (controlCount params n)) :
    columnBound params first second builder a E slot ≤ compilerBound params first second builder a E := by
  exact Finset.le_sup (f := columnBound params first second builder a E) (Finset.mem_univ slot)

/-- The real completed controls, from one draw of the sampler already covered
by the ordinary-source security theorem. -/
def freshOriginal (params : Parameters q) (first second : P → Fin n)
    (builder : Builder params n m P) (bits : Fin n → Bool)
    (masks : Matrix (Fin n) (RecursiveQuadratic.Column n m (p + controlCount params n)) (ZMod q))
    (errors : RecursiveQuadratic.Column n m (p + controlCount params n) → ZMod q) :
    StoredOriginal params n :=
  completeOriginal params
    (GSWLinearCharacterSecurity.freshDraw first second builder (GSWSelfKey.binaryEmbed bits) masks errors).2

theorem freshOriginal_column_bound (params : Parameters q)
    (first second : P → Fin n) (hpair : ∀ pair, first pair ≠ second pair)
    (builder : Builder params n m P) (bits : Fin n → Bool)
    (masks : Matrix (Fin n) (RecursiveQuadratic.Column n m (p + controlCount params n)) (ZMod q))
    (errors : RecursiveQuadratic.Column n m (p + controlCount params n) → ZMod q) (E : ℕ)
    (herror : ∀ column, (LatticeCrypto.centeredRepr (errors column)).natAbs ≤ E)
    (index : Fin n) (coordinate : Feature n) (level : Fin params.levels) :
    let a : Matrix (Fin n) (Fin m) (ZMod q) := fun row column ↦ masks row (.inl column)
    let slot := finProdFinEquiv (index, finProdFinEquiv (featureEquiv n coordinate, level))
    (LatticeCrypto.centeredRepr
      (RecursiveQuadratic.decrypt (GSWSelfKey.binaryEmbed bits)
        (originalView params (freshOriginal params first second builder bits masks errors) index
          (finProdFinEquiv (featureEquiv n coordinate, level))) -
        controlMessage params (GSWSelfKey.binaryEmbed bits) index coordinate level)).natAbs ≤
      (n + 1) * E + columnBound params first second builder a E slot := by
  dsimp only
  let a : Matrix (Fin n) (Fin m) (ZMod q) := fun row column ↦ masks row (.inl column)
  let slot := finProdFinEquiv (index, finProdFinEquiv (featureEquiv n coordinate, level))
  let secret := GSWSelfKey.binaryEmbed (R := ZMod q) bits
  let original := GSWLinearCharacterSecurity.freshDraw first second builder secret masks errors
  have hc := GSWLinearCharacterSecurity.freshDraw_control_error_bound first second hpair builder
    bits masks errors E herror slot
  have hd := cubic_discrepancy_bound first second a (builder a slot)
    (targetPolynomial params index coordinate level) bits
  have hs := controlMessage_split params bits index coordinate level
  rw [freshOriginal, completeOriginal_view, decrypt_addZero, decrypt_polynomialCipher]
  have heq : RecursiveQuadratic.message (controlPolynomial params) secret slot +
      RecursiveQuadratic.decrypt secret (original.2.2 slot) -
        controlMessage params secret index coordinate level =
      (RecursiveQuadratic.decrypt secret (original.2.2 slot) - cubicPhase first second a (builder a slot) secret) +
        (cubicPhase first second a (builder a slot) secret -
          MvPolynomial.eval secret (targetPolynomial params index coordinate level)) := by
    change _ + _ = _ at hs
    dsimp only [secret, slot]
    linear_combination hs
  change (LatticeCrypto.centeredRepr (_ + _ - _)).natAbs ≤ _
  rw [heq]
  exact ((TFHE.NoiseBounds.centeredRepr_add_natAbs_le _ _).trans
    (Nat.add_le_add hc hd)).trans_eq (by simp [columnBound, coordinates, a, slot]; omega)

/-- Every completed original-bit GSW matrix has its actual full-table bound.
The only hypothesis on the scalar errors is their support bound. -/
theorem noiseBound_freshOriginal (params : Parameters q)
    (first second : P → Fin n) (hpair : ∀ pair, first pair ≠ second pair)
    (builder : Builder params n m P) (bits : Fin n → Bool)
    (masks : Matrix (Fin n) (RecursiveQuadratic.Column n m (p + controlCount params n)) (ZMod q))
    (errors : RecursiveQuadratic.Column n m (p + controlCount params n) → ZMod q) (E : ℕ)
    (herror : ∀ column, (LatticeCrypto.centeredRepr (errors column)).natAbs ≤ E)
    (index : Fin n) :
    NoiseBound params (GSWSelfKey.binaryEmbed bits)
      (originalView params (freshOriginal params first second builder bits masks errors) index)
      (GSWGadget.bitMessage (bits index))
      (controlBound params first second builder (fun row column ↦ masks row (.inl column)) E) := by
  intro column
  obtain ⟨⟨featureIndex, level⟩, rfl⟩ := finProdFinEquiv.surjective column
  obtain ⟨coordinate, rfl⟩ := (featureEquiv n).surjective featureIndex
  have h := freshOriginal_column_bound params first second hpair builder bits masks errors E herror
    index coordinate level
  have hb := Nat.add_le_add_left
    (columnBound_le params first second builder (fun row column ↦ masks row (.inl column)) E
      (finProdFinEquiv (index, finProdFinEquiv (featureEquiv n coordinate, level)))) ((n + 1) * E)
  exact h.trans hb

/-- Reusable same-key refresh with the compiler's COMPUTED error bound, not an
assumed correct control table. The remaining margins are the existing evaluator
inequalities; obtaining them asymptotically is still a generator obligation. -/
theorem noiseBound_bootstrap {factor lookup n m p : ℕ} [NeZero factor] [NeZero lookup]
    (params : Parameters (factor * lookup))
    (first second : P → Fin n) (hpair : ∀ pair, first pair ≠ second pair)
    (builder : Builder params n m P) (bits : Fin n → Bool)
    (masks : Matrix (Fin n) (RecursiveQuadratic.Column n m (p + controlCount params n)) (ZMod (factor * lookup)))
    (errors : RecursiveQuadratic.Column n m (p + controlCount params n) → ZMod (factor * lookup))
    (E : ℕ) (herror : ∀ column, (LatticeCrypto.centeredRepr (errors column)).natAbs ≤ E)
    (ciphertext : Batch params n) (level : Fin params.levels) (oneCode : ZMod lookup)
    (bit : Bool) (inputBound : ℕ)
    (hcode : TFHE.Gadget.Base.gadget params level = GSWModulusSwitch.up factor lookup oneCode)
    (hinput : NoiseBound params (GSWSelfKey.binaryEmbed bits) ciphertext (GSWGadget.bitMessage bit) inputBound)
    (hround : 2 * (inputBound + (rows n + 1) * (factor - 1)) <
      factor * TFHE.BootstrappingCorrectness.centeredDistance 0 oneCode) :
    NoiseBound params (GSWSelfKey.binaryEmbed bits)
      (bootstrap params (originalView params (freshOriginal params first second builder bits masks errors))
        ciphertext level oneCode) (GSWGadget.bitMessage bit)
      (lookup * rows n * GSWGadget.growth params (rows n) *
        ((GSWGadget.growth params (rows n) + 1) *
          controlBound params first second builder (fun row column ↦ masks row (.inl column)) E)) := by
  exact RecursiveFeatureBootstrap.noiseBound_bootstrap params bits _ ciphertext level oneCode bit inputBound _
    hcode hinput (noiseBound_freshOriginal params first second hpair builder bits masks errors E herror) hround

/-- Arbitrary finite shared NAND programs use these actual same-key controls.
Only the explicit evaluator margins remain; a separate correct-control premise
has been discharged by the source and public polynomial coefficient bounds. -/
theorem decode_evaluate_from_source {factor lookup n m publicSamples inputs wires : ℕ}
    [NeZero factor] [NeZero lookup] (params : Parameters (factor * lookup))
    (first second : P → Fin n) (hpair : ∀ pair, first pair ≠ second pair)
    (builder : Builder params n m P) (bits : Fin n → Bool)
    (masks : Matrix (Fin n)
      (RecursiveQuadratic.Column n m (publicSamples + controlCount params n)) (ZMod (factor * lookup)))
    (errors : RecursiveQuadratic.Column n m (publicSamples + controlCount params n) → ZMod (factor * lookup))
    (E : ℕ) (herror : ∀ column, (LatticeCrypto.centeredRepr (errors column)).natAbs ≤ E)
    (level : Fin params.levels) (oneCode : ZMod lookup)
    (initial : Vector (GSWAccumulator.StoredCiphertext params (rows n)) inputs)
    (messages : Vector Bool inputs) (program : GSWCircuit.Program inputs wires) (output : Fin wires) (bound : ℕ)
    (hcode : TFHE.Gadget.Base.gadget params level = GSWModulusSwitch.up factor lookup oneCode)
    (hinputs : ∀ index, NoiseBound params (GSWSelfKey.binaryEmbed bits)
      (ofMatrix params (GSWAccumulator.ciphertextView params (initial.get index)))
      (GSWGadget.bitMessage (messages.get index)) bound)
    (houtput : lookup * rows n * GSWGadget.growth params (rows n) *
      ((GSWGadget.growth params (rows n) + 1) *
        controlBound params first second builder (fun row column ↦ masks row (.inl column)) E) ≤ bound)
    (hround : 2 * ((GSWGadget.growth params (rows n) + 1) * bound + (rows n + 1) * (factor - 1)) <
      factor * TFHE.BootstrappingCorrectness.centeredDistance 0 oneCode)
    (hdecode : 2 * bound < TFHE.BootstrappingCorrectness.centeredDistance 0 (TFHE.Gadget.Base.gadget params level)) :
    decode params (GSWSelfKey.binaryEmbed bits)
      (ofMatrix params (GSWAccumulator.ciphertextView params
        ((RecursiveFeatureFHECorrectness.evaluate rfl params
          (freshOriginal params first second builder bits masks errors) level oneCode initial program).get output))) level =
      (GSWCircuit.runBits messages program).get output := by
  exact RecursiveFeatureFHECorrectness.decode_evaluate params level oneCode bits _ initial messages program output
    bound _ hcode (noiseBound_freshOriginal params first second hpair builder bits masks errors E herror)
    hinputs houtput hround hdecode

abbrev StoredView (params : Parameters q) (n m p : ℕ) :=
  GSWPublicKey.PublicKey q (RecursiveFeaturePublicKey.Dimension n) p ×
    (Context params n m × StoredOriginal params n)

/-- Retain the whole old view beside the completed stored evaluator controls. -/
def completeStoredView (params : Parameters q)
    (original : RecursiveFeaturePublicKey.StoredView q n m p (controlCount params n)) :
    StoredView params n m p :=
  (original.1, (original.2, completeOriginal params original.2))

noncomputable def keygen {samples : ℕ} (params : Parameters q)
    (first second : P → Fin n) (builder : Builder params n m P)
    (columns : RecursiveQuadratic.Column n m (p + controlCount params n) ≃ Fin samples)
    (secretSampler : ProbComp (Fin n → ZMod q)) (errorSampler : ProbComp (ZMod q)) :
    ProbComp (StoredView params n m p × (Fin n → ZMod q)) :=
  (fun pair ↦ (completeStoredView params pair.1, pair.2)) <$>
    GSWLinearCharacterSecurity.keygen first second builder columns secretSampler errorSampler

noncomputable local instance (params : Parameters q) :
    SampleableType (Matrix (Fin n) (RecursiveQuadratic.Column n m (p + controlCount params n)) (ZMod q)) :=
  instSampleableTypeFinFunc

/-- Exact sampler identity; the retained base, public zero columns and every
completed control originate in this one shared-key draw. -/
theorem binaryKeygen_eq_draw {samples : ℕ} (params : Parameters q)
    (first second : P → Fin n) (builder : Builder params n m P)
    (columns : RecursiveQuadratic.Column n m (p + controlCount params n) ≃ Fin samples)
    (secretSampler : ProbComp (Fin n → Bool)) (errorSampler : ProbComp (ZMod q)) :
    keygen params first second builder columns (GSWSelfKey.binaryEmbed <$> secretSampler) errorSampler = (do
      let bits ← secretSampler
      let masks ← $ᵗ Matrix (Fin n) (RecursiveQuadratic.Column n m (p + controlCount params n)) (ZMod q)
      let errors ← ProbComp.sampleIID samples errorSampler
      let view := GSWLinearCharacterSecurity.freshDraw first second builder
        (GSWSelfKey.binaryEmbed bits) masks (fun column ↦ errors (columns column))
      pure ((GSWMasking.storeTable view.1, (view.2, completeOriginal params view.2)), GSWSelfKey.binaryEmbed bits)) := by
  simp [keygen, GSWLinearCharacterSecurity.keygen, RecursiveFeaturePublicKey.keygen,
    RecursivePublicKey.keygen, completeStoredView, GSWLinearCharacterSecurity.storeMaterialize,
    GSWLinearCharacterSecurity.freshDraw, GSWLinearCharacterSecurity.materialize,
    RecursiveFeaturePublicKey.storeView, monad_norm]

/-- Actual key-generator support supplies the scalar support premise and both
public-table and completed-control bounds. No correct-control hypothesis is
postulated for the generated public key. -/
theorem keygen_noiseBounds {samples : ℕ} (params : Parameters q)
    (first second : P → Fin n) (hpair : ∀ pair, first pair ≠ second pair)
    (builder : Builder params n m P)
    (columns : RecursiveQuadratic.Column n m (p + controlCount params n) ≃ Fin samples)
    (secretSampler : ProbComp (Fin n → Bool)) (errorSampler : ProbComp (ZMod q)) (E : ℕ)
    (herror : ∀ error ∈ support errorSampler, (LatticeCrypto.centeredRepr error).natAbs ≤ E)
    (keys : StoredView params n m p × (Fin n → ZMod q))
    (hkeys : keys ∈ support
      (keygen params first second builder columns (GSWSelfKey.binaryEmbed <$> secretSampler) errorSampler)) :
    ∃ bits : Fin n → Bool, keys.2 = GSWSelfKey.binaryEmbed bits ∧
      (∀ sample, (LatticeCrypto.centeredRepr
        (dotProduct (featureSecret (GSWSelfKey.binaryEmbed bits))
          (GSWMasking.tableOfPublicKey keys.1.1 sample))).natAbs ≤ (n + 1) * E) ∧
      (∀ index, NoiseBound params (GSWSelfKey.binaryEmbed bits) (originalView params keys.1.2.2 index)
        (GSWGadget.bitMessage (bits index))
        (controlBound params first second builder keys.1.2.1.1.1 E)) := by
  rw [binaryKeygen_eq_draw] at hkeys
  simp only [mem_support_bind_iff] at hkeys
  obtain ⟨bits, _, masks, _, errors, herrors, hkeys⟩ := hkeys
  simp only [support_pure, Set.mem_singleton_iff] at hkeys
  subst keys
  have he : ∀ column, (LatticeCrypto.centeredRepr (errors (columns column))).natAbs ≤ E := by
    intro column
    exact herror _ (TFHE.Native.KeySwitchRecovery.mem_support_mOfFn_apply _ _ errors herrors _)
  refine ⟨bits, rfl, ?_, ?_⟩
  · intro sample
    rw [GSWMasking.tableOfPublicKey_storeTable]
    apply RecursiveFeaturePublicKey.published_column_fresh_bound
      (GSWLinearCharacterSecurity.zeroPolynomial q n (controlCount params n))
      (GSWSelfKey.binaryEmbed bits) masks (fun column ↦ errors (columns column)) E _ he sample
    intro row
    cases hb : bits row <;> simp [GSWSelfKey.binaryEmbed, hb]
  · exact noiseBound_freshOriginal params first second hpair builder bits masks
      (fun column ↦ errors (columns column)) E he

/-- Same secret and encryptor, with the actual completed controls already stored
in the public key. No private work is deferred to the public evaluator. -/
noncomputable def scheme {samples : ℕ} (params : Parameters q) (level : Fin params.levels)
    (first second : P → Fin n) (builder : Builder params n m P)
    (columns : RecursiveQuadratic.Column n m (p + controlCount params n) ≃ Fin samples)
    (secretSampler : ProbComp (Fin n → ZMod q)) (errorSampler : ProbComp (ZMod q)) :
    AsymmEncAlg ProbComp Bool (StoredView params n m p) (Fin n → ZMod q)
      (GSWAccumulator.StoredCiphertext params (RecursiveFeaturePublicKey.Dimension n + 1)) where
  keygen := keygen params first second builder columns secretSampler errorSampler
  encrypt := fun view bit ↦ GSWMasking.encrypt params (GSWMasking.tableOfPublicKey view.1) bit
  decrypt := fun secret ciphertext ↦ pure (some (decode params secret
    (RecursiveFeaturePublicKey.ofStored params ciphertext) level))

def liftINDCPA {samples : ℕ} (params : Parameters q) (level : Fin params.levels)
    (first second : P → Fin n) (builder : Builder params n m P)
    (columns : RecursiveQuadratic.Column n m (p + controlCount params n) ≃ Fin samples)
    (secretSampler : ProbComp (Fin n → ZMod q)) (errorSampler : ProbComp (ZMod q))
    (adversary : AsymmEncAlg.IND_CPA_Adv
      (scheme params level first second builder columns secretSampler errorSampler)) :
    AsymmEncAlg.IND_CPA_Adv
      (GSWLinearCharacterSecurity.scheme params level first second builder columns secretSampler errorSampler) where
  State := adversary.State
  chooseMessages view := adversary.chooseMessages (completeStoredView params view)
  distinguish := adversary.distinguish

/-- The exact complete stored-control game, not a ciphertext-marginal hybrid. -/
theorem oneTime_game_eq {samples : ℕ} (params : Parameters q) (level : Fin params.levels)
    (first second : P → Fin n) (builder : Builder params n m P)
    (columns : RecursiveQuadratic.Column n m (p + controlCount params n) ≃ Fin samples)
    (secretSampler : ProbComp (Fin n → ZMod q)) (errorSampler : ProbComp (ZMod q))
    (adversary : AsymmEncAlg.IND_CPA_Adv
      (scheme params level first second builder columns secretSampler errorSampler)) :
    AsymmEncAlg.IND_CPA_OneTime_Game_ProbComp adversary =
      AsymmEncAlg.IND_CPA_OneTime_Game_ProbComp
        (liftINDCPA params level first second builder columns secretSampler errorSampler adversary) := by
  simp [AsymmEncAlg.IND_CPA_OneTime_Game_ProbComp, scheme, keygen,
    GSWLinearCharacterSecurity.scheme, completeStoredView, liftINDCPA, monad_norm]

/-- Composing this equality with GSWLinearCharacterSecurity's ordinary-LWE
bound covers publication of ALL completed original-bit controls as well. -/
theorem oneTime_signedAdvantage_eq {samples : ℕ} (params : Parameters q) (level : Fin params.levels)
    (first second : P → Fin n) (builder : Builder params n m P)
    (columns : RecursiveQuadratic.Column n m (p + controlCount params n) ≃ Fin samples)
    (secretSampler : ProbComp (Fin n → ZMod q)) (errorSampler : ProbComp (ZMod q))
    (adversary : AsymmEncAlg.IND_CPA_Adv
      (scheme params level first second builder columns secretSampler errorSampler)) :
    AsymmEncAlg.IND_CPA_OneTime_signedAdvantageReal
        (scheme params level first second builder columns secretSampler errorSampler) adversary =
      AsymmEncAlg.IND_CPA_OneTime_signedAdvantageReal
        (GSWLinearCharacterSecurity.scheme params level first second builder columns secretSampler errorSampler)
        (liftINDCPA params level first second builder columns secretSampler errorSampler adversary) := by
  unfold AsymmEncAlg.IND_CPA_OneTime_signedAdvantageReal
  rw [oneTime_game_eq]

end FormalProof4FHE.LWE.GSWLinearCharacterBootstrap
