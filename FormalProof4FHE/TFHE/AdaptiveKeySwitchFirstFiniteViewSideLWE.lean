/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.ParallelBatch
import FormalProof4FHE.Probability.MajorityBatchEquiv
import FormalProof4FHE.TFHE.AdaptiveKeySwitchFirstFiniteViewCircularDecomposition

/-!
# Uniform-BRK Finite TFHE Recovery as Structured Search LWE

After every BRK is made uniform, the remaining secret-dependent public objects are direct TLWE
rows: one KSK block and one zero-message input-tape block per augmented view.  This module packages
all such rows as a single structured heterogeneous LWE problem sharing one binary scalar secret.

The structured problem keeps one two-block transcript per view.  The exact majority-tree
equivalence flattens the native `lweDimension * 3 ^ rounds` view carrier, and the search reduction
samples the independent ring key and uniform BRKs itself.  KSK messages are public to that
reduction after it samples the ring key, so they are deterministic body translations of ordinary
zero-message LWE rows.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.KeySwitchFirstFiniteView

open Native

variable
  {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount rounds : ℕ} [NeZero q]

/-! ## One two-block transcript per flat view -/

/-- Number of direct scalar rows in one native KSK. -/
abbrev sideKeySwitchSamples (ringRank degree keySwitchLevels : ℕ) :=
  (ringRank * degree) * keySwitchLevels

/-- Exact number of flat augmented views used by the common-depth majority solver. -/
abbrev sideViewCount (lweDimension rounds : ℕ) :=
  lweDimension * FormalProof4FHE.MajorityAmplification.majorityBatchViewCount rounds

/-- One public two-block LWE challenge per augmented view. -/
abbrev SideLWEChallenge
    (q lweDimension ringRank degree keySwitchLevels queryCount rounds : ℕ) :=
  Fin (sideViewCount lweDimension rounds) →
    FormalProof4FHE.LWE.TwoBlock.Challenge (ZMod q) lweDimension
      (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount

/-- One two-block LWE output per augmented view. -/
abbrev SideLWEOutput
    (q lweDimension ringRank degree keySwitchLevels queryCount rounds : ℕ) :=
  Fin (sideViewCount lweDimension rounds) →
    FormalProof4FHE.LWE.TwoBlock.Output (ZMod q)
      (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount

/-- One two-block public transcript per augmented view. -/
abbrev SideLWETranscript
    (q lweDimension ringRank degree keySwitchLevels queryCount rounds : ℕ) :=
  SideLWEChallenge q lweDimension ringRank degree keySwitchLevels queryCount rounds ×
    SideLWEOutput q lweDimension ringRank degree keySwitchLevels queryCount rounds

/-- Independent heterogeneous error pair for one KSK/input-tape view. -/
def sideViewErrorSampler
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q)) :
    ProbComp (FormalProof4FHE.LWE.TwoBlock.Output (ZMod q)
      (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount) := do
  let keySwitchError ← ProbComp.sampleIID
    (sideKeySwitchSamples ringRank degree keySwitchLevels) keySwitchErrorSampler
  let inputError ← ProbComp.sampleIID queryCount inputErrorSampler
  return (keySwitchError, inputError)

/-- Structured same-secret LWE problem containing every KSK and input-tape block used by the
finite augmented recovery solver. -/
noncomputable def sideLweProblem
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q)) :
    LearningWithErrors.Problem
      (SideLWEChallenge q lweDimension ringRank degree keySwitchLevels queryCount rounds)
      (BinarySecret lweDimension)
      (SideLWEOutput q lweDimension ringRank degree keySwitchLevels queryCount rounds) where
  sampleChallenge := Fin.mOfFn (sideViewCount lweDimension rounds) fun _ ↦
    $ᵗ (FormalProof4FHE.LWE.TwoBlock.Challenge (ZMod q) lweDimension
      (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount)
  sampleSecret := sampleLweSecret lweDimension
  sampleError := Fin.mOfFn (sideViewCount lweDimension rounds) fun _ ↦
    sideViewErrorSampler (ringRank := ringRank) (degree := degree)
      (keySwitchLevels := keySwitchLevels) keySwitchErrorSampler inputErrorSampler
  noiseless := fun secret challenge view ↦
    (vecMul (embedBinarySecret secret) (challenge view).1,
      vecMul (embedBinarySecret secret) (challenge view).2)
  sampleUniform := Fin.mOfFn (sideViewCount lweDimension rounds) fun _ ↦
    $ᵗ (FormalProof4FHE.LWE.TwoBlock.Output (ZMod q)
      (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount)

/-! ## Deterministic native-view assembly -/

/-- Shift the first block by the native ring-key KSK messages and attach an independent BRK. -/
def viewOfSideTranscript
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (ringSecret : RingBinarySecret ringRank degree)
    (bootstrapKey : Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
    (transcript : FormalProof4FHE.LWE.TwoBlock.Transcript (ZMod q) lweDimension
      (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount) :
    View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount :=
  let shifted := Encryption.Security.shiftFirstBlock
    (Native.keySwitchMessages (ringRank * degree) keySwitchLevels
      keySwitchGadget (keyExtract ringSecret)) transcript
  let blocks := FormalProof4FHE.LWE.TwoBlock.toTranscriptPair shifted
  ((bootstrapKey, blocks.1), blocks.2)

/-- Read a selected per-view transcript from the structured LWE carrier. -/
def sideTranscriptAt
    (transcript : SideLWETranscript q lweDimension ringRank degree
      keySwitchLevels queryCount rounds)
    (view : Fin (sideViewCount lweDimension rounds)) :
    FormalProof4FHE.LWE.TwoBlock.Transcript (ZMod q) lweDimension
      (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount :=
  (transcript.1 view, transcript.2 view)

/-- Search-LWE reduction: sample the independent ring key and uniform BRKs, translate the KSK
bodies, restore the majority-tree shape, and invoke the original augmented-batch solver. -/
noncomputable def sideLweSearchReduction
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) :
    LearningWithErrors.SearchAdversary
      (sideLweProblem (q := q) (ringRank := ringRank) (degree := degree)
        (lweDimension := lweDimension)
        (keySwitchLevels := keySwitchLevels) (queryCount := queryCount)
        (rounds := rounds) (pure 0) (pure 0)) :=
  fun transcript ↦ do
    let ringSecret ← sampleRingSecret ringRank degree
    let views ← Fin.mOfFn (sideViewCount lweDimension rounds) fun view ↦ do
      let bootstrapKey ←
        $ᵗ (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      return viewOfSideTranscript keySwitchGadget ringSecret bootstrapKey
        (sideTranscriptAt transcript view)
    solver
      ((FormalProof4FHE.MajorityAmplification.vectorMajorityBatchEquiv
        (View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount)
        lweDimension rounds).symm views)

/- The error samplers are parameters of the problem but do not occur in the public type of a
search adversary.  This eta-expanded wrapper lets Lean infer the intended problem exactly. -/
noncomputable def sideLweSearchReductionFor
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) :
    LearningWithErrors.SearchAdversary
      (sideLweProblem (q := q) (ringRank := ringRank) (degree := degree)
        (lweDimension := lweDimension)
        (keySwitchLevels := keySwitchLevels) (queryCount := queryCount)
        (rounds := rounds) keySwitchErrorSampler inputErrorSampler) :=
  sideLweSearchReduction keySwitchGadget solver

/-! ## One-view distribution alignment -/

/-- Reorder five independent samplers from `first; second; third; fourth; fifth` to
`second; fourth; third; fifth; first`.  This is the order change between native TFHE view
generation and the two-block LWE presentation below. -/
theorem evalDist_bind_five_reorder
    {First Second Third Fourth Fifth Output : Type}
    (first : ProbComp First) (second : ProbComp Second)
    (third : ProbComp Third) (fourth : ProbComp Fourth)
    (fifth : ProbComp Fifth)
    (finish : First → Second → Third → Fourth → Fifth → ProbComp Output) :
    evalDist (first >>= fun firstValue ↦
      second >>= fun secondValue ↦
      third >>= fun thirdValue ↦
      fourth >>= fun fourthValue ↦
      fifth >>= fun fifthValue ↦
      finish firstValue secondValue thirdValue fourthValue fifthValue) =
    evalDist (second >>= fun secondValue ↦
      fourth >>= fun fourthValue ↦
      third >>= fun thirdValue ↦
      fifth >>= fun fifthValue ↦
      first >>= fun firstValue ↦
      finish firstValue secondValue thirdValue fourthValue fifthValue) := by
  calc
    _ = evalDist (second >>= fun secondValue ↦
        first >>= fun firstValue ↦
        third >>= fun thirdValue ↦
        fourth >>= fun fourthValue ↦
        fifth >>= fun fifthValue ↦
        finish firstValue secondValue thirdValue fourthValue fifthValue) :=
      evalDist_bind_bind_swap first second _
    _ = evalDist (second >>= fun secondValue ↦
        third >>= fun thirdValue ↦
        first >>= fun firstValue ↦
        fourth >>= fun fourthValue ↦
        fifth >>= fun fifthValue ↦
        finish firstValue secondValue thirdValue fourthValue fifthValue) := by
      refine evalDist_bind_congr' second fun secondValue ↦ ?_
      exact evalDist_bind_bind_swap first third _
    _ = evalDist (second >>= fun secondValue ↦
        third >>= fun thirdValue ↦
        fourth >>= fun fourthValue ↦
        first >>= fun firstValue ↦
        fifth >>= fun fifthValue ↦
        finish firstValue secondValue thirdValue fourthValue fifthValue) := by
      refine evalDist_bind_congr' second fun secondValue ↦ ?_
      refine evalDist_bind_congr' third fun thirdValue ↦ ?_
      exact evalDist_bind_bind_swap first fourth _
    _ = evalDist (second >>= fun secondValue ↦
        third >>= fun thirdValue ↦
        fourth >>= fun fourthValue ↦
        fifth >>= fun fifthValue ↦
        first >>= fun firstValue ↦
        finish firstValue secondValue thirdValue fourthValue fifthValue) := by
      refine evalDist_bind_congr' second fun secondValue ↦ ?_
      refine evalDist_bind_congr' third fun thirdValue ↦ ?_
      refine evalDist_bind_congr' fourth fun fourthValue ↦ ?_
      exact evalDist_bind_bind_swap first fifth _
    _ = _ := by
      refine evalDist_bind_congr' second fun secondValue ↦ ?_
      exact evalDist_bind_bind_swap third fourth _

/-- Deterministically assemble a native view from one structured LWE challenge/error pair and a
supplied uniform BRK. -/
def assembleSideLweView
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
      lweDimension ringRank degree)
    (bootstrapKey : Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
    (challenge : FormalProof4FHE.LWE.TwoBlock.Challenge (ZMod q) lweDimension
      (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount)
    (error : FormalProof4FHE.LWE.TwoBlock.Output (ZMod q)
      (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount) :
    View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount :=
  let transcript : FormalProof4FHE.LWE.TwoBlock.Transcript (ZMod q) lweDimension
      (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount :=
    (challenge,
      (vecMul (embedBinarySecret secrets.1) challenge.1,
        vecMul (embedBinarySecret secrets.1) challenge.2) + error)
  viewOfSideTranscript keySwitchGadget secrets.2 bootstrapKey transcript

/-- Assemble one view from an independently sampled two-block challenge/error pair and a uniform
BRK. -/
noncomputable def fixedSideLweView
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
      lweDimension ringRank degree) :
    ProbComp (View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) := do
  let challenge ←
    $ᵗ (FormalProof4FHE.LWE.TwoBlock.Challenge (ZMod q) lweDimension
      (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount)
  let error ← sideViewErrorSampler (ringRank := ringRank) (degree := degree)
    (keySwitchLevels := keySwitchLevels) (queryCount := queryCount)
    keySwitchErrorSampler inputErrorSampler
  let bootstrapKey ←
    $ᵗ (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
  return assembleSideLweView keySwitchGadget secrets bootstrapKey challenge error

/-- For fixed hidden keys, native generation of a uniform-BRK/real-KSK/input-tape view is
exactly the structured two-block LWE sampler followed by deterministic KSK-message translation. -/
theorem fixedUniformBootstrapView_evalDist_eq_fixedSideLweView
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
      lweDimension ringRank degree) :
    evalDist (fixedUniformBootstrapView
        (tgswLevels := tgswLevels) (queryCount := queryCount)
        keySwitchErrorSampler inputErrorSampler keySwitchGadget secrets) =
      evalDist (fixedSideLweView
        (tgswLevels := tgswLevels)
        keySwitchErrorSampler inputErrorSampler keySwitchGadget secrets) := by
  let bootstrapKeys :
      ProbComp (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension) :=
    $ᵗ (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
  let firstChallenges : ProbComp (Matrix (Fin lweDimension)
      (Fin (sideKeySwitchSamples ringRank degree keySwitchLevels)) (ZMod q)) :=
    $ᵗ Matrix (Fin lweDimension)
      (Fin (sideKeySwitchSamples ringRank degree keySwitchLevels)) (ZMod q)
  let firstErrors := ProbComp.sampleIID
    (sideKeySwitchSamples ringRank degree keySwitchLevels) keySwitchErrorSampler
  let secondChallenges : ProbComp (Matrix (Fin lweDimension) (Fin queryCount) (ZMod q)) :=
    $ᵗ Matrix (Fin lweDimension) (Fin queryCount) (ZMod q)
  let secondErrors := ProbComp.sampleIID queryCount inputErrorSampler
  let finish : Native.BootstrappingKey q degree ringRank tgswLevels lweDimension →
      Matrix (Fin lweDimension)
        (Fin (sideKeySwitchSamples ringRank degree keySwitchLevels)) (ZMod q) →
      (Fin (sideKeySwitchSamples ringRank degree keySwitchLevels) → ZMod q) →
      Matrix (Fin lweDimension) (Fin queryCount) (ZMod q) →
      (Fin queryCount → ZMod q) →
      ProbComp (View q degree ringRank tgswLevels lweDimension
        keySwitchLevels queryCount) := fun
      (bootstrapKey : Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (firstChallenge : Matrix (Fin lweDimension)
        (Fin (sideKeySwitchSamples ringRank degree keySwitchLevels)) (ZMod q))
      (firstError : Fin (sideKeySwitchSamples ringRank degree keySwitchLevels) → ZMod q)
      (secondChallenge : Matrix (Fin lweDimension) (Fin queryCount) (ZMod q))
      (secondError : Fin queryCount → ZMod q) ↦
    pure ((bootstrapKey,
      TLWE.batchAssemble (embedBinarySecret secrets.1) firstChallenge
        (Native.keySwitchMessages (ringRank * degree) keySwitchLevels
          keySwitchGadget (keyExtract secrets.2)) firstError),
      TLWE.batchAssemble (embedBinarySecret secrets.1) secondChallenge 0 secondError)
  have native_eq :
      fixedUniformBootstrapView
          (tgswLevels := tgswLevels) (queryCount := queryCount)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget secrets =
        (bootstrapKeys >>= fun bootstrapKey ↦
          firstChallenges >>= fun firstChallenge ↦
          firstErrors >>= fun firstError ↦
          secondChallenges >>= fun secondChallenge ↦
          secondErrors >>= fun secondError ↦
          finish bootstrapKey firstChallenge firstError secondChallenge secondError) := by
    simp [fixedUniformBootstrapView, Native.generateKeySwitchKey, TLWE.batchEncrypt,
      bootstrapKeys, firstChallenges, firstErrors, secondChallenges, secondErrors, finish,
      sideKeySwitchSamples, bind_assoc, monad_norm]
  have uniformChallengeProduct :
      ($ᵗ (FormalProof4FHE.LWE.TwoBlock.Challenge (ZMod q) lweDimension
        (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount) :
        ProbComp (FormalProof4FHE.LWE.TwoBlock.Challenge (ZMod q) lweDimension
          (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount)) =
      Prod.mk <$> firstChallenges <*> secondChallenges := rfl
  have side_eq :
      fixedSideLweView
          (tgswLevels := tgswLevels)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget secrets =
        (firstChallenges >>= fun firstChallenge ↦
          secondChallenges >>= fun secondChallenge ↦
          firstErrors >>= fun firstError ↦
          secondErrors >>= fun secondError ↦
          bootstrapKeys >>= fun bootstrapKey ↦
          finish bootstrapKey firstChallenge firstError secondChallenge secondError) := by
    unfold fixedSideLweView
    rw [uniformChallengeProduct]
    simp [sideViewErrorSampler, assembleSideLweView, viewOfSideTranscript,
      Encryption.Security.shiftFirstBlock,
      FormalProof4FHE.LWE.TwoBlock.toTranscriptPair,
      TLWE.batchAssemble, bootstrapKeys, firstChallenges, firstErrors,
      secondChallenges, secondErrors, finish, sideKeySwitchSamples,
      add_comm, add_left_comm, bind_assoc, monad_norm]
  rw [native_eq, side_eq]
  exact evalDist_bind_five_reorder bootstrapKeys firstChallenges firstErrors
    secondChallenges secondErrors finish

/-! ## Exact flattening of every majority view -/

/-- Presampling two independent finite arrays and processing them coordinatewise has the same
law as sampling and processing the two inputs consecutively at each coordinate. -/
theorem evalDist_presample_two_fin_mOfFn
    {First Second Output : Type}
    [Finite First] [Finite Second] [Finite Output]
    (count : ℕ)
    (first : Fin count → ProbComp First)
    (second : Fin count → ProbComp Second)
    (process : Fin count → First → Second → ProbComp Output) :
    evalDist (do
      let firstValues ← Fin.mOfFn count first
      let secondValues ← Fin.mOfFn count second
      Fin.mOfFn count fun index ↦
        process index (firstValues index) (secondValues index)) =
      evalDist (Fin.mOfFn count fun index ↦ do
        let firstValue ← first index
        let secondValue ← second index
        process index firstValue secondValue) := by
  let zipEquiv := Equiv.arrowProdEquivProdArrow (Fin count)
    (fun _ ↦ First) (fun _ ↦ Second)
  let pairedInputs : ProbComp (Fin count → First × Second) :=
    zipEquiv.symm <$> (do
      let firstValues ← Fin.mOfFn count first
      let secondValues ← Fin.mOfFn count second
      pure (firstValues, secondValues))
  let pairedSampler : Fin count → ProbComp (First × Second) := fun index ↦ do
    let firstValue ← first index
    let secondValue ← second index
    pure (firstValue, secondValue)
  have hzip : evalDist pairedInputs =
      evalDist (Fin.mOfFn count pairedSampler) := by
    simpa only [pairedInputs, pairedSampler, zipEquiv] using
      (FormalProof4FHE.FiniteProduct.evalDist_fin_mOfFn_zip count first second)
  calc
    _ = evalDist (pairedInputs >>= fun inputs ↦
          Fin.mOfFn count fun index ↦
            process index (inputs index).1 (inputs index).2) := by
      simp [pairedInputs, zipEquiv, bind_assoc, monad_norm]
    _ = evalDist ((Fin.mOfFn count pairedSampler) >>= fun inputs ↦
          Fin.mOfFn count fun index ↦
            process index (inputs index).1 (inputs index).2) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hzip _
    _ = evalDist (Fin.mOfFn count fun index ↦ do
          let inputs ← pairedSampler index
          process index inputs.1 inputs.2) :=
      FormalProof4FHE.FiniteProduct.evalDist_presample_fin_mOfFn
        count pairedSampler
          (fun index inputs ↦ process index inputs.1 inputs.2)
    _ = _ := by
      simp [pairedSampler, bind_assoc, monad_norm]

/-- Sample the structured problem's complete challenge and error arrays first, then attach an
independent uniform BRK and assemble each native view. -/
noncomputable def presampledSideLweBatch
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (secrets : Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
      lweDimension ringRank degree) :
    ProbComp (Fin (sideViewCount lweDimension rounds) →
      View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) := do
  let challenges ← (sideLweProblem
    (q := q) (ringRank := ringRank) (degree := degree)
    (lweDimension := lweDimension) (keySwitchLevels := keySwitchLevels)
    (queryCount := queryCount) (rounds := rounds)
    keySwitchErrorSampler inputErrorSampler).sampleChallenge
  let errors ← (sideLweProblem
    (q := q) (ringRank := ringRank) (degree := degree)
    (lweDimension := lweDimension) (keySwitchLevels := keySwitchLevels)
    (queryCount := queryCount) (rounds := rounds)
    keySwitchErrorSampler inputErrorSampler).sampleError
  Fin.mOfFn (sideViewCount lweDimension rounds) fun index ↦ do
    let bootstrapKey ←
      $ᵗ (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
    return assembleSideLweView keySwitchGadget secrets bootstrapKey
      (challenges index) (errors index)

/-- Deferred sampling: the problem-first batch has exactly the same law as independently
sampling the complete structured material of each view. -/
theorem presampledSideLweBatch_evalDist
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (secrets : Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
      lweDimension ringRank degree) :
    evalDist (presampledSideLweBatch
        (tgswLevels := tgswLevels) (queryCount := queryCount)
        keySwitchErrorSampler inputErrorSampler keySwitchGadget rounds secrets) =
      evalDist (Fin.mOfFn (sideViewCount lweDimension rounds) fun _ ↦
        fixedSideLweView (tgswLevels := tgswLevels) (queryCount := queryCount)
          keySwitchErrorSampler inputErrorSampler
          keySwitchGadget secrets) := by
  let challengeSampler : Fin (sideViewCount lweDimension rounds) →
      ProbComp (FormalProof4FHE.LWE.TwoBlock.Challenge (ZMod q) lweDimension
        (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount) := fun _ ↦
    $ᵗ (FormalProof4FHE.LWE.TwoBlock.Challenge (ZMod q) lweDimension
      (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount)
  let errorSampler : Fin (sideViewCount lweDimension rounds) →
      ProbComp (FormalProof4FHE.LWE.TwoBlock.Output (ZMod q)
        (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount) := fun _ ↦
    sideViewErrorSampler (ringRank := ringRank) (degree := degree)
      (keySwitchLevels := keySwitchLevels) (queryCount := queryCount)
      keySwitchErrorSampler inputErrorSampler
  let process := fun (_ : Fin (sideViewCount lweDimension rounds))
      (challenge : FormalProof4FHE.LWE.TwoBlock.Challenge (ZMod q) lweDimension
        (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount)
      (error : FormalProof4FHE.LWE.TwoBlock.Output (ZMod q)
        (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount) ↦ do
    let bootstrapKey ←
      $ᵗ (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
    return assembleSideLweView keySwitchGadget secrets bootstrapKey challenge error
  simpa [presampledSideLweBatch, sideLweProblem, fixedSideLweView,
    challengeSampler, errorSampler, process, bind_assoc, monad_norm] using
    (evalDist_presample_two_fin_mOfFn
      (sideViewCount lweDimension rounds) challengeSampler errorSampler process)

/-- Flattening all native majority trees and then replacing each native view by its structured
two-block presentation preserves the complete fixed-secret batch distribution. -/
theorem fixedUniformBootstrapBatch_flat_evalDist
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (secrets : Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
      lweDimension ringRank degree) :
    evalDist
        (FormalProof4FHE.MajorityAmplification.vectorMajorityBatchEquiv
            (View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount)
            lweDimension rounds <$>
          sampleBatch rounds
            (fixedUniformBootstrapView keySwitchErrorSampler inputErrorSampler
              keySwitchGadget secrets)) =
      evalDist (Fin.mOfFn (sideViewCount lweDimension rounds) fun _ ↦
        fixedSideLweView keySwitchErrorSampler inputErrorSampler
          keySwitchGadget secrets) := by
  calc
    _ = evalDist (Fin.mOfFn (sideViewCount lweDimension rounds) fun _ ↦
          fixedUniformBootstrapView keySwitchErrorSampler inputErrorSampler
            keySwitchGadget secrets) := by
      simpa only [sampleBatch, sideViewCount] using
        (FormalProof4FHE.MajorityAmplification.evalDist_vectorMajorityBatchEquiv_sample
          lweDimension rounds
          (fixedUniformBootstrapView keySwitchErrorSampler inputErrorSampler
            keySwitchGadget secrets))
    _ = _ := FormalProof4FHE.FiniteProduct.evalDist_fin_mOfFn_congr
      (sideViewCount lweDimension rounds) _ _ fun _ ↦
        fixedUniformBootstrapView_evalDist_eq_fixedSideLweView
          keySwitchErrorSampler inputErrorSampler keySwitchGadget secrets

/-! ## Exact search-experiment compilation -/

/-- The uniform-BRK endpoint is exactly the search experiment for the structured scalar-LWE
problem.  The equality preserves the sampled scalar key used in the final success check; it is
therefore a search-LWE reduction and does not make an invalid decisional-LWE claim. -/
theorem uniformBootstrapRecoveryGame_evalDist_eq_sideLweSearchExperiment
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (solver : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) :
    evalDist (uniformBootstrapRecoveryGame keySwitchErrorSampler inputErrorSampler
        keySwitchGadget rounds solver) =
      evalDist (LearningWithErrors.searchExperiment
        (sideLweProblem (q := q) (ringRank := ringRank) (degree := degree)
          (lweDimension := lweDimension) (keySwitchLevels := keySwitchLevels)
          (queryCount := queryCount) (rounds := rounds)
          keySwitchErrorSampler inputErrorSampler)
        (sideLweSearchReductionFor keySwitchErrorSampler inputErrorSampler
          keySwitchGadget solver)) := by
  let scalarSecrets := sampleLweSecret lweDimension
  let ringSecrets := sampleRingSecret ringRank degree
  let problem := sideLweProblem
    (q := q) (ringRank := ringRank) (degree := degree)
    (lweDimension := lweDimension) (keySwitchLevels := keySwitchLevels)
    (queryCount := queryCount) (rounds := rounds)
    keySwitchErrorSampler inputErrorSampler
  let challenges := problem.sampleChallenge
  let errors := problem.sampleError
  let flatten := FormalProof4FHE.MajorityAmplification.vectorMajorityBatchEquiv
    (View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount)
    lweDimension rounds
  let finish := fun (scalarSecret : BinarySecret lweDimension)
      (ringSecret : RingBinarySecret ringRank degree)
      (challengeValues : SideLWEChallenge q lweDimension ringRank degree
        keySwitchLevels queryCount rounds)
      (errorValues : SideLWEOutput q lweDimension ringRank degree
        keySwitchLevels queryCount rounds) ↦ do
    let views ← Fin.mOfFn (sideViewCount lweDimension rounds) fun index ↦ do
      let bootstrapKey ←
        $ᵗ (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      return assembleSideLweView keySwitchGadget (scalarSecret, ringSecret)
        bootstrapKey (challengeValues index) (errorValues index)
    let recovered ← solver (flatten.symm views)
    return decide (recovered = scalarSecret)
  have hBatch (scalarSecret : BinarySecret lweDimension)
      (ringSecret : RingBinarySecret ringRank degree) :
      evalDist (flatten <$> sampleBatch rounds
        (fixedUniformBootstrapView keySwitchErrorSampler inputErrorSampler
          keySwitchGadget (scalarSecret, ringSecret))) =
        evalDist (presampledSideLweBatch
          (tgswLevels := tgswLevels) (queryCount := queryCount)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget rounds
          (scalarSecret, ringSecret)) :=
    (fixedUniformBootstrapBatch_flat_evalDist
      keySwitchErrorSampler inputErrorSampler keySwitchGadget rounds
      (scalarSecret, ringSecret)).trans
        (presampledSideLweBatch_evalDist
          keySwitchErrorSampler inputErrorSampler keySwitchGadget rounds
          (scalarSecret, ringSecret)).symm
  have endpoint_eq :
      evalDist (uniformBootstrapRecoveryGame keySwitchErrorSampler inputErrorSampler
          keySwitchGadget rounds solver) =
        evalDist (scalarSecrets >>= fun scalarSecret ↦
          ringSecrets >>= fun ringSecret ↦
          challenges >>= fun challengeValues ↦
          errors >>= fun errorValues ↦
          finish scalarSecret ringSecret challengeValues errorValues) := by
    calc
      _ = evalDist (scalarSecrets >>= fun scalarSecret ↦
          ringSecrets >>= fun ringSecret ↦
          presampledSideLweBatch
              (tgswLevels := tgswLevels) (queryCount := queryCount)
              keySwitchErrorSampler inputErrorSampler keySwitchGadget rounds
              (scalarSecret, ringSecret) >>= fun views ↦
              solver (flatten.symm views) >>= fun recovered ↦
          pure (decide (recovered = scalarSecret))) := by
        rw [show uniformBootstrapRecoveryGame keySwitchErrorSampler inputErrorSampler
              keySwitchGadget rounds solver =
            (scalarSecrets >>= fun scalarSecret ↦
              ringSecrets >>= fun ringSecret ↦
              sampleBatch rounds
                  (fixedUniformBootstrapView keySwitchErrorSampler inputErrorSampler
                    keySwitchGadget (scalarSecret, ringSecret)) >>= fun batch ↦
              solver batch >>= fun recovered ↦
              pure (decide (recovered = scalarSecret))) by
            simp [uniformBootstrapRecoveryGame, secretSampler, scalarSecrets, ringSecrets,
              bind_assoc, monad_norm]]
        refine evalDist_bind_congr' scalarSecrets fun scalarSecret ↦ ?_
        refine evalDist_bind_congr' ringSecrets fun ringSecret ↦ ?_
        rw [show (sampleBatch rounds
              (fixedUniformBootstrapView keySwitchErrorSampler inputErrorSampler
                keySwitchGadget (scalarSecret, ringSecret)) >>= fun batch ↦
              solver batch >>= fun recovered ↦
              pure (decide (recovered = scalarSecret))) =
            ((flatten <$> sampleBatch rounds
                (fixedUniformBootstrapView keySwitchErrorSampler inputErrorSampler
                  keySwitchGadget (scalarSecret, ringSecret))) >>= fun views ↦
              solver (flatten.symm views) >>= fun recovered ↦
              pure (decide (recovered = scalarSecret))) by
              simp [flatten, bind_assoc, monad_norm]]
        exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
          (hBatch scalarSecret ringSecret) _
      _ = _ := by
        simp [presampledSideLweBatch, problem, challenges, errors, finish,
          flatten, bind_assoc, monad_norm]
  have search_eq :
      LearningWithErrors.searchExperiment problem
          (sideLweSearchReductionFor keySwitchErrorSampler inputErrorSampler
            keySwitchGadget solver) =
        (challenges >>= fun challengeValues ↦
          scalarSecrets >>= fun scalarSecret ↦
          errors >>= fun errorValues ↦
          ringSecrets >>= fun ringSecret ↦
          finish scalarSecret ringSecret challengeValues errorValues) := by
    simp [LearningWithErrors.searchExperiment, problem, sideLweProblem,
      sideLweSearchReductionFor, sideLweSearchReduction, sideTranscriptAt,
      assembleSideLweView, flatten, scalarSecrets, ringSecrets, challenges, errors,
      finish, monad_norm]
  rw [endpoint_eq, show sideLweProblem
      (q := q) (ringRank := ringRank) (degree := degree)
      (lweDimension := lweDimension) (keySwitchLevels := keySwitchLevels)
      (queryCount := queryCount) (rounds := rounds)
      keySwitchErrorSampler inputErrorSampler = problem from rfl, search_eq]
  exact KeySwitchSecurity.evalDist_bind_four_reorder
    scalarSecrets ringSecrets challenges errors finish

/-- The formerly abstract uniform-BRK side-search term is the exact success probability of the
structured scalar search-LWE reduction. -/
theorem uniformBootstrapSideSearch_successProbability_eq_structuredSearchLwe
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (solver : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) :
    LWE.AuxiliaryInput.Search.successProbability
        (uniformBootstrapSideSearchProblem keySwitchErrorSampler inputErrorSampler
          keySwitchGadget rounds)
        (toUniformBootstrapSideSolver solver) =
      Pr[= true | LearningWithErrors.searchExperiment
        (sideLweProblem (q := q) (ringRank := ringRank) (degree := degree)
          (lweDimension := lweDimension) (keySwitchLevels := keySwitchLevels)
          (queryCount := queryCount) (rounds := rounds)
          keySwitchErrorSampler inputErrorSampler)
        (sideLweSearchReductionFor keySwitchErrorSampler inputErrorSampler
          keySwitchGadget solver)] := by
  rw [LWE.AuxiliaryInput.Search.successProbability,
    uniformBootstrapSideSearchGame_eq_recoveryGame]
  exact evalDist_ext_iff.mp
    (uniformBootstrapRecoveryGame_evalDist_eq_sideLweSearchExperiment
      keySwitchErrorSampler inputErrorSampler keySwitchGadget rounds solver) true

/-- **Finite BRK/search-LWE separation.** Real augmented scalar-key recovery is bounded by a
BRK-only circular replacement term plus a conventional structured scalar search-LWE success
probability containing every KSK and input-tape row. -/
theorem successProbability_le_bootstrapBatchCircular_add_structuredSearchLwe
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (solver : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) :
    successProbability ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget rounds solver ≤
      ENNReal.ofReal
          (bootstrapBatchCircularAdvantage ringErrorSampler keySwitchErrorSampler
            inputErrorSampler tgswGadget keySwitchGadget rounds solver) +
        Pr[= true | LearningWithErrors.searchExperiment
          (sideLweProblem (q := q) (ringRank := ringRank) (degree := degree)
            (lweDimension := lweDimension) (keySwitchLevels := keySwitchLevels)
            (queryCount := queryCount) (rounds := rounds)
            keySwitchErrorSampler inputErrorSampler)
          (sideLweSearchReductionFor keySwitchErrorSampler inputErrorSampler
            keySwitchGadget solver)] := by
  simpa only [
    uniformBootstrapSideSearch_successProbability_eq_structuredSearchLwe] using
    (successProbability_le_bootstrapBatchCircular_add_sideSearch
      ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget
      keySwitchGadget rounds solver)

end FormalProof4FHE.TFHE.Encryption.Adaptive.KeySwitchFirstFiniteView
