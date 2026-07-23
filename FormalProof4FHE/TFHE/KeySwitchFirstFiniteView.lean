/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.KeySwitchFirstFreshView

/-!
# Finite-View KSK-First TFHE Search Reduction

This module compiles the fresh-view oracle used by KSK-first majority amplification into one
explicit finite challenge.  At a common amplification depth `rounds`, the challenge contains

`lweDimension * 3 ^ rounds + 1`

independently sampled native BRK+KSK views under the same hidden scalar/ring key pair.  There are
`3 ^ rounds` majority leaves for every scalar coordinate and one additional KSK for checked
ring-key completion.

The finite challenge is strictly more concrete than an unrestricted sampling handle: its type
fixes the complete view budget before the solver runs.  This module proves distributional
equivalence for the concrete reduction and transfers finite-batch paired-search hardness to the
native KSK-first public decision game.  It does not derive that finite-batch search premise from
ordinary LWE/RLWE.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.KeySwitchFirstFiniteView

open KeySwitchFirstCandidateView
open KeySwitchFirstFreshView

/-! ## Generic finite majority batches -/

/-- An explicit family of ternary majority trees, together with one final input used after
coordinate recovery. -/
structure Batch (Input : Type) (count rounds : ℕ) where
  scalar : Fin count → FormalProof4FHE.MajorityAmplification.MajorityBatch Input rounds
  completion : Input

/-- Independently fill every majority leaf and the final completion position. -/
def sampleBatch {Input : Type} (count rounds : ℕ) (sampler : ProbComp Input) :
    ProbComp (Batch Input count rounds) := do
  let scalar ← Fin.mOfFn count fun _ =>
    FormalProof4FHE.MajorityAmplification.sampleMajorityBatch rounds sampler
  let completion ← sampler
  return ⟨scalar, completion⟩

/-- Run one coordinate-dependent trial over each stored majority tree. -/
def runScalarBatch {Input : Type} {count rounds : ℕ}
    (trial : Fin count → Input → ProbComp Bool)
    (scalar : Fin count →
      FormalProof4FHE.MajorityAmplification.MajorityBatch Input rounds) :
    ProbComp (Fin count → Bool) :=
  Fin.mOfFn count fun coordinate =>
    FormalProof4FHE.MajorityAmplification.runMajorityBatch rounds
      (trial coordinate) (scalar coordinate)

/-- Syntactic number of independently sampled inputs used by `sampleBatch`. -/
def viewCount (count rounds : ℕ) : ℕ :=
  count * FormalProof4FHE.MajorityAmplification.majorityBatchViewCount rounds + 1

/-- The explicit paired batch contains exactly `count * 3 ^ rounds + 1` inputs. -/
theorem viewCount_eq (count rounds : ℕ) :
    viewCount count rounds = count * 3 ^ rounds + 1 := by
  simp only [viewCount,
    FormalProof4FHE.MajorityAmplification.majorityBatchViewCount_eq_pow]

/-- Front-loading all scalar-coordinate majority inputs preserves the complete candidate-vector
distribution. -/
theorem evalDist_sampleScalarBatch_run {Input : Type} [Finite Input]
    (count rounds : ℕ) (sampler : ProbComp Input)
    (trial : Fin count → Input → ProbComp Bool) :
    evalDist (do
      let scalar ← Fin.mOfFn count fun _ =>
        FormalProof4FHE.MajorityAmplification.sampleMajorityBatch rounds sampler
      runScalarBatch trial scalar) =
      evalDist
        (FormalProof4FHE.MajorityAmplification.amplifyVector
          (fun _ : Fin count => rounds)
          (fun coordinate (_ : Unit) => sampler >>= trial coordinate) ()) := by
  let treeSampler :=
    FormalProof4FHE.MajorityAmplification.sampleMajorityBatch rounds sampler
  let treeTrial := fun coordinate : Fin count =>
    FormalProof4FHE.MajorityAmplification.runMajorityBatch rounds (trial coordinate)
  have hfront :=
    FormalProof4FHE.FiniteProduct.evalDist_presample_fin_mOfFn
      count (fun _ => treeSampler) (fun coordinate => treeTrial coordinate)
  have htrees :
      evalDist (Fin.mOfFn count fun coordinate =>
        treeSampler >>= treeTrial coordinate) =
      evalDist (Fin.mOfFn count fun coordinate =>
        FormalProof4FHE.MajorityAmplification.amplify rounds
          (fun _ : Unit => sampler >>= trial coordinate) ()) :=
    FormalProof4FHE.FiniteProduct.evalDist_fin_mOfFn_congr count
      (fun coordinate => treeSampler >>= treeTrial coordinate)
      (fun coordinate =>
        FormalProof4FHE.MajorityAmplification.amplify rounds
          (fun _ : Unit => sampler >>= trial coordinate) ())
      (fun coordinate =>
        FormalProof4FHE.MajorityAmplification.evalDist_sampleMajorityBatch_run
          rounds sampler (trial coordinate))
  calc
    evalDist (do
        let scalar ← Fin.mOfFn count fun _ =>
          FormalProof4FHE.MajorityAmplification.sampleMajorityBatch rounds sampler
        runScalarBatch trial scalar) =
      evalDist (Fin.mOfFn count fun coordinate =>
        treeSampler >>= treeTrial coordinate) := by
          simpa only [runScalarBatch, treeSampler, treeTrial] using hfront
    _ = evalDist (Fin.mOfFn count fun coordinate =>
        FormalProof4FHE.MajorityAmplification.amplify rounds
          (fun _ : Unit => sampler >>= trial coordinate) ()) := htrees
    _ = evalDist
        (FormalProof4FHE.MajorityAmplification.amplifyVector
          (fun _ : Fin count => rounds)
          (fun coordinate (_ : Unit) => sampler >>= trial coordinate) ()) := rfl

/-! ## Native centered-binomial finite-view game -/

/-- Native public-view input stored at each finite challenge position. -/
abbrev View
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) :=
  PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels

/-- Explicit finite native challenge for one common amplification depth. -/
abbrev NativeBatch
    (q degree ringRank tgswLevels lweDimension keySwitchLevels rounds : ℕ) :=
  Batch
    (View q degree ringRank tgswLevels lweDimension keySwitchLevels)
    lweDimension rounds

/-- A paired-key solver receiving a fixed finite batch rather than an unrestricted view handle. -/
abbrev Solver
    (q degree ringRank tgswLevels lweDimension keySwitchLevels rounds : ℕ) :=
  NativeBatch q degree ringRank tgswLevels lweDimension keySwitchLevels rounds →
    ProbComp (AuxiliaryInput.Secret lweDimension ringRank degree)

/-- Exact paired-key recovery experiment for a finite native view batch. -/
noncomputable def game
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (solver : Solver q degree ringRank tgswLevels lweDimension keySwitchLevels rounds) :
    ProbComp Bool := do
  let secrets ←
    (Search.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleSecret
  let batch ← sampleBatch lweDimension rounds
    (fixedSecretView ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget secrets)
  let recovered ← solver batch
  return decide (recovered = secrets)

/-- The concrete finite-batch reduction: majority-recover the scalar key, then use the extra
real KSK to complete and check the ring key. -/
noncomputable def amplifiedSolver
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (level : Fin keySwitchLevels)
    (rounds : ℕ)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    Solver q degree ringRank tgswLevels lweDimension keySwitchLevels rounds :=
  fun batch => do
    let candidate ← runScalarBatch
      (fun coordinate context =>
        candidateGuess
          (fun _ => KeySwitchFirstCandidateView.orientation ringErrorSampler
            keySwitchErrorSampler tgswGadget keySwitchGadget distinguisher)
          (KeySwitchFirstCandidateView.toCandidateCheck distinguisher)
          coordinate context)
      batch.scalar
    return Native.KeySwitchRecovery.completeCandidate
      keySwitchGadget level batch.completion.2 candidate

/-- For fixed native secrets, the front-loaded scalar batch has exactly the same output law as
the constant-depth fresh-view scalar solver. -/
theorem evalDist_fixedScalarBatch_eq_freshScalar
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : AuxiliaryInput.Secret lweDimension ringRank degree)
    (rounds : ℕ)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    evalDist (do
      let scalar ← Fin.mOfFn lweDimension fun _ =>
        FormalProof4FHE.MajorityAmplification.sampleMajorityBatch rounds
          (fixedSecretView ringErrorSampler keySwitchErrorSampler
            tgswGadget keySwitchGadget secrets)
      runScalarBatch
        (fun coordinate context =>
          candidateGuess
            (fun _ => KeySwitchFirstCandidateView.orientation ringErrorSampler
              keySwitchErrorSampler tgswGadget keySwitchGadget distinguisher)
            (KeySwitchFirstCandidateView.toCandidateCheck distinguisher)
            coordinate context)
        scalar) =
      evalDist
        (KeySwitchFirstFreshView.amplifiedScalarSolver
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
          (fun _ => rounds) distinguisher
          (oracleOfSecrets ringErrorSampler keySwitchErrorSampler
            tgswGadget keySwitchGadget secrets)) := by
  let viewSampler := fixedSecretView ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget secrets
  let trial := fun coordinate context =>
    candidateGuess
      (fun _ => KeySwitchFirstCandidateView.orientation ringErrorSampler
        keySwitchErrorSampler tgswGadget keySwitchGadget distinguisher)
      (KeySwitchFirstCandidateView.toCandidateCheck distinguisher)
      coordinate context
  let oracle := oracleOfSecrets ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget secrets
  have hcoordinate (coordinate : Fin lweDimension) :
      FormalProof4FHE.MajorityAmplification.amplify rounds
          (fun _ : Unit => viewSampler >>= trial coordinate) () =
        FormalProof4FHE.MajorityAmplification.amplify rounds
          (KeySwitchFirstFreshView.coordinateGuess ringErrorSampler
            keySwitchErrorSampler tgswGadget keySwitchGadget distinguisher coordinate)
          oracle := by
    apply FormalProof4FHE.MajorityAmplification.amplify_eq_of_base_eq
    simp only [trial, viewSampler, oracle,
      KeySwitchFirstFreshView.coordinateGuess,
      KeySwitchFirstFreshView.query_oracleOfSecrets]
  have hvector :
      FormalProof4FHE.MajorityAmplification.amplifyVector
          (fun _ : Fin lweDimension => rounds)
          (fun coordinate (_ : Unit) => viewSampler >>= trial coordinate) () =
        KeySwitchFirstFreshView.amplifiedScalarSolver
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
          (fun _ => rounds) distinguisher oracle := by
    unfold FormalProof4FHE.MajorityAmplification.amplifyVector
      KeySwitchFirstFreshView.amplifiedScalarSolver
    exact congrArg (fun samplers => Fin.mOfFn lweDimension samplers)
      (funext hcoordinate)
  have hbatch := evalDist_sampleScalarBatch_run lweDimension rounds
    viewSampler trial
  rw [hvector] at hbatch
  simpa only [viewSampler, trial, oracle] using hbatch

/-- The canonical finite-batch solver and the corresponding fresh-view solver have exactly the
same paired-recovery distribution. -/
theorem evalDist_game_amplifiedSolver_eq_freshGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (level : Fin keySwitchLevels)
    (rounds : ℕ)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    evalDist
        (game ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
          rounds
          (amplifiedSolver ringErrorSampler keySwitchErrorSampler
            tgswGadget keySwitchGadget level rounds distinguisher)) =
      evalDist
        (KeySwitchFirstFreshView.game ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget
          (KeySwitchFirstFreshView.completeScalarSolver keySwitchGadget level
            (KeySwitchFirstFreshView.amplifiedScalarSolver
              ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
              (fun _ => rounds) distinguisher))) := by
  classical
  unfold game KeySwitchFirstFreshView.game amplifiedSolver
    KeySwitchFirstFreshView.completeScalarSolver
  simp only [bind_assoc, pure_bind]
  apply evalDist_bind_congr'
  intro secrets
  let viewSampler := fixedSecretView ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget secrets
  let scalarSampler : ProbComp
      (Fin lweDimension →
        FormalProof4FHE.MajorityAmplification.MajorityBatch
          (View q degree ringRank tgswLevels lweDimension keySwitchLevels) rounds) :=
    Fin.mOfFn lweDimension fun _ =>
      FormalProof4FHE.MajorityAmplification.sampleMajorityBatch rounds viewSampler
  let scalarSolver :
      (Fin lweDimension →
        FormalProof4FHE.MajorityAmplification.MajorityBatch
          (View q degree ringRank tgswLevels lweDimension keySwitchLevels) rounds) →
        ProbComp (BinarySecret lweDimension) :=
    fun scalar => runScalarBatch
      (fun coordinate context =>
        candidateGuess
          (fun _ => KeySwitchFirstCandidateView.orientation ringErrorSampler
            keySwitchErrorSampler tgswGadget keySwitchGadget distinguisher)
          (KeySwitchFirstCandidateView.toCandidateCheck distinguisher)
          coordinate context)
      scalar
  let finish : BinarySecret lweDimension →
      View q degree ringRank tgswLevels lweDimension keySwitchLevels → ProbComp Bool :=
    fun candidate context =>
      pure (decide
        (Native.KeySwitchRecovery.completeCandidate
          keySwitchGadget level context.2 candidate = secrets))
  have hcomm :
      evalDist (do
        let scalar ← scalarSampler
        let context ← viewSampler
        let candidate ← scalarSolver scalar
        finish candidate context) =
      evalDist (do
        let scalar ← scalarSampler
        let candidate ← scalarSolver scalar
        let context ← viewSampler
        finish candidate context) := by
    apply evalDist_bind_congr'
    intro scalar
    exact OracleComp.DeferredSampling.evalDist_bind_comm
      viewSampler (scalarSolver scalar) (fun context candidate => finish candidate context)
  have hscalar :
      evalDist (scalarSampler >>= scalarSolver) =
      evalDist
        (KeySwitchFirstFreshView.amplifiedScalarSolver
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
          (fun _ => rounds) distinguisher
          (oracleOfSecrets ringErrorSampler keySwitchErrorSampler
            tgswGadget keySwitchGadget secrets)) := by
    simpa only [scalarSampler, scalarSolver, viewSampler] using
      (evalDist_fixedScalarBatch_eq_freshScalar ringErrorSampler
        keySwitchErrorSampler tgswGadget keySwitchGadget secrets rounds distinguisher)
  let freshScalar :=
    KeySwitchFirstFreshView.amplifiedScalarSolver
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
      (fun _ => rounds) distinguisher
      (oracleOfSecrets ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget secrets)
  have hpost :
      evalDist ((scalarSampler >>= scalarSolver) >>= fun candidate =>
        viewSampler >>= fun context => finish candidate context) =
      evalDist (freshScalar >>= fun candidate =>
        viewSampler >>= fun context => finish candidate context) := by
    dsimp only [freshScalar]
    rw [evalDist_bind, hscalar]
    conv_rhs => rw [evalDist_bind]
  calc
    evalDist (do
        let batch ← sampleBatch lweDimension rounds viewSampler
        let candidate ← scalarSolver batch.scalar
        finish candidate batch.completion) =
      evalDist (do
        let scalar ← scalarSampler
        let context ← viewSampler
        let candidate ← scalarSolver scalar
        finish candidate context) := by
          simp only [sampleBatch, scalarSampler, bind_assoc, pure_bind]
    _ = evalDist (do
        let scalar ← scalarSampler
        let candidate ← scalarSolver scalar
        let context ← viewSampler
        finish candidate context) := hcomm
    _ = evalDist (do
        let candidate ← freshScalar
        let context ← viewSampler
        finish candidate context) := by
          simpa only [bind_assoc] using hpost
    _ = evalDist (do
        let candidate ← freshScalar
        let context ←
          (oracleOfSecrets ringErrorSampler keySwitchErrorSampler
            tgswGadget keySwitchGadget secrets).query
        finish candidate context) := by
          rw [KeySwitchFirstFreshView.query_oracleOfSecrets]

/-- Exact success probability of a finite-batch paired-key solver. -/
noncomputable def successProbability
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (solver : Solver q degree ringRank tgswLevels lweDimension keySwitchLevels rounds) :
    ENNReal :=
  Pr[= true |
    game ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
      rounds solver]

/-- The finite-batch paired recovery bound, using exactly
`lweDimension * 3 ^ rounds + 1` native views. -/
theorem one_sub_amplifiedErrorBound_le_successProbability_centeredBinomial
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (level : Fin keySwitchLevels)
    (hmargin : 2 * keySwitchEta <
      BootstrappingCorrectness.centeredDistance 0 (keySwitchGadget level))
    (reference : Fin lweDimension)
    (rounds : ℕ)
    (threshold : ENNReal) (hthreshold_pos : 0 < threshold)
    (hthreshold_one : threshold ≤ 1)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    1 - KeySwitchFirstFreshView.amplifiedErrorBound
        (ringEta := ringEta) (keySwitchEta := keySwitchEta)
        tgswGadget keySwitchGadget (fun _ => rounds) threshold distinguisher ≤
      successProbability
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget rounds
        (amplifiedSolver
          (RLWE.CenteredBinomial.sampler q degree ringEta)
          (CenteredBinomial.scalarSampler q keySwitchEta)
          tgswGadget keySwitchGadget level rounds distinguisher) := by
  rw [show successProbability
      (RLWE.CenteredBinomial.sampler q degree ringEta)
      (CenteredBinomial.scalarSampler q keySwitchEta)
      tgswGadget keySwitchGadget rounds
      (amplifiedSolver
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget level rounds distinguisher) =
      KeySwitchFirstFreshView.successProbability
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget
        (KeySwitchFirstFreshView.amplifiedSolver
          (ringEta := ringEta) (keySwitchEta := keySwitchEta)
          tgswGadget keySwitchGadget level (fun _ => rounds) distinguisher) by
    unfold successProbability KeySwitchFirstFreshView.successProbability
    exact probOutput_congr rfl
      (evalDist_game_amplifiedSolver_eq_freshGame
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget level rounds distinguisher)]
  exact KeySwitchFirstFreshView.one_sub_amplifiedErrorBound_le_successProbability
    (ringEta := ringEta) (keySwitchEta := keySwitchEta)
    tgswGadget keySwitchGadget level hmargin reference (fun _ => rounds)
    threshold hthreshold_pos hthreshold_one distinguisher

/-- KSK-first public advantage is bounded by finite-batch paired-search success plus the same
explicit amplification loss. -/
theorem keySwitchDecisionAdvantage_le_successProbability_add_amplifiedLoss
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (level : Fin keySwitchLevels)
    (hmargin : 2 * keySwitchEta <
      BootstrappingCorrectness.centeredDistance 0 (keySwitchGadget level))
    (reference : Fin lweDimension)
    (rounds : ℕ)
    (threshold : ENNReal) (hthreshold_pos : 0 < threshold)
    (hthreshold_one : threshold ≤ 1)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    KeySwitchFirstCandidateView.keySwitchDecisionAdvantage
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget distinguisher ≤
      (successProbability
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget rounds
        (amplifiedSolver
          (RLWE.CenteredBinomial.sampler q degree ringEta)
          (CenteredBinomial.scalarSampler q keySwitchEta)
          tgswGadget keySwitchGadget level rounds distinguisher)).toReal +
      KeySwitchFirstFreshView.amplifiedLoss
        (ringEta := ringEta) (keySwitchEta := keySwitchEta)
        tgswGadget keySwitchGadget (fun _ => rounds) threshold distinguisher := by
  let finiteSolver := amplifiedSolver
    (RLWE.CenteredBinomial.sampler q degree ringEta)
    (CenteredBinomial.scalarSampler q keySwitchEta)
    tgswGadget keySwitchGadget level rounds distinguisher
  let freshSolver := KeySwitchFirstFreshView.amplifiedSolver
    (ringEta := ringEta) (keySwitchEta := keySwitchEta)
    tgswGadget keySwitchGadget level (fun _ => rounds) distinguisher
  have hsuccess :
      KeySwitchFirstFreshView.successProbability
          (RLWE.CenteredBinomial.sampler q degree ringEta)
          (CenteredBinomial.scalarSampler q keySwitchEta)
          tgswGadget keySwitchGadget freshSolver =
        successProbability
          (RLWE.CenteredBinomial.sampler q degree ringEta)
          (CenteredBinomial.scalarSampler q keySwitchEta)
          tgswGadget keySwitchGadget rounds finiteSolver := by
    unfold KeySwitchFirstFreshView.successProbability successProbability
    exact probOutput_congr rfl
      (evalDist_game_amplifiedSolver_eq_freshGame
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget level rounds distinguisher).symm
  simpa only [finiteSolver, freshSolver, hsuccess] using
    (KeySwitchFirstFreshView.keySwitchDecisionAdvantage_le_successProbability_add_amplifiedLoss
      (ringEta := ringEta) (keySwitchEta := keySwitchEta)
      tgswGadget keySwitchGadget level hmargin reference (fun _ => rounds)
      threshold hthreshold_pos hthreshold_one distinguisher)

/-- Finite-batch paired search hardness on the real centered-binomial native distribution. -/
def RealSearchHardAgainst
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (allowed : Solver q degree ringRank tgswLevels lweDimension keySwitchLevels rounds → Prop)
    (bound : ℝ) : Prop :=
  ∀ batchSolver, allowed batchSolver →
    (successProbability
      (RLWE.CenteredBinomial.sampler q degree ringEta)
      (CenteredBinomial.scalarSampler q keySwitchEta)
      tgswGadget keySwitchGadget rounds batchSolver).toReal ≤ bound

/-- Finite-batch paired-search hardness transfers to native KSK-first public-decision hardness.
The search challenge supplied to the premise contains exactly
`lweDimension * 3 ^ rounds + 1` real native views. -/
theorem nativePublicHardAgainst_of_finiteSearchHardness
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (level : Fin keySwitchLevels)
    (hmargin : 2 * keySwitchEta <
      BootstrappingCorrectness.centeredDistance 0 (keySwitchGadget level))
    (reference : Fin lweDimension)
    (rounds : ℕ)
    (threshold : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels → ENNReal)
    (hthreshold_pos : ∀ distinguisher, 0 < threshold distinguisher)
    (hthreshold_one : ∀ distinguisher, threshold distinguisher ≤ 1)
    (decisionAllowed : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels → Prop)
    (solverAllowed : Solver q degree ringRank tgswLevels
      lweDimension keySwitchLevels rounds → Prop)
    (searchBound lossBound : ℝ)
    (hSearch : RealSearchHardAgainst (ringEta := ringEta)
      (keySwitchEta := keySwitchEta) tgswGadget keySwitchGadget
      rounds solverAllowed searchBound)
    (hClosed : ∀ distinguisher, decisionAllowed distinguisher →
      solverAllowed
        (amplifiedSolver
          (RLWE.CenteredBinomial.sampler q degree ringEta)
          (CenteredBinomial.scalarSampler q keySwitchEta)
          tgswGadget keySwitchGadget level rounds distinguisher))
    (hLoss : ∀ distinguisher, decisionAllowed distinguisher →
      KeySwitchFirstFreshView.amplifiedLoss
        (ringEta := ringEta) (keySwitchEta := keySwitchEta)
        tgswGadget keySwitchGadget (fun _ => rounds)
        (threshold distinguisher) distinguisher ≤ lossBound) :
    KeySwitchFirstSearchToDecision.NativePublicHardAgainst
      (keySwitchEta := keySwitchEta)
      (RLWE.CenteredBinomial.sampler q degree ringEta)
      tgswGadget keySwitchGadget decisionAllowed
      (searchBound + lossBound) := by
  intro distinguisher hallowed
  exact (keySwitchDecisionAdvantage_le_successProbability_add_amplifiedLoss
    tgswGadget keySwitchGadget level hmargin reference rounds
    (threshold distinguisher) (hthreshold_pos distinguisher)
    (hthreshold_one distinguisher) distinguisher).trans
      (add_le_add
        (hSearch _ (hClosed distinguisher hallowed))
        (hLoss distinguisher hallowed))

end FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.KeySwitchFirstFiniteView
