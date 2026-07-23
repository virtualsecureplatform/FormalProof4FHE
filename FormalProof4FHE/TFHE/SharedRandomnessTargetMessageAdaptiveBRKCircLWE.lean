/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SharedRandomnessTargetMessageAdaptiveReduction

set_option autoImplicit false

/-!
# Public BRK CircRLWE Boundary for Adaptive Full-Target-Message TFHE

This file packages the genuine circular bootstrapping-key hop used by adaptive TFHE as a public
auxiliary-input problem.  At positive ring degree the joint public view is

`(BRK(KeyExtract(S_source || S_suffix), S_source),
  Ext(S_suffix, S_source), LWE_KeyExtract(S_source || S_suffix)(0))`.

The challenge is the complete source-key BRK.  Its real branch encrypts every coefficient of the
literal target key `S_source || S_suffix`, its zero branch is a format-identical zero-message BRK,
and its uniform branch is a uniform BRK of the same carrier.  The correlated extension table and
the query-counted target-key tape are retained as auxiliary input in all three branches.  The
compiled distinguisher is public: it receives that view but neither nested secret.

The zero-versus-uniform auxiliary branch is reduced exactly to two advantages for the ordinary
blocked module-RLWE problem that jointly supplies the BRK, extension, and input-tape rows.  Hence
the resulting end-to-end adaptive TFHE theorem has one nonstandard term only: real-versus-uniform
native degree-two BRK CircRLWE.  Its complete real game is also proved exactly equal to the
explicit degree-two monomial presentation, while retaining the extension table and adaptive tape.
This file does not claim that ordinary RLWE proves that remaining circular term.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.AdaptiveBRKCircLWE

noncomputable section

open FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision

/-- The literal nested target key, at positive ring degree `degree + 1`. -/
abbrev Secret (sourceRank suffixRank degree : ℕ) :=
  NestedSecret sourceRank suffixRank (degree + 1)

/-- The complete target-message source BRK is the circular challenge. -/
abbrev Challenge
    (q degree sourceRank suffixRank tgswLevels : ℕ) :=
  SourceBootstrappingKey q (degree + 1) sourceRank suffixRank tgswLevels

/-- The public correlated material retained while the BRK is challenged. -/
abbrev Auxiliary
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) :=
  RingExtensionKey q (degree + 1) sourceRank suffixRank tgswLevels ×
    TLWE.BatchCiphertext (ZMod q)
      (targetScalarDimension sourceRank suffixRank (degree + 1)) queryCount

/-- Public auxiliary-input BRK CircRLWE problem for adaptive full-target-message TFHE.

One common ring-error sampler is used so that the zero/reference branch can be flattened into the
existing blocked module-RLWE problem.  Scalar input errors are its constant-coefficient image. -/
def problem
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1)) :
    FormalProof4FHE.LWE.AuxiliaryInput.Problem
      (Secret sourceRank suffixRank degree)
      (Challenge q degree sourceRank suffixRank tgswLevels)
      (Auxiliary q degree sourceRank suffixRank tgswLevels queryCount) where
  sampleSecret := sampleNestedSecret sourceRank suffixRank (degree + 1)
  sampleReal := fun secret ↦
    generateSourceBootstrappingKey q (degree + 1) sourceRank suffixRank tgswLevels
      errorSampler gadget secret.1 secret.2
  sampleZero := fun secret ↦
    generateZeroSourceBootstrappingKey q (degree + 1) sourceRank suffixRank tgswLevels
      errorSampler gadget secret.1
  sampleUniform :=
    $ᵗ (Challenge q degree sourceRank suffixRank tgswLevels)
  sampleAuxiliary := fun secret ↦ do
    let extensionKey ← generateRingExtensionKey q (degree + 1) sourceRank suffixRank
      tgswLevels errorSampler gadget secret.1 secret.2
    let tape ← TLWE.batchEncrypt
      (targetScalarDimension sourceRank suffixRank (degree + 1)) queryCount
      (AdaptiveReduction.extractedErrorSampler errorSampler)
      (embedBinarySecret (targetMessages secret.1 secret.2)) 0
    return (extensionKey, tape)

/-- Compile the adaptive TFHE experiment into a public BRK distinguisher. -/
def adaptiveDistinguisher
    {Message : Type}
    {q degree sourceRank suffixRank tgswLevels queryCount : ℕ} [NeZero q]
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels) :
    PublicDistinguisher
      (Challenge q degree sourceRank suffixRank tgswLevels)
      (Auxiliary q degree sourceRank suffixRank tgswLevels queryCount) :=
  fun bootstrappingKey auxiliary ↦
    AdaptiveReduction.adaptiveViewContinuation decompose encode adversary
      ((bootstrappingKey, auxiliary.1), auxiliary.2)

/-- Real-target-message versus zero-message BRK advantage with the complete public context. -/
def kdmAdvantage
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels) : ℝ :=
  FormalProof4FHE.LWE.AuxiliaryInput.kdmAdvantage
    (problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler gadget)
    (publicContinuation (adaptiveDistinguisher decompose encode adversary))

/-- The sole native circular term: real target-message BRK versus a uniform BRK, retaining the
real extension table and target-key tape. -/
def circularLweAdvantage
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels) : ℝ :=
  publicAdvantage
    (problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler gadget)
    (adaptiveDistinguisher decompose encode adversary)

/-! ## Exact degree-two monomial presentation -/

/-- The same complete public CircRLWE problem, with the real source BRK written through the
explicit degree-two monomial sampler.  Every other field—including the nested-secret law,
uniform endpoint, correlated extension table, and target-key query tape—is unchanged. -/
def monomialProblem
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1)) :
    FormalProof4FHE.LWE.AuxiliaryInput.Problem
      (Secret sourceRank suffixRank degree)
      (Challenge q degree sourceRank suffixRank tgswLevels)
      (Auxiliary q degree sourceRank suffixRank tgswLevels queryCount) :=
  { problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler gadget with
    sampleReal := fun secret ↦
      PrefixCircLWE.generateMonomialSourceBootstrappingKey q (degree + 1) sourceRank
        suffixRank tgswLevels errorSampler gadget secret.1 secret.2 }

/-- At each fixed nested key, the honest BRK branch and explicit monomial branch have identical
distributions. -/
theorem problem_sampleReal_evalDist_eq_monomialProblem
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (secret : Secret sourceRank suffixRank degree) :
    evalDist
        ((problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler
          gadget).sampleReal secret) =
      evalDist
        ((monomialProblem q degree sourceRank suffixRank tgswLevels queryCount
          errorSampler gadget).sampleReal secret) := by
  simpa [problem, monomialProblem] using
    (PrefixCircLWE.generateSourceBootstrappingKey_evalDist_eq_monomial
      q (degree + 1) sourceRank suffixRank tgswLevels errorSampler gadget
      secret.1 secret.2)

/-- Replacing the honest BRK sampler by its exact monomial presentation preserves the complete
real game for every continuation, including all correlated auxiliary input sampled afterward. -/
theorem realGame_evalDist_eq_monomialRealGame
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (continuation : FormalProof4FHE.LWE.AuxiliaryInput.Continuation
      (Secret sourceRank suffixRank degree)
      (Challenge q degree sourceRank suffixRank tgswLevels)
      (Auxiliary q degree sourceRank suffixRank tgswLevels queryCount)) :
    evalDist
        (FormalProof4FHE.LWE.AuxiliaryInput.realGame
          (problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler gadget)
          continuation) =
      evalDist
        (FormalProof4FHE.LWE.AuxiliaryInput.realGame
          (monomialProblem q degree sourceRank suffixRank tgswLevels queryCount
            errorSampler gadget)
          continuation) := by
  unfold FormalProof4FHE.LWE.AuxiliaryInput.realGame
  refine evalDist_bind_congr' _ fun secret ↦ ?_
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (problem_sampleReal_evalDist_eq_monomialProblem q degree sourceRank suffixRank
      tgswLevels queryCount errorSampler gadget secret)
    (fun challenge ↦
      (problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler
        gadget).sampleAuxiliary secret >>= fun auxiliary ↦
      continuation secret challenge auxiliary)

/-- The uniform branch is definitionally unchanged by the monomial presentation. -/
theorem uniformGame_evalDist_eq_monomialUniformGame
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (continuation : FormalProof4FHE.LWE.AuxiliaryInput.Continuation
      (Secret sourceRank suffixRank degree)
      (Challenge q degree sourceRank suffixRank tgswLevels)
      (Auxiliary q degree sourceRank suffixRank tgswLevels queryCount)) :
    evalDist
        (FormalProof4FHE.LWE.AuxiliaryInput.uniformGame
          (problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler gadget)
          continuation) =
      evalDist
        (FormalProof4FHE.LWE.AuxiliaryInput.uniformGame
          (monomialProblem q degree sourceRank suffixRank tgswLevels queryCount
            errorSampler gadget)
          continuation) := by
  rfl

/-- The remaining native term in the full adaptive TFHE theorem, presented explicitly as a
degree-two monomial CircRLWE advantage. -/
def monomialCircularLweAdvantage
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels) : ℝ :=
  publicAdvantage
    (monomialProblem q degree sourceRank suffixRank tgswLevels queryCount
      errorSampler gadget)
    (adaptiveDistinguisher decompose encode adversary)

/-- The complete honest-BRK CircRLWE advantage and its explicit monomial presentation are
exactly equal for every adaptive public distinguisher. -/
theorem circularLweAdvantage_eq_monomialCircularLweAdvantage
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels) :
    circularLweAdvantage q degree sourceRank suffixRank tgswLevels queryCount
        errorSampler gadget decompose encode adversary =
      monomialCircularLweAdvantage q degree sourceRank suffixRank tgswLevels queryCount
        errorSampler gadget decompose encode adversary := by
  unfold circularLweAdvantage monomialCircularLweAdvantage publicAdvantage
    FormalProof4FHE.LWE.AuxiliaryInput.circularLweAdvantage
    ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (realGame_evalDist_eq_monomialRealGame q degree sourceRank suffixRank tgswLevels
        queryCount errorSampler gadget
        (publicContinuation (adaptiveDistinguisher decompose encode adversary))) true,
    evalDist_ext_iff.mp
      (uniformGame_evalDist_eq_monomialUniformGame q degree sourceRank suffixRank
        tgswLevels queryCount errorSampler gadget
        (publicContinuation (adaptiveDistinguisher decompose encode adversary))) true]

/-- The public BRK challenge is the earlier PKC-style source-prefix CircRLWE challenge with the
adaptive target-key tape sampled inside its secret-aware experiment continuation.  This identifies
the underlying challenge problem exactly; a search-to-decision reduction must still transport the
tape rather than treating it as absent. -/
theorem circularLweAdvantage_eq_prefixCircularLweAdvantage
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels) :
    circularLweAdvantage q degree sourceRank suffixRank tgswLevels queryCount
        errorSampler gadget decompose encode adversary =
      PrefixCircLWE.circularLweAdvantage errorSampler errorSampler gadget
        (compileSourceContinuation q (degree + 1) sourceRank suffixRank tgswLevels
          decompose
          (adaptiveContinuation queryCount
            (AdaptiveReduction.extractedErrorSampler errorSampler) encode adversary)) := by
  unfold circularLweAdvantage publicAdvantage PrefixCircLWE.circularLweAdvantage
    FormalProof4FHE.LWE.AuxiliaryInput.circularLweAdvantage
    ProbComp.boolDistAdvantage
  simp [FormalProof4FHE.LWE.AuxiliaryInput.realGame,
    FormalProof4FHE.LWE.AuxiliaryInput.uniformGame, problem, PrefixCircLWE.problem,
    publicContinuation, adaptiveDistinguisher, PrefixCircLWE.packContinuation,
    compileSourceContinuation, adaptiveContinuation,
    AdaptiveReduction.adaptiveViewContinuation, sampleNestedSecret, bind_assoc,
    monad_norm]

/-- The explicit monomial presentation is consequently the same adaptive instance of the
PKC-style source-prefix CircRLWE game. -/
theorem monomialCircularLweAdvantage_eq_prefixCircularLweAdvantage
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels) :
    monomialCircularLweAdvantage q degree sourceRank suffixRank tgswLevels queryCount
        errorSampler gadget decompose encode adversary =
      PrefixCircLWE.circularLweAdvantage errorSampler errorSampler gadget
        (compileSourceContinuation q (degree + 1) sourceRank suffixRank tgswLevels
          decompose
          (adaptiveContinuation queryCount
            (AdaptiveReduction.extractedErrorSampler errorSampler) encode adversary)) := by
  rw [← circularLweAdvantage_eq_monomialCircularLweAdvantage q degree sourceRank
    suffixRank tgswLevels queryCount errorSampler gadget decompose encode adversary]
  exact circularLweAdvantage_eq_prefixCircularLweAdvantage q degree sourceRank suffixRank
    tgswLevels queryCount errorSampler gadget decompose encode adversary

/-! ### Exact complete-view search endpoint -/

/-- A public solver for the monomial normal form receives the BRK, real extension table, and
query-counted target-key tape, but neither nested secret. -/
abbrev MonomialSolver
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) :=
  FormalProof4FHE.LWE.AuxiliaryInput.Search.Solver
    (Secret sourceRank suffixRank degree)
    (Challenge q degree sourceRank suffixRank tgswLevels)
    (Auxiliary q degree sourceRank suffixRank tgswLevels queryCount)

/-- Exact nested-key recovery from the complete public monomial CircRLWE view. -/
def monomialSearchProblem
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1)) :=
  FormalProof4FHE.LWE.AuxiliaryInput.Search.exactRecoveryProblem
    (monomialProblem q degree sourceRank suffixRank tgswLevels queryCount
      errorSampler gadget)

/-- Complete-view nested-key recovery is bounded by monomial CircRLWE advantage plus recovery
when only the BRK is uniform.  The real extension table and target-key tape remain present in the
uniform recovery term, so that term is not silently treated as independent side information. -/
theorem monomialSearchSuccess_le_circularLwe_add_uniformRecovery
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (solver : MonomialSolver q degree sourceRank suffixRank tgswLevels queryCount) :
    FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
        (monomialSearchProblem q degree sourceRank suffixRank tgswLevels queryCount
          errorSampler gadget)
        solver ≤
      ENNReal.ofReal
          (FormalProof4FHE.LWE.AuxiliaryInput.circularLweAdvantage
            (monomialProblem q degree sourceRank suffixRank tgswLevels queryCount
              errorSampler gadget)
            (FormalProof4FHE.LWE.AuxiliaryInput.Search.recoveryContinuation solver)) +
        Pr[= true |
          FormalProof4FHE.LWE.AuxiliaryInput.Search.uniformRecoveryGame
            (monomialProblem q degree sourceRank suffixRank tgswLevels queryCount
              errorSampler gadget)
            solver] := by
  exact
    FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability_exactRecovery_le_circularLwe_add_uniform
      (monomialProblem q degree sourceRank suffixRank tgswLevels queryCount
        errorSampler gadget)
      solver

/-! ### Complete-view search-to-decision boundary -/

/-- A same-distribution search-to-decision certificate for the complete public monomial BRK
problem.  Its nontrivial field constructs a nested-key solver from a public distinguisher and
proves the quantitative advantage bound. -/
abbrev MonomialDecisionToSearchReduction
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1)) :=
  FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.Reduction
    (monomialProblem q degree sourceRank suffixRank tgswLevels queryCount
      errorSampler gadget)

/-- A widened-decision certificate may use a different complete-view monomial error law for the
decision oracle and the narrow exact-recovery experiment. -/
abbrev MonomialCrossDecisionToSearchReduction
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (decisionErrorSampler searchErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1)) :=
  FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.CrossReduction
    (monomialProblem q degree sourceRank suffixRank tgswLevels queryCount
      decisionErrorSampler gadget)
    (monomialSearchProblem q degree sourceRank suffixRank tgswLevels queryCount
      searchErrorSampler gadget)

/-- A checked same-distribution search-to-decision certificate bounds the concrete adaptive
monomial CircRLWE term by its generated complete-view nested-key solver and explicit loss. -/
theorem monomialCircularLweAdvantage_le_search_add_reductionLoss
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels)
    (reduction : MonomialDecisionToSearchReduction q degree sourceRank suffixRank
      tgswLevels queryCount errorSampler gadget) :
    monomialCircularLweAdvantage q degree sourceRank suffixRank tgswLevels queryCount
        errorSampler gadget decompose encode adversary ≤
      (FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
        (monomialSearchProblem q degree sourceRank suffixRank tgswLevels queryCount
          errorSampler gadget)
        (reduction.toSolver
          (adaptiveDistinguisher decompose encode adversary))).toReal +
        reduction.loss (adaptiveDistinguisher decompose encode adversary) := by
  simpa [monomialCircularLweAdvantage, monomialSearchProblem] using
    (reduction.advantage_le (adaptiveDistinguisher decompose encode adversary))

/-- The paper-aligned widened-decision form bounds the concrete adaptive monomial CircRLWE term
at the decision noise by nested-key recovery at the narrow search noise plus the certified
evaluation, smudging, guessing, and amplification loss. -/
theorem monomialCircularLweAdvantage_le_narrowSearch_add_reductionLoss
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (decisionErrorSampler searchErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels)
    (reduction : MonomialCrossDecisionToSearchReduction q degree sourceRank suffixRank
      tgswLevels queryCount decisionErrorSampler searchErrorSampler gadget) :
    monomialCircularLweAdvantage q degree sourceRank suffixRank tgswLevels queryCount
        decisionErrorSampler gadget decompose encode adversary ≤
      (FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
        (monomialSearchProblem q degree sourceRank suffixRank tgswLevels queryCount
          searchErrorSampler gadget)
        (reduction.toSolver
          (adaptiveDistinguisher decompose encode adversary))).toReal +
        reduction.loss (adaptiveDistinguisher decompose encode adversary) := by
  simpa [monomialCircularLweAdvantage] using
    (reduction.advantage_le (adaptiveDistinguisher decompose encode adversary))

/-- Zero-message BRK versus uniform BRK with the same real extension table and target-key tape. -/
def zeroLweAdvantage
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels) : ℝ :=
  FormalProof4FHE.LWE.AuxiliaryInput.zeroLweAdvantage
    (problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler gadget)
    (publicContinuation (adaptiveDistinguisher decompose encode adversary))

/-! ## Exact native-game alignment -/

/-- The public problem's real branch is exactly the honest adaptive TFHE game. -/
theorem realGame_evalDist_eq_realAdaptiveGame
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels) :
    evalDist
        (FormalProof4FHE.LWE.AuxiliaryInput.realGame
          (problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler gadget)
          (publicContinuation (adaptiveDistinguisher decompose encode adversary))) =
      evalDist
        (realAdaptiveGame q (degree + 1) sourceRank suffixRank tgswLevels queryCount
          errorSampler errorSampler (AdaptiveReduction.extractedErrorSampler errorSampler) gadget
          decompose encode adversary) := by
  simp [FormalProof4FHE.LWE.AuxiliaryInput.realGame, problem, publicContinuation,
    adaptiveDistinguisher, sampleNestedSecret, realAdaptiveGame, realContinuationGame,
    generateCloudKey, adaptiveContinuation, AdaptiveReduction.adaptiveViewContinuation, bind_assoc,
    monad_norm]

/-- The public problem's zero branch is exactly the all-zero-BRK adaptive endpoint. -/
theorem zeroGame_evalDist_eq_bootstrapZeroAdaptiveGame
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels) :
    evalDist
        (FormalProof4FHE.LWE.AuxiliaryInput.zeroGame
          (problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler gadget)
          (publicContinuation (adaptiveDistinguisher decompose encode adversary))) =
      evalDist
        (bootstrapZeroAdaptiveGame q (degree + 1) sourceRank suffixRank tgswLevels
          queryCount errorSampler errorSampler (AdaptiveReduction.extractedErrorSampler errorSampler)
          gadget decompose encode adversary) := by
  simp [FormalProof4FHE.LWE.AuxiliaryInput.zeroGame, problem, publicContinuation,
    adaptiveDistinguisher, sampleNestedSecret, bootstrapZeroAdaptiveGame,
    bootstrapZeroContinuationGame, generateBootstrapZeroCloudKey,
    AdaptiveReduction.adaptiveViewContinuation, adaptiveContinuation, bind_assoc,
    monad_norm]

/-- The existing complete BRK replacement cost is exactly this public real/zero advantage. -/
theorem kdmAdvantage_eq_sourceTargetMessageCircularAdaptiveAdvantage
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels) :
    kdmAdvantage q degree sourceRank suffixRank tgswLevels queryCount errorSampler
        gadget decompose encode adversary =
      sourceTargetMessageCircularAdaptiveAdvantage q (degree + 1) sourceRank suffixRank
        tgswLevels queryCount errorSampler errorSampler
        (AdaptiveReduction.extractedErrorSampler errorSampler) gadget decompose encode adversary := by
  unfold kdmAdvantage FormalProof4FHE.LWE.AuxiliaryInput.kdmAdvantage
    ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (realGame_evalDist_eq_realAdaptiveGame q degree sourceRank suffixRank tgswLevels
        queryCount errorSampler gadget decompose encode adversary) true,
    evalDist_ext_iff.mp
      (zeroGame_evalDist_eq_bootstrapZeroAdaptiveGame q degree sourceRank suffixRank
        tgswLevels queryCount errorSampler gadget decompose encode adversary) true]
  exact bootstrapReplacementAdvantage_eq_sourceTargetMessageCircular q (degree + 1)
    sourceRank suffixRank tgswLevels queryCount errorSampler errorSampler
    (AdaptiveReduction.extractedErrorSampler errorSampler) gadget decompose encode adversary

/-! ## Public zero branch and independent-BRK resampling -/

/-- A continuation of the complete public adaptive view, with no nested secret input. -/
abbrev PublicContinuation
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) :=
  AdaptiveReduction.AdaptiveView q degree sourceRank suffixRank tgswLevels queryCount →
    ProbComp Bool

/-- Native all-zero-BRK view with the real extension table and target-key tape. -/
def zeroViewGame
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (continuation : PublicContinuation q degree sourceRank suffixRank tgswLevels
      queryCount) : ProbComp Bool := do
  let sourceSecret ← Native.sampleRingSecret sourceRank (degree + 1)
  let suffixSecret ← Native.sampleRingSecret suffixRank (degree + 1)
  let bootstrappingKey ← generateZeroSourceBootstrappingKey q (degree + 1)
    sourceRank suffixRank tgswLevels errorSampler gadget sourceSecret
  let extensionKey ← generateRingExtensionKey q (degree + 1) sourceRank suffixRank
    tgswLevels errorSampler gadget sourceSecret suffixSecret
  let tape ← TLWE.batchEncrypt
    (targetScalarDimension sourceRank suffixRank (degree + 1)) queryCount
    (AdaptiveReduction.extractedErrorSampler errorSampler)
    (embedBinarySecret (targetMessages sourceSecret suffixSecret)) 0
  continuation ((bootstrappingKey, extensionKey), tape)

/-- Replace the BRK in a complete public adaptive view by an independently uniform BRK. -/
def resampleBootstrapContinuation
    {q degree sourceRank suffixRank tgswLevels queryCount : ℕ} [NeZero q]
    (continuation : PublicContinuation q degree sourceRank suffixRank tgswLevels
      queryCount) :
    PublicContinuation q degree sourceRank suffixRank tgswLevels queryCount :=
  fun view ↦ do
    let bootstrappingKey ←
      $ᵗ (Challenge q degree sourceRank suffixRank tgswLevels)
    continuation ((bootstrappingKey, view.1.2), view.2)

/-- The auxiliary-input zero branch is the explicit zero-BRK public-view game. -/
theorem auxiliaryZeroGame_evalDist_eq_zeroViewGame
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels) :
    evalDist
        (FormalProof4FHE.LWE.AuxiliaryInput.zeroGame
          (problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler gadget)
          (publicContinuation (adaptiveDistinguisher decompose encode adversary))) =
      evalDist
        (zeroViewGame q degree sourceRank suffixRank tgswLevels queryCount errorSampler
          gadget (AdaptiveReduction.adaptiveViewContinuation decompose encode adversary)) := by
  simp [FormalProof4FHE.LWE.AuxiliaryInput.zeroGame, problem, publicContinuation,
    adaptiveDistinguisher, zeroViewGame, sampleNestedSecret, bind_assoc, monad_norm]

/-- The auxiliary-input uniform-BRK branch is obtained from the zero-BRK view by discarding its
zero BRK and independently resampling that component.  The real extension table and target-key
tape remain untouched. -/
theorem auxiliaryUniformGame_evalDist_eq_zeroViewGame_resampled
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels) :
    evalDist
        (FormalProof4FHE.LWE.AuxiliaryInput.uniformGame
          (problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler gadget)
          (publicContinuation (adaptiveDistinguisher decompose encode adversary))) =
      evalDist
        (zeroViewGame q degree sourceRank suffixRank tgswLevels queryCount errorSampler
          gadget (resampleBootstrapContinuation
            (AdaptiveReduction.adaptiveViewContinuation decompose encode adversary))) := by
  let SourceSecrets := Native.sampleRingSecret sourceRank (degree + 1)
  let SuffixSecrets := Native.sampleRingSecret suffixRank (degree + 1)
  let UniformBootstrap : ProbComp
      (Challenge q degree sourceRank suffixRank tgswLevels) :=
    $ᵗ (Challenge q degree sourceRank suffixRank tgswLevels)
  let ZeroBootstrap := fun sourceSecret : RingBinarySecret sourceRank (degree + 1) ↦
    generateZeroSourceBootstrappingKey q (degree + 1) sourceRank suffixRank
      tgswLevels errorSampler gadget sourceSecret
  let Extension := fun (sourceSecret : RingBinarySecret sourceRank (degree + 1))
      (suffixSecret : RingBinarySecret suffixRank (degree + 1)) ↦
    generateRingExtensionKey q (degree + 1) sourceRank suffixRank tgswLevels
      errorSampler gadget sourceSecret suffixSecret
  let Tape := fun (sourceSecret : RingBinarySecret sourceRank (degree + 1))
      (suffixSecret : RingBinarySecret suffixRank (degree + 1)) ↦
    TLWE.batchEncrypt
      (targetScalarDimension sourceRank suffixRank (degree + 1)) queryCount
      (AdaptiveReduction.extractedErrorSampler errorSampler)
      (embedBinarySecret (targetMessages sourceSecret suffixSecret)) 0
  let Finish : PublicContinuation q degree sourceRank suffixRank tgswLevels queryCount :=
    AdaptiveReduction.adaptiveViewContinuation decompose encode adversary
  dsimp [FormalProof4FHE.LWE.AuxiliaryInput.uniformGame, problem,
    publicContinuation, adaptiveDistinguisher, sampleNestedSecret, zeroViewGame,
    resampleBootstrapContinuation]
  simp only [bind_assoc, pure_bind]
  change evalDist (SourceSecrets >>= fun sourceSecret ↦
      SuffixSecrets >>= fun suffixSecret ↦
      UniformBootstrap >>= fun bootstrappingKey ↦
      Extension sourceSecret suffixSecret >>= fun extensionKey ↦
      Tape sourceSecret suffixSecret >>= fun tape ↦
      Finish ((bootstrappingKey, extensionKey), tape)) =
    evalDist (SourceSecrets >>= fun sourceSecret ↦
      SuffixSecrets >>= fun suffixSecret ↦
      ZeroBootstrap sourceSecret >>= fun _ ↦
      Extension sourceSecret suffixSecret >>= fun extensionKey ↦
      Tape sourceSecret suffixSecret >>= fun tape ↦
      UniformBootstrap >>= fun bootstrappingKey ↦
      Finish ((bootstrappingKey, extensionKey), tape))
  refine evalDist_bind_congr' SourceSecrets fun sourceSecret ↦ ?_
  refine evalDist_bind_congr' SuffixSecrets fun suffixSecret ↦ ?_
  calc
    _ = evalDist (Extension sourceSecret suffixSecret >>= fun extensionKey ↦
          UniformBootstrap >>= fun bootstrappingKey ↦
          Tape sourceSecret suffixSecret >>= fun tape ↦
          Finish ((bootstrappingKey, extensionKey), tape)) :=
      evalDist_bind_bind_swap UniformBootstrap (Extension sourceSecret suffixSecret)
        (fun bootstrappingKey extensionKey ↦
          Tape sourceSecret suffixSecret >>= fun tape ↦
          Finish ((bootstrappingKey, extensionKey), tape))
    _ = evalDist (Extension sourceSecret suffixSecret >>= fun extensionKey ↦
          Tape sourceSecret suffixSecret >>= fun tape ↦
          UniformBootstrap >>= fun bootstrappingKey ↦
          Finish ((bootstrappingKey, extensionKey), tape)) := by
      refine evalDist_bind_congr' (Extension sourceSecret suffixSecret)
        fun extensionKey ↦ ?_
      exact evalDist_bind_bind_swap UniformBootstrap (Tape sourceSecret suffixSecret)
        (fun bootstrappingKey tape ↦
          Finish ((bootstrappingKey, extensionKey), tape))
    _ = _ :=
      (FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        (ZeroBootstrap sourceSecret) (by simp [ZeroBootstrap]) _).symm

/-! ## Ordinary joint module-RLWE reductions for the zero/reference branch -/

/-- Feed the zero-message conversion of the existing joint module-RLWE transcript to any public
adaptive-view continuation. -/
def jointZeroReduction
    {q degree sourceRank suffixRank tgswLevels queryCount : ℕ} [NeZero q]
    {errorSampler : ProbComp (RLWE.Rq q (degree + 1))}
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (continuation : PublicContinuation q degree sourceRank suffixRank tgswLevels
      queryCount) :
    LearningWithErrors.Adversary
      (AdaptiveReduction.problem q degree sourceRank suffixRank tgswLevels queryCount
        errorSampler) :=
  fun transcript ↦ do
    let suffixSecret ← Native.sampleRingSecret suffixRank (degree + 1)
    let suffixChallenge ← $ᵗ Matrix (Fin suffixRank) (Fin queryCount)
      (RLWE.Rq q (degree + 1))
    continuation
      (AdaptiveReduction.convertView q degree sourceRank suffixRank tgswLevels queryCount
        gadget (fun _ ↦ false) suffixSecret suffixChallenge transcript)

/-- Common completely uniform adaptive public-view endpoint. -/
def uniformViewGame
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (continuation : PublicContinuation q degree sourceRank suffixRank tgswLevels
      queryCount) : ProbComp Bool := do
  let view ← $ᵗ (AdaptiveReduction.AdaptiveView q degree sourceRank suffixRank
    tgswLevels queryCount)
  continuation view

/-- Resampling an unused BRK in a completely uniform adaptive view preserves the full view law. -/
theorem uniformViewGame_resampleBootstrapContinuation_evalDist
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (continuation : PublicContinuation q degree sourceRank suffixRank tgswLevels
      queryCount) :
    evalDist
        (uniformViewGame q degree sourceRank suffixRank tgswLevels queryCount
          (resampleBootstrapContinuation continuation)) =
      evalDist
        (uniformViewGame q degree sourceRank suffixRank tgswLevels queryCount
          continuation) := by
  let BootstrappingKey := Challenge q degree sourceRank suffixRank tgswLevels
  let ExtensionKey :=
    RingExtensionKey q (degree + 1) sourceRank suffixRank tgswLevels
  let Tape := TLWE.BatchCiphertext (ZMod q)
    (targetScalarDimension sourceRank suffixRank (degree + 1)) queryCount
  let CloudView := BootstrappingKey × ExtensionKey
  let View := CloudView × Tape
  let views : ProbComp View := $ᵗ View
  let cloudViews : ProbComp CloudView := $ᵗ CloudView
  let bootstrappingKeys : ProbComp BootstrappingKey := $ᵗ BootstrappingKey
  let extensionKeys : ProbComp ExtensionKey := $ᵗ ExtensionKey
  let tapes : ProbComp Tape := $ᵗ Tape
  have uniformViewProduct : views = Prod.mk <$> cloudViews <*> tapes := rfl
  have uniformCloudProduct : cloudViews =
      Prod.mk <$> bootstrappingKeys <*> extensionKeys := rfl
  unfold uniformViewGame resampleBootstrapContinuation
  change evalDist (views >>= fun view ↦
      bootstrappingKeys >>= fun bootstrappingKey ↦
      continuation ((bootstrappingKey, view.1.2), view.2)) =
    evalDist (views >>= continuation)
  rw [uniformViewProduct, uniformCloudProduct]
  simp only [seq_eq_bind_map, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  calc
    _ = evalDist (extensionKeys >>= fun extensionKey ↦
          tapes >>= fun tape ↦
          bootstrappingKeys >>= fun bootstrappingKey ↦
          continuation ((bootstrappingKey, extensionKey), tape)) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        bootstrappingKeys (by simp [bootstrappingKeys]) _
    _ = evalDist (extensionKeys >>= fun extensionKey ↦
          bootstrappingKeys >>= fun bootstrappingKey ↦
          tapes >>= fun tape ↦
          continuation ((bootstrappingKey, extensionKey), tape)) := by
      refine evalDist_bind_congr' extensionKeys fun extensionKey ↦ ?_
      exact (evalDist_bind_bind_swap bootstrappingKeys tapes
        (fun bootstrappingKey tape ↦
          continuation ((bootstrappingKey, extensionKey), tape))).symm
    _ = _ :=
      (evalDist_bind_bind_swap bootstrappingKeys extensionKeys
        (fun bootstrappingKey extensionKey ↦
          tapes >>= fun tape ↦
          continuation ((bootstrappingKey, extensionKey), tape))).symm

/-- Every joint zero reduction has the common completely uniform view as its module-RLWE
uniform branch. -/
theorem jointZeroReduction_game1_evalDist_eq_uniformViewGame
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (continuation : PublicContinuation q degree sourceRank suffixRank tgswLevels
      queryCount) :
    evalDist
        (LearningWithErrors.game1
          (AdaptiveReduction.problem q degree sourceRank suffixRank tgswLevels
            queryCount errorSampler)
          (jointZeroReduction gadget continuation)) =
      evalDist
        (uniformViewGame q degree sourceRank suffixRank tgswLevels queryCount
          continuation) := by
  rw [LearningWithErrors.game1,
    AdaptiveReduction.problem_uniformDistr_eq_uniformSample q degree sourceRank
      suffixRank tgswLevels queryCount]
  let transcripts : ProbComp
      (AdaptiveReduction.JointTranscript q degree sourceRank suffixRank tgswLevels
        queryCount) :=
    $ᵗ (AdaptiveReduction.JointTranscript q degree sourceRank suffixRank tgswLevels
      queryCount)
  let suffixes := Native.sampleRingSecret suffixRank (degree + 1)
  let suffixChallenges : ProbComp
      (Matrix (Fin suffixRank) (Fin queryCount) (RLWE.Rq q (degree + 1))) :=
    $ᵗ Matrix (Fin suffixRank) (Fin queryCount) (RLWE.Rq q (degree + 1))
  let views : ProbComp
      (AdaptiveReduction.AdaptiveView q degree sourceRank suffixRank tgswLevels
        queryCount) :=
    $ᵗ (AdaptiveReduction.AdaptiveView q degree sourceRank suffixRank tgswLevels
      queryCount)
  calc
    evalDist (transcripts >>= jointZeroReduction gadget continuation) =
        evalDist (suffixes >>= fun suffixSecret ↦
          transcripts >>= fun transcript ↦
          suffixChallenges >>= fun suffixChallenge ↦
          continuation
            (AdaptiveReduction.convertView q degree sourceRank suffixRank tgswLevels
              queryCount gadget (fun _ ↦ false) suffixSecret suffixChallenge
              transcript)) := by
      simpa [transcripts, suffixes, suffixChallenges, jointZeroReduction] using
        (evalDist_bind_bind_swap transcripts suffixes
          (fun transcript suffixSecret ↦
            suffixChallenges >>= fun suffixChallenge ↦
            continuation
              (AdaptiveReduction.convertView q degree sourceRank suffixRank
                tgswLevels queryCount gadget (fun _ ↦ false) suffixSecret
                suffixChallenge transcript)))
    _ = evalDist (suffixes >>= fun _ ↦ views >>= continuation) := by
      refine evalDist_bind_congr' suffixes fun suffixSecret ↦ ?_
      simpa [transcripts, suffixChallenges, views, bind_assoc, monad_norm] using
        (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
          (AdaptiveReduction.convertView_uniform_evalDist q degree sourceRank suffixRank
            tgswLevels queryCount gadget (fun _ ↦ false) suffixSecret)
          continuation)
    _ = evalDist (views >>= continuation) := by
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        suffixes (by simp [suffixes]) (views >>= continuation)
    _ = _ := by
      simp [uniformViewGame, views]

/-- The native zero-BRK view is exactly the real branch of its joint module-RLWE reduction, for
an arbitrary public continuation. -/
theorem zeroViewGame_evalDist_eq_jointZeroReduction_game0
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (continuation : PublicContinuation q degree sourceRank suffixRank tgswLevels
      queryCount) :
    evalDist
        (zeroViewGame q degree sourceRank suffixRank tgswLevels queryCount errorSampler
          gadget continuation) =
      evalDist
        (LearningWithErrors.game0
          (AdaptiveReduction.problem q degree sourceRank suffixRank tgswLevels
            queryCount errorSampler)
          (jointZeroReduction gadget continuation)) := by
  let sourceSecrets := Native.sampleRingSecret sourceRank (degree + 1)
  let suffixes := Native.sampleRingSecret suffixRank (degree + 1)
  let suffixChallenges : ProbComp
      (Matrix (Fin suffixRank) (Fin queryCount) (RLWE.Rq q (degree + 1))) :=
    $ᵗ Matrix (Fin suffixRank) (Fin queryCount) (RLWE.Rq q (degree + 1))
  let fixedTranscripts := fun
      (sourceSecret : RingBinarySecret sourceRank (degree + 1)) ↦
    AdaptiveReduction.fixedJointRealTranscript q degree sourceRank suffixRank
      tgswLevels queryCount errorSampler sourceSecret
  have nativeExpanded :
      evalDist
          (zeroViewGame q degree sourceRank suffixRank tgswLevels queryCount
            errorSampler gadget continuation) =
        evalDist (sourceSecrets >>= fun sourceSecret ↦
          suffixes >>= fun suffixSecret ↦
          fixedTranscripts sourceSecret >>= fun transcript ↦
          suffixChallenges >>= fun suffixChallenge ↦
          continuation
            (AdaptiveReduction.convertView q degree sourceRank suffixRank tgswLevels
              queryCount gadget (fun _ ↦ false) suffixSecret suffixChallenge
              transcript)) := by
    unfold zeroViewGame
    refine evalDist_bind_congr' sourceSecrets fun sourceSecret ↦ ?_
    refine evalDist_bind_congr' suffixes fun suffixSecret ↦ ?_
    calc
      evalDist (generateZeroSourceBootstrappingKey q (degree + 1) sourceRank
          suffixRank tgswLevels errorSampler gadget sourceSecret >>= fun bootstrappingKey ↦
        generateRingExtensionKey q (degree + 1) sourceRank suffixRank tgswLevels
            errorSampler gadget sourceSecret suffixSecret >>= fun extensionKey ↦
          TLWE.batchEncrypt
              (targetScalarDimension sourceRank suffixRank (degree + 1)) queryCount
              (AdaptiveReduction.extractedErrorSampler errorSampler)
              (embedBinarySecret (targetMessages sourceSecret suffixSecret)) 0 >>=
            fun tape ↦ continuation ((bootstrappingKey, extensionKey), tape)) =
        evalDist (Native.generateBootstrappingKey q (degree + 1) sourceRank
            tgswLevels (targetScalarDimension sourceRank suffixRank (degree + 1))
            errorSampler gadget (fun _ ↦ false) sourceSecret >>=
          fun bootstrappingKey ↦
            generateRingExtensionKey q (degree + 1) sourceRank suffixRank tgswLevels
                errorSampler gadget sourceSecret suffixSecret >>= fun extensionKey ↦
              TLWE.batchEncrypt
                  (targetScalarDimension sourceRank suffixRank (degree + 1)) queryCount
                  (AdaptiveReduction.extractedErrorSampler errorSampler)
                  (embedBinarySecret (targetMessages sourceSecret suffixSecret)) 0 >>=
                fun tape ↦ continuation ((bootstrappingKey, extensionKey), tape)) := by
          simpa [generateZeroSourceBootstrappingKey] using
            (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
              (AdaptiveReduction.generateBootstrappingKey_false_evalDist_eq_zero q degree
                sourceRank tgswLevels
                (targetScalarDimension sourceRank suffixRank (degree + 1)) errorSampler
                gadget sourceSecret).symm
              (fun bootstrappingKey ↦
                generateRingExtensionKey q (degree + 1) sourceRank suffixRank
                    tgswLevels errorSampler gadget sourceSecret suffixSecret >>=
                  fun extensionKey ↦
                  TLWE.batchEncrypt
                      (targetScalarDimension sourceRank suffixRank (degree + 1))
                      queryCount (AdaptiveReduction.extractedErrorSampler errorSampler)
                      (embedBinarySecret (targetMessages sourceSecret suffixSecret)) 0 >>=
                    fun tape ↦ continuation ((bootstrappingKey, extensionKey), tape)))
      _ = evalDist (fixedTranscripts sourceSecret >>= fun transcript ↦
          suffixChallenges >>= fun suffixChallenge ↦
          continuation
            (AdaptiveReduction.convertView q degree sourceRank suffixRank tgswLevels
              queryCount gadget (fun _ ↦ false) suffixSecret suffixChallenge
              transcript)) := by
        simpa [sourceSecrets, suffixes, suffixChallenges, fixedTranscripts,
          bind_assoc, monad_norm] using
          (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
            (AdaptiveReduction.convertView_fixedReal_evalDist q degree sourceRank
              suffixRank tgswLevels queryCount errorSampler gadget (fun _ ↦ false)
              sourceSecret suffixSecret)
            continuation).symm
  have lweExpanded :
      evalDist
          (LearningWithErrors.game0
            (AdaptiveReduction.problem q degree sourceRank suffixRank tgswLevels
              queryCount errorSampler)
            (jointZeroReduction gadget continuation)) =
        evalDist (sourceSecrets >>= fun sourceSecret ↦
          fixedTranscripts sourceSecret >>= fun transcript ↦
          suffixes >>= fun suffixSecret ↦
          suffixChallenges >>= fun suffixChallenge ↦
          continuation
            (AdaptiveReduction.convertView q degree sourceRank suffixRank tgswLevels
              queryCount gadget (fun _ ↦ false) suffixSecret suffixChallenge
              transcript)) := by
    rw [LearningWithErrors.game0]
    simpa [sourceSecrets, suffixes, suffixChallenges, fixedTranscripts,
      jointZeroReduction, bind_assoc, monad_norm] using
      (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        (AdaptiveReduction.distr_evalDist_eq_sampleSecret_bind_fixedJoint q degree
          sourceRank suffixRank tgswLevels queryCount errorSampler)
        (jointZeroReduction (errorSampler := errorSampler) gadget continuation))
  rw [nativeExpanded, lweExpanded]
  refine evalDist_bind_congr' sourceSecrets fun sourceSecret ↦ ?_
  exact evalDist_bind_bind_swap suffixes (fixedTranscripts sourceSecret)
    (fun suffixSecret transcript ↦
      suffixChallenges >>= fun suffixChallenge ↦
      continuation
        (AdaptiveReduction.convertView q degree sourceRank suffixRank tgswLevels
          queryCount gadget (fun _ ↦ false) suffixSecret suffixChallenge transcript))

/-- **The public zero/reference branch is ordinary module-RLWE.**  Distinguishing a zero-message
BRK from a uniform BRK while retaining the real extension table and target-key tape costs at most
two advantages for the same blocked module-RLWE problem.  The reductions differ only in whether
the converted zero BRK is retained or independently resampled. -/
theorem zeroLweAdvantage_le_two_moduleLwe
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels) :
    zeroLweAdvantage q degree sourceRank suffixRank tgswLevels queryCount errorSampler
        gadget decompose encode adversary ≤
      LearningWithErrors.advantage
          (AdaptiveReduction.problem q degree sourceRank suffixRank tgswLevels
            queryCount errorSampler)
          (jointZeroReduction gadget
            (AdaptiveReduction.adaptiveViewContinuation decompose encode adversary)) +
        LearningWithErrors.advantage
          (AdaptiveReduction.problem q degree sourceRank suffixRank tgswLevels
            queryCount errorSampler)
          (jointZeroReduction gadget
            (resampleBootstrapContinuation
              (AdaptiveReduction.adaptiveViewContinuation decompose encode adversary))) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage,
    FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold zeroLweAdvantage FormalProof4FHE.LWE.AuxiliaryInput.zeroLweAdvantage
    ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (auxiliaryZeroGame_evalDist_eq_zeroViewGame q degree sourceRank suffixRank
        tgswLevels queryCount errorSampler gadget decompose encode adversary) true,
    evalDist_ext_iff.mp
      (auxiliaryUniformGame_evalDist_eq_zeroViewGame_resampled q degree sourceRank
        suffixRank tgswLevels queryCount errorSampler gadget decompose encode adversary)
      true,
    evalDist_ext_iff.mp
      (zeroViewGame_evalDist_eq_jointZeroReduction_game0 q degree sourceRank suffixRank
        tgswLevels queryCount errorSampler gadget
        (AdaptiveReduction.adaptiveViewContinuation decompose encode adversary)) true,
    evalDist_ext_iff.mp
      (zeroViewGame_evalDist_eq_jointZeroReduction_game0 q degree sourceRank suffixRank
        tgswLevels queryCount errorSampler gadget
        (resampleBootstrapContinuation
          (AdaptiveReduction.adaptiveViewContinuation decompose encode adversary))) true]
  let continuation : PublicContinuation q degree sourceRank suffixRank tgswLevels
      queryCount :=
    AdaptiveReduction.adaptiveViewContinuation decompose encode adversary
  let zeroProbability : ℝ :=
    (Pr[= true | LearningWithErrors.game0
      (AdaptiveReduction.problem q degree sourceRank suffixRank tgswLevels queryCount
        errorSampler)
      (jointZeroReduction gadget continuation)]).toReal
  let uniformZeroProbability : ℝ :=
    (Pr[= true | LearningWithErrors.game1
      (AdaptiveReduction.problem q degree sourceRank suffixRank tgswLevels queryCount
        errorSampler)
      (jointZeroReduction gadget continuation)]).toReal
  let resampledProbability : ℝ :=
    (Pr[= true | LearningWithErrors.game0
      (AdaptiveReduction.problem q degree sourceRank suffixRank tgswLevels queryCount
        errorSampler)
      (jointZeroReduction gadget
        (resampleBootstrapContinuation continuation))]).toReal
  let uniformResampledProbability : ℝ :=
    (Pr[= true | LearningWithErrors.game1
      (AdaptiveReduction.problem q degree sourceRank suffixRank tgswLevels queryCount
        errorSampler)
      (jointZeroReduction gadget
        (resampleBootstrapContinuation continuation))]).toReal
  have hUniform : uniformZeroProbability = uniformResampledProbability := by
    apply congrArg ENNReal.toReal
    exact evalDist_ext_iff.mp
      ((jointZeroReduction_game1_evalDist_eq_uniformViewGame q degree sourceRank
          suffixRank tgswLevels queryCount errorSampler gadget continuation).trans
        ((uniformViewGame_resampleBootstrapContinuation_evalDist q degree sourceRank
            suffixRank tgswLevels queryCount continuation).symm.trans
          (jointZeroReduction_game1_evalDist_eq_uniformViewGame q degree sourceRank
            suffixRank tgswLevels queryCount errorSampler gadget
            (resampleBootstrapContinuation continuation)).symm)) true
  change |zeroProbability - resampledProbability| ≤
    |zeroProbability - uniformZeroProbability| +
      |resampledProbability - uniformResampledProbability|
  rw [hUniform, abs_sub_comm resampledProbability uniformResampledProbability]
  exact abs_sub_le zeroProbability uniformResampledProbability resampledProbability

/-! ## Fully uniform endpoint and end-to-end adaptive security -/

/-- A query-bounded adaptive adversary succeeds with probability exactly one half on the fully
uniform public view.  The evaluation-key components may be arbitrary fixed values at the inner
step; uniformity of the target-key transcript is the decisive fact. -/
theorem uniformViewGame_probOutput_true
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels)
    (hbound : Encryption.Adaptive.IsQueryBound adversary queryCount) :
    Pr[= true |
      uniformViewGame q degree sourceRank suffixRank tgswLevels queryCount
        (AdaptiveReduction.adaptiveViewContinuation decompose encode adversary)] =
      1 / 2 := by
  let BootstrappingKey := Challenge q degree sourceRank suffixRank tgswLevels
  let ExtensionKey :=
    RingExtensionKey q (degree + 1) sourceRank suffixRank tgswLevels
  let Tape := TLWE.BatchCiphertext (ZMod q)
    (targetScalarDimension sourceRank suffixRank (degree + 1)) queryCount
  let CloudView := BootstrappingKey × ExtensionKey
  let View := CloudView × Tape
  let views : ProbComp View := $ᵗ View
  let cloudViews : ProbComp CloudView := $ᵗ CloudView
  let tapes : ProbComp Tape := $ᵗ Tape
  have uniformProduct : views = Prod.mk <$> cloudViews <*> tapes := rfl
  unfold uniformViewGame
  change Pr[= true | views >>= fun view ↦
      AdaptiveReduction.adaptiveViewContinuation decompose encode adversary view] =
    1 / 2
  rw [uniformProduct]
  simp only [seq_eq_bind_map, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  rw [probOutput_bind_of_const (r := (1 / 2 : ENNReal)) cloudViews]
  · simp
  · intro cloudView _
    let cloudKey : CloudKey q (degree + 1) sourceRank suffixRank tgswLevels :=
      ⟨deriveBootstrappingKey q (degree + 1) sourceRank suffixRank tgswLevels
        decompose cloudView.1 cloudView.2⟩
    let finish := fun (tape : Tape) (bit : Bool) ↦ do
      let guess ← runFromTranscript bit encode adversary cloudKey tape
      return bit == guess
    rw [show Pr[= true | tapes >>= fun tape ↦
          AdaptiveReduction.adaptiveViewContinuation decompose encode adversary
            ((cloudView.1, cloudView.2), tape)] =
        Pr[= true | tapes >>= fun tape ↦
          ($ᵗ Bool) >>= fun bit ↦ finish tape bit] by
      simp [AdaptiveReduction.adaptiveViewContinuation, cloudKey, tapes, finish]]
    rw [probOutput_bind_bind_swap]
    simpa [tapes, finish, cloudKey, Tape] using
      (uniformTranscript_adaptive_probOutput_true queryCount encode adversary cloudKey
        (hbound cloudKey))

/-- **End-to-end public circular-security theorem.**  For positive ring degree and a common ring
error sampler, every query-bounded adaptive TFHE adversary is bounded by exactly:

1. one public native real-target-message-BRK versus uniform-BRK CircRLWE advantage, retaining the
   real extension table and target-key tape; and
2. one ordinary blocked module-RLWE advantage that replaces the remaining extension and tape
   rows by a fully uniform view.

The first term is the precise degree-two circular-security research obligation.  The second is a
standard same-source-secret module-RLWE problem. -/
theorem abs_signedAdvantage_realAdaptive_le_circularLwe_add_moduleLwe
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels)
    (hbound : Encryption.Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (realAdaptiveGame q (degree + 1) sourceRank suffixRank tgswLevels queryCount
        errorSampler errorSampler (AdaptiveReduction.extractedErrorSampler errorSampler)
        gadget decompose encode adversary)| ≤
      circularLweAdvantage q degree sourceRank suffixRank tgswLevels queryCount
          errorSampler gadget decompose encode adversary +
        LearningWithErrors.advantage
          (AdaptiveReduction.problem q degree sourceRank suffixRank tgswLevels
            queryCount errorSampler)
          (jointZeroReduction gadget
            (resampleBootstrapContinuation
              (AdaptiveReduction.adaptiveViewContinuation decompose encode adversary))) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold Encryption.signedAdvantage circularLweAdvantage publicAdvantage
    FormalProof4FHE.LWE.AuxiliaryInput.circularLweAdvantage
    ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (realGame_evalDist_eq_realAdaptiveGame q degree sourceRank suffixRank tgswLevels
        queryCount errorSampler gadget decompose encode adversary) true,
    evalDist_ext_iff.mp
      (auxiliaryUniformGame_evalDist_eq_zeroViewGame_resampled q degree sourceRank
        suffixRank tgswLevels queryCount errorSampler gadget decompose encode adversary)
      true,
    evalDist_ext_iff.mp
      (zeroViewGame_evalDist_eq_jointZeroReduction_game0 q degree sourceRank suffixRank
        tgswLevels queryCount errorSampler gadget
        (resampleBootstrapContinuation
          (AdaptiveReduction.adaptiveViewContinuation decompose encode adversary))) true,
    evalDist_ext_iff.mp
      (jointZeroReduction_game1_evalDist_eq_uniformViewGame q degree sourceRank
        suffixRank tgswLevels queryCount errorSampler gadget
        (resampleBootstrapContinuation
          (AdaptiveReduction.adaptiveViewContinuation decompose encode adversary))) true,
    evalDist_ext_iff.mp
      (uniformViewGame_resampleBootstrapContinuation_evalDist q degree sourceRank
        suffixRank tgswLevels queryCount
        (AdaptiveReduction.adaptiveViewContinuation decompose encode adversary)) true,
    uniformViewGame_probOutput_true q degree sourceRank suffixRank tgswLevels queryCount
      decompose encode adversary hbound]
  norm_num
  exact abs_sub_le
    (Pr[= true |
      realAdaptiveGame q (degree + 1) sourceRank suffixRank tgswLevels queryCount
        errorSampler errorSampler (AdaptiveReduction.extractedErrorSampler errorSampler)
        gadget decompose encode adversary]).toReal
    (Pr[= true |
      LearningWithErrors.game0
        (AdaptiveReduction.problem q degree sourceRank suffixRank tgswLevels queryCount
          errorSampler)
        (jointZeroReduction gadget
          (resampleBootstrapContinuation
            (AdaptiveReduction.adaptiveViewContinuation decompose encode adversary)))]).toReal
    (1 / 2 : ℝ)

/-- **Monomial-normal-form adaptive TFHE security.**  The nonstandard term in the complete
public-view theorem is exactly—not merely bounded by—the degree-two monomial CircRLWE advantage.
The other term remains the ordinary blocked module-RLWE advantage. -/
theorem abs_signedAdvantage_realAdaptive_le_monomialCircularLwe_add_moduleLwe
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels)
    (hbound : Encryption.Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (realAdaptiveGame q (degree + 1) sourceRank suffixRank tgswLevels queryCount
        errorSampler errorSampler (AdaptiveReduction.extractedErrorSampler errorSampler)
        gadget decompose encode adversary)| ≤
      monomialCircularLweAdvantage q degree sourceRank suffixRank tgswLevels queryCount
          errorSampler gadget decompose encode adversary +
        LearningWithErrors.advantage
          (AdaptiveReduction.problem q degree sourceRank suffixRank tgswLevels
            queryCount errorSampler)
          (jointZeroReduction gadget
            (resampleBootstrapContinuation
              (AdaptiveReduction.adaptiveViewContinuation decompose encode adversary))) := by
  rw [← circularLweAdvantage_eq_monomialCircularLweAdvantage q degree sourceRank
    suffixRank tgswLevels queryCount errorSampler gadget decompose encode adversary]
  exact abs_signedAdvantage_realAdaptive_le_circularLwe_add_moduleLwe q degree sourceRank
    suffixRank tgswLevels queryCount errorSampler gadget decompose encode adversary hbound

/-- **Complete-view search-normal-form TFHE security.**  A checked same-noise native
search-to-decision certificate replaces the sole monomial CircRLWE term by exact nested-key
recovery and the certificate loss; the remaining hybrid is ordinary blocked module-RLWE. -/
theorem abs_signedAdvantage_realAdaptive_le_monomialSearch_add_reductionLoss_add_moduleLwe
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels)
    (hbound : Encryption.Adaptive.IsQueryBound adversary queryCount)
    (reduction : MonomialDecisionToSearchReduction q degree sourceRank suffixRank
      tgswLevels queryCount errorSampler gadget) :
    |Encryption.signedAdvantage
      (realAdaptiveGame q (degree + 1) sourceRank suffixRank tgswLevels queryCount
        errorSampler errorSampler (AdaptiveReduction.extractedErrorSampler errorSampler)
        gadget decompose encode adversary)| ≤
      (FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
        (monomialSearchProblem q degree sourceRank suffixRank tgswLevels queryCount
          errorSampler gadget)
        (reduction.toSolver
          (adaptiveDistinguisher decompose encode adversary))).toReal +
        reduction.loss (adaptiveDistinguisher decompose encode adversary) +
        LearningWithErrors.advantage
          (AdaptiveReduction.problem q degree sourceRank suffixRank tgswLevels
            queryCount errorSampler)
          (jointZeroReduction gadget
            (resampleBootstrapContinuation
              (AdaptiveReduction.adaptiveViewContinuation decompose encode adversary))) := by
  exact
    (abs_signedAdvantage_realAdaptive_le_monomialCircularLwe_add_moduleLwe q degree
      sourceRank suffixRank tgswLevels queryCount errorSampler gadget decompose encode
      adversary hbound).trans
      (add_le_add
        (monomialCircularLweAdvantage_le_search_add_reductionLoss q degree sourceRank
          suffixRank tgswLevels queryCount errorSampler gadget decompose encode adversary
          reduction)
        (le_refl _))

/-- **Widened-decision search-normal-form TFHE security.**  The honest and ordinary module-RLWE
games use the decision error law, while nested-key recovery may use a separate narrow search law.
All widening, shifted evaluation, guessing, and amplification cost is confined to the supplied
cross-reduction's explicit loss. -/
theorem abs_signedAdvantage_realAdaptive_le_narrowMonomialSearch_add_reductionLoss_add_moduleLwe
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (decisionErrorSampler searchErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels)
    (hbound : Encryption.Adaptive.IsQueryBound adversary queryCount)
    (reduction : MonomialCrossDecisionToSearchReduction q degree sourceRank suffixRank
      tgswLevels queryCount decisionErrorSampler searchErrorSampler gadget) :
    |Encryption.signedAdvantage
      (realAdaptiveGame q (degree + 1) sourceRank suffixRank tgswLevels queryCount
        decisionErrorSampler decisionErrorSampler
        (AdaptiveReduction.extractedErrorSampler decisionErrorSampler)
        gadget decompose encode adversary)| ≤
      (FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
        (monomialSearchProblem q degree sourceRank suffixRank tgswLevels queryCount
          searchErrorSampler gadget)
        (reduction.toSolver
          (adaptiveDistinguisher decompose encode adversary))).toReal +
        reduction.loss (adaptiveDistinguisher decompose encode adversary) +
        LearningWithErrors.advantage
          (AdaptiveReduction.problem q degree sourceRank suffixRank tgswLevels
            queryCount decisionErrorSampler)
          (jointZeroReduction gadget
            (resampleBootstrapContinuation
              (AdaptiveReduction.adaptiveViewContinuation decompose encode adversary))) := by
  exact
    (abs_signedAdvantage_realAdaptive_le_monomialCircularLwe_add_moduleLwe q degree
      sourceRank suffixRank tgswLevels queryCount decisionErrorSampler gadget decompose
      encode adversary hbound).trans
      (add_le_add
        (monomialCircularLweAdvantage_le_narrowSearch_add_reductionLoss q degree
          sourceRank suffixRank tgswLevels queryCount decisionErrorSampler
          searchErrorSampler gadget decompose encode adversary reduction)
        (le_refl _))

/-! ## Adversary-class security composition -/

/-- Concrete adaptive TFHE security for an allowed, explicitly query-bounded adversary class. -/
def HardAgainst
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (allowed : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels → Prop)
    (bound : ℝ) : Prop :=
  ∀ adversary, allowed adversary →
    Encryption.Adaptive.IsQueryBound adversary queryCount →
      |Encryption.signedAdvantage
        (realAdaptiveGame q (degree + 1) sourceRank suffixRank tgswLevels queryCount
          errorSampler errorSampler
          (AdaptiveReduction.extractedErrorSampler errorSampler) gadget decompose encode
          adversary)| ≤ bound

/-- Public native BRK CircRLWE hardness and ordinary joint module-RLWE hardness imply adaptive
TFHE security.  The closure hypotheses record the two explicit public reductions. -/
theorem hardAgainst_of_circularLwe_and_moduleLwe
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adaptiveAllowed : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels → Prop)
    (circularAllowed : PublicDistinguisher
      (Challenge q degree sourceRank suffixRank tgswLevels)
      (Auxiliary q degree sourceRank suffixRank tgswLevels queryCount) → Prop)
    (moduleLweAllowed : LearningWithErrors.Adversary
      (AdaptiveReduction.problem q degree sourceRank suffixRank tgswLevels queryCount
        errorSampler) → Prop)
    (circularBound moduleLweBound : ℝ)
    (hCircularClosed : ∀ adversary, adaptiveAllowed adversary →
      circularAllowed (adaptiveDistinguisher decompose encode adversary))
    (hModuleLweClosed : ∀ adversary, adaptiveAllowed adversary →
      moduleLweAllowed
        (jointZeroReduction gadget
          (resampleBootstrapContinuation
            (AdaptiveReduction.adaptiveViewContinuation decompose encode adversary))))
    (hCircular : PublicHardAgainst
      (problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler gadget)
      circularAllowed circularBound)
    (hModuleLwe : FormalProof4FHE.LWE.HardAgainst
      (AdaptiveReduction.problem q degree sourceRank suffixRank tgswLevels queryCount
        errorSampler)
      moduleLweAllowed moduleLweBound) :
    HardAgainst q degree sourceRank suffixRank tgswLevels queryCount errorSampler gadget
      decompose encode adaptiveAllowed (circularBound + moduleLweBound) := by
  intro adversary hAllowed hBound
  exact
    (abs_signedAdvantage_realAdaptive_le_circularLwe_add_moduleLwe q degree sourceRank
      suffixRank tgswLevels queryCount errorSampler gadget decompose encode adversary
      hBound).trans
      (add_le_add
        (hCircular (adaptiveDistinguisher decompose encode adversary)
          (hCircularClosed adversary hAllowed))
        (hModuleLwe
          (jointZeroReduction gadget
            (resampleBootstrapContinuation
              (AdaptiveReduction.adaptiveViewContinuation decompose encode adversary)))
          (hModuleLweClosed adversary hAllowed)))

/-- The same adversary-class composition stated directly for the exact degree-two monomial
presentation of the native public BRK CircRLWE problem. -/
theorem hardAgainst_of_monomialCircularLwe_and_moduleLwe
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adaptiveAllowed : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels → Prop)
    (monomialAllowed : PublicDistinguisher
      (Challenge q degree sourceRank suffixRank tgswLevels)
      (Auxiliary q degree sourceRank suffixRank tgswLevels queryCount) → Prop)
    (moduleLweAllowed : LearningWithErrors.Adversary
      (AdaptiveReduction.problem q degree sourceRank suffixRank tgswLevels queryCount
        errorSampler) → Prop)
    (monomialBound moduleLweBound : ℝ)
    (hMonomialClosed : ∀ adversary, adaptiveAllowed adversary →
      monomialAllowed (adaptiveDistinguisher decompose encode adversary))
    (hModuleLweClosed : ∀ adversary, adaptiveAllowed adversary →
      moduleLweAllowed
        (jointZeroReduction gadget
          (resampleBootstrapContinuation
            (AdaptiveReduction.adaptiveViewContinuation decompose encode adversary))))
    (hMonomial : PublicHardAgainst
      (monomialProblem q degree sourceRank suffixRank tgswLevels queryCount
        errorSampler gadget)
      monomialAllowed monomialBound)
    (hModuleLwe : FormalProof4FHE.LWE.HardAgainst
      (AdaptiveReduction.problem q degree sourceRank suffixRank tgswLevels queryCount
        errorSampler)
      moduleLweAllowed moduleLweBound) :
    HardAgainst q degree sourceRank suffixRank tgswLevels queryCount errorSampler gadget
      decompose encode adaptiveAllowed (monomialBound + moduleLweBound) := by
  intro adversary hAllowed hBound
  exact
    (abs_signedAdvantage_realAdaptive_le_monomialCircularLwe_add_moduleLwe q degree
      sourceRank suffixRank tgswLevels queryCount errorSampler gadget decompose encode
      adversary hBound).trans
      (add_le_add
        (hMonomial (adaptiveDistinguisher decompose encode adversary)
          (hMonomialClosed adversary hAllowed))
        (hModuleLwe
          (jointZeroReduction gadget
            (resampleBootstrapContinuation
              (AdaptiveReduction.adaptiveViewContinuation decompose encode adversary)))
          (hModuleLweClosed adversary hAllowed)))

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.AdaptiveBRKCircLWE
