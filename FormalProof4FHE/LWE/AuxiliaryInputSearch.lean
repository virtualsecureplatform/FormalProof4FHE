/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.AuxiliaryInput

/-!
# Search Problems for Auxiliary-Input Circular LWE

This module gives the search side of the real-versus-uniform auxiliary-input CircLWE interface.
A solver receives the real challenge and its correlated auxiliary input, but not the hidden secret,
and returns a candidate secret.  The experiment verifies that candidate explicitly.

`exactRecoveryProblem` derives this search experiment from the real branch of an existing
`LWE.AuxiliaryInput.Problem`.  Exact recovery is bounded by the corresponding circular decision
advantage plus recovery at the uniform endpoint.  When that endpoint is independent of a uniform
finite secret, its recovery probability is proved to be exactly the inverse secret-space size.
This decomposition does not turn an arbitrary decision distinguisher into a search solver; that
scheme-specific direction still requires its own reduction.
-/

open OracleComp

namespace FormalProof4FHE.LWE.AuxiliaryInput.Search

/-- A search problem with a secret-dependent challenge, correlated auxiliary input, and an
explicit Boolean verifier for recovered secrets. -/
structure Problem (Secret Challenge Auxiliary : Type) where
  sampleSecret : ProbComp Secret
  sampleChallenge : Secret → ProbComp Challenge
  sampleAuxiliary : Secret → ProbComp Auxiliary
  verify : Secret → Secret → Bool

/-- A search solver sees only the public challenge and auxiliary input. -/
abbrev Solver (Secret Challenge Auxiliary : Type) :=
  Challenge → Auxiliary → ProbComp Secret

section Games

variable {Secret Challenge Auxiliary : Type}

/-- Run a search solver on the correlated real view and verify its recovered secret. -/
def game (problem : Problem Secret Challenge Auxiliary)
    (solver : Solver Secret Challenge Auxiliary) : ProbComp Bool := do
  let secret ← problem.sampleSecret
  let challenge ← problem.sampleChallenge secret
  let auxiliary ← problem.sampleAuxiliary secret
  let recovered ← solver challenge auxiliary
  return problem.verify secret recovered

/-- Exact success probability of an auxiliary-input search solver. -/
noncomputable def successProbability (problem : Problem Secret Challenge Auxiliary)
    (solver : Solver Secret Challenge Auxiliary) : ENNReal :=
  Pr[= true | game problem solver]

/-- Search hardness for a selected solver class and an explicit success bound. -/
def HardAgainst (problem : Problem Secret Challenge Auxiliary)
    (allowed : Solver Secret Challenge Auxiliary → Prop) (bound : ENNReal) : Prop :=
  ∀ solver, allowed solver → successProbability problem solver ≤ bound

/-- The exact-secret-recovery search problem associated with the real branch of an
auxiliary-input CircLWE problem. -/
def exactRecoveryProblem [DecidableEq Secret]
    (problem : FormalProof4FHE.LWE.AuxiliaryInput.Problem Secret Challenge Auxiliary) :
    Problem Secret Challenge Auxiliary where
  sampleSecret := problem.sampleSecret
  sampleChallenge := problem.sampleReal
  sampleAuxiliary := problem.sampleAuxiliary
  verify := fun secret recovered => decide (recovered = secret)

/-- Turn a search solver into the secret-aware recovery continuation used only by the experiment
to check whether the solver's public-view output is correct. -/
def recoveryContinuation [DecidableEq Secret]
    (solver : Solver Secret Challenge Auxiliary) :
    FormalProof4FHE.LWE.AuxiliaryInput.Continuation Secret Challenge Auxiliary :=
  fun secret challenge auxiliary => do
    let recovered ← solver challenge auxiliary
    return decide (recovered = secret)

/-- Exact recovery search is definitionally the real auxiliary-input game with the corresponding
recovery continuation. -/
theorem game_exactRecoveryProblem_eq_realGame [DecidableEq Secret]
    (problem : FormalProof4FHE.LWE.AuxiliaryInput.Problem Secret Challenge Auxiliary)
    (solver : Solver Secret Challenge Auxiliary) :
    game (exactRecoveryProblem problem) solver =
      FormalProof4FHE.LWE.AuxiliaryInput.realGame problem
        (recoveryContinuation solver) := by
  simp [game, exactRecoveryProblem,
    FormalProof4FHE.LWE.AuxiliaryInput.realGame, recoveryContinuation, monad_norm]

/-- Run the same recovery continuation at the uniform-challenge endpoint.  The correlated
auxiliary input is retained, so this baseline is not assumed negligible. -/
def uniformRecoveryGame [DecidableEq Secret]
    (problem : FormalProof4FHE.LWE.AuxiliaryInput.Problem Secret Challenge Auxiliary)
    (solver : Solver Secret Challenge Auxiliary) : ProbComp Bool :=
  FormalProof4FHE.LWE.AuxiliaryInput.uniformGame problem
    (recoveryContinuation solver)

/-- CircLWE advantage for a recovery continuation is exactly the distance between the real
search experiment and its uniform-challenge recovery baseline. -/
theorem circularLweAdvantage_recoveryContinuation [DecidableEq Secret]
    (problem : FormalProof4FHE.LWE.AuxiliaryInput.Problem Secret Challenge Auxiliary)
    (solver : Solver Secret Challenge Auxiliary) :
    FormalProof4FHE.LWE.AuxiliaryInput.circularLweAdvantage problem
        (recoveryContinuation solver) =
      (game (exactRecoveryProblem problem) solver).boolDistAdvantage
        (uniformRecoveryGame problem solver) := by
  rw [game_exactRecoveryProblem_eq_realGame]
  rfl

/-- Exact-recovery success is bounded by the real-versus-uniform CircLWE advantage plus recovery
success at the uniform-challenge endpoint.  This is the generic decision/search decomposition:
it does not assume that the retained auxiliary input is harmless, so the uniform baseline remains
an explicit term. -/
theorem successProbability_exactRecovery_le_circularLwe_add_uniform [DecidableEq Secret]
    (problem : FormalProof4FHE.LWE.AuxiliaryInput.Problem Secret Challenge Auxiliary)
    (solver : Solver Secret Challenge Auxiliary) :
    successProbability (exactRecoveryProblem problem) solver ≤
      ENNReal.ofReal
          (FormalProof4FHE.LWE.AuxiliaryInput.circularLweAdvantage problem
            (recoveryContinuation solver)) +
        Pr[= true | uniformRecoveryGame problem solver] := by
  have h := ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage
    (game (exactRecoveryProblem problem) solver)
    (uniformRecoveryGame problem solver)
  rw [← circularLweAdvantage_recoveryContinuation problem solver] at h
  simpa only [successProbability, add_comm] using h

/-- An arbitrary public computation cannot predict an independently sampled uniform finite
secret with probability other than the reciprocal of the secret-space cardinality. -/
theorem probOutput_uniformSecret_recovery_eq_inv_card
    {Public : Type} [Fintype Secret] [DecidableEq Secret] [SampleableType Secret]
    (publicView : ProbComp Public) (solver : Public → ProbComp Secret) :
    Pr[= true | do
      let secret ← $ᵗ Secret
      let view ← publicView
      let recovered ← solver view
      return decide (recovered = secret)] =
        (Fintype.card Secret : ENNReal)⁻¹ := by
  have hsingle (recovered : Secret) :
      Pr[= true | ($ᵗ Secret) >>= fun secret =>
        pure (decide (recovered = secret))] =
          (Fintype.card Secret : ENNReal)⁻¹ := by
    simp only [probOutput_bind_eq_tsum, probOutput_uniformSample, probOutput_pure]
    rw [tsum_fintype, Finset.sum_eq_single recovered]
    · simp
    · intro secret _ hne
      simp [show recovered ≠ secret from fun h => hne h.symm]
    · exact absurd (Finset.mem_univ recovered)
  rw [probOutput_bind_bind_swap]
  rw [probOutput_bind_of_const (r := (Fintype.card Secret : ENNReal)⁻¹) _ fun view _ => by
    rw [probOutput_bind_bind_swap]
    rw [probOutput_bind_of_const (r := (Fintype.card Secret : ENNReal)⁻¹) _
      fun recovered _ => hsingle recovered]
    simp]
  simp

end Games

end FormalProof4FHE.LWE.AuxiliaryInput.Search
