/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.Basic

/-!
# Fixed Auxiliary-Input Circular LWE Games

Circular LWE is a statement about a joint distribution, not about an ordinary LWE sample in
isolation.  Besides the LWE-like challenge, a construction may publish fixed side information
that is correlated with the same hidden secret.  This file gives that distinction a small generic
interface.

`Problem` records three challenge branches conditioned on one secret:

* `sampleReal` is the key-dependent-message branch;
* `sampleZero` retains the encryption format but replaces the encoded function by zero; and
* `sampleUniform` is the pseudorandom endpoint used in the CircLWE formulation.

The same fixed auxiliary input is retained in every branch.  The contextual continuation may
also receive the hidden secret so that a reduction can generate later challenges under it; this
does not assert security against continuations that reveal the secret to their internal
adversary.  As elsewhere in the library, the selected `allowed` class records that efficiency and
information-flow restriction.

The triangle theorems show that real-versus-zero KDM security and real-versus-uniform CircLWE
security are equivalent modulo the explicit zero-versus-uniform side-information LWE term.  No
claim that this final term follows from ordinary LWE is built into the interface.
-/

open OracleComp

namespace FormalProof4FHE.LWE.AuxiliaryInput

/-- A fixed-side-information circular/KDM distinguishing problem.

`sampleUniform` is secret independent by type.  `sampleAuxiliary` may depend on the secret and is
sampled unchanged in all three branches. -/
structure Problem (Secret Challenge Auxiliary : Type) where
  sampleSecret : ProbComp Secret
  sampleReal : Secret → ProbComp Challenge
  sampleZero : Secret → ProbComp Challenge
  sampleUniform : ProbComp Challenge
  sampleAuxiliary : Secret → ProbComp Auxiliary

/-- A secret-dependent downstream context.  The secret is available to the experiment so it can
generate later ciphertexts; an admissible continuation need not expose it to its adversary. -/
abbrev Continuation (Secret Challenge Auxiliary : Type) :=
  Secret → Challenge → Auxiliary → ProbComp Bool

section Games

variable {Secret Challenge Auxiliary : Type}

/-- Key-dependent real branch with the fixed correlated auxiliary input. -/
def realGame (problem : Problem Secret Challenge Auxiliary)
    (continuation : Continuation Secret Challenge Auxiliary) : ProbComp Bool := do
  let secret ← problem.sampleSecret
  let challenge ← problem.sampleReal secret
  let auxiliary ← problem.sampleAuxiliary secret
  continuation secret challenge auxiliary

/-- Zero-message encryption branch with the same fixed correlated auxiliary input. -/
def zeroGame (problem : Problem Secret Challenge Auxiliary)
    (continuation : Continuation Secret Challenge Auxiliary) : ProbComp Bool := do
  let secret ← problem.sampleSecret
  let challenge ← problem.sampleZero secret
  let auxiliary ← problem.sampleAuxiliary secret
  continuation secret challenge auxiliary

/-- Uniform challenge branch with the same fixed correlated auxiliary input. -/
def uniformGame (problem : Problem Secret Challenge Auxiliary)
    (continuation : Continuation Secret Challenge Auxiliary) : ProbComp Bool := do
  let secret ← problem.sampleSecret
  let challenge ← problem.sampleUniform
  let auxiliary ← problem.sampleAuxiliary secret
  continuation secret challenge auxiliary

/-- Real-versus-zero fixed-hint KDM advantage. -/
noncomputable def kdmAdvantage (problem : Problem Secret Challenge Auxiliary)
    (continuation : Continuation Secret Challenge Auxiliary) : ℝ :=
  (realGame problem continuation).boolDistAdvantage
    (zeroGame problem continuation)

/-- Real-versus-uniform auxiliary-input CircLWE advantage. -/
noncomputable def circularLweAdvantage (problem : Problem Secret Challenge Auxiliary)
    (continuation : Continuation Secret Challenge Auxiliary) : ℝ :=
  (realGame problem continuation).boolDistAdvantage
    (uniformGame problem continuation)

/-- Zero-message-versus-uniform LWE advantage in the presence of the fixed side information. -/
noncomputable def zeroLweAdvantage (problem : Problem Secret Challenge Auxiliary)
    (continuation : Continuation Secret Challenge Auxiliary) : ℝ :=
  (zeroGame problem continuation).boolDistAdvantage
    (uniformGame problem continuation)

/-- KDM replacement is bounded by auxiliary-input CircLWE plus the zero-message
side-information LWE term. -/
theorem kdmAdvantage_le_circularLwe_add_zeroLwe
    (problem : Problem Secret Challenge Auxiliary)
    (continuation : Continuation Secret Challenge Auxiliary) :
    kdmAdvantage problem continuation ≤
      circularLweAdvantage problem continuation +
        zeroLweAdvantage problem continuation := by
  have h := ProbComp.boolDistAdvantage_triangle
    (realGame problem continuation)
    (uniformGame problem continuation)
    (zeroGame problem continuation)
  unfold kdmAdvantage circularLweAdvantage zeroLweAdvantage
  rw [show (uniformGame problem continuation).boolDistAdvantage
      (zeroGame problem continuation) =
      (zeroGame problem continuation).boolDistAdvantage
        (uniformGame problem continuation) by
    unfold ProbComp.boolDistAdvantage
    rw [abs_sub_comm]] at h
  exact h

/-- Conversely, CircLWE is bounded by fixed-hint KDM plus the same zero-message
side-information LWE term. -/
theorem circularLweAdvantage_le_kdm_add_zeroLwe
    (problem : Problem Secret Challenge Auxiliary)
    (continuation : Continuation Secret Challenge Auxiliary) :
    circularLweAdvantage problem continuation ≤
      kdmAdvantage problem continuation +
        zeroLweAdvantage problem continuation := by
  exact ProbComp.boolDistAdvantage_triangle
    (realGame problem continuation)
    (zeroGame problem continuation)
    (uniformGame problem continuation)

/-- Concrete KDM hardness for a selected continuation class. -/
def KDMHardAgainst (problem : Problem Secret Challenge Auxiliary)
    (allowed : Continuation Secret Challenge Auxiliary → Prop) (bound : ℝ) : Prop :=
  ∀ continuation, allowed continuation → kdmAdvantage problem continuation ≤ bound

/-- Concrete auxiliary-input CircLWE hardness for a selected continuation class. -/
def CircularLWEHardAgainst (problem : Problem Secret Challenge Auxiliary)
    (allowed : Continuation Secret Challenge Auxiliary → Prop) (bound : ℝ) : Prop :=
  ∀ continuation, allowed continuation → circularLweAdvantage problem continuation ≤ bound

/-- Concrete zero-message side-information LWE hardness for a selected continuation class. -/
def ZeroLWEHardAgainst (problem : Problem Secret Challenge Auxiliary)
    (allowed : Continuation Secret Challenge Auxiliary → Prop) (bound : ℝ) : Prop :=
  ∀ continuation, allowed continuation → zeroLweAdvantage problem continuation ≤ bound

/-- CircLWE and zero-message side-information LWE bounds imply fixed-hint KDM security. -/
theorem kdmHardAgainst_of_circularLwe_and_zeroLwe
    (problem : Problem Secret Challenge Auxiliary)
    (allowed : Continuation Secret Challenge Auxiliary → Prop)
    (circularBound zeroBound : ℝ)
    (hCircular : CircularLWEHardAgainst problem allowed circularBound)
    (hZero : ZeroLWEHardAgainst problem allowed zeroBound) :
    KDMHardAgainst problem allowed (circularBound + zeroBound) := by
  intro continuation hallowed
  exact (kdmAdvantage_le_circularLwe_add_zeroLwe problem continuation).trans
    (add_le_add (hCircular continuation hallowed) (hZero continuation hallowed))

/-- Fixed-hint KDM and zero-message side-information LWE bounds imply CircLWE security. -/
theorem circularLweHardAgainst_of_kdm_and_zeroLwe
    (problem : Problem Secret Challenge Auxiliary)
    (allowed : Continuation Secret Challenge Auxiliary → Prop)
    (kdmBound zeroBound : ℝ)
    (hKDM : KDMHardAgainst problem allowed kdmBound)
    (hZero : ZeroLWEHardAgainst problem allowed zeroBound) :
    CircularLWEHardAgainst problem allowed (kdmBound + zeroBound) := by
  intro continuation hallowed
  exact (circularLweAdvantage_le_kdm_add_zeroLwe problem continuation).trans
    (add_le_add (hKDM continuation hallowed) (hZero continuation hallowed))

end Games

end FormalProof4FHE.LWE.AuxiliaryInput
