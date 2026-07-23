/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.DiscreteGaussianSampler
import FormalProof4FHE.TFHE.ScalarSecretRandomization

/-!
# Exactly Symmetric Compiled Discrete-Gaussian Samplers

A finite ticket table may approximate a centered modular discrete Gaussian without being exactly
invariant under negation.  Native TFHE's complementary-control normalization needs exact
negation symmetry, while its smudging estimates need only the existing Gaussian approximation
certificate.

This file separates those requirements.  `TicketNegationSymmetric` is a finite, checkable count
condition on an existing scalar certificate.  It implies exact negation symmetry of both the
scalar sampler and its coefficientwise ring lift.  Thus callers may use one proof-carrying table
for exact message-one normalization and for the already certified Gaussian shift bounds.
-/

open OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.DiscreteGaussianSampler

/-- Every residue and its additive inverse occur equally often in the compiled ticket table. -/
def TicketNegationSymmetric
    {q : ℕ} [NeZero q] {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : ScalarCertificate q alpha halpha) : Prop :=
  ∀ residue : ZMod q,
    certificate.table.tickets.toList.count (-residue) =
      certificate.table.tickets.toList.count residue

/-- A symmetric ticket count gives exact negation symmetry of the executable scalar sampler. -/
theorem scalarSampler_negationSymmetric
    {q : ℕ} [NeZero q] {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : ScalarCertificate q alpha halpha)
    (hsymmetric : TicketNegationSymmetric certificate) :
    Native.ScalarSecretRandomization.NegationSymmetric
      (scalarSampler certificate) := by
  intro residue
  unfold scalarSampler
  rw [FinitePMFCompiler.TicketTable.probOutput_sampler,
    FinitePMFCompiler.TicketTable.probOutput_sampler, hsymmetric residue]

/-- Rebuilding a vector-backed polynomial from its coefficients is injective. -/
theorem polyOfPi_injective {Coefficient : Type} {degree : ℕ} :
    Function.Injective
      (LatticeCrypto.Poly.ofPi : (Fin degree → Coefficient) →
        LatticeCrypto.Poly Coefficient degree) := by
  intro left right heq
  rw [← LatticeCrypto.Poly.toPi_ofPi left,
    ← LatticeCrypto.Poly.toPi_ofPi right, heq]

/-- Coefficient extraction commutes with negation in the executable negacyclic carrier. -/
theorem polyToPi_neg {q degree : ℕ} (error : RLWE.Rq q degree) :
    LatticeCrypto.Poly.toPi (-error) =
      -LatticeCrypto.Poly.toPi error := by
  funext coefficient
  simpa [RLWE.negacyclicRing, LatticeCrypto.Poly.toPi,
      LatticeCrypto.vectorNegacyclicRing_backend,
      LatticeCrypto.vectorBackend, Vector.get] using
    (LatticeCrypto.NegacyclicRing.coeff_neg
      (RLWE.negacyclicRing q degree) error coefficient)

/-- The coefficientwise lift of a symmetric scalar ticket table is exactly negation symmetric
as a ring-error sampler. -/
theorem ringSampler_negationSymmetric
    {q : ℕ} [NeZero q] (degree : ℕ)
    {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : ScalarCertificate q alpha halpha)
    (hsymmetric : TicketNegationSymmetric certificate) :
    Native.ScalarSecretRandomization.NegationSymmetric
      (ringSampler degree certificate) := by
  intro error
  let coefficients := ProbComp.sampleIID degree (scalarSampler certificate)
  have hscalar := scalarSampler_negationSymmetric certificate hsymmetric
  unfold ringSampler
  calc
    Pr[= -error | LatticeCrypto.Poly.ofPi <$> coefficients] =
        Pr[= LatticeCrypto.Poly.toPi (-error) | coefficients] := by
      simpa [coefficients] using
        (probOutput_map_injective coefficients
          (f := LatticeCrypto.Poly.ofPi)
          (polyOfPi_injective (Coefficient := ZMod q) (degree := degree))
          (LatticeCrypto.Poly.toPi (-error)))
    _ = ∏ coefficient,
        Pr[= (LatticeCrypto.Poly.toPi (-error)) coefficient |
          scalarSampler certificate] :=
      FormalProof4FHE.SharedRandomness.probOutput_sampleIID degree
        (scalarSampler certificate) (LatticeCrypto.Poly.toPi (-error))
    _ = ∏ coefficient,
        Pr[= (LatticeCrypto.Poly.toPi error) coefficient |
          scalarSampler certificate] := by
      apply Finset.prod_congr rfl
      intro coefficient _
      rw [polyToPi_neg]
      exact hscalar ((LatticeCrypto.Poly.toPi error) coefficient)
    _ = Pr[= LatticeCrypto.Poly.toPi error | coefficients] :=
      (FormalProof4FHE.SharedRandomness.probOutput_sampleIID degree
        (scalarSampler certificate) (LatticeCrypto.Poly.toPi error)).symm
    _ = Pr[= error | LatticeCrypto.Poly.ofPi <$> coefficients] := by
      simpa [coefficients] using
        (probOutput_map_injective coefficients
          (f := LatticeCrypto.Poly.ofPi)
          (polyOfPi_injective (Coefficient := ZMod q) (degree := degree))
          (LatticeCrypto.Poly.toPi error)).symm

end FormalProof4FHE.TFHE.DiscreteGaussianSampler
