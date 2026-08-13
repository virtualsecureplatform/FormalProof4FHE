/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.SquareZeroQuadraticCircularRq

/-!
# Exact BFV quadratic-circular normal form

This file formalizes the compatible core of
`sketch/bfv_quadratic_circular_security.tex`.

For a radix gadget `(1, B, ..., B^levels)`, adjacent differencing sends a vector `x` to

`x 0, x 1 - B*x 0, ..., x levels - B*x (levels-1)`.

The map is an explicit equivalence over every ring.  Applying it simultaneously to the masks and
bodies of a stock same-key BFV relinearization key cancels every quadratic gadget coordinate
except the first.  The resulting rows are linear in the secret, with correlated error source

`s^2 + e_0, e_1 - B*e_0, ..., e_levels - B*e_(levels-1)`.

The real and uniform games are transported exactly in both directions.  Thus the stock
quadratic-circular advantage is equal, not merely bounded, to the decisional correlated-HNF
advantage for this source.  Combining this equality with the zero-message ordinary-RLWE endpoint
gives the standard two-hop KDM bound.

No hardness theorem for the correlated source is asserted.  In particular, search M-LWE for a
bounded entropic source does not by itself prove the decisional pseudorandomness used here.
-/

open Matrix OracleComp

namespace FormalProof4FHE.RLWE.BFVQuadraticCircularSecurity

noncomputable section

variable {R : Type} [CommRing R]

/-- A nonempty radix-gadget batch. -/
abbrev Batch (R : Type) (levels : ℕ) :=
  SquareZeroQuadraticCircular.Vector R (Fin (levels + 1))

/-- Public mask/body batch. -/
abbrev Transcript (R : Type) (levels : ℕ) :=
  SquareZeroQuadraticCircular.Transcript R (Fin (levels + 1))

/-! ## Adjacent differencing -/

/-- Lower-bidiagonal adjacent-difference map with diagonal one and subdiagonal `-B`. -/
def adjacentTransform (levels : ℕ) (radix : R)
    (value : Batch R levels) : Batch R levels :=
  fun row ↦ Fin.cases (value 0)
    (fun previous ↦ value previous.succ - radix * value previous.castSucc) row

/-- Recursive inverse of adjacent differencing. -/
def adjacentRecover (levels : ℕ) (radix : R)
    (value : Batch R levels) : Batch R levels :=
  fun row ↦ Fin.induction (value 0)
    (fun previous recovered ↦ value previous.succ + radix * recovered) row

@[simp]
theorem adjacentTransform_zero (levels : ℕ) (radix : R) (value : Batch R levels) :
    adjacentTransform levels radix value 0 = value 0 := by
  simp [adjacentTransform]

@[simp]
theorem adjacentTransform_succ (levels : ℕ) (radix : R)
    (value : Batch R levels) (previous : Fin levels) :
    adjacentTransform levels radix value previous.succ =
      value previous.succ - radix * value previous.castSucc := by
  simp [adjacentTransform]

@[simp]
theorem adjacentRecover_zero (levels : ℕ) (radix : R) (value : Batch R levels) :
    adjacentRecover levels radix value 0 = value 0 := by
  simp [adjacentRecover]

@[simp]
theorem adjacentRecover_succ (levels : ℕ) (radix : R)
    (value : Batch R levels) (previous : Fin levels) :
    adjacentRecover levels radix value previous.succ =
      value previous.succ + radix *
        adjacentRecover levels radix value previous.castSucc := by
  simp [adjacentRecover]

theorem adjacentTransform_recover (levels : ℕ) (radix : R)
    (value : Batch R levels) :
    adjacentTransform levels radix (adjacentRecover levels radix value) = value := by
  funext row
  refine Fin.cases ?_ (fun previous ↦ ?_) row
  · simp
  · simp

theorem adjacentRecover_transform (levels : ℕ) (radix : R)
    (value : Batch R levels) :
    adjacentRecover levels radix (adjacentTransform levels radix value) = value := by
  funext row
  induction row using Fin.induction with
  | zero => simp
  | succ previous ih =>
      rw [adjacentRecover_succ, adjacentTransform_succ, ih]
      ring

/-- Adjacent differencing is an explicit determinant-one equivalence. -/
def adjacentEquiv (levels : ℕ) (radix : R) :
    Batch R levels ≃ Batch R levels where
  toFun := adjacentTransform levels radix
  invFun := adjacentRecover levels radix
  left_inv := adjacentRecover_transform levels radix
  right_inv := adjacentTransform_recover levels radix

/-- Apply adjacent differencing to masks and bodies simultaneously. -/
def transcriptEquiv (levels : ℕ) (radix : R) :
    Transcript R levels ≃ Transcript R levels :=
  (adjacentEquiv levels radix).prodCongr (adjacentEquiv levels radix)

/-- A public-key row together with the relinearization-key batch. -/
abbrev JointTranscript (R : Type) (levels : ℕ) :=
  (R × R) × Transcript R levels

/-- Leave the public-key row unchanged and adjacent-difference only the relinearization rows. -/
def jointTranscriptEquiv (levels : ℕ) (radix : R) :
    JointTranscript R levels ≃ JointTranscript R levels :=
  (Equiv.refl (R × R)).prodCongr (transcriptEquiv levels radix)

/-! ## Stock and correlated-HNF rows -/

/-- Radix gadget weight `B^i`. -/
def radixWeight {levels : ℕ} (radix : R) (row : Fin (levels + 1)) : R :=
  radix ^ row.val

/-- Stock positive-sign BFV quadratic-circular transcript. -/
def stockTranscript (levels : ℕ) (radix secret : R)
    (error mask : Batch R levels) : Transcript R levels :=
  (mask, fun row ↦
    mask row * secret + error row + radixWeight radix row * secret ^ 2)

/-- Error source after adjacent gadget cancellation. -/
def correlatedError (levels : ℕ) (radix secret : R)
    (error : Batch R levels) : Batch R levels :=
  fun row ↦ Fin.cases (secret ^ 2 + error 0)
    (fun previous ↦ error previous.succ - radix * error previous.castSucc) row

@[simp]
theorem correlatedError_zero (levels : ℕ) (radix secret : R)
    (error : Batch R levels) :
    correlatedError levels radix secret error 0 = secret ^ 2 + error 0 := by
  simp [correlatedError]

@[simp]
theorem correlatedError_succ (levels : ℕ) (radix secret : R)
    (error : Batch R levels) (previous : Fin levels) :
    correlatedError levels radix secret error previous.succ =
      error previous.succ - radix * error previous.castSucc := by
  simp [correlatedError]

/-- Linear HNF transcript with the explicit correlated source. -/
def correlatedHNFTranscript (levels : ℕ) (radix secret : R)
    (error mask : Batch R levels) : Transcript R levels :=
  (mask, fun row ↦ mask row * secret + correlatedError levels radix secret error row)

/-- Exact cancellation of every radix gadget coordinate except the first. -/
theorem adjacent_stockTranscript (levels : ℕ) (radix secret : R)
    (error mask : Batch R levels) :
    transcriptEquiv levels radix (stockTranscript levels radix secret error mask) =
      correlatedHNFTranscript levels radix secret error
        (adjacentTransform levels radix mask) := by
  apply Prod.ext
  · rfl
  · funext row
    refine Fin.cases ?_ (fun previous ↦ ?_) row
    · change
        adjacentTransform levels radix
            (fun row ↦ mask row * secret + error row +
              radixWeight radix row * secret ^ 2) 0 =
          adjacentTransform levels radix mask 0 * secret +
            correlatedError levels radix secret error 0
      simp [radixWeight]
      ring
    · change
        adjacentTransform levels radix
            (fun row ↦ mask row * secret + error row +
              radixWeight radix row * secret ^ 2) previous.succ =
          adjacentTransform levels radix mask previous.succ * secret +
            correlatedError levels radix secret error previous.succ
      simp [radixWeight, pow_succ]
      ring

/-- Stock public key and same-key quadratic relinearization key for fixed randomness. -/
def jointStockTranscript (levels : ℕ) (radix secret publicMask publicError : R)
    (error mask : Batch R levels) : JointTranscript R levels :=
  ((publicMask, publicMask * secret + publicError),
    stockTranscript levels radix secret error mask)

/-- The matching public key and correlated-HNF normal form. -/
def jointCorrelatedHNFTranscript
    (levels : ℕ) (radix secret publicMask publicError : R)
    (error mask : Batch R levels) : JointTranscript R levels :=
  ((publicMask, publicMask * secret + publicError),
    correlatedHNFTranscript levels radix secret error mask)

/-- The adjacent transform leaves the public-key row literally unchanged and performs the same
exact gadget cancellation on the relinearization-key rows. -/
theorem joint_adjacent_stockTranscript
    (levels : ℕ) (radix secret publicMask publicError : R)
    (error mask : Batch R levels) :
    jointTranscriptEquiv levels radix
        (jointStockTranscript levels radix secret publicMask publicError error mask) =
      jointCorrelatedHNFTranscript levels radix secret publicMask publicError error
        (adjacentTransform levels radix mask) := by
  change
    ((publicMask, publicMask * secret + publicError),
        transcriptEquiv levels radix (stockTranscript levels radix secret error mask)) =
      ((publicMask, publicMask * secret + publicError),
        correlatedHNFTranscript levels radix secret error
          (adjacentTransform levels radix mask))
  rw [adjacent_stockTranscript]

/-! ## Entropy-preserving source equivalence -/

/-- First-coordinate square spike. -/
def squareSpike (levels : ℕ) (secret : R) : Batch R levels :=
  fun row ↦ Fin.cases (secret ^ 2) (fun _previous ↦ 0) row

theorem correlatedError_eq_adjacent_add_spike
    (levels : ℕ) (radix secret : R) (error : Batch R levels) :
    correlatedError levels radix secret error =
      adjacentTransform levels radix error + squareSpike levels secret := by
  funext row
  refine Fin.cases ?_ (fun previous ↦ ?_) row <;>
    simp [squareSpike]
  ring

/-- The original independent `(secret,error)` coordinates and correlated-HNF source coordinates
are in explicit bijection. -/
def correlatedSourceEquiv (levels : ℕ) (radix : R) :
    (R × Batch R levels) ≃ (R × Batch R levels) where
  toFun source :=
    (source.1, correlatedError levels radix source.1 source.2)
  invFun source :=
    (source.1, (adjacentEquiv levels radix).symm
      (source.2 - squareSpike levels source.1))
  left_inv source := by
    rcases source with ⟨secret, error⟩
    apply Prod.ext
    · rfl
    · change
        (adjacentEquiv levels radix).symm
            (correlatedError levels radix secret error - squareSpike levels secret) = error
      rw [correlatedError_eq_adjacent_add_spike]
      have hSub :
          adjacentTransform levels radix error + squareSpike levels secret -
              squareSpike levels secret = adjacentTransform levels radix error := by
        funext row
        simp
      rw [hSub]
      change (adjacentEquiv levels radix).symm
          (adjacentEquiv levels radix error) = error
      exact (adjacentEquiv levels radix).symm_apply_apply error
  right_inv source := by
    rcases source with ⟨secret, error⟩
    apply Prod.ext
    · rfl
    · change
        correlatedError levels radix secret
            ((adjacentEquiv levels radix).symm
              (error - squareSpike levels secret)) = error
      rw [correlatedError_eq_adjacent_add_spike]
      change
        adjacentEquiv levels radix
            ((adjacentEquiv levels radix).symm
              (error - squareSpike levels secret)) + squareSpike levels secret = error
      rw [Equiv.apply_symm_apply]
      funext row
      simp

/-- Mapping any joint source sampler through the source equivalence preserves every point mass.
This is the exact finite statement behind preservation of min-entropy. -/
theorem correlatedSource_probOutput
    (levels : ℕ) (radix : R)
    (sourceSampler : ProbComp (R × Batch R levels))
    (source : R × Batch R levels) :
    Pr[= correlatedSourceEquiv levels radix source |
        correlatedSourceEquiv levels radix <$> sourceSampler] =
      Pr[= source | sourceSampler] := by
  exact probOutput_map_injective sourceSampler
    (correlatedSourceEquiv levels radix).injective source

/-- With a public-key error appended, the original `(secret, publicError, errors)` source and its
correlated-HNF coordinates are still explicitly equivalent. -/
def jointCorrelatedSourceEquiv (levels : ℕ) (radix : R) :
    ((R × R) × Batch R levels) ≃ ((R × R) × Batch R levels) where
  toFun source :=
    (source.1, correlatedError levels radix source.1.1 source.2)
  invFun source :=
    (source.1, (adjacentEquiv levels radix).symm
      (source.2 - squareSpike levels source.1.1))
  left_inv source := by
    rcases source with ⟨⟨secret, publicError⟩, error⟩
    apply Prod.ext
    · rfl
    · change
        (adjacentEquiv levels radix).symm
            (correlatedError levels radix secret error - squareSpike levels secret) = error
      rw [correlatedError_eq_adjacent_add_spike]
      have hSub :
          adjacentTransform levels radix error + squareSpike levels secret -
              squareSpike levels secret = adjacentTransform levels radix error := by
        funext row
        simp
      rw [hSub]
      exact (adjacentEquiv levels radix).symm_apply_apply error
  right_inv source := by
    rcases source with ⟨⟨secret, publicError⟩, error⟩
    apply Prod.ext
    · rfl
    · change
        correlatedError levels radix secret
            ((adjacentEquiv levels radix).symm
              (error - squareSpike levels secret)) = error
      rw [correlatedError_eq_adjacent_add_spike]
      change
        adjacentEquiv levels radix
            ((adjacentEquiv levels radix).symm
              (error - squareSpike levels secret)) + squareSpike levels secret = error
      rw [Equiv.apply_symm_apply]
      funext row
      simp

/-- The joint source equivalence, including the public-key error, preserves every point mass. -/
theorem jointCorrelatedSource_probOutput
    (levels : ℕ) (radix : R)
    (sourceSampler : ProbComp ((R × R) × Batch R levels))
    (source : (R × R) × Batch R levels) :
    Pr[= jointCorrelatedSourceEquiv levels radix source |
        jointCorrelatedSourceEquiv levels radix <$> sourceSampler] =
      Pr[= source | sourceSampler] := by
  exact probOutput_map_injective sourceSampler
    (jointCorrelatedSourceEquiv levels radix).injective source

/-! ## Complete finite games -/

/-- Stock quadratic-circular sampler. -/
def stockSampler [Fintype R] [SampleableType R]
    (levels : ℕ) (radix : R)
    (secretSampler : ProbComp R) (errorSampler : ProbComp (Batch R levels)) :
    ProbComp (Transcript R levels) := do
  let mask ← $ᵗ (SquareZeroQuadraticCircular.Vector R (Fin (levels + 1)))
  let secret ← secretSampler
  let error ← errorSampler
  return stockTranscript levels radix secret error mask

/-- Correlated-HNF sampler generated from the same independent secret/error source. -/
def correlatedHNFSampler [Fintype R] [SampleableType R]
    (levels : ℕ) (radix : R)
    (secretSampler : ProbComp R) (errorSampler : ProbComp (Batch R levels)) :
    ProbComp (Transcript R levels) := do
  let mask ← $ᵗ (SquareZeroQuadraticCircular.Vector R (Fin (levels + 1)))
  let secret ← secretSampler
  let error ← errorSampler
  return correlatedHNFTranscript levels radix secret error mask

/-- Matching zero-message RLWE sampler. -/
def zeroSampler [Fintype R] [SampleableType R]
    (levels : ℕ)
    (secretSampler : ProbComp R) (errorSampler : ProbComp (Batch R levels)) :
    ProbComp (Transcript R levels) := do
  let mask ← $ᵗ (SquareZeroQuadraticCircular.Vector R (Fin (levels + 1)))
  let secret ← secretSampler
  let error ← errorSampler
  return (mask, fun row ↦ mask row * secret + error row)

/-- Fully uniform endpoint. -/
def uniformSampler [Fintype R] [SampleableType R]
    (levels : ℕ) : ProbComp (Transcript R levels) :=
  $ᵗ (SquareZeroQuadraticCircular.Transcript R (Fin (levels + 1)))

/-- The zero-message sampler has exactly the distribution of the repository's ordinary
common-secret batch-LWE problem (and is rank-one RLWE when `R` is an `Rq` carrier).  The statement
is distributional because Lean has two extensionally identical finite-function sampling
instances. -/
theorem zeroSampler_baseProblem_evalDist
    [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ)
    (secretSampler : ProbComp R) (errorSampler : ProbComp (Batch R levels)) :
    evalDist (zeroSampler levels secretSampler errorSampler) =
      evalDist (LearningWithErrors.distr
        (SquareZeroQuadraticCircular.baseProblem
          (Row := Fin (levels + 1)) secretSampler errorSampler)) := by
  have hMask :
      evalDist ($ᵗ (SquareZeroQuadraticCircular.Vector R (Fin (levels + 1)))) =
        evalDist
          (SquareZeroQuadraticCircular.baseProblem
            (Row := Fin (levels + 1)) secretSampler errorSampler).sampleChallenge := by
    apply evalDist_ext
    intro mask
    simp only [SquareZeroQuadraticCircular.baseProblem, probOutput_uniformSample]
  have hBind := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hMask
    (fun mask ↦ secretSampler >>= fun secret ↦
      errorSampler >>= fun error ↦ pure (mask, fun row ↦ mask row * secret + error row))
  have hBody (mask : Batch R levels) (secret : R) (error : Batch R levels) :
      (fun row ↦ mask row * secret) + error =
        (fun row ↦ mask row * secret + error row) := by
    funext row
    rfl
  simpa only [zeroSampler, LearningWithErrors.distr,
    SquareZeroQuadraticCircular.baseProblem, bind_assoc, pure_bind, hBody] using hBind

/-- Adjacent differencing maps a stock real batch exactly to its correlated-HNF normal form. -/
theorem stock_to_correlatedHNF_evalDist
    [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (radix : R)
    (secretSampler : ProbComp R) (errorSampler : ProbComp (Batch R levels)) :
    evalDist (transcriptEquiv levels radix <$>
      stockSampler levels radix secretSampler errorSampler) =
    evalDist (correlatedHNFSampler levels radix secretSampler errorSampler) := by
  have hMask :
      evalDist (adjacentTransform levels radix <$>
        ($ᵗ (SquareZeroQuadraticCircular.Vector R (Fin (levels + 1))))) =
        evalDist
          ($ᵗ (SquareZeroQuadraticCircular.Vector R (Fin (levels + 1)))) :=
    evalDist_map_bijective_uniform_cross
      (α := Batch R levels) (β := Batch R levels)
      (adjacentTransform levels radix) (adjacentEquiv levels radix).bijective
  have hBind := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hMask
    (fun mask ↦ secretSampler >>= fun secret ↦
      errorSampler >>= fun error ↦
        pure (correlatedHNFTranscript levels radix secret error mask))
  simpa only [stockSampler, correlatedHNFSampler, map_eq_bind_pure_comp,
    Function.comp_def, bind_assoc, pure_bind, adjacent_stockTranscript] using hBind

/-- The complete transcript transform preserves the uniform endpoint exactly. -/
theorem transcriptEquiv_uniform_evalDist
    [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (radix : R) :
    evalDist (transcriptEquiv levels radix <$> uniformSampler (R := R) levels) =
      evalDist (uniformSampler (R := R) levels) := by
  exact evalDist_map_bijective_uniform_cross
    (α := Transcript R levels) (β := Transcript R levels)
    (transcriptEquiv levels radix) (transcriptEquiv levels radix).bijective

/-- The public-key-extended transcript transform also preserves the fully uniform endpoint
exactly. -/
theorem jointTranscriptEquiv_uniform_evalDist
    [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (radix : R) :
    evalDist (jointTranscriptEquiv levels radix <$>
      ($ᵗ (JointTranscript R levels))) =
      evalDist ($ᵗ (JointTranscript R levels)) := by
  exact evalDist_map_bijective_uniform_cross
    (α := JointTranscript R levels) (β := JointTranscript R levels)
    (jointTranscriptEquiv levels radix) (jointTranscriptEquiv levels radix).bijective

/-- A batch distinguisher. -/
abbrev Distinguisher (R : Type) (levels : ℕ) :=
  Transcript R levels → ProbComp Bool

/-- Stock real-versus-uniform quadratic-circular advantage. -/
noncomputable def stockUniformAdvantage
    [Fintype R] [SampleableType R]
    (levels : ℕ) (radix : R)
    (secretSampler : ProbComp R) (errorSampler : ProbComp (Batch R levels))
    (adversary : Distinguisher R levels) : ℝ :=
  (stockSampler levels radix secretSampler errorSampler >>= adversary).boolDistAdvantage
    (uniformSampler (R := R) levels >>= adversary)

/-- Correlated-HNF real-versus-uniform advantage. -/
noncomputable def correlatedHNFAdvantage
    [Fintype R] [SampleableType R]
    (levels : ℕ) (radix : R)
    (secretSampler : ProbComp R) (errorSampler : ProbComp (Batch R levels))
    (adversary : Distinguisher R levels) : ℝ :=
  (correlatedHNFSampler levels radix secretSampler errorSampler >>= adversary).boolDistAdvantage
    (uniformSampler (R := R) levels >>= adversary)

/-- Forward normal-form reduction. -/
def forwardDistinguisher (levels : ℕ) (radix : R)
    (adversary : Distinguisher R levels) : Distinguisher R levels :=
  fun transcript ↦ adversary (transcriptEquiv levels radix transcript)

/-- Reverse normal-form reduction. -/
def reverseDistinguisher (levels : ℕ) (radix : R)
    (adversary : Distinguisher R levels) : Distinguisher R levels :=
  fun transcript ↦ adversary ((transcriptEquiv levels radix).symm transcript)

/-- Every correlated-HNF distinguisher has exactly the same advantage against stock BFV after
the public adjacent-difference transform. -/
theorem correlatedHNFAdvantage_eq_stock_forward
    [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (radix : R)
    (secretSampler : ProbComp R) (errorSampler : ProbComp (Batch R levels))
    (adversary : Distinguisher R levels) :
    correlatedHNFAdvantage levels radix secretSampler errorSampler adversary =
      stockUniformAdvantage levels radix secretSampler errorSampler
        (forwardDistinguisher levels radix adversary) := by
  have hReal := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (stock_to_correlatedHNF_evalDist levels radix secretSampler errorSampler) adversary
  have hUniform := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (transcriptEquiv_uniform_evalDist (R := R) levels radix) adversary
  unfold correlatedHNFAdvantage stockUniformAdvantage forwardDistinguisher
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] at hReal hUniform
  unfold ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp hReal true, evalDist_ext_iff.mp hUniform true]

/-- Conversely, every stock-BFV distinguisher has exactly the same advantage against the
correlated-HNF game after applying the inverse public transform. -/
theorem stockUniformAdvantage_eq_correlatedHNF_reverse
    [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (radix : R)
    (secretSampler : ProbComp R) (errorSampler : ProbComp (Batch R levels))
    (adversary : Distinguisher R levels) :
    stockUniformAdvantage levels radix secretSampler errorSampler adversary =
      correlatedHNFAdvantage levels radix secretSampler errorSampler
        (reverseDistinguisher levels radix adversary) := by
  rw [correlatedHNFAdvantage_eq_stock_forward]
  congr 1
  funext transcript
  simp [forwardDistinguisher, reverseDistinguisher]

/-! ## Conditional one-key quadratic-KDM theorem -/

/-- Stock real-versus-zero one-key quadratic-KDM advantage. -/
noncomputable def stockKDMAdvantage
    [Fintype R] [SampleableType R]
    (levels : ℕ) (radix : R)
    (secretSampler : ProbComp R) (errorSampler : ProbComp (Batch R levels))
    (adversary : Distinguisher R levels) : ℝ :=
  (stockSampler levels radix secretSampler errorSampler >>= adversary).boolDistAdvantage
    (zeroSampler levels secretSampler errorSampler >>= adversary)

/-- Ordinary zero-message RLWE real-versus-uniform endpoint. -/
noncomputable def zeroUniformAdvantage
    [Fintype R] [SampleableType R]
    (levels : ℕ)
    (secretSampler : ProbComp R) (errorSampler : ProbComp (Batch R levels))
    (adversary : Distinguisher R levels) : ℝ :=
  (zeroSampler levels secretSampler errorSampler >>= adversary).boolDistAdvantage
    (uniformSampler (R := R) levels >>= adversary)

/-- The named zero endpoint is exactly the ordinary common-secret batch-LWE/RLWE advantage of the
same adversary. -/
theorem zeroUniformAdvantage_eq_baseProblem
    [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ)
    (secretSampler : ProbComp R) (errorSampler : ProbComp (Batch R levels))
    (adversary : Distinguisher R levels) :
    zeroUniformAdvantage levels secretSampler errorSampler adversary =
      LearningWithErrors.advantage
        (SquareZeroQuadraticCircular.baseProblem
          (Row := Fin (levels + 1)) secretSampler errorSampler) adversary := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold zeroUniformAdvantage LearningWithErrors.game0 LearningWithErrors.game1
  have hReal := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (zeroSampler_baseProblem_evalDist levels secretSampler errorSampler) adversary
  have hBaseUniform := SquareZeroQuadraticCircular.base_uniformDistr_evalDist
    (Row := Fin (levels + 1)) secretSampler errorSampler
  have hCanonical :
      evalDist (@uniformSample
        (SquareZeroQuadraticCircular.Transcript R (Fin (levels + 1)))
        (@instSampleableTypeProd
          (SquareZeroQuadraticCircular.Vector R (Fin (levels + 1)))
          (SquareZeroQuadraticCircular.Vector R (Fin (levels + 1)))
          instSampleableTypePiFintype instSampleableTypePiFintype)) =
        evalDist (uniformSampler (R := R) levels) := by
    apply evalDist_ext
    intro output
    simp only [uniformSampler, probOutput_uniformSample]
  have hUniform :
      evalDist (LearningWithErrors.uniformDistr
        (SquareZeroQuadraticCircular.baseProblem
          (Row := Fin (levels + 1)) secretSampler errorSampler) >>= adversary) =
        evalDist (uniformSampler (R := R) levels >>= adversary) := by
    exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
      (hBaseUniform.trans hCanonical) adversary
  unfold ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp hReal true, ← evalDist_ext_iff.mp hUniform true]

/-- Conditional security of the stock relinearization key: the exact correlated-HNF term plus
the ordinary zero-message RLWE term. -/
theorem stockKDMAdvantage_le_correlatedHNF_add_zero
    [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (radix : R)
    (secretSampler : ProbComp R) (errorSampler : ProbComp (Batch R levels))
    (adversary : Distinguisher R levels) :
    stockKDMAdvantage levels radix secretSampler errorSampler adversary ≤
      correlatedHNFAdvantage levels radix secretSampler errorSampler
        (reverseDistinguisher levels radix adversary) +
      zeroUniformAdvantage levels secretSampler errorSampler adversary := by
  have hTriangle := ProbComp.boolDistAdvantage_triangle
    (stockSampler levels radix secretSampler errorSampler >>= adversary)
    (uniformSampler (R := R) levels >>= adversary)
    (zeroSampler levels secretSampler errorSampler >>= adversary)
  rw [show
      (uniformSampler (R := R) levels >>= adversary).boolDistAdvantage
          (zeroSampler levels secretSampler errorSampler >>= adversary) =
        (zeroSampler levels secretSampler errorSampler >>= adversary).boolDistAdvantage
          (uniformSampler (R := R) levels >>= adversary) by
      unfold ProbComp.boolDistAdvantage
      rw [abs_sub_comm]] at hTriangle
  calc
    stockKDMAdvantage levels radix secretSampler errorSampler adversary ≤
        stockUniformAdvantage levels radix secretSampler errorSampler adversary +
          zeroUniformAdvantage levels secretSampler errorSampler adversary := hTriangle
    _ = _ := congrArg₂ (fun left right ↦ left + right)
      (stockUniformAdvantage_eq_correlatedHNF_reverse levels radix secretSampler
        errorSampler adversary) rfl

/-! ## Relinearization and auxiliary algebra from the manuscript -/

/-- The noiseless scalar discriminant is always a square.  Over an odd finite field with nonzero
weight this yields the quadratic-residuosity distinguisher from the manuscript; the probability
count is field-specific, while this identity is valid over every commutative ring. -/
theorem noiselessDiscriminant
    (secret mask weight : R) :
    mask ^ 2 + 4 * weight * (-mask * secret + weight * secret ^ 2) =
      (mask - 2 * weight * secret) ^ 2 := by
  ring

/-- Rewriting a quadratic row as a linear row requires shifting the published mask by the hidden
secret.  This identity records the algebra and, deliberately, does not present that hidden shift
as a public reduction. -/
theorem secretDependentMaskShift
    (secret mask error weight : R) :
    mask * secret + error + weight * secret ^ 2 =
      (mask + weight * secret) * secret + error := by
  ring

/-- Standard stock BFV relinearization preserves the quadratic phase and adds exactly the
gadget-weighted evaluation-key errors. -/
theorem relinearization_phase
    {Row : Type}
    [Fintype Row]
    (weight digit mask error : Row → R) (secret c0 c1 c2 : R)
    (hDecomposition : c2 = ∑ row, digit row * weight row) :
    let body := fun row ↦ mask row * secret + error row + weight row * secret ^ 2
    (c0 + ∑ row, digit row * body row) +
        (c1 - ∑ row, digit row * mask row) * secret =
      c0 + c1 * secret + c2 * secret ^ 2 +
        ∑ row, digit row * error row := by
  dsimp only
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [show (∑ row, digit row * (mask row * secret)) =
      (∑ row, digit row * mask row) * secret by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro row _
        ring]
  rw [show (∑ row, digit row * (weight row * secret ^ 2)) =
      (∑ row, digit row * weight row) * secret ^ 2 by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro row _
        ring]
  rw [hDecomposition]
  ring

/-- Complete-square identity.  It is exact, but changes the target error from `e` to
`e - d*f^2`. -/
theorem completeSquare
    (secret mask error alpha hintError coefficient : R) :
    let hint := alpha * secret + hintError
    let weight := coefficient * alpha ^ 2
    let targetMask := mask - 2 * coefficient * alpha * hint
    mask * secret + error - coefficient * hint ^ 2 =
      targetMask * secret + weight * secret ^ 2 +
        (error - coefficient * hintError ^ 2) := by
  dsimp only
  ring

/-- Exact two-hint square-leakage relation. -/
theorem squareLeakageDifference
    (secret firstHint secondHint firstSquareNoise secondSquareNoise : R) :
    let firstLeak := firstHint ^ 2 - (firstHint - secret) ^ 2 - firstSquareNoise
    let secondLeak := secondHint ^ 2 - (secondHint - secret) ^ 2 - secondSquareNoise
    firstLeak - secondLeak =
      2 * (firstHint - secondHint) * secret -
        (firstSquareNoise - secondSquareNoise) := by
  dsimp only
  ring

/-- With exact square leakage and a unit difference coefficient, the secret is recovered
algebraically. -/
theorem recoverSecret_of_exactSquareLeakage
    (secret firstHint secondHint : R)
    (differenceUnit : Rˣ)
    (hDifference : (differenceUnit : R) = 2 * (firstHint - secondHint)) :
    (↑(differenceUnit⁻¹) : R) *
        ((firstHint ^ 2 - (firstHint - secret) ^ 2) -
          (secondHint ^ 2 - (secondHint - secret) ^ 2)) = secret := by
  have hLeak := squareLeakageDifference secret firstHint secondHint 0 0
  simp only [sub_zero] at hLeak
  rw [hLeak]
  rw [← hDifference]
  simp

end

end FormalProof4FHE.RLWE.BFVQuadraticCircularSecurity
