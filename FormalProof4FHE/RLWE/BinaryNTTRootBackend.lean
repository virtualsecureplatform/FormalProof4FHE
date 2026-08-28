/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.BinaryNTTRegularQH
import Mathlib.Data.Finset.Max

/-!
# Concrete finite-field root and product-unit backends for regular Binary-NTT reductions

The exhaustive square-root routine is intentionally simple and executable.  It closes the
formal backend interface; high-performance implementations may replace it with Tonelli--Shanks
while reusing the same one-line square certificate.
-/

open OracleComp

namespace FormalProof4FHE.RLWE.BinaryNTTSecurity.Regular.RootBackend

noncomputable section

/-- All square roots of one finite-ring value. -/
def squareCandidates {K : Type} [CommRing K] [Fintype K] [DecidableEq K]
    (value : K) : Finset K :=
  Finset.univ.filter fun candidate => candidate ^ 2 = value

/-- Deterministically choose the least square root in the finite enumeration, returning zero for
a nonsquare.  This is executable for concrete `Fintype`/`LinearOrder` instances. -/
def exhaustiveSquareRoot {K : Type}
    [CommRing K] [Fintype K] [DecidableEq K] [LinearOrder K]
    (value : K) : K :=
  if h : (squareCandidates value).Nonempty then
    (squareCandidates value).min' h
  else 0

theorem exhaustiveSquareRoot_sq_of_isSquare
    {K : Type} [CommRing K] [Fintype K] [DecidableEq K] [LinearOrder K]
    (value candidate : K) (hvalue : value = candidate ^ 2) :
    exhaustiveSquareRoot value ^ 2 = value := by
  have hcandidate : candidate ∈ squareCandidates value := by
    simp [squareCandidates, hvalue]
  have hnonempty : (squareCandidates value).Nonempty := ⟨candidate, hcandidate⟩
  rw [exhaustiveSquareRoot, dif_pos hnonempty]
  exact (Finset.mem_filter.mp (Finset.min'_mem _ hnonempty)).2

/-- Certified deterministic coordinate-root implementation for every finite linearly ordered
commutative ring. -/
def exhaustiveCoordinateSquareRoot
    (K : Type) [CommRing K] [Fintype K] [DecidableEq K] [LinearOrder K] :
    Regular.CoordinateSquareRoot K where
  root := exhaustiveSquareRoot
  square value candidate hvalue :=
    exhaustiveSquareRoot_sq_of_isSquare value candidate hvalue

/-- Concrete `ZMod` backend.  Primality is only needed by the later normalization theorem, not by
the exhaustive root search itself. -/
def zmodCoordinateSquareRoot (q : ℕ) [NeZero q] :
    Regular.CoordinateSquareRoot (ZMod q) := by
  letI : LinearOrder (ZMod q) := LinearOrder.lift' ZMod.val (ZMod.val_injective q)
  exact exhaustiveCoordinateSquareRoot (ZMod q)

/-! ## Independent nonzero-coordinate sampling -/

/-- Units of a function ring are exactly functions into coordinate units. -/
def coordinateUnitsEquiv (Slot K : Type) [Monoid K] :
    (Slot → Kˣ) ≃ ((Slot → K)ˣ) :=
  MulEquiv.piUnits.symm.toEquiv

/-- Sample one independent uniform unit in every coordinate and assemble the product-ring unit. -/
def coordinateUnitSampler {Slot K : Type}
    [Monoid K] [SampleableType (Slot → Kˣ)] : ProbComp ((Slot → K)ˣ) :=
  coordinateUnitsEquiv Slot K <$> ($ᵗ (Slot → Kˣ))

/-- Independent uniform coordinate units produce the exact canonical uniform law on product-ring
units. -/
theorem coordinateUnitSampler_uniform_evalDist
    {Slot K : Type} [Finite Slot] [DecidableEq Slot]
    [Monoid K] [Finite K] [DecidableEq K]
    [SampleableType Kˣ] [SampleableType (Slot → Kˣ)]
    [SampleableType ((Slot → K)ˣ)] :
    evalDist (coordinateUnitSampler (Slot := Slot) (K := K)) =
      evalDist ($ᵗ ((Slot → K)ˣ)) :=
  evalDist_map_bijective_uniform_cross
    (α := Slot → Kˣ) (β := (Slot → K)ˣ)
    (coordinateUnitsEquiv Slot K) (coordinateUnitsEquiv Slot K).bijective

/-- End-to-end regular signed-root law instantiated with the exhaustive backend. -/
theorem exhaustive_normalizedSignedRootSampler_uniform_evalDist
    {Slot K : Type} [Fintype Slot] [DecidableEq Slot]
    [Field K] [Fintype K] [DecidableEq K] [LinearOrder K] [SampleableType K]
    (u v secret : Slot → K)
    (htwo : (2 : K) ≠ 0)
    (hhint : v = BinaryNTTSecurity.quadraticHint u secret)
    (hregular : IsUnit (u - 2 * secret)) :
    evalDist
        (Regular.normalizedSignedRootSampler
          (exhaustiveCoordinateSquareRoot K) u v secret) =
      evalDist (($ᵗ (Slot → Bool)) >>= fun signs =>
        pure (Regular.binaryFromSigns (fun _ : Slot => false) signs)) :=
  Regular.normalizedSignedRootSampler_uniform_evalDist
    (exhaustiveCoordinateSquareRoot K) u v secret htwo hhint hregular

end

end FormalProof4FHE.RLWE.BinaryNTTSecurity.Regular.RootBackend
