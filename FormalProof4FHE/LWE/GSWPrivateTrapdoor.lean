/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/
import FormalProof4FHE.LWE.GSWQuadraticPreimage

/-!
# Private gadget-trapdoor quadratic preimages

If A*T=G, signed gadget decompositions and gadget-kernel randomization
give shortness-compatible exact quadratic certificates. T and the resulting
preimages may stay private. These are algebraic correctness results; neither
the joint public-view security nor a challenge-matrix trapdoor simulator is
asserted. The public-builder source reduction cannot be applied to a private
trapdoor merely because the matrix marginal is nearly uniform.
-/

open Matrix

namespace FormalProof4FHE.LWE.GSWPrivateTrapdoor

def preimage {R : Type} [CommRing R] {n m w h : ℕ}
    (trapdoor : Matrix (Fin m) (Fin w) R)
    (decomposition : Matrix (Fin n) (Fin w) R)
    (kernel : Matrix (Fin w) (Fin h) R)
    (randomizer : Matrix (Fin n) (Fin h) R) : Matrix (Fin n) (Fin m) R :=
  (decomposition + randomizer * kernel.transpose) * trapdoor.transpose

theorem preimage_mul_transpose {R : Type} [CommRing R] {n m w h : ℕ}
    (a : Matrix (Fin n) (Fin m) R) (g : Matrix (Fin n) (Fin w) R)
    (trapdoor : Matrix (Fin m) (Fin w) R)
    (decomposition : Matrix (Fin n) (Fin w) R)
    (kernel : Matrix (Fin w) (Fin h) R)
    (randomizer : Matrix (Fin n) (Fin h) R)
    (htrapdoor : a * trapdoor = g) (hkernel : g * kernel = 0) :
    preimage trapdoor decomposition kernel randomizer * a.transpose =
      decomposition * g.transpose := by
  unfold preimage
  rw [Matrix.mul_assoc, ← Matrix.transpose_mul, htrapdoor, Matrix.add_mul]
  have hz : (randomizer * kernel.transpose) * g.transpose = 0 := by
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hkernel]
    simp
  rw [hz, add_zero]

theorem certificate {R : Type} [CommRing R] {n m w h : ℕ}
    (a : Matrix (Fin n) (Fin m) R) (g : Matrix (Fin n) (Fin w) R)
    (trapdoor : Matrix (Fin m) (Fin w) R)
    (decomposition : Matrix (Fin n) (Fin w) R)
    (kernel : Matrix (Fin w) (Fin h) R)
    (randomizer : Matrix (Fin n) (Fin h) R)
    (target alternating : Matrix (Fin n) (Fin n) R)
    (htrapdoor : a * trapdoor = g) (hkernel : g * kernel = 0)
    (hdecomposition : decomposition * g.transpose = target + alternating - alternating.transpose) :
    preimage trapdoor decomposition kernel randomizer * a.transpose =
      target + alternating - alternating.transpose := by
  rw [preimage_mul_transpose a g trapdoor decomposition kernel randomizer htrapdoor hkernel,
    hdecomposition]

/-- The actual shared residual survives private kernel randomization. -/
theorem projected_body {R : Type} [CommRing R] {n m w h : ℕ}
    (a : Matrix (Fin n) (Fin m) R) (g : Matrix (Fin n) (Fin w) R)
    (trapdoor : Matrix (Fin m) (Fin w) R)
    (decomposition : Matrix (Fin n) (Fin w) R)
    (kernel : Matrix (Fin w) (Fin h) R)
    (randomizer : Matrix (Fin n) (Fin h) R)
    (target alternating : Matrix (Fin n) (Fin n) R)
    (htrapdoor : a * trapdoor = g) (hkernel : g * kernel = 0)
    (hdecomposition : decomposition * g.transpose = target + alternating - alternating.transpose)
    (secret : Fin n → R) (error : Fin m → R) :
    dotProduct secret ((preimage trapdoor decomposition kernel randomizer).mulVec
      (vecMul secret a + error)) =
      dotProduct secret (target.mulVec secret) +
        dotProduct secret ((preimage trapdoor decomposition kernel randomizer).mulVec error) := by
  rw [← mulVec_transpose a secret, mulVec_add, dotProduct_add, mulVec_mulVec]
  rw [GSWQuadraticPreimage.quadratic_eq_of_certificate a
    (preimage trapdoor decomposition kernel randomizer) target alternating
    (certificate a g trapdoor decomposition kernel randomizer target alternating
      htrapdoor hkernel hdecomposition) secret]

/-- Extending an unknown-secret LWE challenge to the gadget-programmed block
requires the additional G-secret term. The identity is not an impossibility
claim about alternative simulators or a security assumption. -/
theorem programmed_source_body {R : Type} [CommRing R] {n m w : ℕ}
    (base : Matrix (Fin n) (Fin m) R) (g : Matrix (Fin n) (Fin w) R)
    (r : Matrix (Fin m) (Fin w) R) (secret : Fin n → R)
    (baseError : Fin m → R) (extraError : Fin w → R) :
    vecMul secret (g - base * r) + extraError =
      vecMul secret g - vecMul (vecMul secret base + baseError) r +
        (vecMul baseError r + extraError) := by
  rw [vecMul_sub, ← vecMul_vecMul, add_vecMul]
  abel

/-- This exposure statement requires an explicitly published left-invertible
factorization. It does not apply when preimages or their factors stay private. -/
theorem recover_disclosed_factor {R : Type} [CommRing R] {m w k : ℕ}
    (trapdoor : Matrix (Fin m) (Fin w) R)
    (factor : Matrix (Fin k) (Fin w) R)
    (leftInverse : Matrix (Fin w) (Fin k) R)
    (hleft : leftInverse * factor = 1) :
    leftInverse * (factor * trapdoor.transpose) = trapdoor.transpose := by
  rw [← Matrix.mul_assoc, hleft, Matrix.one_mul]

end FormalProof4FHE.LWE.GSWPrivateTrapdoor
