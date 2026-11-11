module
public import FormalProof4FHE.HasteBoots.RefinedScalarSourceKernel
@[expose] public section

/-! Fixed complete families and raw lookup factors fix the actual native
partial/full factor tables and source-derived honest polynomials. All source
padding lanes and the helper's independent width remain part of the tables. -/
namespace FormalProof4FHE.HasteBoots.LookupIdentityTableCongruence
open MatrixFold (Cube)
open NativeFields (Goldilocks)
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
open NativeGoldExtensionArithmetic (Word)
open NativeFieldWire (goldExtensionValue)
open NativeScalarQueryShape (laneBits)
noncomputable section

theorem partial_tables {lp rp lr rr lh rh lc rc : ℕ}
    (leftPoint : Fin (laneBits (3+lp)+lr) → Word) (rightPoint : Fin (laneBits (3+rp)+rr) → Word)
    (leftY rightY : Word) (leftLength rightLength : ℕ)
    (leftShape : 3+lp = 2^laneBits (3+lp)) (rightShape : 3+rp = 2^laneBits (3+rp))
    (leftSources : Fin lc → Cube lr → Fin (3+lp) → Goldilocks) (rightSources : Fin rc → Cube rr → Fin (3+rp) → Goldilocks)
    (leftHelper : Cube (laneBits (3+lp)+lr) → Fin (3+lh) → Goldilocks) (rightHelper : Cube (laneBits (3+rp)+rr) → Fin (3+rh) → Goldilocks)
    (padding : lp = rp) (rows : lr = rr) (helperPadding : lh = rh) (columns : lc = rc)
    (point : List.ofFn leftPoint = List.ofFn rightPoint) (y : leftY = rightY) (length : leftLength = rightLength)
    (sources : HEq leftSources rightSources) (helpers : HEq leftHelper rightHelper) :
    HEq (ExtensionLookupIdentity.factors (fun i => goldExtensionValue (leftPoint i)) (goldExtensionValue leftY)
      (fun column => LookupSourceFlattening.flatten leftShape (leftSources column))
      (fun cell => PaddedExtension.decode goldilocksBasis (leftHelper cell)) leftLength)
      (ExtensionLookupIdentity.factors (fun i => goldExtensionValue (rightPoint i)) (goldExtensionValue rightY)
      (fun column => LookupSourceFlattening.flatten rightShape (rightSources column))
      (fun cell => PaddedExtension.decode goldilocksBasis (rightHelper cell)) rightLength) := by
  subst rp
  subst rr
  subst rh
  subst rc
  have pointEq := List.ofFn_inj.mp point
  cases pointEq
  cases y
  cases length
  cases sources
  cases helpers
  rfl

theorem full_tables {lp rp lr rr lh rh lc rc : ℕ}
    (leftPoint : Fin (laneBits (3+lp)+lr) → Word) (rightPoint : Fin (laneBits (3+rp)+rr) → Word)
    (leftR rightR leftY rightY : Word)
    (leftShape : 3+lp = 2^laneBits (3+lp)) (rightShape : 3+rp = 2^laneBits (3+rp))
    (leftSources : Fin lc → Cube lr → Fin (3+lp) → Goldilocks) (rightSources : Fin rc → Cube rr → Fin (3+rp) → Goldilocks)
    (leftHelper : Cube (laneBits (3+lp)+lr) → Fin (3+lh) → Goldilocks) (rightHelper : Cube (laneBits (3+rp)+rr) → Fin (3+rh) → Goldilocks)
    (padding : lp = rp) (rows : lr = rr) (helperPadding : lh = rh) (columns : lc = rc)
    (point : List.ofFn leftPoint = List.ofFn rightPoint) (r : leftR = rightR) (y : leftY = rightY)
    (sources : HEq leftSources rightSources) (helpers : HEq leftHelper rightHelper) :
    HEq (LookupPairArithmetic.fullTables (fun i => goldExtensionValue (leftPoint i)) (goldExtensionValue leftR) (goldExtensionValue leftY)
      (fun column => LookupSourceFlattening.flatten leftShape (leftSources column))
      (fun cell => PaddedExtension.decode goldilocksBasis (leftHelper cell)))
      (LookupPairArithmetic.fullTables (fun i => goldExtensionValue (rightPoint i)) (goldExtensionValue rightR) (goldExtensionValue rightY)
      (fun column => LookupSourceFlattening.flatten rightShape (rightSources column))
      (fun cell => PaddedExtension.decode goldilocksBasis (rightHelper cell))) := by
  subst rp
  subst rr
  subst rh
  subst rc
  have pointEq := List.ofFn_inj.mp point
  cases pointEq
  cases r
  cases y
  cases sources
  cases helpers
  rfl

theorem honest {Factor Term : Type} [Fintype Term] (arity : Term → ℕ)
    (leftCoefficient rightCoefficient : Term → Goldilocks3) (indices : (term : Term) → Fin (arity term) → Factor)
    {leftN rightN : ℕ} (left : Factor → Cube leftN → Goldilocks3) (right : Factor → Cube rightN → Goldilocks3)
    (dimension : leftN = rightN) (tables : HEq left right) (coefficient : leftCoefficient = rightCoefficient)
    (prior : List Word) :
    ScalarNativeSourceHealing.honest arity leftCoefficient indices leftN left prior =
      ScalarNativeSourceHealing.honest arity rightCoefficient indices rightN right prior := by
  subst rightN
  cases tables
  cases coefficient
  rfl

end
end FormalProof4FHE.HasteBoots.LookupIdentityTableCongruence
