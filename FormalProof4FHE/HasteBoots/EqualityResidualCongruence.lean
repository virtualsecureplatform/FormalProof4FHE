module
public import FormalProof4FHE.HasteBoots.EqualityFactorCandidate
@[expose] public section

/-! Complete masked reciprocal residuals preserve original scalar flattening,
independent helper width and the original active prefix. Equality points do
not appear in these fixed Boolean tables. -/
namespace FormalProof4FHE.HasteBoots.EqualityResidualCongruence
open MatrixFold (Cube)
open NativeFields (Goldilocks)
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
open NativeGoldExtensionArithmetic (Word)
open NativeFieldWire (goldExtensionValue)
open NativeScalarQueryShape (laneBits)
noncomputable section

def packed {padding rows helperPadding columns : ℕ} (shape : 3+padding = 2^laneBits (3+padding))
    (r y : Word) (count : ℕ)
    (sources : Fin columns → Cube rows → Fin (3+padding) → Goldilocks)
    (helpers : Cube (laneBits (3+padding)+rows) → Fin (3+helperPadding) → Goldilocks) :
    Cube (laneBits (3+padding)+rows) → Goldilocks3 := fun cell =>
  ReciprocalMask.residual (goldExtensionValue r)
    (ExtensionLookupIdentity.hashTable (goldExtensionValue y) (fun column => LookupSourceFlattening.flatten shape (sources column)) cell)
    (PaddedExtension.decode goldilocksBasis (helpers cell))
    (decide ((FlatMatrixFold.index (laneBits (3+padding)+rows) cell).val < count))

theorem packed_congr {lp rp lr rr lh rh lc rc : ℕ}
    (leftShape : 3+lp = 2^laneBits (3+lp)) (rightShape : 3+rp = 2^laneBits (3+rp))
    (leftR rightR leftY rightY : Word) (leftCount rightCount : ℕ)
    (leftSources : Fin lc → Cube lr → Fin (3+lp) → Goldilocks) (rightSources : Fin rc → Cube rr → Fin (3+rp) → Goldilocks)
    (leftHelpers : Cube (laneBits (3+lp)+lr) → Fin (3+lh) → Goldilocks) (rightHelpers : Cube (laneBits (3+rp)+rr) → Fin (3+rh) → Goldilocks)
    (padding : lp = rp) (rows : lr = rr) (helperPadding : lh = rh) (columns : lc = rc)
    (r : leftR = rightR) (y : leftY = rightY) (count : leftCount = rightCount)
    (sources : HEq leftSources rightSources) (helpers : HEq leftHelpers rightHelpers) :
    HEq (packed leftShape leftR leftY leftCount leftSources leftHelpers)
      (packed rightShape rightR rightY rightCount rightSources rightHelpers) := by
  subst rp rr rh rc
  cases r
  cases y
  cases count
  cases sources
  cases helpers
  rfl

theorem native_transport {ln rn lm rm : ℕ} (leftDimension : ln = lm) (rightDimension : rn = rm)
    (nativeDimension : ln = rn) (scalarDimension : lm = rm)
    (left : Cube lm → Goldilocks3) (right : Cube rm → Goldilocks3) (tables : HEq left right) :
    HEq (fun cell : Cube ln => left (cast (congrArg Cube leftDimension) cell))
      (fun cell : Cube rn => right (cast (congrArg Cube rightDimension) cell)) := by
  cases nativeDimension
  cases scalarDimension
  cases tables
  rfl

end
end FormalProof4FHE.HasteBoots.EqualityResidualCongruence
