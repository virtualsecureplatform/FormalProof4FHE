module
public import FormalProof4FHE.HasteBoots.OriginalHelperRoots
public import FormalProof4FHE.HasteBoots.FamilyPosteriorMismatch
@[expose] public section

/-! The original parent family and complete ordered helper-root vector share
one actual scalar input. Root alignment is a byte-format consequence and
adds no oracle collision event or independent root-matching assumption. -/
namespace FormalProof4FHE.HasteBoots.OriginalScalarFamily
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativePrefixCodec (Vector)
open OracleProgram (Program runPrefix)
noncomputable section

structure Family {A : Type} (program : Program A) (position : ℕ) (world : World) where
  parent : OriginalParentFamily.Family program position world
  input : Input
  roots : Vector Digest
  parsed : HelperRootsView.parse input = some roots
  quote : NativeChildSeedView.quote input = some (InputIndexedOracle.block world parent.input 0 64)

theorem compare {A : Type} (program : Program A) (position : ℕ) (world other : World)
    (left : Family program position world) (right : Family program position other) (dummy : Digest)
    (input : left.input = right.input)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run) :
    (FamilyPosteriorMismatch.Agrees left.parent right.parent ∧ left.roots = right.roots) ∨
      ProgramParentSeedCollision.Bad program world ∨ NativeRootFamilyLifetime.Bad dummy (runPrefix position program world).run.2 ∨
        ProgramContextTarget.Bad program world ∨ ProgramContextTarget.Bad program other := by
  have rightQuote : NativeChildSeedView.quote left.input = some (InputIndexedOracle.block other right.parent.input 0 64) := by
    rw [input]
    exact right.quote
  rcases OriginalParentFamily.compare program position world other left.parent right.parent left.input dummy left.quote rightQuote same with equal | bad
  · exact Or.inl ⟨equal,OriginalHelperRoots.compare left.input right.input left.roots right.roots left.parsed right.parsed input⟩
  · exact Or.inr bad

/-- Every corresponding original root ordinal is fixed, including repeated
roots. Equality searches over roots are never used to select an ordinal. -/
theorem ordinal {A : Type} (program : Program A) (position : ℕ) (world other : World)
    (left : Family program position world) (right : Family program position other) (input : left.input = right.input)
    (leftIndex : Fin left.roots.val.length) (rightIndex : Fin right.roots.val.length) (same : leftIndex.val = rightIndex.val) :
    left.roots.val.get leftIndex = right.roots.val.get rightIndex :=
  OriginalHelperRoots.ordinal left.input right.input left.roots right.roots left.parsed right.parsed input leftIndex rightIndex same

/-- Complete helper tables now use their fixed original root ordinals rather
than an independently supplied common-root certificate. -/
theorem helper_table {A : Type} (program : Program A) (position : ℕ) (world other : World)
    (left : Family program position world) (right : Family program position other) (input : left.input = right.input)
    (parameters : left.parent.helper = right.parent.helper) (bindings : left.parent.bindings = right.parent.bindings)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run)
    (leftIndex : Fin left.roots.val.length) (rightIndex : Fin right.roots.val.length) (index : leftIndex.val = rightIndex.val)
    (leftContext rightContext : NativeGoldBatchPcsProgram.Context)
    (leftParameters : leftContext.parameters = left.parent.helper) (rightParameters : rightContext.parameters = right.parent.helper)
    (dummy : Digest) (radius : ℕ)
    (leftCapacity : GoldCommonSourceTable.Capacity leftContext.parameters) (rightCapacity : GoldCommonSourceTable.Capacity rightContext.parameters)
    (leftGeometry : GoldHistorySourceTable.Geometry leftContext.parameters) (rightGeometry : GoldHistorySourceTable.Geometry rightContext.parameters)
    {leftPadding rightPadding : ℕ} (leftWidth : leftContext.parameters.width.val = 3+leftPadding) (rightWidth : rightContext.parameters.width.val = 3+rightPadding) :
    HEq (ScalarPublicSourceModel.publicPacked leftContext dummy (InputIndexedOracle.sha512 world (GoldContextInput.bytes left.parent.helper))
      (left.roots.val.get leftIndex) (runPrefix position program world).run.2 radius leftCapacity leftGeometry leftWidth)
      (ScalarPublicSourceModel.publicPacked rightContext dummy (InputIndexedOracle.sha512 other (GoldContextInput.bytes right.parent.helper))
      (right.roots.val.get rightIndex) (runPrefix position program other).run.2 radius rightCapacity rightGeometry rightWidth) := by
  rw [← ordinal program position world other left right input leftIndex rightIndex index]
  exact OriginalPackedFamily.helper program position world other left.parent right.parent parameters bindings same leftContext rightContext
    leftParameters rightParameters dummy _ radius leftCapacity rightCapacity leftGeometry rightGeometry leftWidth rightWidth

end
end FormalProof4FHE.HasteBoots.OriginalScalarFamily
