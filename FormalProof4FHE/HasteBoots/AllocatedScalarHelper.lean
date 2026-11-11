module
public import FormalProof4FHE.HasteBoots.AllocatedLookupContext
public import FormalProof4FHE.HasteBoots.HelperPublicSource
public import FormalProof4FHE.HasteBoots.SourceFrontierStability
@[expose] public section

/-! Scalar helper factors retain the same original borrowed helper object and
original proof-root ordinal. The factor has no future PCS response argument.
Source and helper objects are assembled from the same immutable store. -/
namespace FormalProof4FHE.HasteBoots.AllocatedScalarHelper
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (Input World)
noncomputable section

variable (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (handle : ℕ) (references : Vector Reference) (template ctx : Context (Vector Opening))
    (assembled : AllocatedLookupContext.assemble entries handle references template = some ctx)

/-- Select the object from the actual original helper borrow. -/
def entry : Entry := Classical.choose (AllocatedLookupContext.helper_entry entries reachable handle references template ctx assembled)

theorem entry_spec : entries[handle]? = some (entry entries reachable handle references template ctx assembled) ∧
    NativeGoldParameterStore.GoodEntry (entry entries reachable handle references template ctx assembled) ∧
    ctx.helper = (entry entries reachable handle references template ctx assembled).initialized.parameters := by
  have original := Classical.choose_spec (AllocatedLookupContext.helper_entry entries reachable handle references template ctx assembled)
  exact ⟨original.1,original.2.1,congrArg (fun context => context.helper) original.2.2⟩

variable (index : Fin ctx.proof.roots.val.length)

def reference : NativeGoldBatchPcsProgram.Context :=
  HelperPublicSource.context ctx (entry entries reachable handle references template ctx assembled) (ctx.proof.roots.val.get index)

def origin : CacheBackedCodeOrigin.Origin (reference entries reachable handle references template ctx assembled index) :=
  HelperPublicSource.origin ctx (entry entries reachable handle references template ctx assembled)
    (entry_spec entries reachable handle references template ctx assembled).2.1 (ctx.proof.roots.val.get index)

theorem origin_data : (origin entries reachable handle references template ctx assembled index).request =
      (entry entries reachable handle references template ctx assembled).request ∧
    (origin entries reachable handle references template ctx assembled index).config =
      (entry entries reachable handle references template ctx assembled).config := ⟨rfl,rfl⟩

/-- A helper coefficient query uses one decoded extension value per original
row. Its row dimension is already the full scalar dimension: helper packing
lanes must not become additional point coordinates. -/
def factor (dummy context : Digest) (history : List Observation) (radius : ℕ)
    (geometry : GoldHistorySourceTable.Geometry (reference entries reachable handle references template ctx assembled index).parameters)
    {padding : ℕ} (width : (reference entries reachable handle references template ctx assembled index).parameters.width.val = 3+padding) :=
  fun cell => PaddedExtension.decode NativeExtensionFields.goldilocksBasis
    (ScalarPublicSourceModel.publicPacked (reference entries reachable handle references template ctx assembled index) dummy context
      (ctx.proof.roots.val.get index) history radius
      ((origin entries reachable handle references template ctx assembled index).capacityAt _ rfl) geometry width cell)

/-- The actual coefficient query evaluates exactly this decoded-row helper
factor, without any zero-padding assumption on the original table. -/
theorem query (dummy context : Digest) (history : List Observation) (radius : ℕ)
    (geometry : GoldHistorySourceTable.Geometry (reference entries reachable handle references template ctx assembled index).parameters)
    {padding : ℕ} (width : (reference entries reachable handle references template ctx assembled index).parameters.width.val = 3+padding)
    (point : Fin (reference entries reachable handle references template ctx assembled index).parameters.numVariables.val → NativeExtensionFields.Goldilocks3) :
    (ExtensionQuery.coefficientsQuery NativeExtensionFields.goldilocksBasis point).evaluate
      (ScalarPublicSourceModel.publicPacked (reference entries reachable handle references template ctx assembled index) dummy context
        (ctx.proof.roots.val.get index) history radius
        ((origin entries reachable handle references template ctx assembled index).capacityAt _ rfl) geometry width) =
      PaddedExtension.encode (padding := padding) NativeExtensionFields.goldilocksBasis
        (ExtensionQuery.evaluate _ point (factor entries reachable handle references template ctx assembled index dummy context history radius geometry width)) :=
  ExtensionQuery.coefficients_evaluate _ point _

theorem read (dummy context : Digest) (before after : List Observation) (radius : ℕ)
    (geometry : GoldHistorySourceTable.Geometry (reference entries reachable handle references template ctx assembled index).parameters)
    {padding : ℕ} (width : (reference entries reachable handle references template ctx assembled index).parameters.width.val = 3+padding)
    (input : Input) (offset : ℕ) (values : Input) (positive : values ≠ [])
    (resolved : (context,ctx.proof.roots.val.get index) ∈ NativeParentLedger.resolve
      (NativeRootFamilyHistory.reconstruct NativeGoldColumnAuthentication.encoding dummy before).1.1
      (NativeRootFamilyHistory.reconstruct NativeGoldColumnAuthentication.encoding dummy before).1.2 input) :
    factor entries reachable handle references template ctx assembled index dummy context
        (before ++ .output input offset values :: after) radius geometry width =
      factor entries reachable handle references template ctx assembled index dummy context before radius geometry width := by
  unfold factor ScalarPublicSourceModel.publicPacked
  rw [SourceFrontierStability.cube_read _ _ _ _ _ _ _ _ _ input offset values positive resolved]

/-- Actual helper-context ancestry and the committed original root supply the
pre-read decoded helper, with the existing seed-order bad event kept explicit. -/
theorem ancestry_read {S A : Type} (step : S → OracleMachine.Command S A) (fuel : ℕ) (initial : S) (world : World)
    (dummy context : Digest) (radius : ℕ)
    (geometry : GoldHistorySourceTable.Geometry (reference entries reachable handle references template ctx assembled index).parameters)
    {padding : ℕ} (width : (reference entries reachable handle references template ctx assembled index).parameters.width.val = 3+padding)
    (parent : Input) (parentIndex : ℕ)
    (realized : NativeSeedAncestry.Realized world (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2
      parent parentIndex (.helper context))
    (position : ℕ) (input : Input) (offset : ℕ) (values : Input) (positive : values ≠ [])
    (positioned : (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2[position]? = some (.output input offset values))
    (quoted : NativeChildSeedView.quote input = some (InputIndexedOracle.block world parent 0 64))
    (committed : ctx.proof.roots.val.get index ∈ NativeParentLedger.roots input) :
    factor entries reachable handle references template ctx assembled index dummy context
        (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2 radius geometry width =
      factor entries reachable handle references template ctx assembled index dummy context
        ((OracleProgram.run (OracleMachine.take step fuel initial) world).run.2.take position) radius geometry width ∨
      SeedQuoteOrder.Bad step initial world := by
  have member : (context,ctx.proof.roots.val.get index) ∈ NativeSeedAncestry.Keys input (.helper context) :=
    List.mem_map.mpr ⟨ctx.proof.roots.val.get index,committed,rfl⟩
  rcases SourceFrontierStability.ancestry_cube_read step fuel initial world _ dummy context _ radius _ geometry
      parent parentIndex (.helper context) realized position input offset values positive positioned quoted member with same | bad
  · apply Or.inl
    unfold factor ScalarPublicSourceModel.publicPacked
    rw [same]
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.AllocatedScalarHelper
