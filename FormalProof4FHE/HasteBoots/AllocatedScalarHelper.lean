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

/-- Original helper parameters, original proof root, all packing lanes. -/
def factor (dummy context : Digest) (history : List Observation) (radius : ℕ)
    (geometry : GoldHistorySourceTable.Geometry (reference entries reachable handle references template ctx assembled index).parameters)
    {padding c : ℕ} (width : (reference entries reachable handle references template ctx assembled index).parameters.width.val = 3+padding)
    (shape : 3+padding = 2^c) :=
  ScalarPublicSourceModel.publicScalar (reference entries reachable handle references template ctx assembled index) dummy context
    (ctx.proof.roots.val.get index) history radius
    ((origin entries reachable handle references template ctx assembled index).capacityAt _ rfl) geometry width shape

theorem read (dummy context : Digest) (before after : List Observation) (radius : ℕ)
    (geometry : GoldHistorySourceTable.Geometry (reference entries reachable handle references template ctx assembled index).parameters)
    {padding c : ℕ} (width : (reference entries reachable handle references template ctx assembled index).parameters.width.val = 3+padding)
    (shape : 3+padding = 2^c) (input : Input) (offset : ℕ) (values : Input) (positive : values ≠ [])
    (resolved : (context,ctx.proof.roots.val.get index) ∈ NativeParentLedger.resolve
      (NativeRootFamilyHistory.reconstruct NativeGoldColumnAuthentication.encoding dummy before).1.1
      (NativeRootFamilyHistory.reconstruct NativeGoldColumnAuthentication.encoding dummy before).1.2 input) :
    factor entries reachable handle references template ctx assembled index dummy context
        (before ++ .output input offset values :: after) radius geometry width shape =
      factor entries reachable handle references template ctx assembled index dummy context before radius geometry width shape :=
  SourceFrontierStability.scalar_read _ _ _ _ _ _ _ _ _ width shape input offset values positive resolved

/-- Actual helper-context ancestry and the committed original root supply the
pre-read table, with the existing seed-order bad event kept explicit. -/
theorem ancestry_read {S A : Type} (step : S → OracleMachine.Command S A) (fuel : ℕ) (initial : S) (world : World)
    (dummy context : Digest) (radius : ℕ)
    (geometry : GoldHistorySourceTable.Geometry (reference entries reachable handle references template ctx assembled index).parameters)
    {padding c : ℕ} (width : (reference entries reachable handle references template ctx assembled index).parameters.width.val = 3+padding)
    (shape : 3+padding = 2^c) (parent : Input) (parentIndex : ℕ)
    (realized : NativeSeedAncestry.Realized world (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2
      parent parentIndex (.helper context))
    (position : ℕ) (input : Input) (offset : ℕ) (values : Input) (positive : values ≠ [])
    (positioned : (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2[position]? = some (.output input offset values))
    (quoted : NativeChildSeedView.quote input = some (InputIndexedOracle.block world parent 0 64))
    (committed : ctx.proof.roots.val.get index ∈ NativeParentLedger.roots input) :
    factor entries reachable handle references template ctx assembled index dummy context
        (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2 radius geometry width shape =
      factor entries reachable handle references template ctx assembled index dummy context
        ((OracleProgram.run (OracleMachine.take step fuel initial) world).run.2.take position) radius geometry width shape ∨
      SeedQuoteOrder.Bad step initial world := by
  apply SourceFrontierStability.ancestry_scalar_read step fuel initial world _ dummy context _ radius _ geometry width shape
    parent parentIndex (.helper context) realized position input offset values positive positioned quoted
  exact List.mem_map.mpr ⟨ctx.proof.roots.val.get index,committed,rfl⟩

end
end FormalProof4FHE.HasteBoots.AllocatedScalarHelper
