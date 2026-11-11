module
public import FormalProof4FHE.HasteBoots.ScalarSourcePolynomial
public import FormalProof4FHE.HasteBoots.GoldHistoryPublicExtraction
@[expose] public section

/-! Honest scalar factors obtained from the original executable public source
cube. Packing lanes are flattened before row bits, independently of the code
block width. All original padding lanes are retained without a zero premise. -/
namespace FormalProof4FHE.HasteBoots.ScalarPublicSourceModel
open MatrixFold (Cube)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open NativeGoldBatchPcsProgram (Context)
open NativeFields (Goldilocks)
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
noncomputable section

variable {F K Factor Term : Type} [Field F] [Field K] [Algebra F K] [Fintype Term]
  {c row d padding : ℕ}

def packed (shape : d + padding = 2^c) (table : Cube row → Fin (d+padding) → F) : Cube (c+row) → K :=
  fun cell => algebraMap F K (LookupSourceFlattening.flatten shape table cell)

/-- The source-derived honest terminal is the original packed-source MLE,
with no new source commitment or source-dependent padding assertion. -/
theorem terminal (arity : Term → ℕ) (coefficient : Term → K) (indices : (term : Term) → Fin (arity term) → Factor)
    (shape : d + padding = 2^c) (tables : Factor → Cube row → Fin (d+padding) → F) (point : Fin (c+row) → K) :
    ScalarSourcePolynomial.truth arity coefficient indices (c+row) (List.ofFn point) (fun factor => packed shape (tables factor)) =
      PackedSumcheckRound.expression arity coefficient indices (fun factor => ExtensionLookupTerminal.sourceTruth shape point (tables factor)) := by
  rw [ScalarSourcePolynomial.terminal]
  apply congrArg (PackedSumcheckRound.expression arity coefficient indices)
  funext factor
  exact (LookupSourceFlattening.sourceTruth_eq_evaluate shape point (tables factor)).symm

/-- This conversion alone reads only the actual original public cube. -/
def publicPacked (ctx : Context) (dummy context root : Digest) (history : List Observation) (radius : ℕ)
    (capacity : GoldCommonSourceTable.Capacity ctx.parameters) (geometry : GoldHistorySourceTable.Geometry ctx.parameters)
    {padding : ℕ} (width : ctx.parameters.width.val = 3+padding) :
    Cube ctx.parameters.numVariables.val → Fin (3+padding) → Goldilocks :=
  fun cell lane => GoldHistoryPublicExtraction.cube ctx dummy context root history radius capacity geometry cell (Fin.cast width.symm lane)

def publicScalar (ctx : Context) (dummy context root : Digest) (history : List Observation) (radius : ℕ)
    (capacity : GoldCommonSourceTable.Capacity ctx.parameters) (geometry : GoldHistorySourceTable.Geometry ctx.parameters)
    {padding c : ℕ} (width : ctx.parameters.width.val = 3+padding) (shape : 3+padding = 2^c) :
    Cube (c+ctx.parameters.numVariables.val) → Goldilocks3 :=
  packed shape (publicPacked ctx dummy context root history radius capacity geometry width)

theorem publicScalar_evaluate (ctx : Context) (dummy context root : Digest) (history : List Observation) (radius : ℕ)
    (capacity : GoldCommonSourceTable.Capacity ctx.parameters) (geometry : GoldHistorySourceTable.Geometry ctx.parameters)
    {padding c : ℕ} (width : ctx.parameters.width.val = 3+padding) (shape : 3+padding = 2^c)
    (point : Fin (c+ctx.parameters.numVariables.val) → Goldilocks3) :
    ExtensionQuery.evaluate _ point (publicScalar ctx dummy context root history radius capacity geometry width shape) =
      ExtensionLookupTerminal.sourceTruth shape point (publicPacked ctx dummy context root history radius capacity geometry width) :=
  (LookupSourceFlattening.sourceTruth_eq_evaluate shape point _).symm

/-- The existing original base-field opening query evaluates this same scalar
source, including nonzero unused coefficient lanes. -/
theorem publicScalar_query (ctx : Context) (dummy context root : Digest) (history : List Observation) (radius : ℕ)
    (capacity : GoldCommonSourceTable.Capacity ctx.parameters) (geometry : GoldHistorySourceTable.Geometry ctx.parameters)
    {padding c : ℕ} (width : ctx.parameters.width.val = 3+padding) (shape : 3+padding = 2^c)
    (point : Fin (c+ctx.parameters.numVariables.val) → Goldilocks3) :
    (ExtensionLookupTerminal.sourceQuery goldilocksBasis shape point).evaluate
        (publicPacked ctx dummy context root history radius capacity geometry width) =
      PaddedExtension.encode (padding := padding) goldilocksBasis
        (ExtensionQuery.evaluate _ point (publicScalar ctx dummy context root history radius capacity geometry width shape)) :=
  LookupSourceFlattening.source_query_evaluate goldilocksBasis shape point _

/-- Original constructor provenance supplies the common analysis cube. Code
width never appears in the packing-width transport or flattening order. -/
theorem publicScalar_eq_analysis (ctx : Context) (origin : CacheBackedCodeOrigin.Origin ctx)
    (dummy context root : Digest) (history : List Observation) (radius : ℕ)
    (small : 3*radius < ctx.parameters.code.blocks.val-ctx.parameters.code.messageBlocks.val+1)
    (geometry : GoldHistorySourceTable.Geometry ctx.parameters) {padding c : ℕ}
    (width : ctx.parameters.width.val = 3+padding) (shape : 3+padding = 2^c) :
    publicScalar ctx dummy context root history radius (origin.capacityAt ctx rfl) geometry width shape =
      packed shape (fun cell lane => GoldHistorySourceTable.table ctx.parameters (origin.primitiveAt ctx rfl)
        (origin.capacityAt ctx rfl) dummy context root history radius geometry cell (Fin.cast width.symm lane)) := by
  unfold publicScalar publicPacked
  rw [GoldHistoryPublicExtraction.cube_eq_analysis ctx origin dummy context root history radius small geometry]

/-- Once the original source key is recorded, later history cannot change
this factor table or any honest polynomial built from it. -/
theorem publicScalar_append (ctx : Context) (origin : CacheBackedCodeOrigin.Origin ctx)
    (dummy context root : Digest) (before after : List Observation) (radius : ℕ)
    (small : 3*radius < ctx.parameters.code.blocks.val-ctx.parameters.code.messageBlocks.val+1)
    (geometry : GoldHistorySourceTable.Geometry ctx.parameters) {padding c : ℕ}
    (width : ctx.parameters.width.val = 3+padding) (shape : 3+padding = 2^c)
    (height : NativeMerkleShapeFamily.Height) (sourceLog : NativeRootFamilySourceSelection.Log)
    (present : ⟨(context,height),⟨root,sourceLog⟩⟩ ∈
      (NativeGoldBatchFamilyAvailability.reconstructed dummy before).checkpoints.checkpoints) :
    publicScalar ctx dummy context root (before++after) radius (origin.capacityAt ctx rfl) geometry width shape =
      publicScalar ctx dummy context root before radius (origin.capacityAt ctx rfl) geometry width shape := by
  have same := GoldHistoryPublicExtraction.cube_append ctx origin dummy context root before after radius small geometry height sourceLog present
  exact congrArg (fun table : Cube ctx.parameters.numVariables.val → Fin ctx.parameters.width.val → Goldilocks =>
    packed shape (fun cell lane => table cell (Fin.cast width.symm lane))) same

end
end FormalProof4FHE.HasteBoots.ScalarPublicSourceModel
