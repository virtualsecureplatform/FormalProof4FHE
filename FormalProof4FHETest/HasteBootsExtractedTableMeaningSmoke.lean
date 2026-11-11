module
import all FormalProof4FHE.HasteBoots.SingleOpeningExtractedTableMeaning
import all FormalProof4FHETest.HasteBootsSingleSelectedSmoke

namespace FormalProof4FHE.HasteBoots.ExtractedTableMeaningSmoke
open NativeFields (Goldilocks)
open HasteBootsBatchMeaningSmoke (usize)
open scoped Matrix
noncomputable section

def parameters := SingleSelectedSmoke.ctx.parameters

def a : NativeGoldPcsWire.Matrix := ⟨usize 3,⟨[0,1,0,0,0,0,0,0,0],by decide⟩⟩
def b : NativeGoldPcsWire.Matrix := ⟨usize 3,⟨[0,0,0,1,0,0,0,0,0],by decide⟩⟩
def raw : NativeGoldPcsWire.Query := ⟨[(a,a),(b,b)],by decide⟩
def interpreted := NativeGoldCoefficientsQuery.interpret 3 2 ⟨raw.models,none⟩
def query := interpreted.get (by decide +kernel)
theorem read : NativeGoldCoefficientsQuery.interpret 3 2 ⟨raw.models,none⟩ = some query := (Option.some_get _).symm

def table : Fin 2 → Fin 2 → Fin 3 → Goldilocks := fun left right lane =>
  if left.val = 0 ∧ right.val = 0 ∧ lane.val = 1 then 1 else 0

/-- The actual PCS layout has packing width three and code-symbol width four. -/
example : parameters.width.val = 3 ∧ parameters.code.blockWidth.val = 4 ∧
    parameters.leftVariables.val = 1 ∧ parameters.code.messageLength.val = 2 := by decide +kernel

/-- Later matrices act after earlier matrices: B*A preserves lane one. -/
example : matrixEvaluation (SingleOpeningFixedResponseData.left parameters raw)
    (SingleOpeningFixedResponseData.right parameters raw) table = ![0,1,0] := by
  funext lane
  fin_cases lane <;> decide +kernel

/-- Reversing this noncommuting pair changes the result, catching order errors. -/
def reversed : NativeGoldPcsWire.Query := ⟨[(b,b),(a,a)],by decide⟩
example : matrixEvaluation (SingleOpeningFixedResponseData.left parameters reversed)
    (SingleOpeningFixedResponseData.right parameters reversed) table = 0 := by decide +kernel

/-- The new bridge equates the same table's interpreted cube fold with the
native rectangular evaluation for this noncommuting original matrix query. -/
example : query.query.fold (QueryRectangularNativeMeaning.source parameters 1 rfl table) =
    matrixEvaluation (SingleOpeningFixedResponseData.left parameters raw) (SingleOpeningFixedResponseData.right parameters raw) table :=
  QueryRectangularNativeMeaning.fold_source parameters raw 1 query read rfl table

/-- The first variable is the low native address bit. -/
example : QueryRectangularNativeMeaning.source parameters 1 rfl table (false,(false,())) = ![0,1,0] ∧
    QueryRectangularNativeMeaning.source parameters 1 rfl table (true,(false,())) = 0 ∧
    QueryRectangularNativeMeaning.source parameters 1 rfl table (false,(true,())) = 0 := by
  refine ⟨?_,?_,?_⟩ <;> (funext lane; fin_cases lane <;> decide +kernel)

/-- Zero variables retain the sole original vector, with no hidden padding. -/
def parameters0 := {parameters with leftVariables := usize 0, code := {parameters.code with messageLength := usize 1}}
def raw0 : NativeGoldPcsWire.Query := ⟨[],by decide⟩
def query0 : ExtensionQuery.Broadcast Goldilocks 3 0 := ⟨.nil,none⟩
def table0 (_ : Fin 1) (_ : Fin 1) : Fin 3 → Goldilocks := ![2,3,4]
example : query0.query.fold (QueryRectangularNativeMeaning.source parameters0 0 rfl table0) =
    matrixEvaluation (SingleOpeningFixedResponseData.left parameters0 raw0) (SingleOpeningFixedResponseData.right parameters0 raw0) table0 :=
  QueryRectangularNativeMeaning.fold_source parameters0 raw0 0 query0 rfl rfl table0

/-- Raw aliases of a canonical field coefficient have the same total lane view. -/
def aliasRow : NativeLookupRequestWire.Row := ⟨[usize (NativeFields.goldilocksModulus+1),0,0],by decide⟩
example : SingleOpeningFixedResponseData.claimed SingleSelectedSmoke.ctx aliasRow = ![1,0,0] :=
  SingleOpeningExtractedTableMeaning.claimed_of_encoded _ _ _ (by decide +kernel)

/-- The real original single-opening prefix supplies all split dimensions. -/
example : SingleSelectedSmoke.ctx.parameters.numVariables.val = SingleSelectedSmoke.ctx.parameters.leftVariables.val +
      (SingleSelectedSmoke.ctx.parameters.numVariables.val - SingleSelectedSmoke.ctx.parameters.leftVariables.val) ∧
    SingleSelectedSmoke.ctx.parameters.code.messageLength.val =
      2^(SingleSelectedSmoke.ctx.parameters.numVariables.val - SingleSelectedSmoke.ctx.parameters.leftVariables.val) :=
  SingleOpeningExtractedTableMeaning.prepared_dimensions _ _ _ SingleSelectedSmoke.prepared

end
end FormalProof4FHE.HasteBoots.ExtractedTableMeaningSmoke
