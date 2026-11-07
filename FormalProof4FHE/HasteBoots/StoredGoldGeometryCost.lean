module
public import FormalProof4FHE.HasteBoots.StoredGeometryArithmeticCost
@[expose] public section

/-! Closed stored-Gold geometry validation with cached measured arithmetic.
Native accessors are fixed projections of the retained code object. No table,
row-description or encoder callback executes. This matches the existing native
parameter constructor; code-root validity and physical/backend refinement remain
separate. Fixed charges count scalar accesses/arithmetic/Boolean/record steps. -/
namespace FormalProof4FHE.HasteBoots.StoredGoldGeometryCost
open SolverOperationCost (Run)
open StoredGeometryArithmeticCost (power2 bitLength)
open NativeBrakedownParameters (Geometry)
abbrev Parameters := NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored

structure Parts where
  columns : ℕ
  full : ℕ
  left : ℕ
  height : ℕ
  leaves : ℕ

def compute (parameters : Parameters) : Run Parts :=
  let columns := power2 (parameters.numVariables.val-parameters.leftVariables.val)
  let full := power2 parameters.numVariables.val
  let left := power2 parameters.leftVariables.val
  let height := bitLength (parameters.code.blocks.val-1)
  let leaves := power2 height.value
  ⟨⟨columns.value,full.value,left.value,height.value,leaves.value⟩,
    columns.cost+full.cost+left.cost+height.cost+leaves.cost+12⟩

theorem compute_value (parameters : Parameters) :
    (compute parameters).value = ⟨2^(parameters.numVariables.val-parameters.leftVariables.val),
      2^parameters.numVariables.val,2^parameters.leftVariables.val,
      NativeBrakedownParameters.height parameters.code.blocks.val,
      2^(NativeBrakedownParameters.height parameters.code.blocks.val)⟩ := by
  simp only [compute,StoredGeometryArithmeticCost.power2_value,StoredGeometryArithmeticCost.bitLength_value,
    NativeBrakedownParameters.height]

theorem compute_cost (parameters : Parameters) (valid : NativeBrakedownParameters.basic parameters = true) :
    (compute parameters).cost ≤ 1100 := by
  have basic := of_decide_eq_true valid
  change parameters.width.val ≠ 0 ∧ parameters.leftVariables.val ≤ parameters.numVariables.val ∧
    parameters.numVariables.val < 64 ∧ parameters.queries.val ≠ 0 at basic
  have sized : (parameters.code.blocks.val-1).size ≤ 64 :=
    Nat.size_le.mpr ((Nat.sub_le _ _).trans_lt parameters.code.blocks.isLt)
  simp only [compute,StoredGeometryArithmeticCost.power2_cost,StoredGeometryArithmeticCost.bitLength_cost,
    StoredGeometryArithmeticCost.bitLength_value]
  omega

def codeShape (parameters : Parameters) (parts : Parts) : Run Bool :=
  let blocks := parameters.code.blocks.val
  let block := parameters.code.blockWidth.val
  ⟨decide (parameters.code.messageLength.val = parts.columns ∧ blocks*block < 2^64 ∧
    parts.columns ≤ blocks*block ∧ blocks ≠ 0 ∧ block ≠ 0),33⟩

def allocations (parameters : Parameters) (parts : Parts) : Run Bool :=
  let rows := parts.left*parameters.width.val
  let blocks := parameters.code.blocks.val
  let block := parameters.code.blockWidth.val
  ⟨decide (parts.full*parameters.width.val < 2^64 ∧ rows < 2^64 ∧
    rows*blocks < 2^64 ∧ rows*blocks*block < 2^64 ∧ rows*parameters.width.val < 2^64 ∧
    parts.leaves < 2^64 ∧ parts.leaves*2 < 2^64),96⟩

theorem codeShape_value (parameters : Parameters) :
    (codeShape parameters (compute parameters).value).value =
      NativeBrakedownParameters.codeShape NativeGoldBlockCode.description parameters := by
  apply Bool.eq_iff_iff.mpr
  simp only [codeShape,compute_value,NativeBrakedownParameters.codeShape,NativeGoldBlockCode.description,decide_eq_true_eq]
  constructor
  · intro valid; exact decide_eq_true valid
  · intro valid; exact of_decide_eq_true valid

theorem allocations_value (parameters : Parameters) :
    (allocations parameters (compute parameters).value).value =
      decide (NativeBrakedownParameters.allocations NativeGoldBlockCode.description parameters) := by
  apply Bool.eq_iff_iff.mpr
  simp only [allocations,compute_value,NativeBrakedownParameters.allocations,NativeGoldBlockCode.description,decide_eq_true_eq]
  constructor
  · intro valid; exact decide_eq_true valid
  · intro valid; exact of_decide_eq_true valid

def geometry (parameters : Parameters) (parts : Parts) (fits : (allocations parameters parts).value = true) : Geometry :=
  let rows := parts.left*parameters.width.val
  let blocks := parameters.code.blocks.val
  let block := parameters.code.blockWidth.val
  have randomFits : rows*parameters.width.val < 2^64 := (of_decide_eq_true fits).2.2.2.2.1
  ⟨parts.columns,blocks,block,rows,blocks*block,rows*block,parameters.width.val*parts.columns,
    parts.height,⟨rows*parameters.width.val,randomFits⟩⟩

def build (parameters : Parameters) : Run (Option Geometry) :=
  let basic : Run Bool := ⟨NativeBrakedownParameters.basic parameters,21⟩
  if basic.value then
    let parts := compute parameters
    let shape := codeShape parameters parts.value
    if shape.value then
      let fits := allocations parameters parts.value
      if valid : fits.value = true then
        ⟨some (geometry parameters parts.value valid),basic.cost+parts.cost+shape.cost+fits.cost+64⟩
      else ⟨none,basic.cost+parts.cost+shape.cost+fits.cost+5⟩
    else ⟨none,basic.cost+parts.cost+shape.cost+4⟩
  else ⟨none,basic.cost+3⟩

theorem build_value (parameters : Parameters) :
    (build parameters).value = NativeBrakedownParameters.build NativeGoldBlockCode.description parameters := by
  simp only [build,NativeBrakedownParameters.build,codeShape_value,allocations_value,decide_eq_true_eq]
  split
  · split
    · split
      · simp only [geometry,compute_value,NativeBrakedownParameters.geometry,NativeGoldBlockCode.description]
      · rfl
    · rfl
  · rfl

theorem build_cost (parameters : Parameters) : (build parameters).cost ≤ 1500 := by
  simp only [build]
  split
  · rename_i valid
    have parts := compute_cost parameters valid
    split
    · split <;> dsimp only [codeShape,allocations] <;> omega
    · dsimp only [codeShape]; omega
  · dsimp only; omega

theorem build_spec (parameters : Parameters) (result : Geometry)
    (success : (build parameters).value = some result) :
    NativeBrakedownParameters.Spec NativeGoldBlockCode.description parameters result := by
  rw [build_value] at success
  exact NativeBrakedownParameters.build_spec _ _ _ success
end FormalProof4FHE.HasteBoots.StoredGoldGeometryCost
