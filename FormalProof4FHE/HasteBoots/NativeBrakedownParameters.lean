module

public import FormalProof4FHE.HasteBoots.NativeBrakedownContext
import all Init.Data.Nat.Bitwise.Basic

@[expose] public section

/-! Native new_encoded parameter construction. Row-code accessors describe the
same trusted code object as the context; they do not certify its distance or
encoder implementation. Atomic sampling's separate power-of-two gate is not
added to this constructor. All sizes use the selected 64-bit machine model. -/
namespace FormalProof4FHE.HasteBoots.NativeBrakedownParameters

open NativeBrakedownContext (RowDescription Parameters)

structure Description (Code : Type) where
  row : RowDescription Code
  messageLength : Code → NativeUsizeMessage.Usize

structure Geometry where
  columns : ℕ
  blocks : ℕ
  blockWidth : ℕ
  rows : ℕ
  stride : ℕ
  columnWords : ℕ
  responseWords : ℕ
  height : ℕ
  randomCount : NativeUsizeMessage.Usize

/-- ceil(log2(blocks)), including blocks=1. -/
def height (blocks : ℕ) : ℕ := (blocks-1).size

def basic {C : Type} (parameters : Parameters C) : Bool :=
  decide (parameters.width.val ≠ 0 ∧ parameters.leftVariables.val ≤ parameters.numVariables.val ∧
    parameters.numVariables.val < 64 ∧ parameters.queries.val ≠ 0)

def codeShape {C : Type} (description : Description C) (parameters : Parameters C) : Bool :=
  let columns := 2^(parameters.numVariables.val-parameters.leftVariables.val)
  let blocks := (description.row.blocks parameters.code).val
  let block := (description.row.blockWidth parameters.code).val
  decide ((description.messageLength parameters.code).val = columns ∧ blocks*block < 2^64 ∧
    columns ≤ blocks*block ∧ blocks ≠ 0 ∧ block ≠ 0)

def allocations {C : Type} (description : Description C) (parameters : Parameters C) : Prop :=
  let rows := 2^parameters.leftVariables.val*parameters.width.val
  let blocks := (description.row.blocks parameters.code).val
  let block := (description.row.blockWidth parameters.code).val
  2^parameters.numVariables.val*parameters.width.val < 2^64 ∧ rows < 2^64 ∧
    rows*blocks < 2^64 ∧ rows*blocks*block < 2^64 ∧ rows*parameters.width.val < 2^64 ∧
    2^(height blocks) < 2^64 ∧ 2^(height blocks)*2 < 2^64

instance {C : Type} (description : Description C) (parameters : Parameters C) : Decidable (allocations description parameters) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def geometry {C : Type} (description : Description C) (parameters : Parameters C) (fits : allocations description parameters) : Geometry :=
  let blocks := (description.row.blocks parameters.code).val
  let block := (description.row.blockWidth parameters.code).val
  let columns := 2^(parameters.numVariables.val-parameters.leftVariables.val)
  let rows := 2^parameters.leftVariables.val*parameters.width.val
  ⟨columns,blocks,block,rows,blocks*block,rows*block,parameters.width.val*columns,height blocks,
    ⟨rows*parameters.width.val,fits.2.2.2.2.1⟩⟩

def build {C : Type} (description : Description C) (parameters : Parameters C) : Option Geometry :=
  if basic parameters then
    if codeShape description parameters then
      if fits : allocations description parameters then some (geometry description parameters fits) else none
    else none
  else none

structure Spec {C : Type} (description : Description C) (parameters : Parameters C) (result : Geometry) : Prop where
  basic : parameters.width.val ≠ 0 ∧ parameters.leftVariables.val ≤ parameters.numVariables.val ∧
    parameters.numVariables.val < 64 ∧ parameters.queries.val ≠ 0
  code : (description.messageLength parameters.code).val = 2^(parameters.numVariables.val-parameters.leftVariables.val) ∧
    (description.row.blocks parameters.code).val*(description.row.blockWidth parameters.code).val < 2^64 ∧
    2^(parameters.numVariables.val-parameters.leftVariables.val) ≤ (description.row.blocks parameters.code).val*(description.row.blockWidth parameters.code).val ∧
    (description.row.blocks parameters.code).val ≠ 0 ∧ (description.row.blockWidth parameters.code).val ≠ 0
  allocations : allocations description parameters
  computed : result = geometry description parameters allocations

theorem build_spec {C : Type} (description : Description C) (parameters : Parameters C) (result : Geometry)
    (success : build description parameters = some result) : Spec description parameters result := by
  unfold build at success
  split at success
  next valid =>
    split at success
    next code =>
      split at success
      next fits =>
        have same := Option.some.inj success
        exact ⟨of_decide_eq_true valid,of_decide_eq_true code,fits,same.symm⟩
      next invalid => contradiction
    next invalid => contradiction
  next invalid => contradiction

theorem build_complete {C : Type} (description : Description C) (parameters : Parameters C)
    (valid : basic parameters = true) (code : codeShape description parameters = true) (fits : allocations description parameters) :
    build description parameters = some (geometry description parameters fits) := by
  simp only [build,valid,code,ite_true,dite_eq_left fits]

theorem computed_sizes {C : Type} (description : Description C) (parameters : Parameters C) (result : Geometry)
    (success : build description parameters = some result) :
    result.columns = 2^(parameters.numVariables.val-parameters.leftVariables.val) ∧
    result.blocks = (description.row.blocks parameters.code).val ∧ result.blockWidth = (description.row.blockWidth parameters.code).val ∧
    result.rows = 2^parameters.leftVariables.val*parameters.width.val ∧ result.stride = result.blocks*result.blockWidth ∧
    result.columnWords = result.rows*result.blockWidth ∧ result.responseWords = parameters.width.val*result.columns ∧
    result.height = height result.blocks ∧ result.randomCount.val = result.rows*parameters.width.val := by
  rw [(build_spec description parameters result success).computed]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- The checked next power is the least power-of-two covering all blocks. -/
theorem leaves_cover (blocks : ℕ) (positive : 0 < blocks) : blocks ≤ 2^(height blocks) := by
  have bound := Nat.lt_size_self (blocks-1)
  change blocks-1 < 2^(height blocks) at bound
  omega

theorem height_minimal (blocks exponent : ℕ) (covers : blocks ≤ 2^exponent) : height blocks ≤ exponent := by
  by_contra rejected
  have smaller : exponent < (blocks-1).size := by change exponent < height blocks; omega
  have lower := Nat.lt_size.mp smaller
  have positive : 0 < 2^exponent := by positivity
  omega

theorem path_shift {C : Type} (description : Description C) (parameters : Parameters C) (result : Geometry)
    (success : build description parameters = some result) : result.height+1 < 64 := by
  have spec := build_spec description parameters result success
  rw [spec.computed]
  have bound := spec.allocations.2.2.2.2.2.2
  change 2^(height (description.row.blocks parameters.code).val)*2 < 2^64 at bound
  rw [← pow_succ] at bound
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp bound

end FormalProof4FHE.HasteBoots.NativeBrakedownParameters
