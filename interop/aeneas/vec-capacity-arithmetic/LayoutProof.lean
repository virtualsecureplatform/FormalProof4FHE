namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

/-- The original continuous prefix computes size and overflow while preserving
arbitrary unrelated locals, types and the complete incoming world. -/
theorem layout_initial_exact (ambient : Frame) (capacity : NativeWord64Memory.Word) (next : Body) :
    eval (layoutInitialPrefix next) (layoutFrame ambient capacity) = eval next (layoutProductFrame ambient capacity) := by
  have encoded : NativeRecordArithmetic.word capacity.val = capacity := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt capacity.isLt
  have noOverflow : ¬ 18446744073709551616 ≤ capacity.val := by
    have bound := capacity.isLt
    change capacity.val < 18446744073709551616 at bound
    omega
  simp [layoutInitialPrefix,layoutFrame,layoutProductFrame,layoutTypes,byteLayout,byteAlignment,alignmentDiscriminants,
    expr_checkedMultiply,eval,evalRvalue,evalArithmetic,evalArgs,evalOperand,storageLive,storageDead,
    NativeRecordLLBC.read,write,retag,NativeSliceLLBC.retagValue,NativeRecordValues.typeAt,NativeRecordValues.get,
    NativeRecordValues.replace,NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,
    NativeRecordValues.copyable,NativeSliceLLBC.fits,NativeRecordArithmetic.eval,encoded,noOverflow]

theorem byte_layout_bound (capacity : NativeWord64Memory.Word) :
    decide (capacity.val ≤ 9223372036854775807) = decide (capacity.val < 2^63) := by
  by_cases bound : capacity.val < 2^63
  · have accepted : capacity.val ≤ 9223372036854775807 := by omega
    exact (decide_eq_true accepted).trans (decide_eq_true bound).symm
  · have rejected : ¬ capacity.val ≤ 9223372036854775807 := by omega
    exact (decide_eq_false rejected).trans (decide_eq_false bound).symm

/-- The source alignment conversion, checked subtraction and comparison produce
the exact signed allocation-size bound for byte alignment one. -/
theorem layout_check_exact (ambient : Frame) (capacity : NativeWord64Memory.Word) (next : Body) :
    eval (layoutCheckPrefix next) (layoutProductFrame ambient capacity) = eval next (layoutComparedFrame ambient capacity) := by
  simp [layoutCheckPrefix,layoutProductFrame,layoutComparedFrame,layoutTypes,byteAlignment,alignmentDiscriminants,
    expr_uncheckedSubtract,expr_lessEqual,eval,evalRvalue,evalArithmetic,evalEnumWord,enumWordValue,
    evalArgs,evalOperand,storageLive,storageDead,NativeRecordLLBC.read,write,NativeRecordValues.typeAt,NativeRecordValues.get,
    NativeRecordValues.replace,NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,
    NativeRecordValues.copyable,NativeSliceLLBC.fits,NativeRecordArithmetic.eval,byte_layout_bound]

def continueWith (next : Body) : Flow → Flow
  | .normal changed => eval next changed
  | flow => flow

theorem boolean_dispatch {frame caller : Frame} {operand : Operand} {condition : Bool}
    (yes no next : Body) (selected : evalBooleanOperand frame operand = some (condition,caller)) :
    eval (.switchBoolean operand yes no next) frame = eval (.constIf condition yes no next) caller := by
  simp only [eval,selected]

theorem false_branch_continuation (yes no next : Body) (frame : Frame) :
    eval (.constIf false yes no next) frame = continueWith next (eval no frame) := rfl

theorem constant_branch_tail (condition : Bool) (yes no next : Body) (frame : Frame) :
    continueWith next (eval (.constIf condition yes no .done) frame) = eval (.constIf condition yes no next) frame := by
  cases condition with
  | false =>
    simp only [eval,Bool.false_eq_true,ite_false]
    cases evaluated : eval no frame <;> rfl
  | true =>
    simp only [eval,ite_true]
    cases evaluated : eval yes frame <;> rfl

/-- For every choice of source suffixes, the byte prefix selects exactly the
layout-valid or layout-overflow suffix, then preserves normal continuation. -/
theorem layout_prefix_exact (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (overflow accepted rejected next : Body) :
    eval (layoutPrefix overflow accepted rejected next) (layoutFrame ambient capacity) =
      eval (.constIf (decide (capacity.val < 2^63)) accepted rejected next) (layoutAfterFrame ambient capacity) := by
  have selected : evalBooleanOperand (layoutProductFrame ambient capacity) (.copy 24 []) =
      some (false,layoutProductFrame ambient capacity) := by
    simp [evalBooleanOperand,evalOperand,layoutProductFrame,layoutTypes,NativeRecordLLBC.read,NativeRecordValues.typeAt,
      NativeRecordValues.get,NativeRecordValues.complete,NativeRecordValues.fits,NativeRecordValues.compatible,NativeRecordValues.copyable]
  have consumed : evalBooleanOperand (layoutComparedFrame ambient capacity) (.move 30 []) =
      some (decide (capacity.val < 2^63),layoutAfterFrame ambient capacity) := by
    simp [evalBooleanOperand,evalOperand,layoutComparedFrame,layoutAfterFrame,layoutTypes,NativeRecordLLBC.read,
      NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.complete,NativeRecordValues.fits,
      NativeRecordValues.compatible,NativeRecordValues.replace]
  rw [layoutPrefix,layout_initial_exact,boolean_dispatch _ _ _ selected,false_branch_continuation,
    layout_check_exact,boolean_dispatch _ _ _ consumed,constant_branch_tail]

end HasteBootsVecCapacityArithmetic
