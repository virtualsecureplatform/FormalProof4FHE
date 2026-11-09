module
import FormalProof4FHE.HasteBoots.NativeRecordLLBC

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordArithmetic.Operation' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordArithmetic.Operation

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordArithmetic.word' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordArithmetic.word

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordArithmetic.eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordArithmetic.eval

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordArithmetic.checked_multiply_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordArithmetic.checked_multiply_bounded

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordArithmetic.checked_byte_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordArithmetic.checked_byte_capacity

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordArithmetic.unchecked_subtract_underflow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordArithmetic.unchecked_subtract_underflow

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordArithmetic.logical_not_twice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordArithmetic.logical_not_twice

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordArithmetic.boolean_distinct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordArithmetic.boolean_distinct

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordArithmetic.Operation.checkedMultiply' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordArithmetic.Operation.checkedMultiply

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordArithmetic.Operation.greater' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordArithmetic.Operation.greater

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordArithmetic.Operation.lessEqual' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordArithmetic.Operation.lessEqual

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordArithmetic.Operation.equal' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordArithmetic.Operation.equal

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordArithmetic.Operation.wrappingSubtract' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordArithmetic.Operation.wrappingSubtract

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordArithmetic.Operation.uncheckedSubtract' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordArithmetic.Operation.uncheckedSubtract

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordArithmetic.Operation.wrappingShiftLeft' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordArithmetic.Operation.wrappingShiftLeft

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordArithmetic.Operation.bitOr' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordArithmetic.Operation.bitOr

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordArithmetic.Operation.logicalNot' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordArithmetic.Operation.logicalNot

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordLLBC.evalArithmetic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordLLBC.evalArithmetic

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordLLBC.evalArithmetic_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordLLBC.evalArithmetic_world

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordLLBC.evalBooleanOperand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordLLBC.evalBooleanOperand

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordLLBC.evalBooleanOperand_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordLLBC.evalBooleanOperand_world

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordValues.Ty.boolean' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordValues.Ty.boolean

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordValues.Value.boolean' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordValues.Value.boolean

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordLLBC.Input.boolean' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordLLBC.Input.boolean

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordLLBC.Operand.boolean' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordLLBC.Operand.boolean

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordLLBC.Rvalue.arithmetic' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordLLBC.Rvalue.arithmetic

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordLLBC.Body.switchBoolean' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordLLBC.Body.switchBoolean

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordLLBC.eval_matchChoice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordLLBC.eval_matchChoice


/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordLLBC.ZeroSizeEnum.valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordLLBC.ZeroSizeEnum.valid

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordLLBC.ZeroSizeEnum.read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordLLBC.ZeroSizeEnum.read

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordLLBC.ZeroSizeEnum.read_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordLLBC.ZeroSizeEnum.read_exact

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordLLBC.ZeroSizeEnum.inhabited_discriminant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordLLBC.ZeroSizeEnum.inhabited_discriminant

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordLLBC.evalKnownDiscriminant_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordLLBC.evalKnownDiscriminant_world
