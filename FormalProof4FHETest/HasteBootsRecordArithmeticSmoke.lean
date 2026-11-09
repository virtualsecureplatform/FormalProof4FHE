module
import FormalProof4FHE.HasteBoots.NativeRecordLLBC
namespace FormalProof4FHETest.HasteBootsRecordArithmeticSmoke
open FormalProof4FHE.HasteBoots
open NativeRecordArithmetic
open NativeRecordLLBC (Frame Body Flow)
example (capacity : NativeWord64Memory.Word) :
    eval .checkedMultiply [.scalar (.usize 1),.scalar (.usize capacity)] =
      some (.pair (.scalar (.usize capacity)) (.pair (.boolean false) (.scalar .unit))) := checked_byte_capacity capacity
example : eval .checkedMultiply [.scalar (.usize 7),.scalar (.usize 9)] =
    some (.pair (.scalar (.usize 63)) (.pair (.boolean false) (.scalar .unit))) := by decide
example : eval .checkedMultiply [.scalar (.usize (2^64-1)),.scalar (.usize 2)] =
    some (.pair (.scalar (.usize (2^64-2))) (.pair (.boolean true) (.scalar .unit))) := by decide
example : eval .wrappingSubtract [.scalar (.usize 0),.scalar (.usize 1)] = some (.scalar (.usize (2^64-1))) := by decide
example : eval .uncheckedSubtract [.scalar (.usize 0),.scalar (.usize 1)] = none := by decide
example : eval .uncheckedSubtract [.scalar (.usize 8),.scalar (.usize 3)] = some (.scalar (.usize 5)) := by decide
example : eval .greater [.scalar (.usize (2^64-1)),.scalar (.usize 0)] = some (.boolean true) := by decide
example : eval .lessEqual [.scalar (.usize 3),.scalar (.usize 3)] = some (.boolean true) := by decide
example : eval .equal [.scalar (.usize (2^64-1)),.scalar (.usize (2^64-1))] = some (.boolean true) := by decide
example : eval .wrappingShiftLeft [.scalar (.usize 1),.scalar (.usize 64)] = some (.scalar (.usize 1)) := by decide
example : eval .bitOr [.scalar (.usize 8),.scalar (.usize 4)] = some (.scalar (.usize 12)) := by decide
example : eval .logicalNot [.boolean true] = some (.boolean false) := by decide
example : eval .logicalNot [.scalar (.usize 1)] = none ∧ eval .checkedMultiply [.scalar (.usize 1)] = none := by decide
example (value : Bool) (word : NativeWord64Memory.Word) :
    NativeRecordValues.fits .boolean (.boolean value) = true ∧
      NativeRecordValues.fits .boolean (.scalar (.usize word)) = false ∧
      NativeRecordValues.fits (.scalar .usize) (.boolean value) = false := boolean_distinct value word
example (world : NativeReferenceMachine.State) (condition : Bool) :
    NativeRecordLLBC.eval (.switchBoolean (.boolean condition) .done (.unsupported "allocator failure") .done) ⟨[],[],world⟩ =
      if condition then .normal ⟨[],[],world⟩ else .unsupported "allocator failure" world := by
  cases condition <;> rfl
example (world : NativeReferenceMachine.State) :
    NativeRecordLLBC.eval (.switchBoolean (.usize 1) .done .done .done) ⟨[],[],world⟩ = .invalid world := rfl
example (world : NativeReferenceMachine.State) :
    NativeRecordLLBC.eval (.switchBoolean (.move 0 []) .done .abort .done)
      ⟨[.boolean],[.live (some (.boolean true))],world⟩ =
      .normal ⟨[.boolean],[.live (some .uninit)],world⟩ := by
  simp [NativeRecordLLBC.eval,NativeRecordLLBC.evalBooleanOperand,NativeRecordLLBC.evalOperand,NativeRecordLLBC.read,
    NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.complete,NativeRecordValues.fits,
    NativeRecordValues.compatible,NativeRecordValues.replace]
end FormalProof4FHETest.HasteBootsRecordArithmeticSmoke
