namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

example : decide ((0 : Nat) < 2^63) = true := by decide
example : decide ((9223372036854775807 : Nat) < 2^63) = true := by decide
example : decide ((9223372036854775808 : Nat) < 2^63) = false := by decide
example : decide ((18446744073709551615 : Nat) < 2^63) = false := by decide

example (ambient : Frame) (capacity : NativeWord64Memory.Word) (a b yes no next : Body) :
    eval (layoutPrefix a yes no next) (layoutFrame ambient capacity) =
    eval (layoutPrefix b yes no next) (layoutFrame ambient capacity) := by
  rw [layout_prefix_exact,layout_prefix_exact]

example (ambient : Frame) (capacity : NativeWord64Memory.Word) :
    (layoutAfterFrame ambient capacity).world = ambient.world := rfl

example (ambient : Frame) (capacity : NativeWord64Memory.Word) :
    (layoutAfterFrame ambient capacity).slots[2]? = some (ambient.slots[2]?.getD .dead) := rfl

example (ambient : Frame) (capacity : NativeWord64Memory.Word) :
    (layoutAfterFrame ambient capacity).slots[3]? = some (ambient.slots[3]?.getD .dead) := rfl

example (yes no next : Body) (frame : Frame) :
    continueWith next (eval (.constIf true yes no .done) frame) =
    eval (.constIf true yes no next) frame := constant_branch_tail true yes no next frame
end HasteBootsVecCapacityArithmetic
