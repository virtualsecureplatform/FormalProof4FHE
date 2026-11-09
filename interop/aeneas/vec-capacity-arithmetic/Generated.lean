module
public import FormalProof4FHE.HasteBoots.NativeRecordCallValues
@[expose] public section
namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC
-- Original assignment SHA256 37d92bed7ddb159eb68017984a9a93765fd066ce5fef61b9864dbb0f9dee4d14
def expr_wrappingSubtract : Rvalue := .arithmetic .wrappingSubtract [(.copy 10 []), (.usize 0)]
def step_wrappingSubtract : Body := .assign 9 expr_wrappingSubtract .done
-- Original assignment SHA256 13799316c44ab7c15f87a46993a1afafc6b11108f93ae6331afc6bbd1a55420d
def expr_greater : Rvalue := .arithmetic .greater [(.copy 1 []), (.move 9 [])]
def step_greater : Body := .assign 6 expr_greater .done
-- Original assignment SHA256 3e950efdec7ab88189a28e946b2568d49d2dfba6a527cf894aebcb34e45d12e7
def expr_logicalNot : Rvalue := .arithmetic .logicalNot [(.move 6 [])]
def step_logicalNot : Body := .assign 5 expr_logicalNot .done
-- Original assignment SHA256 b23365657c9a2153e7f7bd0499ea1ca075b3b5ebfa33cee8fd8f7c3d1f0e0033
def expr_checkedMultiply : Rvalue := .arithmetic .checkedMultiply [(.move 26 []), (.move 27 [])]
def step_checkedMultiply : Body := .assign 25 expr_checkedMultiply .done
-- Original assignment SHA256 c2421d8684e6513e8479941425cb448bde99a4107c0411a8d3474760d403703f
def expr_uncheckedSubtract : Rvalue := .arithmetic .uncheckedSubtract [(.usize 9223372036854775808), (.move 33 [])]
def step_uncheckedSubtract : Body := .assign 32 expr_uncheckedSubtract .done
-- Original assignment SHA256 8db28f6cc8a171e349409869e9f791b546086da268f91d27f37206923f1bb82a
def expr_lessEqual : Rvalue := .arithmetic .lessEqual [(.copy 28 []), (.move 32 [])]
def step_lessEqual : Body := .assign 30 expr_lessEqual .done
-- Original assignment SHA256 917bc79f5c8f8d8f43d34bd1c01dcfe28a81c4c934ca5c8aa64bb239f99b8a87
def expr_equal : Rvalue := .arithmetic .equal [(.copy 32 []), (.usize 1)]
def step_equal : Body := .assign 33 expr_equal .done
-- Original assignment SHA256 22c38f98d775e56e7afc1dcd1d38639d0954b458f17078dc9b1a64a907b6e778
def expr_wrappingShiftLeft : Rvalue := .arithmetic .wrappingShiftLeft [(.move 11 []), (.usize 1)]
def step_wrappingShiftLeft : Body := .assign 10 expr_wrappingShiftLeft .done
-- Original assignment SHA256 6a0d38b7f179388a70b6b075e5aa79fc500ea6b08bd17df21b83f66da0e7c4fb
def expr_bitOr : Rvalue := .arithmetic .bitOr [(.move 10 []), (.usize 1)]
def step_bitOr : Body := .assign 9 expr_bitOr .done
def checkedLeft : Nat := 26
def checkedRight : Nat := 27
def checkedDestination : Nat := 25
def checkedFrame (world : NativeReferenceMachine.State) (left right : NativeWord64Memory.Word) : Frame :=
  ⟨[(.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.pair (.scalar .usize) (.pair .boolean (.scalar .unit))), (.scalar .usize), (.scalar .usize)], [.dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, (.live none), (.live (some (.scalar (.usize left)))), (.live (some (.scalar (.usize right))))], world⟩
def checkedAfter (world : NativeReferenceMachine.State) (left right : NativeWord64Memory.Word) : Frame :=
  ⟨[(.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.scalar .unit), (.pair (.scalar .usize) (.pair .boolean (.scalar .unit))), (.scalar .usize), (.scalar .usize)], [.dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, (.live (some (.pair (.scalar (.usize (NativeRecordArithmetic.word (left.val*right.val)))) (.pair (.boolean (decide (2^64 ≤ left.val*right.val))) (.scalar .unit))))), (.live (some .uninit)), (.live (some .uninit))], world⟩
end HasteBootsVecCapacityArithmetic
