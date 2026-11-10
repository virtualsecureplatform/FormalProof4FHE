module
import FormalProof4FHE.HasteBoots.SingleHelperNativeValue

namespace FormalProof4FHE.HasteBoots.SingleHelperSmoke
open NativeFields NativeFieldRepresentation NativeFieldWire

def zero : GoldExtension := fun _ => 0
def aliasZero : GoldExtension := fun _ => ⟨goldilocksModulus, by decide +kernel⟩

/-- Native equality accepts both raw spellings of zero. -/
example : NativeGoldInterpolation.equal zero aliasZero = true := by decide +kernel

/-- Guard equality cannot replace the original raw coefficient packet. -/
example : NativeGoldHelper.vector 3 zero ≠ NativeGoldHelper.vector 3 aliasZero := by decide +kernel

/-- The field interpretation, which the algebraic reduction needs, does agree. -/
example : (NativeGoldHelper.vector 3 zero).map goldValue =
    (NativeGoldHelper.vector 3 aliasZero).map goldValue :=
  SingleHelperNativeValue.matched_vector 3 zero aliasZero (by decide +kernel)

end FormalProof4FHE.HasteBoots.SingleHelperSmoke
