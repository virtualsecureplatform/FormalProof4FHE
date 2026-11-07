module
import all FormalProof4FHE.HasteBoots.ConcreteNTTU256Division
import all FormalProof4FHE.HasteBoots.ConcreteNTTDiv64Initialization
import all FormalProof4FHE.HasteBoots.ConcreteNTTInitializedPower
import all FormalProof4FHE.HasteBoots.ConcreteNTTModularPower
import all FormalProof4FHE.HasteBoots.ConcreteNTTU256Mul128
import all FormalProof4FHE.HasteBoots.ConcreteNTTU256Add
import all FormalProof4FHE.HasteBoots.ConcreteNTTLimbAdd
import all FormalProof4FHE.HasteBoots.ConcreteNTTU256Mul64
import all FormalProof4FHE.HasteBoots.ConcreteNTTLimbArithmetic
import all FormalProof4FHE.HasteBoots.ConcreteNTTDiv64
import all FormalProof4FHE.HasteBoots.ReciprocalRemainder
import all Mathlib.Data.ZMod.Basic
import all Mathlib.Data.ZMod.Defs
import all Mathlib.Algebra.Group.Fin.Basic
import all FormalProof4FHE.HasteBoots.ConcreteNTTInitializedSearch
import all FormalProof4FHE.HasteBoots.ConcreteNTTInitializedSquareRoot
import all FormalProof4FHE.HasteBoots.ConcreteNTTInitializedRootConstruction
import all FormalProof4FHE.HasteBoots.ConcreteNTTWordSearch
import all FormalProof4FHE.HasteBoots.ConcreteNTTWordSquareRoot
import all FormalProof4FHE.HasteBoots.ConcreteNTTWordRootConstruction
import all FormalProof4FHE.HasteBoots.ConcreteNTTRootConstruction
import all FormalProof4FHE.HasteBoots.NativeFields

import all FormalProof4FHE.HasteBoots.ConcreteNTTMillerRabinField
import all FormalProof4FHE.HasteBoots.ConcreteNTTMillerRabinRound
import all FormalProof4FHE.HasteBoots.ConcreteNTTPrimeGate

namespace FormalProof4FHETest.HasteBootsConcreteNTTPrimeGateSmoke
open FormalProof4FHE.HasteBoots
open ConcreteNTTLimbArithmetic (radix Limb)
private def limb (n : Nat) : Limb := Fin.ofNat radix n

-- Independent trial division checks every small input, including zero and one.
/-- info: true -/
#guard_msgs in
#eval (List.range 200).all fun n =>
  decide (ConcreteNTTPrimeGate.check (limb n) =
    ConcreteNTTPrimeGate.Outcome.checked (decide (Nat.Prime n)))

-- Both kernel-proved native fields pass the literal retained-state gate.
/-- info: true -/
#guard_msgs in
#eval [NativeFields.goldilocksModulus, NativeFields.babyBearModulus].all fun n =>
  decide (ConcreteNTTPrimeGate.check (limb n) = ConcreteNTTPrimeGate.Outcome.checked true)

-- Large composites include pseudoprimes that pass shorter base sequences.
/-- info: true -/
#guard_msgs in
#eval [18446744073709551615, 341550071728321, 3825123056546413051].all fun n =>
  decide (ConcreteNTTPrimeGate.check (limb n) = ConcreteNTTPrimeGate.Outcome.checked false)

-- Preserve the locked sequence, including its final bases.
/-- info: true -/
#guard_msgs in
#eval decide (ConcreteNTTPrimeGate.bases = [2,3,5,7,11,13,17,19,23,29,31,37])

end FormalProof4FHETest.HasteBootsConcreteNTTPrimeGateSmoke
