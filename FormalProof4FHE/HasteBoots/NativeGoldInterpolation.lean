module

public import FormalProof4FHE.HasteBoots.NativeInterpolationField
public import FormalProof4FHE.HasteBoots.NativeGoldLookup

@[expose] public section

/-!
# Native raw Goldilocks interpolation arithmetic

The literal operation core is instantiated by the previously proved raw
addition, subtraction, Karatsuba multiplication, negation and cubic division.
Known-node results return the exact received word. No normalization is
inserted. Unchecked native panic preconditions are explicit failures here.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldInterpolation

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeGoldExtensionArithmetic (Word)
open NativeInterpolationCore

def equal (left right : Word) : Bool := decide (∀ i, goldCanonical (left i) = goldCanonical (right i))

def arithmetic : Arithmetic Word :=
  ⟨NativeGoldLookup.zero, NativeGoldLookup.one, NativeGoldExtensionArithmetic.add,
    NativeGoldExtensionArithmetic.sub, NativeGoldCubic.mul, NativeGoldExtensionArithmetic.neg,
    equal, NativeGoldCubicInverse.divResult⟩

def interpolate (values : List Word) (point : Word) : Option Word :=
  NativeInterpolationCore.interpolate arithmetic values point

noncomputable section

theorem equal_value (left right : Word) :
    equal left right = (NativeInterpolationField.arithmetic Goldilocks3).equal
      (goldExtensionValue left) (goldExtensionValue right) := by
  apply Bool.eq_iff_iff.mpr
  simp only [equal, NativeInterpolationField.arithmetic, decide_eq_true_eq]
  exact NativeGoldExtensionArithmetic.equal_iff left right

/-- Both zero spellings fail raw inversion; this is a failed unchecked
native precondition, not a graceful verifier rejection claim. -/
theorem inverse_zero (value : Word) (zero : goldExtensionValue value = 0) :
    NativeGoldCubicInverse.inverseResult value = none := by
  have coordinate (i : Fin 3) : goldValue (value i) = 0 := by
    have same := congrArg (fun v => goldilocksBasis.equivFun v i) zero
    simpa only [goldExtension_coordinate, map_zero, Pi.zero_apply] using same
  have determinantZero : goldValue (NativeGoldCubicInverse.determinant value) = 0 := by
    rw [NativeGoldCubicInverse.determinant_value, coordinate 0, coordinate 1, coordinate 2]
    ring
  rw [NativeGoldCubicInverse.inverseResult,
    (NativeGoldInverse.tryInverse_none _).mpr determinantZero, Option.map_none]

theorem divide_value (left right : Word) :
    (NativeGoldCubicInverse.divResult left right).map goldExtensionValue =
      (NativeInterpolationField.arithmetic Goldilocks3).divide (goldExtensionValue left) (goldExtensionValue right) := by
  by_cases zero : goldExtensionValue right = 0
  · simp only [NativeGoldCubicInverse.divResult, inverse_zero right zero, Option.map_none,
      NativeInterpolationField.arithmetic, zero, ite_true]
  · simpa only [NativeInterpolationField.arithmetic, zero, ite_false] using
      NativeGoldCubicInverse.divResult_value left right zero

/-- Every primitive of the concrete raw algorithm has a checked field
interpretation, including equality branches and failed division. -/
theorem arithmetic_hom : Hom arithmetic (NativeInterpolationField.arithmetic Goldilocks3) goldExtensionValue where
  map_zero := NativeGoldLookup.zero_value
  map_one := NativeGoldLookup.one_value
  map_add := NativeGoldExtensionArithmetic.add_value
  map_sub := NativeGoldExtensionArithmetic.sub_value
  map_mul := NativeGoldCubic.mul_value
  map_neg := NativeGoldExtensionArithmetic.neg_value
  map_equal := equal_value
  map_divide := divide_value

/-- Full branch- and failure-preserving interpretation of the actual raw
algorithm in the same literal field loop. Polynomial correspondence remains
separate from this representation refinement. -/
theorem interpolate_value (values : List Word) (point : Word) :
    (interpolate values point).map goldExtensionValue =
      NativeInterpolationCore.interpolate (NativeInterpolationField.arithmetic Goldilocks3)
        (values.map goldExtensionValue) (goldExtensionValue point) :=
  NativeInterpolationCore.interpolate_map arithmetic_hom values point

theorem factorial_value (count : ℕ) :
    (goldExtensionValue (NativeInterpolationCore.factorial arithmetic count).1,
      goldExtensionValue (NativeInterpolationCore.factorial arithmetic count).2) =
      ((count.factorial : Goldilocks3), ((count + 1 : ℕ) : Goldilocks3)) := by
  exact (NativeInterpolationCore.factorial_map arithmetic_hom count).trans
    (NativeInterpolationField.factorial_value count)

/-- A sampled zero node returns the message's original raw representative. -/
theorem interpolate_zero_node (first : Word) (rest : List Word) (point : Word)
    (zero : goldExtensionValue point = 0) : interpolate (first :: rest) point = some first := by
  apply NativeInterpolationCore.interpolate_at_zero arithmetic first rest point
  change equal point NativeGoldLookup.zero = true
  rw [equal_value]
  simp [NativeInterpolationField.arithmetic, zero, NativeGoldLookup.zero_value]

end

end FormalProof4FHE.HasteBoots.NativeGoldInterpolation
