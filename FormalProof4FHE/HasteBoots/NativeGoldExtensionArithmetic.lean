module

public import FormalProof4FHE.HasteBoots.NativeGoldArithmetic
public import FormalProof4FHE.HasteBoots.NativeFieldWire

@[expose] public section

/-!
# Raw Goldilocks extension arithmetic used in lookup claims

Addition/subtraction and multiplication by a base-field word follow the
coordinate loops of `BinomialExtensionField`. Exact raw outputs are retained.
Full extension multiplication/inversion and instruction refinement remain open.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldExtensionArithmetic

open NativeFieldRepresentation NativeFieldWire NativeExtensionFields

abbrev Word := GoldExtension

def add (left right : Word) : Word := fun i => NativeGoldArithmetic.add (left i) (right i)
def sub (left right : Word) : Word := fun i => NativeGoldArithmetic.sub (left i) (right i)
def neg (word : Word) : Word := fun i => NativeGoldArithmetic.neg (word i)
def scale (word : Word) (scalar : GoldWord) : Word := fun i => NativeGoldArithmetic.mul (word i) scalar

/-- Literal ordered zip/fold in `packed_extension_lookup::table_sum`.
Extra entries on either side are ignored, as in the Rust iterator. -/
def tableSum (inverses : List Word) (multiplicities : List GoldWord) : Word :=
  (inverses.zip multiplicities).foldl
    (fun out pair => add out (scale pair.1 pair.2)) (fun _ => 0)

noncomputable section

theorem zero_value : goldExtensionValue (fun _ => 0) = 0 := by
  apply goldilocksBasis.equivFun.injective
  ext i
  simp [goldExtension_coordinate, goldValue]

theorem add_value (left right : Word) :
    goldExtensionValue (add left right) = goldExtensionValue left + goldExtensionValue right := by
  apply goldilocksBasis.equivFun.injective
  ext i
  simp only [map_add, Pi.add_apply, goldExtension_coordinate, add, NativeGoldArithmetic.add_value]

theorem sub_value (left right : Word) :
    goldExtensionValue (sub left right) = goldExtensionValue left - goldExtensionValue right := by
  apply goldilocksBasis.equivFun.injective
  ext i
  simp only [map_sub, Pi.sub_apply, goldExtension_coordinate, sub, NativeGoldArithmetic.sub_value]

theorem neg_value (word : Word) : goldExtensionValue (neg word) = -goldExtensionValue word := by
  apply goldilocksBasis.equivFun.injective
  ext i
  simp only [map_neg, Pi.neg_apply, goldExtension_coordinate, neg, NativeGoldArithmetic.neg_value]

theorem scale_value (word : Word) (scalar : GoldWord) :
    goldExtensionValue (scale word scalar) = goldValue scalar • goldExtensionValue word := by
  apply goldilocksBasis.equivFun.injective
  ext i
  simp only [map_smul, Pi.smul_apply, goldExtension_coordinate, scale, NativeGoldArithmetic.mul_value, smul_eq_mul, mul_comm]

private theorem tableFold_value (pairs : List (Word × GoldWord)) (initial : Word) :
    goldExtensionValue (pairs.foldl (fun out pair => add out (scale pair.1 pair.2)) initial) =
      goldExtensionValue initial +
        (pairs.map (fun pair => goldValue pair.2 • goldExtensionValue pair.1)).sum := by
  induction pairs generalizing initial with
  | nil => simp
  | cons pair tail ih =>
    simp only [List.foldl_cons, ih, add_value, scale_value, List.map_cons, List.sum_cons, add_assoc]

theorem tableSum_value (inverses : List Word) (multiplicities : List GoldWord) :
    goldExtensionValue (tableSum inverses multiplicities) =
      ((inverses.zip multiplicities).map
        (fun pair => goldValue pair.2 • goldExtensionValue pair.1)).sum := by
  rw [tableSum, tableFold_value, zero_value, zero_add]

/-- Native canonical coordinate comparison, with raw storage left intact. -/
def Equal (left right : Word) : Prop := ∀ i, goldCanonical (left i) = goldCanonical (right i)

theorem equal_iff (left right : Word) : Equal left right ↔ goldExtensionValue left = goldExtensionValue right := by
  constructor
  · intro same
    apply goldilocksBasis.equivFun.injective
    ext i
    simp only [goldExtension_coordinate]
    exact (goldValue_eq_iff _ _).mpr (same i)
  · intro same i
    apply (goldValue_eq_iff _ _).mp
    have coords := congrArg (fun value => goldilocksBasis.equivFun value i) same
    simpa only [goldExtension_coordinate] using coords

/-- The independently checked native sumcheck recurrence. -/
theorem recurrence_iff (first second claim : Word) :
    Equal (add first second) claim ↔
      goldExtensionValue first + goldExtensionValue second = goldExtensionValue claim := by
  rw [equal_iff, add_value]

end

end FormalProof4FHE.HasteBoots.NativeGoldExtensionArithmetic
