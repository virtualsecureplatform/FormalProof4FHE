module

public import FormalProof4FHE.HasteBoots.NativeGoldCoefficientsQuery
public import FormalProof4FHE.HasteBoots.NativeTerminalBits

@[expose] public section

/-!
# Raw scalar-source lane weights

The native scalar-query loop multiplies low point coordinates in their
original order, selecting x or 1-x from the actual lane shift-and-mask bit.
The raw accumulator and its offset are retained. Its field interpretation
is the existing low-bit-first tensor weight, without a supplied bit decoder.
The outer scalar-query shape/ilog2 check and instruction refinement are
separate obligations.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldLaneWeights

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeGoldExtensionArithmetic (Word)
open NativeUsizeMessage (Usize)
open scoped BigOperators

/-- Total word embedding; validated matrix lanes are proved not to wrap. -/
def laneWord (lane : ℕ) : Usize := ⟨lane % (2 ^ 64), Nat.mod_lt _ (by decide)⟩

def weightFrom (lane : Usize) : ℕ → List Word → Word → Word
  | _, [], out => out
  | offset, x :: tail, out => weightFrom lane (offset + 1) tail
      (NativeGoldCubic.mul out (if NativeTerminalBits.bit lane offset then x
        else NativeGoldExtensionArithmetic.sub NativeGoldLookup.one x))

def weight (lane : Usize) (point : List Word) : Word := weightFrom lane 0 point NativeGoldLookup.one

theorem laneWord_val (lane : ℕ) (fits : lane < 2 ^ 64) : (laneWord lane).val = lane := Nat.mod_eq_of_lt fits

/-- Matrix-square validation already bounds every lane; no work cap is added. -/
theorem width_fits (width : ℕ) (shape : NativeGoldProjection.dimensions width = true) : width < 2 ^ 64 :=
  (Nat.le_mul_self width).trans_lt ((NativeGoldProjection.dimensions_iff width).mp shape).2

/-- The checked packing shape bounds every native shift in the lane loop. -/
theorem lane_bits_fits {width c : ℕ} (shape : NativeGoldProjection.dimensions width = true)
    (power : width = 2 ^ c) : c < 64 := by
  have bound := width_fits width shape
  rw [power] at bound
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp bound

/-- The recursive loop is the literal enumerated left fold used by Rust. -/
theorem weightFrom_fold (lane : Usize) (offset : ℕ) (point : List Word) (out : Word) :
    weightFrom lane offset point out = (point.zipIdx offset).foldl (fun current pair =>
      NativeGoldCubic.mul current (if NativeTerminalBits.bit lane pair.2 then pair.1
        else NativeGoldExtensionArithmetic.sub NativeGoldLookup.one pair.1)) out := by
  induction point generalizing offset out with
  | nil => rfl
  | cons x tail ih => rw [weightFrom, List.zipIdx_cons, List.foldl_cons, ih]

noncomputable section

theorem weightFrom_value {n : ℕ} (lane : Usize) (offset : ℕ) (point : Fin n → Word) (out : Word) :
    goldExtensionValue (weightFrom lane offset (List.ofFn point) out) = goldExtensionValue out *
      ∏ i : Fin n, if NativeTerminalBits.bit lane (offset + i.val) then goldExtensionValue (point i)
        else 1 - goldExtensionValue (point i) := by
  induction n generalizing offset out with
  | zero => simp only [List.ofFn_zero, weightFrom, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  | succ n ih =>
    rw [List.ofFn_succ, weightFrom, ih, NativeGoldCubic.mul_value]
    simp only [apply_ite goldExtensionValue, NativeGoldExtensionArithmetic.sub_value, NativeGoldLookup.one_value,
      Fin.prod_univ_succ, Fin.val_zero, Nat.add_zero, Fin.val_succ]
    have offsets (i : Fin n) : offset + 1 + i.val = offset + (i.val + 1) := by omega
    simp only [offsets, mul_assoc]
    rfl

theorem weight_value {n : ℕ} (lane : Usize) (point : Fin n → Word) :
    goldExtensionValue (weight lane (List.ofFn point)) =
      ∏ i : Fin n, if NativeTerminalBits.bit lane i.val then goldExtensionValue (point i)
        else 1 - goldExtensionValue (point i) := by
  rw [weight, weightFrom_value, NativeGoldLookup.one_value, one_mul]
  simp only [Nat.zero_add]

/-- The shift-and-mask predicate is derived from the actual source lane's
canonical low-bit address, in the same order as the generic query. -/
theorem lane_bit {padding c : ℕ} (shape : NativeGoldProjection.dimensions (3 + padding) = true)
    (power : 3 + padding = 2 ^ c) (lane : Fin (3 + padding)) (i : Fin c) :
    NativeTerminalBits.bit (laneWord lane.val) i.val =
      finTwoEquiv (PackedEqualityCube.bits c (ExtensionQuery.nativeLanes power lane) i) := by
  have fits : lane.val < 2 ^ 64 := lane.isLt.trans (width_fits _ shape)
  have address : (NativeEqualityTable.address c
      (PackedEqualityCube.bits c (ExtensionQuery.nativeLanes power lane))).val = lane.val := by
    simp only [NativeEqualityTable.address, Equiv.trans_apply, Equiv.symm_apply_apply]
    exact ExtensionQuery.nativeLanes_index power lane
  rw [NativeTerminalBits.bit_testBit, laneWord_val _ fits, ← address,
    NativeTerminalBits.address_testBit]

/-- Every raw lane weight is the tensor weight of that same original lane. -/
theorem weight_nativeLanes {padding c : ℕ} (point : Fin c → Word)
    (shape : NativeGoldProjection.dimensions (3 + padding) = true)
    (power : 3 + padding = 2 ^ c) (lane : Fin (3 + padding)) :
    goldExtensionValue (weight (laneWord lane.val) (List.ofFn point)) =
      ExtensionQuery.laneWeights (ExtensionQuery.nativeLanes power) (fun i => goldExtensionValue (point i)) lane := by
  rw [weight_value, ExtensionQuery.laneWeights, PackedEqualityCube.weight, PackedZeroEquality.equality_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [lane_bit shape power lane i]
  generalize PackedEqualityCube.bits c (ExtensionQuery.nativeLanes power lane) i = selected
  fin_cases selected <;> rfl

end

end FormalProof4FHE.HasteBoots.NativeGoldLaneWeights
