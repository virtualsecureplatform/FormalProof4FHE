module

public import FormalProof4FHE.HasteBoots.NativeEqualityTable
public import FormalProof4FHE.HasteBoots.ExtensionQuery
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-!
# Active-prefix masks at arbitrary extension-field points

The threshold is represented by its canonical low-bit address coordinates.
The native high-to-low loop tracks `same` and `out`. Its field result is the
ordinary MLE of the active-prefix indicator, including the separate full-table
branch. This is exact field/address semantics; linking Rust shift operations,
word sizes and concrete field representations remains a refinement obligation.
-/

open scoped BigOperators Classical

namespace FormalProof4FHE.HasteBoots.NativePrefixMask

noncomputable section

variable {K : Type} [Field K] {n : ℕ}

abbrev Cell := PackedZeroEquality.Cell

def mle (point : Fin n → K) (values : Cell n → K) : K :=
  ∑ cell, PackedZeroEquality.equality point cell * values cell

/-- Split on the high address bit, retaining every lower coordinate. -/
theorem mle_snoc (point : Fin (n + 1) → K) (values : Cell (n + 1) → K) :
    mle point values =
      (1 - point (Fin.last n)) * mle (fun i => point i.castSucc) (fun cell => values (Fin.snoc cell 0)) +
        point (Fin.last n) * mle (fun i => point i.castSucc) (fun cell => values (Fin.snoc cell 1)) := by
  unfold mle
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => Fin 2)).sum_comp]
  change (∑ pair : Fin 2 × (Fin n → Fin 2),
    PackedZeroEquality.equality point (Fin.snoc pair.2 pair.1) * values (Fin.snoc pair.2 pair.1)) = _
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two,
    NativeEqualityTable.equality_succ, Fin.snoc_castSucc, Fin.snoc_last, ite_true,
    one_ne_zero, ite_false]
  simp only [Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro cell _ <;> ring

theorem mle_one (point : Fin n → K) : mle point (fun _ => 1) = 1 := by
  induction n with
  | zero => simp [mle, PackedZeroEquality.equality_prod]
  | succ n ih => rw [mle_snoc, ih]; ring

theorem mle_zero (point : Fin n → K) : mle point (fun _ => 0) = 0 := by simp [mle]

def core : (n : ℕ) → Cell n → (Fin n → K) → K
  | 0, _, _ => 0
  | n + 1, threshold, point =>
    if threshold (Fin.last n) = 0 then
      (1 - point (Fin.last n)) * core n (fun i => threshold i.castSucc) (fun i => point i.castSucc)
    else
      (1 - point (Fin.last n)) + point (Fin.last n) * core n (fun i => threshold i.castSucc) (fun i => point i.castSucc)

/-- Direct state-passing semantics of the native descending-coordinate loop. -/
def loop : (n : ℕ) → Cell n → (Fin n → K) → K → K → K
  | 0, _, _, _, out => out
  | n + 1, threshold, point, same, out =>
    if threshold (Fin.last n) = 0 then
      loop n (fun i => threshold i.castSucc) (fun i => point i.castSucc) (same * (1 - point (Fin.last n))) out
    else
      loop n (fun i => threshold i.castSucc) (fun i => point i.castSucc)
        (same * point (Fin.last n)) (out + same * (1 - point (Fin.last n)))

theorem loop_affine (threshold : Cell n) (point : Fin n → K) (same out : K) :
    loop n threshold point same out = out + same * core n threshold point := by
  induction n generalizing same out with
  | zero => simp [loop, core]
  | succ n ih =>
    simp only [loop, core]
    split <;> rw [ih] <;> ring

theorem loop_result (threshold : Cell n) (point : Fin n → K) :
    loop n threshold point 1 0 = core n threshold point := by rw [loop_affine, one_mul, zero_add]

theorem address_snoc (cell : Cell n) (bit : Fin 2) :
    (NativeEqualityTable.address (n + 1) (Fin.snoc cell bit)).val =
      (NativeEqualityTable.address n cell).val + 2 ^ n * bit.val := by
  rw [NativeEqualityTable.address_succ]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- The high-to-low field loop equals the full tensor interpolation of the
strictly-less-than-threshold Boolean table. -/
theorem core_eq_mle (threshold : Cell n) (point : Fin n → K) :
    core n threshold point = mle point (fun cell =>
      if (NativeEqualityTable.address n cell).val < (NativeEqualityTable.address n threshold).val then 1 else 0) := by
  induction n with
  | zero =>
    have allZero (cell : Cell 0) : (NativeEqualityTable.address 0 cell).val = 0 := by
      have bound := (NativeEqualityTable.address 0 cell).isLt
      simp only [pow_zero] at bound
      omega
    simp only [core, allZero, lt_self_iff_false, ite_false, mle_zero]
  | succ n ih =>
    let lowThreshold : Cell n := fun i => threshold i.castSucc
    have thresholdAddress := NativeEqualityTable.address_succ threshold
    have thresholdBound := (NativeEqualityTable.address n lowThreshold).isLt
    have zeroSide (cell : Cell n) := address_snoc cell 0
    have oneSide (cell : Cell n) := address_snoc cell 1
    by_cases highZero : threshold (Fin.last n) = 0
    · have thresholdLow : (NativeEqualityTable.address (n + 1) threshold).val =
          (NativeEqualityTable.address n lowThreshold).val := by
        simpa only [highZero, Fin.val_zero, mul_zero, add_zero] using thresholdAddress
      have zeroValues : (fun cell : Cell n => if (NativeEqualityTable.address (n + 1) (Fin.snoc cell 0)).val <
          (NativeEqualityTable.address (n + 1) threshold).val then (1 : K) else 0) =
          fun cell => if (NativeEqualityTable.address n cell).val < (NativeEqualityTable.address n lowThreshold).val then 1 else 0 := by
        funext cell
        simp only [zeroSide, Fin.val_zero, mul_zero, add_zero, thresholdLow]
      have oneValues : (fun cell : Cell n => if (NativeEqualityTable.address (n + 1) (Fin.snoc cell 1)).val <
          (NativeEqualityTable.address (n + 1) threshold).val then (1 : K) else 0) = fun _ => 0 := by
        funext cell
        have side := oneSide cell
        simp only [Fin.val_one, mul_one] at side
        have outside : ¬(NativeEqualityTable.address (n + 1) (Fin.snoc cell 1)).val <
            (NativeEqualityTable.address (n + 1) threshold).val := by omega
        exact ite_eq_right outside
      rw [core, ite_eq_left highZero, mle_snoc, zeroValues, oneValues, mle_zero, mul_zero, add_zero, ← ih]
    · have highOne : threshold (Fin.last n) = 1 := Fin.eq_one_of_ne_zero _ highZero
      have thresholdHigh : (NativeEqualityTable.address (n + 1) threshold).val =
          (NativeEqualityTable.address n lowThreshold).val + 2 ^ n := by
        simpa only [highOne, Fin.val_one, mul_one] using thresholdAddress
      have zeroValues : (fun cell : Cell n => if (NativeEqualityTable.address (n + 1) (Fin.snoc cell 0)).val <
          (NativeEqualityTable.address (n + 1) threshold).val then (1 : K) else 0) = fun _ => 1 := by
        funext cell
        have side := zeroSide cell
        have bound := (NativeEqualityTable.address n cell).isLt
        simp only [Fin.val_zero, mul_zero, add_zero] at side
        have inside : (NativeEqualityTable.address (n + 1) (Fin.snoc cell 0)).val <
            (NativeEqualityTable.address (n + 1) threshold).val := by omega
        exact ite_eq_left inside
      have oneValues : (fun cell : Cell n => if (NativeEqualityTable.address (n + 1) (Fin.snoc cell 1)).val <
          (NativeEqualityTable.address (n + 1) threshold).val then (1 : K) else 0) =
          fun cell => if (NativeEqualityTable.address n cell).val < (NativeEqualityTable.address n lowThreshold).val then 1 else 0 := by
        funext cell
        simp only [oneSide, Fin.val_one, mul_one, thresholdHigh, Nat.add_lt_add_iff_right]
      rw [core, ite_eq_right highZero, mle_snoc, zeroValues, oneValues, mle_one, mul_one, ← ih]

/-- The native full-table shortcut is separate from the strict-prefix loop. -/
def evaluatePrefix (point : Fin n → K) (count : ℕ) (enough : count ≤ 2 ^ n) : K :=
  if full : count = 2 ^ n then 1 else
    loop n ((NativeEqualityTable.address n).symm ⟨count, by omega⟩) point 1 0

theorem prefix_eq_mle (point : Fin n → K) (count : ℕ) (enough : count ≤ 2 ^ n) :
    evaluatePrefix point count enough = mle point (fun cell => if (NativeEqualityTable.address n cell).val < count then 1 else 0) := by
  unfold evaluatePrefix
  split
  · rename_i full
    have values : (fun cell : Cell n => if (NativeEqualityTable.address n cell).val < count then (1 : K) else 0) = fun _ => 1 := by
      funext cell
      exact ite_eq_left (by simpa only [full] using (NativeEqualityTable.address n cell).isLt)
    rw [values, mle_one]
  · rw [loop_result, core_eq_mle]
    simp only [Equiv.apply_symm_apply]

/-- Public prefix evaluation is exactly the mask source evaluated through the
same ordered scalar MLE used by extension source queries. -/
theorem prefix_eq_evaluate (point : Fin n → K) (count : ℕ) (enough : count ≤ 2 ^ n) :
    evaluatePrefix point count enough = ExtensionQuery.evaluate n point
      (fun cell => if (FlatMatrixFold.index n cell).val < count then 1 else 0) := by
  rw [ExtensionQuery.evaluate_eq_sum, PackedEqualityCube.weighted_sum]
  exact prefix_eq_mle point count enough

/-- Boolean points recover the literal trusted active-prefix table. -/
theorem prefix_boolean (cell : Cell n) (count : ℕ) (enough : count ≤ 2 ^ n) :
    evaluatePrefix (fun i => (cell i : K)) count enough =
      if (NativeEqualityTable.address n cell).val < count then 1 else 0 := by
  rw [prefix_eq_mle]
  unfold mle
  rw [PackedZeroEquality.weighted_sum, MvPolynomial.MLE_eval_zeroOne]

theorem prefix_full (point : Fin n → K) : evaluatePrefix point (2 ^ n) le_rfl = 1 := by
  simp [evaluatePrefix]

theorem prefix_zero (point : Fin n → K) : evaluatePrefix point 0 (Nat.zero_le _) = 0 := by
  rw [prefix_eq_mle]
  simp only [Nat.not_lt_zero, ite_false, mle_zero]

end

end FormalProof4FHE.HasteBoots.NativePrefixMask
