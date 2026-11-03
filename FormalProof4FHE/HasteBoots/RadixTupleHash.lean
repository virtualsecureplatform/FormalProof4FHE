module

public import FormalProof4FHE.HasteBoots.TupleHash
public import FormalProof4FHE.HasteBoots.RadixCanonicity
public import Mathlib.Data.List.Nodup

@[expose] public section

/-!
# Tuple hashing for the actual radix comparison tables

The native table has exactly 2*radix ordered triples. Under radix<p its
digit/borrow coordinates make those triples distinct. One fixed false row,
or one false row selected from fixed sources before hashing, pays the
2*radix table union and degree two, over the actual hash field cardinality.
The hash field may be an extension distinct from the PCS analysis alphabet.
This is only the hash-collision component of lookup soundness.
-/

open OracleSpec OracleComp

namespace FormalProof4FHE.HasteBoots.RadixTupleHash

noncomputable section

def row (p radix bound : ℕ) (pair : Fin radix × Fin 2) : Fin 3 → ZMod p :=
  ![(pair.1.val : ZMod p), (pair.2.val : ZMod p),
    ((if bound < pair.1.val + pair.2.val then 1 else 0 : ℕ) : ZMod p)]

theorem table_as_product (p radix bound : ℕ) :
    RadixCanonicity.table p radix bound =
      (List.finRange radix ×ˢ List.finRange 2).map (row p radix bound) := by
  simp [RadixCanonicity.table, row, SProd.sprod, List.product, List.map_flatMap, List.map_map, Function.comp_def]

theorem table_length (p radix bound : ℕ) : (RadixCanonicity.table p radix bound).length = 2 * radix := by
  rw [table_as_product, List.length_map, List.length_product, List.length_finRange, List.length_finRange]
  omega

theorem row_injective {p radix : ℕ} (bound : ℕ) (radixSmall : radix < p) :
    Function.Injective (row p radix bound) := by
  intro first second equal
  have digitEqual := congrArg ZMod.val (congrFun equal 0)
  have bitEqual := congrArg ZMod.val (congrFun equal 1)
  change (first.1.val : ZMod p).val = (second.1.val : ZMod p).val at digitEqual
  change (first.2.val : ZMod p).val = (second.2.val : ZMod p).val at bitEqual
  rw [ZMod.val_natCast_of_lt (first.1.isLt.trans radixSmall),
    ZMod.val_natCast_of_lt (second.1.isLt.trans radixSmall)] at digitEqual
  rw [ZMod.val_natCast_of_lt (by have := first.2.isLt; omega),
    ZMod.val_natCast_of_lt (by have := second.2.isLt; omega)] at bitEqual
  exact Prod.ext (Fin.ext digitEqual) (Fin.ext bitEqual)

theorem table_nodup {p radix : ℕ} (bound : ℕ) (radixSmall : radix < p) :
    (RadixCanonicity.table p radix bound).Nodup := by
  rw [table_as_product]
  exact ((List.nodup_finRange radix).product (List.nodup_finRange 2)).map
    (row_injective bound radixSmall)

variable {p radix : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
  [DecidableEq K] [Fintype K] [SampleableType K]

theorem collision_bound (bound : ℕ) (candidate : Fin 3 → ZMod p)
    (outside : candidate ∉ RadixCanonicity.table p radix bound) :
    Pr{let y ← $ᵗ K}[∃ entry ∈ RadixCanonicity.table p radix bound,
      TupleHash.hash y candidate = TupleHash.hash y entry] ≤
      ((2 * radix : ℕ) : ENNReal) * ((2 : ENNReal) / Fintype.card K) := by
  simpa only [table_length, Nat.reduceSub, Nat.cast_ofNat] using TupleHash.list_collision_bound (K := K) candidate _ outside

theorem family_miss_bound {Position : Type} (bound : ℕ) (sources : Position → Fin 3 → ZMod p)
    (bad : ∃ position, sources position ∉ RadixCanonicity.table p radix bound) :
    Pr{let y ← $ᵗ K}[∀ position, ∃ entry ∈ RadixCanonicity.table p radix bound,
      TupleHash.hash y (sources position) = TupleHash.hash y entry] ≤
      ((2 * radix : ℕ) : ENNReal) * ((2 : ENNReal) / Fintype.card K) := by
  simpa only [table_length, Nat.reduceSub, Nat.cast_ofNat] using TupleHash.list_family_miss_bound (K := K) sources _ bad

end

end FormalProof4FHE.HasteBoots.RadixTupleHash
