module

public import FormalProof4FHE.HasteBoots.NativeScalarQueryShape

@[expose] public section

/-!
# Numeric prefix of canonical lookup binding

These are the native source-count, extension/packing, checked-add,
u32/usize shift and source/helper geometry checks before context hashing.
The source matrix-square check is not part of this prefix and is not added.
Helper width may be the source width or the extension degree three.
Context validation/framing and checked Rust refinement remain separate.
-/

namespace FormalProof4FHE.HasteBoots.NativeLookupBindGeometry

open NativeUsizeMessage (Usize)

structure Parameters where
  numVariables : Usize
  width : Usize
  deriving DecidableEq

structure Output where
  numVariables : Usize
  width : Usize
  capacity : Usize
  deriving DecidableEq

def addVariables (source width : Usize) : Option Usize :=
  if fits : source.val + NativeScalarQueryShape.laneBits width.val < 2 ^ 64 then
    some ⟨source.val + NativeScalarQueryShape.laneBits width.val, fits⟩ else none

def capacity (numVariables : Usize) : Option Usize :=
  if numVariables.val < 2 ^ 32 then
    if shift : numVariables.val < 64 then
      some ⟨2 ^ numVariables.val, (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mpr shift⟩
    else none
  else none

def compatible (sources : List Parameters) (first helper : Parameters) (logicalLength : Usize) (n size : Usize) : Bool :=
  decide (n.val ≠ 0) && decide (helper.numVariables = n) &&
    (decide (helper.width = first.width) || decide (helper.width.val = 3)) &&
    decide (logicalLength.val ≤ size.val) && sources.all (fun source =>
      decide (source.numVariables = first.numVariables) && decide (source.width = first.width))

def bind (columns : ℕ) (logicalLength : Usize) (helper : Parameters) (sources : List Parameters) : Option Output :=
  if sources.length ≠ columns then none else
    sources.head?.bind (fun first =>
      if first.width.val < 3 ∨ NativeScalarQueryShape.powerOfTwo first.width.val ≠ true then none else
        (addVariables first.numVariables first.width).bind (fun n =>
          (capacity n).bind (fun size =>
            if compatible sources first helper logicalLength n size then some ⟨n, first.width, size⟩ else none)))

structure Spec (columns : ℕ) (logicalLength : Usize) (helper : Parameters) (sources : List Parameters) (out : Output) : Prop where
  count : sources.length = columns
  first : ∃ first, sources.head? = some first ∧ out.width = first.width ∧ 3 ≤ first.width.val ∧
    NativeScalarQueryShape.powerOfTwo first.width.val = true ∧
    out.numVariables.val = first.numVariables.val + NativeScalarQueryShape.laneBits first.width.val ∧
    ∀ source ∈ sources, source.numVariables = first.numVariables ∧ source.width = first.width
  positive : out.numVariables.val ≠ 0
  shift : out.numVariables.val < 64
  capacity : out.capacity.val = 2 ^ out.numVariables.val
  logical : logicalLength.val ≤ 2 ^ out.numVariables.val
  helperVariables : helper.numVariables = out.numVariables
  helperWidth : helper.width = out.width ∨ helper.width.val = 3

theorem addVariables_some (source width n : Usize) (success : addVariables source width = some n) :
    n.val = source.val + NativeScalarQueryShape.laneBits width.val := by
  unfold addVariables at success
  split at success
  · exact congrArg Fin.val (Option.some.inj success).symm
  · contradiction

theorem capacity_some (n size : Usize) (success : capacity n = some size) :
    n.val < 64 ∧ size.val = 2 ^ n.val := by
  unfold capacity at success
  split at success
  · split at success
    · rename_i shift
      exact ⟨shift, congrArg Fin.val (Option.some.inj success).symm⟩
    · contradiction
  · contradiction

theorem compatible_iff (sources : List Parameters) (first helper : Parameters) (logicalLength : Usize) (n size : Usize) :
    compatible sources first helper logicalLength n size = true ↔ n.val ≠ 0 ∧ helper.numVariables = n ∧
      (helper.width = first.width ∨ helper.width.val = 3) ∧ logicalLength.val ≤ size.val ∧
      ∀ source ∈ sources, source.numVariables = first.numVariables ∧ source.width = first.width := by
  simp only [compatible, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true, and_assoc]

theorem bind_spec (columns : ℕ) (logicalLength : Usize) (helper : Parameters) (sources : List Parameters) (out : Output)
    (success : bind columns logicalLength helper sources = some out) : Spec columns logicalLength helper sources out := by
  unfold bind at success
  by_cases count : sources.length ≠ columns
  · rw [ite_eq_left count] at success; contradiction
  · rw [ite_eq_right count] at success
    rcases Option.bind_eq_some_iff.mp success with ⟨first, head, rest⟩
    by_cases bad : first.width.val < 3 ∨ NativeScalarQueryShape.powerOfTwo first.width.val ≠ true
    · rw [ite_eq_left bad] at rest; contradiction
    · rw [ite_eq_right bad] at rest
      rcases Option.bind_eq_some_iff.mp rest with ⟨n, nGet, rest⟩
      rcases Option.bind_eq_some_iff.mp rest with ⟨size, sizeGet, rest⟩
      by_cases good : compatible sources first helper logicalLength n size = true
      · rw [ite_eq_left good] at rest
        have same := Option.some.inj rest
        subst out
        have properties := (compatible_iff sources first helper logicalLength n size).mp good
        have geometry := capacity_some n size sizeGet
        refine ⟨by omega, ⟨first, head, rfl, by omega, (by by_contra rejected; exact bad (Or.inr rejected)), addVariables_some _ _ _ nGet, properties.2.2.2.2⟩,
          properties.1, geometry.1, geometry.2, ?_, properties.2.1, properties.2.2.1⟩
        rw [← geometry.2]
        exact properties.2.2.2.1
      · rw [ite_eq_right good] at rest; contradiction

/-- The real checked shift supplies the terminal prefix domain and active
prefix bound, independently of the later matrix construction. -/
theorem terminal_bounds (columns : ℕ) (logicalLength : Usize) (helper : Parameters) (sources : List Parameters) (out : Output)
    (success : bind columns logicalLength helper sources = some out) :
    out.numVariables.val < 64 ∧ logicalLength.val ≤ 2 ^ out.numVariables.val :=
  ⟨(bind_spec columns logicalLength helper sources out success).shift,
    (bind_spec columns logicalLength helper sources out success).logical⟩

end FormalProof4FHE.HasteBoots.NativeLookupBindGeometry
