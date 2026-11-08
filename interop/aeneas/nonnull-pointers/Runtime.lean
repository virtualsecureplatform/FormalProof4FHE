/-! Checked non-null pattern construction. The predicate concerns only the data
address: it grants no alignment, liveness, provenance, borrow or heap permission. -/
namespace HasteBootsPointerRuntime
open Aeneas Aeneas.Std

def check_nonnull {T : Type} {mutable : Bool} (pointer : RawPtr T mutable) :
    Result { pointer : RawPtr T mutable // pointer.storage.address ≠ 0 } :=
  if valid : pointer.storage.address ≠ 0 then .ok ⟨pointer, valid⟩ else .fail .undef

theorem check_nonnull_valid {T : Type} {mutable : Bool} (pointer : RawPtr T mutable)
    (valid : pointer.storage.address ≠ 0) :
    check_nonnull pointer = .ok ⟨pointer, valid⟩ := by
  simp only [check_nonnull, dite_eq_left valid]

theorem check_nonnull_zero {T : Type} {mutable : Bool} (pointer : RawPtr T mutable)
    (zero : pointer.storage.address = 0) : check_nonnull pointer = .fail .undef := by
  simp only [check_nonnull, zero, ne_eq, not_true_eq_false, dite_false]

theorem check_nonnull_ok_iff {T : Type} {mutable : Bool} (pointer : RawPtr T mutable)
    (result : { pointer : RawPtr T mutable // pointer.storage.address ≠ 0 }) :
    check_nonnull pointer = .ok result ↔ pointer = result.val := by
  by_cases valid : pointer.storage.address ≠ 0
  · simp only [check_nonnull, dite_eq_left valid, Result.ok.injEq]
    exact ⟨fun same => congrArg Subtype.val same, fun same => Subtype.ext same⟩
  · simp only [check_nonnull, dite_eq_right valid]
    constructor
    · intro impossible; cases impossible
    · intro same; exact False.elim (valid (same ▸ result.property))

theorem check_nonnull_roundtrip {T : Type} {mutable : Bool}
    (pointer : { pointer : RawPtr T mutable // pointer.storage.address ≠ 0 }) :
    check_nonnull pointer.val = .ok pointer := by
  exact (check_nonnull_ok_iff pointer.val pointer).mpr rfl

end HasteBootsPointerRuntime
