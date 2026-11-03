module

public import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved

@[expose] public section

/-!
# Native block-symbol Reed--Solomon code

For native unpadded layouts, `m` is the coefficient count PER coordinate and
`b` is the symbol width. Thus ArkLib's total dimension parameter is `b*m`,
not `m`. The metric counts differing whole symbols, not scalar coordinates.
This semantic code is not yet linked to the Rust NTT encoder.
-/

namespace FormalProof4FHE.HasteBoots.BlockCode

variable {F Position : Type*} [Field F] [Fintype Position]

/-- Coordinate polynomials of degree less than `m`, evaluated on one common domain. -/
noncomputable def code (domain : Position ↪ F) (m b : ℕ) :
    Submodule F (Position → Fin b → F) :=
  ReedSolomon.Interleaved.irsCode domain (b * m) b

/-- Whole-symbol minimum distance of the native semantic code. -/
theorem minDist (domain : Position ↪ F) (m b : ℕ)
    [Nonempty Position] [DecidableEq F] [NeZero b] (hm : 0 < m) :
    Code.minDist ((code domain m b : Submodule F (Position → Fin b → F)) :
      Set (Position → Fin b → F)) = Fintype.card Position - m + 1 := by
  have hb : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
  simpa [code, Nat.mul_div_right _ hb] using
    ReedSolomon.Interleaved.minDist_irsCode domain (b * m) b (by
      simpa [Nat.mul_div_right _ hb] using hm)

/-- Unpadded dimension below saturation; useful for checking native layout parameters. -/
theorem dimension (domain : Position ↪ F) (m b : ℕ) [NeZero b]
    (hm : m ≤ Fintype.card Position) :
    Module.finrank F (code domain m b) = b * m := by
  have hb : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
  unfold code
  rw [ReedSolomon.Interleaved.dim_irsCode_eq_min, Nat.mul_div_right _ hb,
    min_eq_left hm]

end FormalProof4FHE.HasteBoots.BlockCode
