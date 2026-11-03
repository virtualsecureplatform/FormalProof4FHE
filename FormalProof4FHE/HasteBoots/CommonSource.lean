module

public import FormalProof4FHE.HasteBoots.BlockCode

@[expose] public section

/-!
# A common decoded source for all openings of an available word

Distances count whole columns, whose symbols contain ALL rows. A decoding
radius is fixed before any opening. Existence and uniqueness below are purely
information-theoretic: they do not establish availability from a Merkle root
or efficient extraction. Those are separate cryptographic obligations.
-/

namespace FormalProof4FHE.HasteBoots.CommonSource

variable {Position Row Symbol : Type*} [Fintype Position]
  [DecidableEq Symbol] [DecidableEq (Row → Symbol)]

/-- Every row of the same decoded matrix belongs to the same symbol code. -/
def RowsIn (C : Set (Position → Symbol)) (word : Position → Row → Symbol) : Prop :=
  ∀ row, (fun pos => word pos row) ∈ C

/-- Projecting a whole-column word onto one row cannot increase disagreement count. -/
theorem row_distance_le (left right : Position → Row → Symbol) (row : Row) :
    hammingDist (fun pos => left pos row) (fun pos => right pos row) ≤
      hammingDist left right :=
  hammingDist_comp_le_hammingDist (x := left) (y := right) (fun _ (v : Row → Symbol) => v row)

/-- A false coded response must disagree on at least distance-minus-radius columns.
This bound does not require fresh queries or independence of the two PCS tests. -/
theorem falseResponse_distance (C : Set (Position → Symbol)) (radius : ℕ)
    (raw correct claimed : Position → Symbol) (correctC : correct ∈ C)
    (claimedC : claimed ∈ C) (different : correct ≠ claimed)
    (close : hammingDist raw correct ≤ radius) :
    Code.minDist C - radius ≤ hammingDist raw claimed := by
  have lower := Code.minDist_le_dist correctC claimedC different
  have upper := hammingDist_triangle correct raw claimed
  rw [hammingDist_comm correct raw] at upper
  omega

/-- A single nearby coded matrix is uniquely determined by the complete available word. -/
theorem nearby_unique (C : Set (Position → Symbol)) (radius : ℕ)
    (margin : 2 * radius < Code.minDist C)
    (word left right : Position → Row → Symbol)
    (hl : RowsIn C left) (hr : RowsIn C right)
    (closeLeft : hammingDist word left ≤ radius)
    (closeRight : hammingDist word right ≤ radius) : left = right := by
  classical
  funext pos row
  have equalRow : (fun i => left i row) = (fun i => right i row) := by
    by_contra different
    have lower := Code.minDist_le_dist (hl row) (hr row) different
    have upper := hammingDist_triangle (fun i => left i row)
      (fun i => word i row) (fun i => right i row)
    have hleft := row_distance_le word left row
    have hright := row_distance_le word right row
    rw [hammingDist_comm (fun i => left i row) (fun i => word i row)] at upper
    omega
  exact congrFun equalRow pos

section Decoder

variable [Zero Symbol]

/-- One total decoder per fixed available word and radius, with a zero fallback outside promise. -/
noncomputable def decode (C : Set (Position → Symbol)) (radius : ℕ)
    (word : Position → Row → Symbol) : Position → Row → Symbol := by
  classical
  exact if h : ∃ source, RowsIn C source ∧ hammingDist word source ≤ radius then
    Classical.choose h else 0

omit [DecidableEq Symbol] in
theorem decode_nearby (C : Set (Position → Symbol)) (radius : ℕ)
    (word : Position → Row → Symbol)
    (near : ∃ source, RowsIn C source ∧ hammingDist word source ≤ radius) :
    RowsIn C (decode C radius word) ∧ hammingDist word (decode C radius word) ≤ radius := by
  simp only [decode, dite_eq_left near]
  exact Classical.choose_spec near

theorem decode_eq_of_nearby (C : Set (Position → Symbol)) (radius : ℕ)
    (margin : 2 * radius < Code.minDist C) (word source : Position → Row → Symbol)
    (coded : RowsIn C source) (close : hammingDist word source ≤ radius) :
    decode C radius word = source := by
  have chosen := decode_nearby C radius word ⟨source, coded, close⟩
  exact nearby_unique C radius margin word _ source chosen.1 coded chosen.2 close

omit [DecidableEq Symbol] in
theorem decode_fallback (C : Set (Position → Symbol)) (radius : ℕ)
    (word : Position → Row → Symbol)
    (far : ¬ ∃ source, RowsIn C source ∧ hammingDist word source ≤ radius) :
    decode C radius word = 0 := by
  simp only [decode, dite_eq_right far]

omit [DecidableEq Symbol] in
/-- Even the fallback is a coded source, but it carries NO closeness guarantee. -/
theorem decode_rowsIn (C : Set (Position → Symbol)) (radius : ℕ)
    (zeroC : (0 : Position → Symbol) ∈ C) (word : Position → Row → Symbol) :
    RowsIn C (decode C radius word) := by
  classical
  by_cases near : ∃ source, RowsIn C source ∧ hammingDist word source ≤ radius
  · exact (decode_nearby C radius word near).1
  · rw [decode_fallback C radius word near]
    exact fun _ => zeroC

end Decoder

/-- The conservative one-third radius is strictly inside the block unique-decoding radius. -/
theorem block_margin {F : Type*} [Field F] [DecidableEq F] [Nonempty Position]
    (domain : Position ↪ F) (m b : ℕ) [NeZero b] (hm : 0 < m) :
    2 * ((Fintype.card Position - m) / 3) <
      Code.minDist ((BlockCode.code domain m b :
        Submodule F (Position → Fin b → F)) : Set (Position → Fin b → F)) := by
  rw [BlockCode.minDist domain m b hm]
  omega

end FormalProof4FHE.HasteBoots.CommonSource
