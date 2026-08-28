/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.BinaryNTTFixedPointFreeAutomorphism

/-!
# Common fixed-subring boundary for Binary-NTT automorphism keys

The simultaneous tower compiler writes a full Binary-NTT secret as `S = H*T + C` and absorbs
each message `g_σ * σ(S)` into a lower-dimensional RLWE mask.  For a joint family of
automorphisms, the same algebra works when `T` is fixed by every member of the family.

This module checks the resulting boundary.  A single paired involution leaves one independent
binary coordinate per orbit.  In contrast, any transitive permutation family leaves only the two
constant binary vectors.  Thus a common-fixed-secret reduction for a transitive trace family
would reduce to a one-bit secret source, not to growing-dimensional Binary-NTT RLWE.
-/

open OracleComp

namespace FormalProof4FHE.RLWE.BinaryNTTSecurity.AutomorphismFixedSubringBoundary

noncomputable section

/-- A public family of permutations of the split NTT coordinates.  Closure under composition is
not required for the fixed-vector statements. -/
structure PermutationFamily (Index Slot : Type) where
  permutation : Index → Equiv.Perm Slot

/-- Binary vectors fixed by every public permutation in a family. -/
def FixedByFamily {Index Slot : Type} (family : PermutationFamily Index Slot)
    (bits : Slot → Bool) : Prop :=
  ∀ index slot, bits (family.permutation index slot) = bits slot

/-- The family is transitive on NTT coordinates. -/
def IsTransitive {Index Slot : Type} (family : PermutationFamily Index Slot) : Prop :=
  ∀ source target : Slot, ∃ index, family.permutation index source = target

/-- A binary vector fixed by a transitive family is constant. -/
theorem fixedByFamily_eq_of_transitive {Index Slot : Type}
    (family : PermutationFamily Index Slot) (htransitive : IsTransitive family)
    (bits : Slot → Bool) (hfixed : FixedByFamily family bits)
    (source target : Slot) : bits source = bits target := by
  obtain ⟨index, hindex⟩ := htransitive source target
  rw [← hindex]
  exact (hfixed index source).symm

/-- The type of fixed binary vectors. -/
abbrev FixedBits {Index Slot : Type} (family : PermutationFamily Index Slot) :=
  {bits : Slot → Bool // FixedByFamily family bits}

/-- Constant binary vectors are fixed by every permutation family. -/
def constantFixedBits {Index Slot : Type} (family : PermutationFamily Index Slot)
    (bit : Bool) : FixedBits family :=
  ⟨fun _ => bit, by simp [FixedByFamily]⟩

/-- A transitive family has exactly one independent fixed binary coordinate. -/
def transitiveFixedBitsEquiv {Index Slot : Type} [Nonempty Slot]
    (family : PermutationFamily Index Slot) (htransitive : IsTransitive family) :
    FixedBits family ≃ Bool where
  toFun bits := bits.1 (Classical.choice ‹Nonempty Slot›)
  invFun := constantFixedBits family
  left_inv bits := by
    apply Subtype.ext
    funext slot
    exact (fixedByFamily_eq_of_transitive family htransitive bits.1 bits.2
      slot (Classical.choice ‹Nonempty Slot›)).symm
  right_inv bit := rfl

/-- Consequently the common fixed Binary-NTT support of a transitive family has cardinality two. -/
theorem card_fixedBits_of_transitive {Index Slot : Type}
    [Fintype Index] [Fintype Slot] [Nonempty Slot]
    (family : PermutationFamily Index Slot) (htransitive : IsTransitive family) :
    Nat.card (FixedBits family) = 2 := by
  rw [Nat.card_congr (transitiveFixedBitsEquiv family htransitive)]
  simp

/-- Adding more automorphisms can only shrink the common fixed set. -/
def restrictFixedBits {Small Big Slot : Type}
    (small : PermutationFamily Small Slot) (big : PermutationFamily Big Slot)
    (embed : Small → Big)
    (hperm : ∀ index, small.permutation index = big.permutation (embed index)) :
    FixedBits big → FixedBits small :=
  fun bits => ⟨bits.1, by
    intro index slot
    rw [hperm]
    exact bits.2 (embed index) slot⟩

theorem restrictFixedBits_injective {Small Big Slot : Type}
    (small : PermutationFamily Small Slot) (big : PermutationFamily Big Slot)
    (embed : Small → Big)
    (hperm : ∀ index, small.permutation index = big.permutation (embed index)) :
    Function.Injective (restrictFixedBits small big embed hperm) := by
  intro left right heq
  rcases left with ⟨left, hleft⟩
  rcases right with ⟨right, hright⟩
  simp only [restrictFixedBits] at heq
  cases heq
  rfl

/-- The regular left action of a group on itself.  This models a simply transitive Galois action
after choosing one NTT coordinate as an origin. -/
def regularPermutationFamily (GroupIndex : Type) [Group GroupIndex] :
    PermutationFamily GroupIndex GroupIndex where
  permutation := Equiv.mulLeft

theorem regularPermutationFamily_transitive (GroupIndex : Type) [Group GroupIndex] :
    IsTransitive (regularPermutationFamily GroupIndex) := by
  intro source target
  refine ⟨target * source⁻¹, ?_⟩
  simp [regularPermutationFamily]

/-- A regular trace action therefore leaves only the all-zero and all-one Binary-NTT vectors. -/
theorem card_regularFixedBits (GroupIndex : Type)
    [Group GroupIndex] [Fintype GroupIndex] [Nonempty GroupIndex] :
    Nat.card (FixedBits (regularPermutationFamily GroupIndex)) = 2 :=
  card_fixedBits_of_transitive (regularPermutationFamily GroupIndex)
    (regularPermutationFamily_transitive GroupIndex)

/-! ## One fixed-point-free involution retains half the coordinates -/

/-- Binary vectors fixed by the canonical paired involution. -/
def PairedFixedBits (Slot : Type) :=
  {bits : FixedPointFreeAutomorphism.PairedSlot Slot → Bool //
    ∀ coordinate, bits (FixedPointFreeAutomorphism.orbitInvolution coordinate) = bits coordinate}

/-- Duplicate one bit across each two-coordinate orbit. -/
def duplicateOrbitBits {Slot : Type} (bits : Slot → Bool) : PairedFixedBits Slot :=
  ⟨fun coordinate => bits coordinate.1, by
    intro coordinate
    rcases coordinate with ⟨slot, side⟩
    cases side <;> rfl⟩

/-- Restrict an orbit-constant vector to one side of every orbit. -/
def restrictOrbitBits {Slot : Type} (bits : PairedFixedBits Slot) : Slot → Bool :=
  fun slot => bits.1 (slot, false)

/-- The fixed binary vectors of one paired involution are exactly one binary vector on the
half-size orbit set. -/
def pairedFixedBitsEquiv (Slot : Type) : PairedFixedBits Slot ≃ (Slot → Bool) where
  toFun := restrictOrbitBits
  invFun := duplicateOrbitBits
  left_inv bits := by
    apply Subtype.ext
    funext coordinate
    rcases coordinate with ⟨slot, side⟩
    cases side
    · rfl
    · exact (bits.2 (slot, false)).symm
  right_inv bits := by funext slot; rfl

theorem card_pairedFixedBits (Slot : Type) [Fintype Slot] :
    Nat.card (PairedFixedBits Slot) = 2 ^ Fintype.card Slot := by
  rw [Nat.card_congr (pairedFixedBitsEquiv Slot), Nat.card_fun]
  simp [Nat.card_eq_fintype_card]

/-- Compared with all full binary vectors, the single-involution fixed set has exactly the
square-root support size. -/
theorem card_all_paired_bits (Slot : Type) [Fintype Slot] :
    Nat.card (FixedPointFreeAutomorphism.PairedSlot Slot → Bool) =
      (2 ^ Fintype.card Slot) ^ 2 := by
  rw [Nat.card_fun, Nat.card_prod]
  simp [Nat.card_eq_fintype_card, pow_mul]

/-! ## Joint family compiler algebra -/

/-- Apply the tower automorphism encoder to every automorphism and every gadget row at once. -/
def familyAutomorphismBatch {Auto Row R : Type} [CommRing R]
    (sigma : Auto → R ≃+* R) (gadget : Auto → Row → R)
    (offset : R) (multiplier : Rˣ)
    (source : Auto → Row → R × R) : Auto → Row → R × R :=
  fun automorphism row =>
    FixedPointFreeAutomorphism.automorphismRow (sigma automorphism) (gadget automorphism row)
      offset multiplier (source automorphism row)

def familyAutomorphismBatchInv {Auto Row R : Type} [CommRing R]
    (sigma : Auto → R ≃+* R) (gadget : Auto → Row → R)
    (offset : R) (multiplier : Rˣ)
    (target : Auto → Row → R × R) : Auto → Row → R × R :=
  fun automorphism row =>
    FixedPointFreeAutomorphism.automorphismRowInv (sigma automorphism) (gadget automorphism row)
      offset multiplier (target automorphism row)

theorem familyAutomorphismBatch_bijective {Auto Row R : Type} [CommRing R]
    (sigma : Auto → R ≃+* R) (gadget : Auto → Row → R)
    (offset : R) (multiplier : Rˣ) :
    Function.Bijective (familyAutomorphismBatch sigma gadget offset multiplier) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨familyAutomorphismBatchInv sigma gadget offset multiplier, ?_, ?_⟩
  · intro source
    funext automorphism row
    simp [familyAutomorphismBatch, familyAutomorphismBatchInv]
  · intro target
    funext automorphism row
    simp [familyAutomorphismBatch, familyAutomorphismBatchInv]

/-- The entire multi-automorphism random transcript remains exactly uniform. -/
theorem familyAutomorphismBatch_uniform_evalDist
    {Auto Row R : Type} [CommRing R]
    [Finite Auto] [DecidableEq Auto] [Finite Row] [DecidableEq Row]
    [Fintype R] [SampleableType R]
    [SampleableType (Auto → Row → R × R)]
    (sigma : Auto → R ≃+* R) (gadget : Auto → Row → R)
    (offset : R) (multiplier : Rˣ) :
    evalDist (familyAutomorphismBatch sigma gadget offset multiplier <$>
        ($ᵗ (Auto → Row → R × R))) =
      evalDist ($ᵗ (Auto → Row → R × R)) :=
  evalDist_map_bijective_uniform_cross
    (α := Auto → Row → R × R) (β := Auto → Row → R × R)
    (familyAutomorphismBatch sigma gadget offset multiplier)
    (familyAutomorphismBatch_bijective sigma gadget offset multiplier)

/-- Pointwise real-branch identity for the joint family.  The only family-specific algebraic
hypothesis is that the lower-dimensional secret is fixed by every automorphism. -/
theorem familyAutomorphismBatch_real
    {Auto Row R : Type} [CommRing R]
    (sigma : Auto → R ≃+* R) (gadget : Auto → Row → R)
    (offset fixedSecret : R) (multiplier : Rˣ)
    (mask error : Auto → Row → R)
    (hfixed : ∀ automorphism, sigma automorphism fixedSecret = fixedSecret)
    (automorphism : Auto) (row : Row) :
    (familyAutomorphismBatch sigma gadget offset multiplier
      (fun auto index =>
        (mask auto index, mask auto index * fixedSecret + error auto index))
      automorphism row).2 =
      (familyAutomorphismBatch sigma gadget offset multiplier
        (fun auto index =>
          (mask auto index, mask auto index * fixedSecret + error auto index))
        automorphism row).1 *
          FixedPointFreeAutomorphism.completedRingSecret (multiplier : R) fixedSecret offset +
        error automorphism row + gadget automorphism row *
          sigma automorphism
            (FixedPointFreeAutomorphism.completedRingSecret (multiplier : R) fixedSecret offset) := by
  exact FixedPointFreeAutomorphism.automorphismBody_real (sigma automorphism) (gadget automorphism row)
    multiplier offset fixedSecret (error automorphism row) (mask automorphism row)
    (hfixed automorphism)

/-- The cardinality collapse is independent of the ambient coefficient field: on binary NTT
secrets, a transitive joint family exposes only one independent source bit to this compiler. -/
theorem transitive_common_source_cardinality {Auto Slot : Type}
    [Fintype Auto] [Fintype Slot] [Nonempty Slot]
    (family : PermutationFamily Auto Slot) (htransitive : IsTransitive family) :
    Nat.card (FixedBits family) = Nat.card Bool := by
  rw [card_fixedBits_of_transitive family htransitive]
  simp

end

end FormalProof4FHE.RLWE.BinaryNTTSecurity.AutomorphismFixedSubringBoundary
