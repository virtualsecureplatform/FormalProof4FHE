/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.RegularCoverBGVInstantiation

/-!
# Technical foundations for compact regular covers

This module closes the information-theoretic and partial-cover algebra needed before stating the
remaining compact-cover security theorem.
-/

namespace FormalProof4FHE.RLWE.BinaryNTTSecurity.CompactCoverTechnical

noncomputable section

/-- Partial cover containing only one scheduled frontier of labels. -/
abbrev PartialCover (Label R : Type) := Label → R

/-- An exact global encoder with a left inverse is injective and therefore cannot reduce finite
cardinality. -/
theorem exactCompression_card_le {Full Compact : Type}
    [Finite Full] [Finite Compact]
    (encode : Full → Compact) (decode : Compact → Full)
    (hexact : Function.LeftInverse decode encode) :
    Nat.card Full ≤ Nat.card Compact :=
  Nat.card_le_card_of_injective encode hexact.injective

/-- Cardinality of a complete function-space cover. -/
theorem card_fullCover (GroupIndex R : Type) [Finite GroupIndex] [Finite R] :
    Nat.card (GroupIndex → R) = Nat.card R ^ Nat.card GroupIndex := by
  rw [Nat.card_fun]

/-- Any exact encoding of the full regular cover into a width-`Width` partial cover obeys the
corresponding power-cardinality lower bound. -/
theorem exactFullCover_power_le
    {GroupIndex Width R : Type}
    [Finite GroupIndex] [Finite Width] [Finite R]
    (encode : (GroupIndex → R) → (Width → R))
    (decode : (Width → R) → (GroupIndex → R))
    (hexact : Function.LeftInverse decode encode) :
    Nat.card R ^ Nat.card GroupIndex ≤ Nat.card R ^ Nat.card Width := by
  simpa only [card_fullCover] using exactCompression_card_le encode decode hexact

/-! ## Restricted fixed embedding -/

/-- Embed one base-ring element into the automorphism labels selected by a frontier. -/
def restrictedFixedEmbedding
    {Label GroupIndex R : Type} [Group GroupIndex] [CommRing R]
    (action : GroupIndex →* R ≃+* R) (label : Label → GroupIndex)
    (value : R) : PartialCover Label R :=
  fun index => action (label index) value

/-- Every nonempty partial frontier still contains one full base-ring secret. -/
theorem restrictedFixedEmbedding_injective
    {Label GroupIndex R : Type} [Nonempty Label]
    [Group GroupIndex] [CommRing R]
    (action : GroupIndex →* R ≃+* R) (label : Label → GroupIndex) :
    Function.Injective (restrictedFixedEmbedding action label) := by
  intro left right heq
  let selected : Label := Classical.choice ‹Nonempty Label›
  have hcoordinate := congrFun heq selected
  exact (action (label selected)).injective hcoordinate

/-! ## Reindexing and scheduled relabeling -/

/-- Restrict, duplicate, or reorder a partial cover through a public label map. -/
def reindex {Source Target R : Type}
    (mapping : Target → Source) (value : PartialCover Source R) :
    PartialCover Target R :=
  fun target => value (mapping target)

@[simp]
theorem reindex_add {Source Target R : Type} [Add R]
    (mapping : Target → Source) (left right : PartialCover Source R) :
    reindex mapping (left + right) = reindex mapping left + reindex mapping right := by
  rfl

@[simp]
theorem reindex_mul {Source Target R : Type} [Mul R]
    (mapping : Target → Source) (left right : PartialCover Source R) :
    reindex mapping (left * right) = reindex mapping left * reindex mapping right := by
  rfl

/-- Relabel a scheduled frontier and apply a possibly different public base automorphism at each
target coordinate. -/
def relabel {Source Target GroupIndex R : Type}
    [Group GroupIndex] [CommRing R]
    (action : GroupIndex →* R ≃+* R)
    (source : Target → Source) (automorphism : Target → GroupIndex)
    (value : PartialCover Source R) : PartialCover Target R :=
  fun target => action (automorphism target) (value (source target))

@[simp]
theorem relabel_add {Source Target GroupIndex R : Type}
    [Group GroupIndex] [CommRing R]
    (action : GroupIndex →* R ≃+* R)
    (source : Target → Source) (automorphism : Target → GroupIndex)
    (left right : PartialCover Source R) :
    relabel action source automorphism (left + right) =
      relabel action source automorphism left +
        relabel action source automorphism right := by
  funext target
  simp [relabel]

@[simp]
theorem relabel_mul {Source Target GroupIndex R : Type}
    [Group GroupIndex] [CommRing R]
    (action : GroupIndex →* R ≃+* R)
    (source : Target → Source) (automorphism : Target → GroupIndex)
    (left right : PartialCover Source R) :
    relabel action source automorphism (left * right) =
      relabel action source automorphism left *
        relabel action source automorphism right := by
  funext target
  simp [relabel]

/-- Relabeling carries the restricted fixed embedding to the publicly composed labels. -/
theorem relabel_restrictedFixedEmbedding
    {Source Target GroupIndex R : Type}
    [Group GroupIndex] [CommRing R]
    (action : GroupIndex →* R ≃+* R)
    (sourceLabel : Source → GroupIndex)
    (source : Target → Source) (automorphism : Target → GroupIndex)
    (value : R) :
    relabel action source automorphism
        (restrictedFixedEmbedding action sourceLabel value) =
      restrictedFixedEmbedding action
        (fun target => automorphism target * sourceLabel (source target)) value := by
  funext target
  change action (automorphism target)
      (action (sourceLabel (source target)) value) =
    action (automorphism target * sourceLabel (source target)) value
  change (action (automorphism target) * action (sourceLabel (source target))) value = _
  rw [← action.map_mul]

/-! ## Scheduled storage arithmetic -/

/-- Number of modular residues in one partial-cover element. -/
def elementResidues (degree width : ℕ) : ℕ := degree * width

/-- Number of modular residues in a two-component ciphertext with `limbs` RNS residues per
coefficient. -/
def ciphertextResidues (degree width limbs : ℕ) : ℕ :=
  2 * degree * width * limbs

theorem ciphertextResidues_mono_width
    (degree limbs leftWidth rightWidth : ℕ)
    (hwidth : leftWidth ≤ rightWidth) :
    ciphertextResidues degree leftWidth limbs ≤
      ciphertextResidues degree rightWidth limbs := by
  simpa [ciphertextResidues, mul_assoc] using
    Nat.mul_le_mul_right limbs (Nat.mul_le_mul_left (2 * degree) hwidth)

/-- Peak live width controls peak ciphertext storage independently of the order of the generated
group. -/
theorem scheduled_peak_le_full
    (degree limbs activeWidth groupOrder : ℕ)
    (hwidth : activeWidth ≤ groupOrder) :
    ciphertextResidues degree activeWidth limbs ≤
      ciphertextResidues degree groupOrder limbs :=
  ciphertextResidues_mono_width degree limbs activeWidth groupOrder hwidth

/-- Baby-step/giant-step bad-dimension evaluator: two baby arrays plus four scalar temporaries. -/
def badDimensionPeakWidth (babyProduct : ℕ) : ℕ := 2 * babyProduct + 4

@[simp]
theorem target_badDimensionPeakWidth : badDimensionPeakWidth 182 = 368 := by
  decide

/-- Exact target storage counts for the extracted schedule, expressed in 64-bit residues. -/
@[simp]
theorem target_fullCiphertextResidues :
    ciphertextResidues 65536 65536 15 = 128849018880 := by
  decide

@[simp]
theorem target_scheduledCiphertextResidues :
    ciphertextResidues 65536 368 15 = 723517440 := by
  decide

end

end FormalProof4FHE.RLWE.BinaryNTTSecurity.CompactCoverTechnical
