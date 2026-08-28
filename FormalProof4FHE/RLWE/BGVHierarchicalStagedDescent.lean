/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.BinaryNTTAutomorphismFixedSubringBoundary

/-!
# Hierarchical staged descent for BGV

This module formalizes the finite algebraic core of
`sketch/proof-common-fixed-secret-etc.md`.

The key observation is stronger than the manuscript's normalized-trace construction.  Once the
affine completion descriptors `H,C` are public and

`S = H * ι(T) + C`,

one can project an arbitrary ciphertext from the large ring to the small ring directly.  No
automorphism evaluation key is needed for the descent itself.  The optional trace theorem is
retained to check the doubled-error normalization proposed in the manuscript.
-/

open OracleComp

namespace FormalProof4FHE.RLWE.BinaryNTTSecurity.BGVHierarchicalStagedDescent

noncomputable section

/-- An additive index-two projection together with its multiplicative fixed-subring law. -/
structure DescentTower (Base Full : Type) [CommRing Base] [CommRing Full] where
  embed : Base →+* Full
  evenPart : Full →+ Base
  even_embed : ∀ value, evenPart (embed value) = value
  even_mul_embed : ∀ value scalar,
    evenPart (value * embed scalar) = evenPart value * scalar

/-- Public affine-completion data.  The multiplier is a unit by construction. -/
structure Completion (Full : Type) [CommRing Full] where
  multiplier : Fullˣ
  offset : Full

/-- Complete a lower secret into the advertised upper secret. -/
def upperSecret {Base Full : Type} [CommRing Base] [CommRing Full]
    (tower : DescentTower Base Full) (completion : Completion Full)
    (lowerSecret : Base) : Full :=
  completion.multiplier * tower.embed lowerSecret + completion.offset

/-- The embedded lower secret is publicly recoverable from the upper secret and completion
descriptor. -/
def recoverEmbeddedSecret {Full : Type} [CommRing Full]
    (completion : Completion Full) (upper : Full) : Full :=
  ↑(completion.multiplier⁻¹) * (upper - completion.offset)

theorem recoverEmbeddedSecret_upperSecret
    {Base Full : Type} [CommRing Base] [CommRing Full]
    (tower : DescentTower Base Full) (completion : Completion Full)
    (lowerSecret : Base) :
    recoverEmbeddedSecret completion (upperSecret tower completion lowerSecret) =
      tower.embed lowerSecret := by
  simp [recoverEmbeddedSecret, upperSecret]

/-- A rank-one RLWE ciphertext `(mask, body)`. -/
abbrev Ciphertext (R : Type) := R × R

/-- Decryption phase `body - mask*secret`. -/
def phase {R : Type} [Ring R] (secret : R) (ciphertext : Ciphertext R) : R :=
  ciphertext.2 - ciphertext.1 * secret

/-- Public large-to-small ciphertext descent. -/
def descend {Base Full : Type} [CommRing Base] [CommRing Full]
    (tower : DescentTower Base Full) (completion : Completion Full)
    (ciphertext : Ciphertext Full) : Ciphertext Base :=
  (tower.evenPart (ciphertext.1 * completion.multiplier),
    tower.evenPart (ciphertext.2 - ciphertext.1 * completion.offset))

/-- **Exact public descent.**  It applies to every ciphertext, with no assumption that its phase
already belongs to the fixed subring. -/
theorem phase_descend
    {Base Full : Type} [CommRing Base] [CommRing Full]
    (tower : DescentTower Base Full) (completion : Completion Full)
    (lowerSecret : Base) (ciphertext : Ciphertext Full) :
    phase lowerSecret (descend tower completion ciphertext) =
      tower.evenPart (phase (upperSecret tower completion lowerSecret) ciphertext) := by
  calc
    phase lowerSecret (descend tower completion ciphertext) =
        tower.evenPart (ciphertext.2 - ciphertext.1 * completion.offset) -
          tower.evenPart (ciphertext.1 * completion.multiplier) * lowerSecret := rfl
    _ = tower.evenPart (ciphertext.2 - ciphertext.1 * completion.offset) -
          tower.evenPart
            ((ciphertext.1 * completion.multiplier) * tower.embed lowerSecret) := by
      rw [tower.even_mul_embed]
    _ = tower.evenPart
          ((ciphertext.2 - ciphertext.1 * completion.offset) -
            (ciphertext.1 * completion.multiplier) * tower.embed lowerSecret) := by
      exact (map_sub tower.evenPart _ _).symm
    _ = tower.evenPart
          (phase (upperSecret tower completion lowerSecret) ciphertext) := by
      apply congrArg tower.evenPart
      simp only [phase, upperSecret]
      ring

/-- Direct descent is already the exact even-part projection.  An automorphism trace is not
needed to obtain this phase. -/
theorem direct_descent_needs_no_automorphism
    {Base Full : Type} [CommRing Base] [CommRing Full]
    (tower : DescentTower Base Full) (completion : Completion Full)
    (lowerSecret : Base) (ciphertext : Ciphertext Full) :
    phase lowerSecret (descend tower completion ciphertext) =
      tower.evenPart (phase (upperSecret tower completion lowerSecret) ciphertext) :=
  phase_descend tower completion lowerSecret ciphertext

/-- A split-coordinate witness used to prove that a descended public mask is exactly uniform. -/
structure SplitDescentTower (Base Full Fiber : Type)
    [CommRing Base] [CommRing Full] where
  tower : DescentTower Base Full
  split : Full ≃ (Base × Fiber)
  split_fst : ∀ value, (split value).1 = tower.evenPart value

/-- Split the unit-twisted large mask into its lower mask and discarded component. -/
def splitTwistedMask {Base Full Fiber : Type}
    [CommRing Base] [CommRing Full]
    (tower : SplitDescentTower Base Full Fiber)
    (multiplier : Fullˣ) (mask : Full) : Base × Fiber :=
  tower.split (mask * multiplier)

def splitTwistedMaskInv {Base Full Fiber : Type}
    [CommRing Base] [CommRing Full]
    (tower : SplitDescentTower Base Full Fiber)
    (multiplier : Fullˣ) (parts : Base × Fiber) : Full :=
  tower.split.symm parts * ↑(multiplier⁻¹)

theorem splitTwistedMask_bijective {Base Full Fiber : Type}
    [CommRing Base] [CommRing Full]
    (tower : SplitDescentTower Base Full Fiber) (multiplier : Fullˣ) :
    Function.Bijective (splitTwistedMask tower multiplier) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨splitTwistedMaskInv tower multiplier, ?_, ?_⟩
  · intro mask
    simp [splitTwistedMask, splitTwistedMaskInv]
  · intro parts
    simp [splitTwistedMask, splitTwistedMaskInv]

/-- A uniform large-ring mask descends to an exactly uniform lower-ring mask. -/
theorem descendedMask_uniform_evalDist
    {Base Full Fiber : Type}
    [CommRing Base] [CommRing Full]
    [Fintype Base] [SampleableType Base]
    [Fintype Full] [SampleableType Full]
    [Fintype Fiber] [SampleableType Fiber]
    [SampleableType (Base × Fiber)]
    (tower : SplitDescentTower Base Full Fiber) (multiplier : Fullˣ) :
    evalDist ((fun mask => tower.tower.evenPart (mask * multiplier)) <$> ($ᵗ Full)) =
      evalDist ($ᵗ Base) := by
  have hsplit :
      evalDist (splitTwistedMask tower multiplier <$> ($ᵗ Full)) =
        evalDist ($ᵗ (Base × Fiber)) :=
    evalDist_map_bijective_uniform_cross
      (α := Full) (β := Base × Fiber) (splitTwistedMask tower multiplier)
      (splitTwistedMask_bijective tower multiplier)
  calc
    evalDist ((fun mask => tower.tower.evenPart (mask * multiplier)) <$> ($ᵗ Full)) =
      evalDist (Prod.fst <$> (splitTwistedMask tower multiplier <$> ($ᵗ Full))) := by
        simp only [Functor.map_map, splitTwistedMask]
        apply congrArg evalDist
        congr 1
        funext mask
        exact (tower.split_fst (mask * multiplier)).symm
    _ = evalDist (Prod.fst <$> ($ᵗ (Base × Fiber))) := by
      simpa only [evalDist_map] using
        congrArg (fun distribution => Prod.fst <$> distribution) hsplit
    _ = evalDist ($ᵗ Base) := evalDist_map_fst_uniformSample_prod

/-! ## Public lift -/

/-- Deterministic lift of a lower-ring ciphertext to the upper secret. -/
def deterministicLift {Base Full : Type} [CommRing Base] [CommRing Full]
    (tower : DescentTower Base Full) (completion : Completion Full)
    (ciphertext : Ciphertext Base) : Ciphertext Full :=
  let mask := tower.embed ciphertext.1 * ↑(completion.multiplier⁻¹)
  (mask, tower.embed ciphertext.2 + mask * completion.offset)

/-- The deterministic lift embeds the lower phase exactly. -/
theorem phase_deterministicLift
    {Base Full : Type} [CommRing Base] [CommRing Full]
    (tower : DescentTower Base Full) (completion : Completion Full)
    (lowerSecret : Base) (ciphertext : Ciphertext Base) :
    phase (upperSecret tower completion lowerSecret)
        (deterministicLift tower completion ciphertext) =
      tower.embed (phase lowerSecret ciphertext) := by
  have hunit :
      (↑(completion.multiplier⁻¹) : Full) * completion.multiplier = 1 := by
    simp
  simp only [phase, deterministicLift, upperSecret, map_sub, map_mul]
  ring_nf
  rw [mul_assoc (tower.embed ciphertext.1), hunit]
  ring

/-- Componentwise ciphertext addition. -/
def addCiphertext {R : Type} [Add R]
    (left right : Ciphertext R) : Ciphertext R :=
  (left.1 + right.1, left.2 + right.2)

theorem phase_addCiphertext {R : Type} [Ring R]
    (secret : R) (left right : Ciphertext R) :
    phase secret (addCiphertext left right) =
      phase secret left + phase secret right := by
  simp only [phase, addCiphertext, add_mul]
  abel

/-- Rerandomize a deterministic lift with an ordinary upper-key zero encryption. -/
def publicLift {Base Full : Type} [CommRing Base] [CommRing Full]
    (tower : DescentTower Base Full) (completion : Completion Full)
    (ciphertext : Ciphertext Base) (zeroEncryption : Ciphertext Full) : Ciphertext Full :=
  addCiphertext (deterministicLift tower completion ciphertext) zeroEncryption

/-- Exact phase of the rerandomized public lift. -/
theorem phase_publicLift
    {Base Full : Type} [CommRing Base] [CommRing Full]
    (tower : DescentTower Base Full) (completion : Completion Full)
    (lowerSecret : Base) (ciphertext : Ciphertext Base)
    (zeroEncryption : Ciphertext Full) :
    phase (upperSecret tower completion lowerSecret)
        (publicLift tower completion ciphertext zeroEncryption) =
      tower.embed (phase lowerSecret ciphertext) +
        phase (upperSecret tower completion lowerSecret) zeroEncryption := by
  rw [publicLift, phase_addCiphertext,
    phase_deterministicLift tower completion lowerSecret ciphertext]

/-- Adding a fixed lifted mask to an independent upper mask is a permutation. -/
def liftedMaskTranslation {Full : Type} [AddGroup Full]
    (fixedMask freshMask : Full) : Full :=
  fixedMask + freshMask

theorem liftedMaskTranslation_bijective {Full : Type} [AddGroup Full]
    (fixedMask : Full) : Function.Bijective (liftedMaskTranslation fixedMask) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun value => -fixedMask + value, ?_, ?_⟩
  · intro value
    simp [liftedMaskTranslation]
  · intro value
    simp [liftedMaskTranslation]

/-- Hence rerandomizing with an independent uniform zero-encryption mask gives an exactly uniform
upper mask. -/
theorem liftedMaskTranslation_uniform_evalDist
    {Full : Type} [AddCommGroup Full]
    [Fintype Full] [SampleableType Full]
    (fixedMask : Full) :
    evalDist (liftedMaskTranslation fixedMask <$> ($ᵗ Full)) =
      evalDist ($ᵗ Full) :=
  evalDist_map_bijective_uniform_cross
    (α := Full) (β := Full) (liftedMaskTranslation fixedMask)
    (liftedMaskTranslation_bijective fixedMask)

/-! ## Exact public scaling of an RLWE row -/

/-- Scale an entire public row by a unit. -/
def scaleRowByUnit {R : Type} [CommRing R]
    (unit : Rˣ) (row : Ciphertext R) : Ciphertext R :=
  (unit * row.1, unit * row.2)

def scaleRowByUnitInv {R : Type} [CommRing R]
    (unit : Rˣ) (row : Ciphertext R) : Ciphertext R :=
  (↑(unit⁻¹) * row.1, ↑(unit⁻¹) * row.2)

theorem scaleRowByUnit_bijective {R : Type} [CommRing R] (unit : Rˣ) :
    Function.Bijective (scaleRowByUnit unit) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨scaleRowByUnitInv unit, ?_, ?_⟩
  · intro row
    rcases row with ⟨mask, body⟩
    simp [scaleRowByUnit, scaleRowByUnitInv]
  · intro row
    rcases row with ⟨mask, body⟩
    simp [scaleRowByUnit, scaleRowByUnitInv]

/-- Scaling a row scales its error/phase by exactly the same unit. -/
theorem phase_scaleRowByUnit {R : Type} [CommRing R]
    (unit : Rˣ) (secret : R) (row : Ciphertext R) :
    phase secret (scaleRowByUnit unit row) = unit * phase secret row := by
  simp [phase, scaleRowByUnit]
  ring

/-- Unit scaling preserves the exact uniform row endpoint. -/
theorem scaleRowByUnit_uniform_evalDist {R : Type} [CommRing R]
    [Fintype R] [SampleableType R] [SampleableType (Ciphertext R)]
    (unit : Rˣ) :
    evalDist (scaleRowByUnit unit <$> ($ᵗ (Ciphertext R))) =
      evalDist ($ᵗ (Ciphertext R)) :=
  evalDist_map_bijective_uniform_cross
    (α := Ciphertext R) (β := Ciphertext R) (scaleRowByUnit unit)
    (scaleRowByUnit_bijective unit)

/-! ## Optional normalized trace with doubled key-switch error -/

/-- Scale both components of a ciphertext. -/
def scaleCiphertext {R : Type} [Mul R]
    (scalar : R) (ciphertext : Ciphertext R) : Ciphertext R :=
  (scalar * ciphertext.1, scalar * ciphertext.2)

theorem phase_scaleCiphertext {R : Type} [CommRing R]
    (scalar secret : R) (ciphertext : Ciphertext R) :
    phase secret (scaleCiphertext scalar ciphertext) =
      scalar * phase secret ciphertext := by
  simp [phase, scaleCiphertext]
  ring

/-- Involution data needed only by the optional trace presentation. -/
structure TraceTower (Base Full : Type) [CommRing Base] [CommRing Full]
    extends DescentTower Base Full where
  sigma : Full ≃+* Full
  even_trace : ∀ value,
    evenPart (value + sigma value) = 2 * evenPart value

/-- Trace, descend, and divide by two in the lower ring. -/
def traceDescend {Base Full : Type} [CommRing Base] [CommRing Full]
    (tower : TraceTower Base Full) (completion : Completion Full)
    (half : Base) (ciphertext automorphed : Ciphertext Full) : Ciphertext Base :=
  scaleCiphertext half
    (descend tower.toDescentTower completion (addCiphertext ciphertext automorphed))

/-- If key switching produces `sigma(phase)+2*kappa`, normalized trace descent adds `kappa`
once and never scales a narrow error by the modular representative of `1/2`. -/
theorem phase_traceDescend
    {Base Full : Type} [CommRing Base] [CommRing Full]
    (tower : TraceTower Base Full) (completion : Completion Full)
    (half : Base) (hhalf : half * 2 = 1)
    (lowerSecret : Base) (ciphertext automorphed : Ciphertext Full)
    (kappa : Full)
    (hautomorphed :
      phase (upperSecret tower.toDescentTower completion lowerSecret) automorphed =
        tower.sigma
          (phase (upperSecret tower.toDescentTower completion lowerSecret) ciphertext) +
          2 * kappa) :
    phase lowerSecret
        (traceDescend tower completion half ciphertext automorphed) =
      tower.evenPart
          (phase (upperSecret tower.toDescentTower completion lowerSecret) ciphertext) +
        tower.evenPart kappa := by
  rw [traceDescend, phase_scaleCiphertext,
    phase_descend tower.toDescentTower completion lowerSecret,
    phase_addCiphertext, hautomorphed]
  rw [map_add, map_add]
  let inputPhase :=
    phase (upperSecret tower.toDescentTower completion lowerSecret) ciphertext
  have hcombine :
      tower.evenPart inputPhase +
          (tower.evenPart (tower.sigma inputPhase) + tower.evenPart (2 * kappa)) =
        tower.evenPart (inputPhase + tower.sigma inputPhase) +
          tower.evenPart (2 * kappa) := by
    rw [map_add]
    abel
  have hkappa : tower.evenPart (2 * kappa) = 2 * tower.evenPart kappa := by
    rw [show 2 * kappa = kappa + kappa by ring, map_add]
    ring
  change half *
      (tower.evenPart inputPhase +
        (tower.evenPart (tower.sigma inputPhase) + tower.evenPart (2 * kappa))) = _
  rw [hcombine, tower.even_trace, hkappa]
  change half * (2 * tower.evenPart inputPhase + 2 * tower.evenPart kappa) =
    tower.evenPart inputPhase + tower.evenPart kappa
  calc
    _ = (half * 2) *
        (tower.evenPart inputPhase + tower.evenPart kappa) := by ring
    _ = _ := by rw [hhalf, one_mul]

/-! ## Exact finite-depth Binary-NTT completion -/

/-- NTT slot type after `depth` successive index-two extensions. -/
def TowerSlot (depth : ℕ) (BottomSlot : Type) : Type :=
  match depth with
  | 0 => BottomSlot
  | depth + 1 => FixedPointFreeAutomorphism.PairedSlot (TowerSlot depth BottomSlot)

/-- Bottom secret bits together with one fresh completion vector at every tower level. -/
def HierarchyCoins (depth : ℕ) (BottomSlot : Type) : Type :=
  match depth with
  | 0 => BottomSlot → Bool
  | depth + 1 =>
      HierarchyCoins depth BottomSlot × (TowerSlot depth BottomSlot → Bool)

/-- Iterating the one-level completion equivalence yields one exact full-degree Binary-NTT
vector. -/
def hierarchyCompletionEquiv (depth : ℕ) (BottomSlot : Type) :
    HierarchyCoins depth BottomSlot ≃ (TowerSlot depth BottomSlot → Bool) := by
  induction depth with
  | zero => exact Equiv.refl _
  | succ depth ih =>
      exact (ih.prodCongr (Equiv.refl _)).trans
        (FixedPointFreeAutomorphism.completionEquiv _)

/-- The complete hierarchy contains exactly as much randomness as the top Binary-NTT secret. -/
theorem hierarchyCoins_card (depth : ℕ) (BottomSlot : Type)
    [Finite BottomSlot] :
    Nat.card (HierarchyCoins depth BottomSlot) =
      Nat.card (TowerSlot depth BottomSlot → Bool) :=
  Nat.card_congr (hierarchyCompletionEquiv depth BottomSlot)

/-- Uniform hierarchy coins produce the exact uniform top-secret law. -/
theorem hierarchyCompletion_uniform_evalDist
    (depth : ℕ) (BottomSlot : Type)
    [Fintype (HierarchyCoins depth BottomSlot)]
    [Fintype (TowerSlot depth BottomSlot → Bool)]
    [SampleableType (HierarchyCoins depth BottomSlot)]
    [SampleableType (TowerSlot depth BottomSlot → Bool)] :
    evalDist (hierarchyCompletionEquiv depth BottomSlot <$>
        ($ᵗ (HierarchyCoins depth BottomSlot))) =
      evalDist ($ᵗ (TowerSlot depth BottomSlot → Bool)) :=
  evalDist_map_bijective_uniform_cross
    (α := HierarchyCoins depth BottomSlot)
    (β := TowerSlot depth BottomSlot → Bool)
    (hierarchyCompletionEquiv depth BottomSlot)
    (hierarchyCompletionEquiv depth BottomSlot).bijective

/-! ## Recursive sample accounting -/

/-- Bottom samples consumed by row counts listed from top level to bottom level. -/
def bottomSampleCount : List ℕ → ℕ
  | [] => 0
  | count :: lowerCounts => count * 2 ^ lowerCounts.length + bottomSampleCount lowerCounts

@[simp]
theorem bottomSampleCount_nil : bottomSampleCount [] = 0 := rfl

@[simp]
theorem bottomSampleCount_cons (count : ℕ) (lowerCounts : List ℕ) :
    bottomSampleCount (count :: lowerCounts) =
      count * 2 ^ lowerCounts.length + bottomSampleCount lowerCounts := rfl

/-- Two comparison pools consume exactly twice the one-transcript recursive source count. -/
theorem comparisonPoolSampleCount (counts : List ℕ) :
    bottomSampleCount counts + bottomSampleCount counts = 2 * bottomSampleCount counts := by
  omega

end

end FormalProof4FHE.RLWE.BinaryNTTSecurity.BGVHierarchicalStagedDescent
