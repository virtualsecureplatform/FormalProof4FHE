module
public import FormalProof4FHE.HasteBoots.PackedPBSCoverage
@[expose] public section

/-! Deterministic earliest-stage localization for the complete corrected PBS.
The ordered witness is derived from arithmetic failure, not supplied by an
acceptance certificate. Native execution and probability are not asserted. -/
namespace FormalProof4FHE.HasteBoots.PBSFirstStageCoverage
open NativeBlindRotation
noncomputable section

/-- Localize failure without assuming a nonempty dimension. -/
theorem first_failure {count : ℕ} (valid : Fin count → Prop)
    (failed : ¬∀ index, valid index) :
    ∃ index, ¬valid index ∧ ∀ earlier, earlier.val < index.val → valid earlier := by
  classical
  have existsBad : ∃ n : ℕ, ∃ index : Fin count, index.val = n ∧ ¬valid index := by
    obtain ⟨index, bad⟩ := not_forall.mp failed
    exact ⟨index.val, index, rfl, bad⟩
  obtain ⟨index, position, bad⟩ := Nat.find_spec existsBad
  refine ⟨index, bad, ?_⟩
  intro earlier before
  by_contra badEarlier
  exact Nat.find_min existsBad (position ▸ before) ⟨earlier, rfl, badEarlier⟩

section
variable {q log levels mc mw ec ew : ℕ} [Fact q.Prime]

def BlindFailure (psi : ZMod q) (bits exponent : ℕ) (control : Control q (2^log) levels)
    (input product difference external : Cipher q (2^log)) (stage : PackedBlindRotationTrace.Stages q log levels mc mw ec ew) : Prop :=
    ¬PBSHadamard.Relation stage.monomial ∨
    (∃ half, BlindRotationNTT.transform log psi (input half) ≠ PBSMonomialBlindRotation.project stage.monomial (stage.monomialAddress half) (.inl (0,false))) ∨
    (∃ half, PBSMonomialBlindRotation.project stage.monomial (stage.monomialAddress half) (.inl (0,true)) ≠ BlindRotationMonomial.powers log psi exponent) ∨
    (∃ half, BlindRotationNTT.transform log psi (product half) ≠ PBSMonomialBlindRotation.project stage.monomial (stage.monomialAddress half) (.inr ())) ∨
    ¬PBSHadamard.Relation stage.external ∨
    (∃ half source level, BlindRotationNTT.transform log psi (digit bits level (difference source)) ≠ PBSHadamardBlindRotation.project stage.external (stage.externalAddress half) (.inl (PBSHadamardBlindRotation.digitIndex (source,level),false))) ∨
    (∃ half source level, BlindRotationNTT.transform log psi (control source level half) ≠ PBSHadamardBlindRotation.project stage.external (stage.externalAddress half) (.inl (PBSHadamardBlindRotation.digitIndex (source,level),true))) ∨
    (∃ half, BlindRotationNTT.transform log psi (external half) ≠ PBSHadamardBlindRotation.project stage.external (stage.externalAddress half) (.inr ()))

end

section
variable {q log levels cells width : ℕ} [Fact q.Prime]

def KeyFailure (psi : ZMod q) (bits : ℕ)
    (key : NativeKeySwitch.Key q (2^log) levels) (mask : Poly q (2^log))
    (result : Cipher q (2^log)) (stage : PackedKeySwitchStage.Stage q log levels cells width) : Prop :=
    ¬PBSHadamard.Relation stage.tables ∨
    (∃ half level, BlindRotationNTT.transform log psi (digit bits level (-mask)) ≠
      CanonicalKeySwitch.project stage.tables (stage.address half) (.inl (level,false))) ∨
    (∃ half level, BlindRotationNTT.transform log psi (key level half) ≠
      CanonicalKeySwitch.project stage.tables (stage.address half) (.inl (level,true))) ∨
    (∃ half, BlindRotationNTT.transform log psi (result half) ≠
      CanonicalKeySwitch.project stage.tables (stage.address half) (.inr ()))

end

variable {q dimension brLevels ksLevels c lanes r mc mw ec ew kc kw : ℕ}
variable {F : Type} [Field F] [Fact q.Prime]

theorem first_stage_coverage
    (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(c+lanes+1))) (embed : ZMod q →+* F)
    (brBits ksBits stride : ℕ) (shape : dimension ≤ 2^(c+lanes))
    (positive : 0 < dimension) (fits : dimension ≤ 2^r)
    (key : NativePBS.PublicKey q (2^(c+lanes)) dimension brLevels ksLevels) (input : NativePBS.Inputs q dimension)
    (tables : AccumulatorTrace.Tables q (2^(c+lanes)) (2^r)) (final increment : Cipher q (2^(c+lanes)))
    (decompositionA decompositionB : AccumulatorMatrixSoundness.Table F (2^lanes) c r)
    (stages : Fin dimension → PackedBlindRotationTrace.Stages q (c+lanes) brLevels mc mw ec ew)
    (keyStage : PackedKeySwitchStage.Stage q (c+lanes) ksLevels kc kw)
    (output : NativePublic.Ciphertext q dimension)
    (wrong : output ≠ CanonicalPBS.evaluate brBits ksBits stride shape key input) :
    ¬(AccumulatorEndpointSoundness.FullHolds (PackedAccumulatorTrace.sources embed
      (CanonicalPBS.rounds positive fits) tables
      (NativePBS.initial (NativePublic.frontend (n := 2^(c+lanes)) stride input.1 input.2)) final decompositionA decompositionB)) ∨
    (∃ round : Fin dimension,
      BlindFailure psi brBits
        ((NativePublic.frontend (n := 2^(c+lanes)) stride input.1 input.2).rotations round)
        (key.blind round)
        (tables.input (AccumulatorTrace.active (CanonicalPBS.rounds positive fits).shape round))
        (tables.product (AccumulatorTrace.active (CanonicalPBS.rounds positive fits).shape round))
        (tables.difference (AccumulatorTrace.active (CanonicalPBS.rounds positive fits).shape round))
        (tables.external (AccumulatorTrace.active (CanonicalPBS.rounds positive fits).shape round)) (stages round) ∧
      ∀ earlier : Fin dimension, earlier.val < round.val →
        PackedBlindRotationTrace.Holds psi brBits
          ((NativePublic.frontend (n := 2^(c+lanes)) stride input.1 input.2).rotations earlier)
          (key.blind earlier)
          (tables.input (AccumulatorTrace.active (CanonicalPBS.rounds positive fits).shape earlier))
          (tables.product (AccumulatorTrace.active (CanonicalPBS.rounds positive fits).shape earlier))
          (tables.difference (AccumulatorTrace.active (CanonicalPBS.rounds positive fits).shape earlier))
          (tables.external (AccumulatorTrace.active (CanonicalPBS.rounds positive fits).shape earlier)) (stages earlier)) ∨
    KeyFailure psi ksBits key.switching ((NativePBS.bias final) false) increment keyStage ∨
    ¬(PBSHadamard.Relation (KeySwitchExtraction.tables (c := c) (lanes := lanes)
      positive (NativePBS.bias final) increment output)) := by
  rcases PackedPBSCoverage.wrong_output_coverage psi primitive embed brBits ksBits stride
    shape positive fits key input tables final increment decompositionA decompositionB stages
    keyStage output wrong with arithmetic | multiplication | switched | extracted
  · exact Or.inl arithmetic
  · obtain ⟨round, bad, before⟩ := first_failure _ multiplication
    exact Or.inr (Or.inl ⟨round,
      PackedBlindRotationTrace.false_stage_coverage _ _ _ _ _ _ _ _ _ bad, before⟩)
  · exact Or.inr (Or.inr (Or.inl (PackedKeySwitchStage.false_stage_coverage _ _ _ _ _ _ switched)))
  · exact Or.inr (Or.inr (Or.inr extracted))

end
end FormalProof4FHE.HasteBoots.PBSFirstStageCoverage
