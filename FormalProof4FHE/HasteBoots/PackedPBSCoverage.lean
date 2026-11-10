module
public import FormalProof4FHE.HasteBoots.CanonicalPBS
public import FormalProof4FHE.HasteBoots.PackedKeySwitchStage
public import FormalProof4FHE.HasteBoots.KeySwitchExtraction
@[expose] public section

/-! Complete coefficient-source coverage for the corrected public PBS reference.
The final packed product and public extraction use the SAME increment. This is
an arithmetic refinement, not a native verifier acceptance or security theorem. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSCoverage
open NativeBlindRotation
noncomputable section
variable {q dimension brLevels ksLevels c lanes r mc mw ec ew kc kw : ℕ}
variable {F : Type} [Field F] [Fact q.Prime]

/-- All stage packings remain independent; the final switched polynomial is
computed from the supplied increment rather than accepted as another source. -/
theorem output_of_constraints
    (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(c+lanes+1))) (embed : ZMod q →+* F)
    (brBits ksBits stride : ℕ) (shape : dimension ≤ 2^(c+lanes))
    (positive : 0 < dimension) (fits : dimension ≤ 2^r)
    (key : NativePBS.PublicKey q (2^(c+lanes)) dimension brLevels ksLevels) (input : NativePBS.Inputs q dimension)
    (tables : AccumulatorTrace.Tables q (2^(c+lanes)) (2^r)) (final increment : Cipher q (2^(c+lanes)))
    (decompositionA decompositionB : AccumulatorMatrixSoundness.Table F (2^lanes) c r)
    (stages : Fin dimension → PackedBlindRotationTrace.Stages q (c+lanes) brLevels mc mw ec ew)
    (keyStage : PackedKeySwitchStage.Stage q (c+lanes) ksLevels kc kw)
    (output : NativePublic.Ciphertext q dimension)
    (arithmetic : AccumulatorEndpointSoundness.FullHolds (PackedAccumulatorTrace.sources embed
      (CanonicalPBS.rounds positive fits) tables
      (NativePBS.initial (NativePublic.frontend (n := 2^(c+lanes)) stride input.1 input.2)) final decompositionA decompositionB))
    (multiplication : PackedBlindRotationTrace.AllHolds psi brBits (CanonicalPBS.rounds positive fits) tables
      (fun i => (key.blind i,(NativePublic.frontend (n := 2^(c+lanes)) stride input.1 input.2).rotations i)) stages)
    (switched : PackedKeySwitchStage.Holds psi ksBits key.switching ((NativePBS.bias final) false) increment keyStage)
    (extracted : PBSHadamard.Relation (KeySwitchExtraction.tables (c := c) (lanes := lanes)
      positive (NativePBS.bias final) increment output)) :
    output = CanonicalPBS.evaluate brBits ksBits stride shape key input := by
  have product := PackedKeySwitchStage.increment_of_holds psi primitive ksBits key.switching
    ((NativePBS.bias final) false) increment keyStage switched
  have extraction := KeySwitchExtraction.extraction_of_relation (c := c) (lanes := lanes)
    shape positive (NativePBS.bias final) increment output extracted
  let trace : CanonicalKeySwitch.Trace q (2^(c+lanes)) :=
    ⟨increment,NativeKeySwitch.initial (NativePBS.bias final)+increment⟩
  have valid := CanonicalKeySwitch.valid_of_extraction ksBits key.switching shape (NativePBS.bias final)
    trace output product rfl extraction
  exact CanonicalPBS.relation_output brBits ksBits stride shape key input output _
    (CanonicalPBS.relation_of_packed psi primitive embed brBits ksBits stride shape positive fits
      key input tables final decompositionA decompositionB stages arithmetic multiplication trace output valid)

theorem wrong_output_coverage
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
    ¬(PackedBlindRotationTrace.AllHolds psi brBits (CanonicalPBS.rounds positive fits) tables
      (fun i => (key.blind i,(NativePublic.frontend (n := 2^(c+lanes)) stride input.1 input.2).rotations i)) stages) ∨
    ¬(PackedKeySwitchStage.Holds psi ksBits key.switching ((NativePBS.bias final) false) increment keyStage) ∨
    ¬(PBSHadamard.Relation (KeySwitchExtraction.tables (c := c) (lanes := lanes)
      positive (NativePBS.bias final) increment output)) := by
  classical
  by_contra absent
  push Not at absent
  exact wrong (output_of_constraints psi primitive embed brBits ksBits stride shape positive fits
    key input tables final increment decompositionA decompositionB stages keyStage output
    absent.1 absent.2.1 absent.2.2.1 absent.2.2.2)

end
end FormalProof4FHE.HasteBoots.PackedPBSCoverage
