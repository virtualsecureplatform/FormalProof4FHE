module
public import FormalProof4FHE.HasteBoots.RectangularDecodedRadix
public import FormalProof4FHE.HasteBoots.DecodedKeySwitchIncrement
@[expose] public section

/-! The executed rectangular comparison event supplies the radix constraints
for the canonical signed key-switch increment on the common recorded family.
The key is decoded from that family; its trusted setup association is separate. -/
namespace FormalProof4FHE.HasteBoots.RectangularDecodedKeySwitch
open BinaryTree
open scoped BigOperators
open PaddedMixedWidthLookupOpeningFamily MixedWidthSharedLookupPCSAlgebra
open RectangularOwnedLookupSources (Owners Outcome)
open NativeBlindRotation (Poly)
noncomputable section
variable {q d c bits : ℕ} [Fact q.Prime]
  {K Message Memory Cfg Input Digest SourceMemory HelperMemory RetainedMemory Result Index : Type}
  [Field K] [Algebra (ZMod q) K] [DecidableEq Input] [DecidableEq Digest]
  {repetitions : Fin d → ℕ} {mode : Mode} {heights : Cfg → ℕ}
  {tag : Root (2*d+1) (∑ i, repetitions i) → Cfg}
  {g : Geometry 2 (c+1) (2*d+1) (∑ i, repetitions i)}
  {symbolWidth : Root (2*d+1) (∑ i, repetitions i) → ℕ}

theorem increment_of_not_false
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest)
    (config : RectangularRequestLookup.Parameters (ZMod q) K Message Memory Cfg Input Digest SourceMemory HelperMemory
      3 1 2 (c+1) (2*d+1) d (fun _ => 3) (fun _ => (2^bits)*2) repetitions mode)
    (domain : ∀ root, Fin (2^heights (tag root)) ↪ ZMod q)
    (capacity : ∀ root, 2^g.suffix root ≤ g.m root * symbolWidth root)
    (radius : Root (2*d+1) (∑ i, repetitions i) → ℕ)
    (sourceSymbols : ∀ source, symbolWidth (.inl source) = 4)
    (outcome : Outcome (2*d+1) (∑ i, repetitions i) Cfg Input Digest SourceMemory RetainedMemory Result heights)
    (owner : Owners Input Digest heights tag)
    (recorded : ∀ source, (owner source).root = outcome.1.1.1 source ∧
      ⟨tag (.inl source),owner source⟩ ∈ outcome.2.2.2.checkpoints.checkpoints)
    (clear : ¬RectangularOwnedRequestSources.OriginalFalse enc dummy config domain capacity radius outcome)
    (world : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Index heights 4)
    (factors : Fin (2*d+2) → Index) (keys : Fin d → Index) (result : Index)
    (evaluations : PBSHadamard.Factor d → Index)
    (associated : ∀ source, RectangularLookupSourceInterpretation.squareParameters (d := 3) (padding := 1)
      domain capacity radius sourceSymbols source = world.parameters (RadixLookupSources.comparisonRegistry factors source))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (worldRecorded : RecordedPaddedSourceFamily.Recorded world state)
    (retained : ∀ source, ⟨tag (.inl source),owner source⟩ ∈ state.checkpoints.checkpoints)
    (roots : ∀ source, (owner source).root = world.roots (RadixLookupSources.comparisonRegistry factors source))
    (noBad : ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state)
    (slotOrder : config.slots = RadixLookupSources.comparisonSlots)
    (publicTables : config.tables = fun limb => RadixLookupSources.publicTable q (2^bits)
      (RadixCanonicity.modulusDigit q (2^bits) limb.val))
    (full : ∀ limb, config.active limb = 2^(2+(c+1)))
    (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(c+2+1)))
    (radixLarge : 1 < 2^bits) (radixSmall : 2^bits < q) (enough : q-1 < (2^bits)^d)
    (linear : DecompositionLinear.Relation (2^bits : ZMod q)
      (fun factor => RecordedPaddedSourceFamily.logical world enc dummy (c+1) (factors factor)))
    (mask : Poly q (2^(c+2)))
    (known : ∀ half, PackedCipherSource.familyCipher (c := c) (lanes := 2) world enc dummy (factors DecompositionLinear.input) half = -mask)
    (digitTransform : ∀ level half, BlindRotationNTT.transform (c+2) psi
      (PackedCipherSource.familyCipher (c := c) (lanes := 2) world enc dummy (factors (DecompositionLinear.digit level)) half) =
      PackedCipherSource.familyCipher (c := c) (lanes := 2) world enc dummy (evaluations (.inl (level,false))) half)
    (keyTransform : ∀ level half, BlindRotationNTT.transform (c+2) psi
      (PackedCipherSource.familyCipher (c := c) (lanes := 2) world enc dummy (keys level) half) =
      PackedCipherSource.familyCipher (c := c) (lanes := 2) world enc dummy (evaluations (.inl (level,true))) half)
    (resultTransform : ∀ half, BlindRotationNTT.transform (c+2) psi
      (PackedCipherSource.familyCipher (c := c) (lanes := 2) world enc dummy result half) =
      PackedCipherSource.familyCipher (c := c) (lanes := 2) world enc dummy (evaluations (.inr ())) half)
    (product : PackedCipherSource.familyCipher (c := c) (lanes := 2) world enc dummy (evaluations (.inr ())) =
      ∑ level : Fin d, PackedCipherSource.familyCipher (c := c) (lanes := 2) world enc dummy (evaluations (.inl (level,false))) *
        PackedCipherSource.familyCipher (c := c) (lanes := 2) world enc dummy (evaluations (.inl (level,true)))) :
    PackedCipherSource.familyCipher (c := c) (lanes := 2) world enc dummy result = CanonicalKeySwitch.increment bits
      (fun level => PackedCipherSource.familyCipher (c := c) (lanes := 2) world enc dummy (keys level)) mask := by
  have lookup := RectangularDecodedRadix.lookup_of_not_false enc dummy config domain capacity radius sourceSymbols
    outcome owner recorded clear world factors associated state audited worldRecorded retained roots noBad slotOrder publicTables full
  exact DecodedKeySwitchIncrement.increment_of_family_constraints (c := c) (lanes := 2) world enc dummy factors keys result evaluations
    psi primitive bits radixLarge radixSmall enough linear lookup mask known digitTransform keyTransform resultTransform product

/-- A wrong decoded increment exposes an executed comparison failure or one
of the other semantic constraint families, with the same final collision event. -/
theorem wrong_increment_coverage
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest)
    (config : RectangularRequestLookup.Parameters (ZMod q) K Message Memory Cfg Input Digest SourceMemory HelperMemory
      3 1 2 (c+1) (2*d+1) d (fun _ => 3) (fun _ => (2^bits)*2) repetitions mode)
    (domain : ∀ root, Fin (2^heights (tag root)) ↪ ZMod q)
    (capacity : ∀ root, 2^g.suffix root ≤ g.m root * symbolWidth root)
    (radius : Root (2*d+1) (∑ i, repetitions i) → ℕ)
    (sourceSymbols : ∀ source, symbolWidth (.inl source) = 4)
    (outcome : Outcome (2*d+1) (∑ i, repetitions i) Cfg Input Digest SourceMemory RetainedMemory Result heights)
    (owner : Owners Input Digest heights tag)
    (recorded : ∀ source, (owner source).root = outcome.1.1.1 source ∧
      ⟨tag (.inl source),owner source⟩ ∈ outcome.2.2.2.checkpoints.checkpoints)
    (world : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Index heights 4)
    (factors : Fin (2*d+2) → Index) (keys : Fin d → Index) (result : Index)
    (evaluations : PBSHadamard.Factor d → Index)
    (associated : ∀ source, RectangularLookupSourceInterpretation.squareParameters (d := 3) (padding := 1)
      domain capacity radius sourceSymbols source = world.parameters (RadixLookupSources.comparisonRegistry factors source))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (worldRecorded : RecordedPaddedSourceFamily.Recorded world state)
    (retained : ∀ source, ⟨tag (.inl source),owner source⟩ ∈ state.checkpoints.checkpoints)
    (roots : ∀ source, (owner source).root = world.roots (RadixLookupSources.comparisonRegistry factors source))
    (slotOrder : config.slots = RadixLookupSources.comparisonSlots)
    (publicTables : config.tables = fun limb => RadixLookupSources.publicTable q (2^bits)
      (RadixCanonicity.modulusDigit q (2^bits) limb.val))
    (full : ∀ limb, config.active limb = 2^(2+(c+1)))
    (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(c+2+1)))
    (radixLarge : 1 < 2^bits) (radixSmall : 2^bits < q) (enough : q-1 < (2^bits)^d)
    (mask : Poly q (2^(c+2)))
    (wrong : PackedCipherSource.familyCipher (c := c) (lanes := 2) world enc dummy result ≠
      CanonicalKeySwitch.increment bits
        (fun level => PackedCipherSource.familyCipher (c := c) (lanes := 2) world enc dummy (keys level)) mask) :
    RectangularOwnedRequestSources.OriginalFalse enc dummy config domain capacity radius outcome ∨
    CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state ∨
    ¬DecompositionLinear.Relation (2^bits : ZMod q)
      (fun factor => RecordedPaddedSourceFamily.logical world enc dummy (c+1) (factors factor)) ∨
    (∃ half, PackedCipherSource.familyCipher (c := c) (lanes := 2) world enc dummy (factors DecompositionLinear.input) half ≠ -mask) ∨
    (∃ level half, BlindRotationNTT.transform (c+2) psi
      (PackedCipherSource.familyCipher (c := c) (lanes := 2) world enc dummy (factors (DecompositionLinear.digit level)) half) ≠
      PackedCipherSource.familyCipher (c := c) (lanes := 2) world enc dummy (evaluations (.inl (level,false))) half) ∨
    (∃ level half, BlindRotationNTT.transform (c+2) psi
      (PackedCipherSource.familyCipher (c := c) (lanes := 2) world enc dummy (keys level) half) ≠
      PackedCipherSource.familyCipher (c := c) (lanes := 2) world enc dummy (evaluations (.inl (level,true))) half) ∨
    (∃ half, BlindRotationNTT.transform (c+2) psi
      (PackedCipherSource.familyCipher (c := c) (lanes := 2) world enc dummy result half) ≠
      PackedCipherSource.familyCipher (c := c) (lanes := 2) world enc dummy (evaluations (.inr ())) half) ∨
    PackedCipherSource.familyCipher (c := c) (lanes := 2) world enc dummy (evaluations (.inr ())) ≠
      ∑ level : Fin d, PackedCipherSource.familyCipher (c := c) (lanes := 2) world enc dummy (evaluations (.inl (level,false))) *
        PackedCipherSource.familyCipher (c := c) (lanes := 2) world enc dummy (evaluations (.inl (level,true))) := by
  classical
  by_contra absent
  push Not at absent
  exact wrong (increment_of_not_false enc dummy config domain capacity radius sourceSymbols outcome owner recorded
    absent.1 world factors keys result evaluations associated state audited worldRecorded retained roots absent.2.1
    slotOrder publicTables full psi primitive radixLarge radixSmall enough absent.2.2.1 mask absent.2.2.2.1
    absent.2.2.2.2.1 absent.2.2.2.2.2.1 absent.2.2.2.2.2.2.1 absent.2.2.2.2.2.2.2)

end
end FormalProof4FHE.HasteBoots.RectangularDecodedKeySwitch
