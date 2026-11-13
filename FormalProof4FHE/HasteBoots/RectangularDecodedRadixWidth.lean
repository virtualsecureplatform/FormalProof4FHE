module
public import FormalProof4FHE.HasteBoots.RecordedSourceWidth
public import FormalProof4FHE.HasteBoots.RectangularDecodedRadix
public import FormalProof4FHE.HasteBoots.RadixLookupSources
@[expose] public section

/-! Preserve the actual rectangular lookup configuration when its total scalar
width is publicly equal to the recorded reconstruction width. -/
namespace FormalProof4FHE.HasteBoots.RectangularDecodedRadixWidth
open OracleSpec OracleComp BinaryTree Matrix
open scoped BigOperators
open InteractiveAuthenticatedOpening PaddedMixedWidthLookupOpeningFamily MixedWidthSharedLookupPCSAlgebra
open RectangularOwnedLookupSources (Owners Outcome)
noncomputable section
variable {q e padding b c row digits radix : ℕ} [Fact q.Prime]
  {K Message Memory Cfg Input Digest SourceMemory HelperMemory RetainedMemory Result Index : Type}
  [Field K] [Algebra (ZMod q) K] [DecidableEq Input] [DecidableEq Digest]
  {repetitions : Fin digits → ℕ} {mode : Mode} {heights : Cfg → ℕ}
  {tag : Root (2*digits+1) (∑ i, repetitions i) → Cfg}
  {g : Geometry c row (2*digits+1) (∑ i, repetitions i)}
  {symbolWidth : Root (2*digits+1) (∑ i, repetitions i) → ℕ}

variable (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest)
  (config : RectangularRequestLookup.Parameters (ZMod q) K Message Memory Cfg Input Digest SourceMemory HelperMemory
    e padding c row (2*digits+1) digits (fun _ => 3) (fun _ => radix*2) repetitions mode)
  (domain : ∀ root, Fin (2^heights (tag root)) ↪ ZMod q)
  (capacity : ∀ root, 2^g.suffix root ≤ g.m root * symbolWidth root)
  (radius : Root (2*digits+1) (∑ i, repetitions i) → ℕ)
  (sourceSymbols : ∀ source, symbolWidth (.inl source) = e+padding)
  (outcome : Outcome (2*digits+1) (∑ i, repetitions i) Cfg Input Digest SourceMemory RetainedMemory Result heights)
  (owner : Owners Input Digest heights tag)
  (recorded : ∀ source, (owner source).root = outcome.1.1.1 source ∧
    ⟨tag (.inl source),owner source⟩ ∈ outcome.2.2.2.checkpoints.checkpoints)
  (clear : ¬RectangularOwnedRequestSources.OriginalFalse enc dummy config domain capacity radius outcome)
  (world : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Index heights b)
  (width : b = e+padding)
  (factors : Fin (2*digits+2) → Index)
  (associated : ∀ source, RectangularLookupSourceInterpretation.squareParameters domain capacity radius sourceSymbols source =
    (RecordedSourceWidth.family width world).parameters (RadixLookupSources.comparisonRegistry factors source))
  (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
  (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
  (worldRecorded : RecordedPaddedSourceFamily.Recorded world state)
  (retained : ∀ source, ⟨tag (.inl source),owner source⟩ ∈ state.checkpoints.checkpoints)
  (roots : ∀ source, (owner source).root = world.roots (RadixLookupSources.comparisonRegistry factors source))
  (noBad : ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state)
  (slotOrder : config.slots = RadixLookupSources.comparisonSlots)
  (publicTables : config.tables = fun limb => RadixLookupSources.publicTable q radix
    (RadixCanonicity.modulusDigit q radix limb.val))
  (full : ∀ limb, config.active limb = 2^(c+row))

include config domain capacity radius sourceSymbols outcome owner recorded clear associated state audited
  worldRecorded retained roots noBad slotOrder publicTables full
/-- Original lookup membership transports back to the executed scalar width,
while keeping the real rectangular request configuration unchanged. -/
theorem lookup_of_not_false (cell : MatrixFold.Cube row) (lane : Fin b) :
    RadixCanonicity.LookupAt q radix
      (fun factor => RecordedPaddedSourceFamily.logical world enc dummy row (factors factor)) cell lane := by
  have castRoots : ∀ source, (owner source).root =
      (RecordedSourceWidth.family width world).roots (RadixLookupSources.comparisonRegistry factors source) := by
    rw [RecordedSourceWidth.roots]
    exact roots
  have actual := RectangularDecodedRadix.lookup_of_not_false enc dummy config domain capacity radius sourceSymbols
    outcome owner recorded clear (RecordedSourceWidth.family width world) factors associated state audited
    (RecordedSourceWidth.recorded width world state worldRecorded) retained castRoots noBad slotOrder publicTables full
    cell (Fin.cast width lane)
  simpa only [RadixCanonicity.LookupAt,RecordedSourceWidth.logical] using actual

include config domain capacity radius sourceSymbols outcome owner recorded clear associated state audited
  worldRecorded retained roots noBad slotOrder publicTables full
/-- The actual lookup layout enforces canonical digits of the original family,
using only a public total-width equality, without changing active/helper padding. -/
theorem digits_of_not_false (radixLarge : 1 < radix) (radixSmall : radix < q)
    (enough : q-1 < radix^digits)
    (linear : DecompositionLinear.Relation (radix : ZMod q)
      (fun factor => RecordedPaddedSourceFamily.logical world enc dummy row (factors factor)))
    (cell : MatrixFold.Cube row) (lane : Fin b) (digit : Fin digits) :
    (RecordedPaddedSourceFamily.logical world enc dummy row (factors (DecompositionLinear.digit digit)) cell lane).val =
      (RecordedPaddedSourceFamily.logical world enc dummy row (factors DecompositionLinear.input) cell lane).val /
        radix^digit.val % radix := by
  have castRoots : ∀ source, (owner source).root =
      (RecordedSourceWidth.family width world).roots (RadixLookupSources.comparisonRegistry factors source) := by
    rw [RecordedSourceWidth.roots]
    exact roots
  have actual := RectangularDecodedRadix.digits_of_not_false enc dummy config domain capacity radius sourceSymbols
    outcome owner recorded clear (RecordedSourceWidth.family width world) factors associated state audited
    (RecordedSourceWidth.recorded width world state worldRecorded) retained castRoots noBad slotOrder publicTables full
    radixLarge radixSmall enough (RecordedSourceWidth.relation width world enc dummy factors (radix : ZMod q) linear)
    cell (Fin.cast width lane) digit
  simpa only [RecordedSourceWidth.logical] using actual

end
end FormalProof4FHE.HasteBoots.RectangularDecodedRadixWidth
