module
public import FormalProof4FHE.HasteBoots.HonestKeyQueryReceipt
public import FormalProof4FHE.HasteBoots.ExecutedHonestProductTranscript
@[expose] public section

/-! Associate actual product key slots with honest setup using factual query
receipts transported by the public descriptor routing. -/
namespace FormalProof4FHE.HasteBoots.ExecutedProductKeyReceipt
open OracleSpec OracleComp BinaryTree ExecutedHonestProductKey
open NativeRootMessage (Digest)
noncomputable section
attribute [local irreducible] MonadAttach.support
variable {q c d : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory : Type}
  [DecidableEq Input] [DecidableEq Digest] {H : Cfg → ℕ}
variable (product : KeySwitchPaddedProduct.Scheme (q := q) (d := d) (b := 4) (n := c)
    (Input := Input) (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory) (heights := H))
    (capacity : ∀ factor, 2^(product.code factor).suffix ≤ (product.code factor).m*4)
    (radius : PBSHadamard.Factor d → ℕ)
variable [SampleableType Digest] [SampleableType (Fin 4 → ZMod q)]
  [SampleableType (PackedZeroReduction.Points (ZMod q) c 4)]
  [SampleableType (Fin 4 → Fin 4 → ZMod q)]
  [∀ factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^(product.code factor).front) 4)]
  [∀ factor, SampleableType (Fin (product.code factor).queries → Fin (2^H (product.tag factor)))]

theorem key_eq_or_bad
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest)
    (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(c+3)))
    (original : NativeKeySwitch.Key q (2^(c+2)) d)
    (family : PackedPBSOriginalReferences.Family d)
    (firstSmall : 15 ≤ q) (roundSmall : 22 ≤ q) (nodes : 8 ≤ 15)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (receipt : HonestKeyQueryReceipt.Receipt (parameters product capacity radius) enc psi original family.keys initial.hash.log)
    (outcome : PaddedZeroCheck.Prefix (Factor := PBSHadamard.Factor d) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) H ×
      PaddedZeroCheck.RunResult (KeySwitchPaddedProduct.stage product enc
        family firstSmall roundSmall nodes))
    (supported : outcome ∈ support (PaddedZeroCheck.witness
      (KeySwitchPaddedProduct.stage product enc family
        firstSmall roundSmall nodes) dummy initial))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state)
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape H) state)
    (sound : RecordedCheckpointQueries.Sound (AmbientMatrixSource.Shape H) state)
    (enough : ∀ level, (parameters product capacity radius level).degree ≤ 2^H (parameters product capacity radius level).tag)
    (margin : ∀ level, 2*(parameters product capacity radius level).radius <
      Code.minDist (BlockCode.code (parameters product capacity radius level).domain
        (parameters product capacity radius level).degree 4 :
        Set (Fin (2^H (parameters product capacity radius level).tag) → Fin 4 → ZMod q)))
    (fits : ∀ level, c+1 ≤ (parameters product capacity radius level).front+(parameters product capacity radius level).suffix) :
    let actual := ExecutedKeySwitchProduct.sourceFamily (c := c) (lanes := 2) product enc
      family firstSmall roundSmall nodes capacity radius outcome.1
    let recorded := CheckpointHistoryChain.family_recorded actual outcome.2.2 state retained
      (ExecutedKeySwitchProduct.sourceFamily_recorded (c := c) (lanes := 2) product enc
        family firstSmall roundSmall nodes capacity radius dummy initial outcome supported)
    DecodedEvaluationKey.key (c+2) psi primitive
      (fun level => PackedCipherSource.familyCipher (c := c) (lanes := 2) (RecordedSourceWorld.family state)
        enc dummy (RecordedSourceWorld.slot actual state recorded (.inl (level,true)))) = original ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape H) state := by
  dsimp only
  obtain ⟨labels, rootValues, logged⟩ := receipt
  have logPrefix := ExecutedHonestProductTranscript.prefix_log product enc dummy family
    firstSmall roundSmall nodes initial outcome supported
  have roots := KeySwitchPaddedProduct.witness_roots product enc family
    firstSmall roundSmall nodes dummy initial outcome supported
  let actual := ExecutedKeySwitchProduct.sourceFamily (c := c) (lanes := 2) product enc family
    firstSmall roundSmall nodes capacity radius outcome.1
  have recorded := CheckpointHistoryChain.family_recorded actual outcome.2.2 state retained
    (ExecutedKeySwitchProduct.sourceFamily_recorded (c := c) (lanes := 2) product enc family
      firstSmall roundSmall nodes capacity radius dummy initial outcome supported)
  exact HonestEvaluationKeyTranscript.key_eq_or_bad (q := q) (c := c) (levels := d) actual
    (fun level => .inl (level,true)) enc dummy psi primitive original labels
    (fun level => (congrFun roots (.inl (level,true))).trans (rootValues level))
    (fun level entry member => logPrefix.sublist.subset (logged level entry member))
    state audited sound recorded enough margin fits

end
end FormalProof4FHE.HasteBoots.ExecutedProductKeyReceipt
