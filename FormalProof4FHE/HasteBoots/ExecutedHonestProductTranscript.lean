module
public import FormalProof4FHE.HasteBoots.HonestMatrixSetupTrace
public import FormalProof4FHE.HasteBoots.HonestEvaluationKeyTranscript
public import FormalProof4FHE.HasteBoots.ExecutedHonestProductKey
@[expose] public section

/-! Native product snapshots include the actual honest setup queries. Setup may
use the earlier single-height handler; no equality of history shapes is needed. -/
namespace FormalProof4FHE.HasteBoots.ExecutedHonestProductTranscript
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

/-- The source snapshots are frozen after the product's actual commitment work,
so they include its complete incoming shared transcript. -/
theorem prefix_log (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest)
    (family : PackedPBSOriginalReferences.Family d)
    (firstSmall : 15 ≤ q) (roundSmall : 22 ≤ q) (nodes : 8 ≤ 15)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (outcome : PaddedZeroCheck.Prefix (Factor := PBSHadamard.Factor d) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) H ×
      PaddedZeroCheck.RunResult (KeySwitchPaddedProduct.stage product enc family firstSmall roundSmall nodes))
    (supported : outcome ∈ support (PaddedZeroCheck.witness
      (KeySwitchPaddedProduct.stage product enc family firstSmall roundSmall nodes) dummy initial)) :
    initial.hash.log <+: outcome.1.2.hash.log := by
  simp only [PaddedZeroCheck.witness, MultiCommitmentPrefix.witness, support_bind, support_pure,
    Set.mem_iUnion, Set.mem_singleton_iff] at supported
  obtain ⟨first, firstSupported, last, _, equal⟩ := supported
  subst outcome
  exact SharedHashLog.run (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape H)
    (KeySwitchPaddedProduct.stage product enc family firstSmall roundSmall nodes).commit initial first firstSupported

/-- Honest key recovery uses actual setup hashes included in the native source
snapshots. Setup records no roots and may use a different extraction shape. -/
theorem key_eq_or_bad {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest)
    (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(c+3)))
    (original : NativeKeySwitch.Key q (2^(c+2)) d)
    (setupShape : Cfg → Skeleton)
    (setupInitial : CheckpointExecution.State (Input := Input) (Digest := Digest) setupShape)
    (built : ((level : Fin d) → FullData Digest (Skeleton.perfect (H (parameters product capacity radius level).tag))) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) setupShape)
    (setupSupported : built ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy setupShape)
      (HonestMatrixSetupTrace.program enc (parameters product capacity radius)
        (HonestRecordedEvaluationKey.table (parameters product capacity radius) psi original))).run setupInitial))
    (family : PackedPBSOriginalReferences.Family d)
    (firstSmall : 15 ≤ q) (roundSmall : 22 ≤ q) (nodes : 8 ≤ 15)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (setupPrefix : built.2.hash.log <+: initial.hash.log)
    (outcome : PaddedZeroCheck.Prefix (Factor := PBSHadamard.Factor d) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) H ×
      PaddedZeroCheck.RunResult (KeySwitchPaddedProduct.stage product enc
        (withKeys family (fun level => (built.1 level).getRootValue)) firstSmall roundSmall nodes))
    (supported : outcome ∈ support (PaddedZeroCheck.witness
      (KeySwitchPaddedProduct.stage product enc (withKeys family (fun level => (built.1 level).getRootValue))
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
      (withKeys family (fun level => (built.1 level).getRootValue)) firstSmall roundSmall nodes capacity radius outcome.1
    let recorded := CheckpointHistoryChain.family_recorded actual outcome.2.2 state retained
      (ExecutedKeySwitchProduct.sourceFamily_recorded (c := c) (lanes := 2) product enc
        (withKeys family (fun level => (built.1 level).getRootValue)) firstSmall roundSmall nodes capacity radius dummy initial outcome supported)
    DecodedEvaluationKey.key (c+2) psi primitive
      (fun level => PackedCipherSource.familyCipher (c := c) (lanes := 2) (RecordedSourceWorld.family state)
        enc dummy (RecordedSourceWorld.slot actual state recorded (.inl (level,true)))) = original ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape H) state := by
  dsimp only
  have logged := HonestMatrixSetupTrace.queries_logged impl enc dummy setupShape
    (parameters product capacity radius) (HonestRecordedEvaluationKey.table (parameters product capacity radius) psi original)
    setupInitial built setupSupported
  have logPrefix := setupPrefix.trans (prefix_log product enc dummy
    (withKeys family (fun level => (built.1 level).getRootValue)) firstSmall roundSmall nodes initial outcome supported)
  have roots := KeySwitchPaddedProduct.witness_roots product enc
    (withKeys family (fun level => (built.1 level).getRootValue)) firstSmall roundSmall nodes dummy initial outcome supported
  let actual := ExecutedKeySwitchProduct.sourceFamily (c := c) (lanes := 2) product enc
    (withKeys family (fun level => (built.1 level).getRootValue)) firstSmall roundSmall nodes capacity radius outcome.1
  have recorded := CheckpointHistoryChain.family_recorded actual outcome.2.2 state retained
    (ExecutedKeySwitchProduct.sourceFamily_recorded (c := c) (lanes := 2) product enc
      (withKeys family (fun level => (built.1 level).getRootValue)) firstSmall roundSmall nodes capacity radius dummy initial outcome supported)
  exact HonestEvaluationKeyTranscript.key_eq_or_bad (q := q) (c := c) (levels := d) actual
    (fun level => .inl (level,true)) enc dummy psi primitive original built.1
    (fun level => congrFun roots (.inl (level,true)))
    (fun level entry member => logPrefix.sublist.subset (logged level entry member))
    state audited sound recorded enough margin fits

end
end FormalProof4FHE.HasteBoots.ExecutedHonestProductTranscript
