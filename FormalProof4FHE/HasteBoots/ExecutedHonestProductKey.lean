module
public import FormalProof4FHE.HasteBoots.ExecutedHonestEvaluationKey
public import FormalProof4FHE.HasteBoots.ExecutedKeySwitchProduct
public import FormalProof4FHE.HasteBoots.CheckpointHistoryChain
@[expose] public section

/-! Route executed honest setup roots directly into the native product's key
references. Product geometry determines setup descriptors, so neither descriptor
nor root matching is a caller-supplied semantic association. -/
namespace FormalProof4FHE.HasteBoots.ExecutedHonestProductKey
open OracleSpec OracleComp BinaryTree
open NativeRootMessage (Digest)
noncomputable section
variable {q c d : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory : Type}
  [DecidableEq Input] [DecidableEq Digest] {H : Cfg → ℕ}

/-- Install the computed key roots in the existing borrowed-reference family. -/
def withKeys (family : PackedPBSOriginalReferences.Family d) (roots : Fin d → Digest) :
    PackedPBSOriginalReferences.Family d := {family with keys := roots}

variable (product : KeySwitchPaddedProduct.Scheme (q := q) (d := d) (b := 4) (n := c)
    (Input := Input) (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory) (heights := H))
    (capacity : ∀ factor, 2^(product.code factor).suffix ≤ (product.code factor).m*4)
    (radius : PBSHadamard.Factor d → ℕ)

/-- Honest setup and the product borrow the same public physical descriptor. -/
def parameters (level : Fin d) : RecordedPaddedSource.Parameters (ZMod q) Cfg H 4 :=
  PaddedStageSourceInterpretation.zeroParameters product capacity radius (.inl (level,true))

def setup {ι : Type} {base : OracleSpec ι}
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q)))
    (psi : ZMod q) (original : NativeKeySwitch.Key q (2^(c+2)) d) :
    OracleComp (CheckpointExecution.Spec base Cfg Input Digest) (Fin d → Digest) :=
  ExecutedHonestEvaluationKey.setup (parameters product capacity radius) enc psi original

variable [SampleableType Digest] [SampleableType (Fin 4 → ZMod q)]
  [SampleableType (PackedZeroReduction.Points (ZMod q) c 4)]
  [SampleableType (Fin 4 → Fin 4 → ZMod q)]
  [∀ factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^(product.code factor).front) 4)]
  [∀ factor, SampleableType (Fin (product.code factor).queries → Fin (2^H (product.tag factor)))]

/-- A reached native product uses the honestly initialized key in the canonical
final source world, or the existing final Bad occurs. All root/descriptor
associations follow from construction and the product's supported execution. -/
theorem source_key_eq_or_bad {ι Result : Type} {base : OracleSpec ι}
    (impl : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest)
    (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(c+3)))
    (original : NativeKeySwitch.Key q (2^(c+2)) d)
    (built : (Fin d → Digest) × CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (setupSupported : built ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy
      (AmbientMatrixSource.Shape H)) (setup product capacity radius enc psi original)).run
        (CheckpointExecution.empty (AmbientMatrixSource.Shape H))))
    (continuation : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) Result)
    (result : Result × CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy
      (AmbientMatrixSource.Shape H)) continuation).run built.2))
    (family : PackedPBSOriginalReferences.Family d)
    (firstSmall : 15 ≤ q) (roundSmall : 22 ≤ q) (nodes : 8 ≤ 15)
    (productInitial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (outcome : PaddedZeroCheck.Prefix (Factor := PBSHadamard.Factor d) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) H ×
      PaddedZeroCheck.RunResult (KeySwitchPaddedProduct.stage product enc (withKeys family built.1) firstSmall roundSmall nodes))
    (productSupported : outcome ∈ support (PaddedZeroCheck.witness
      (KeySwitchPaddedProduct.stage product enc (withKeys family built.1) firstSmall roundSmall nodes) dummy productInitial))
    (retained : CheckpointHistoryChain.Retains outcome.2.2 result.2)
    (enough : ∀ level, (parameters product capacity radius level).degree ≤
      2^H (parameters product capacity radius level).tag)
    (margin : ∀ level, 2*(parameters product capacity radius level).radius <
      Code.minDist (BlockCode.code (parameters product capacity radius level).domain
        (parameters product capacity radius level).degree 4 :
        Set (Fin (2^H (parameters product capacity radius level).tag) → Fin 4 → ZMod q)))
    (fits : ∀ level, c+1 ≤ (parameters product capacity radius level).front+
      (parameters product capacity radius level).suffix) :
    let actual := ExecutedKeySwitchProduct.sourceFamily (c := c) (lanes := 2) product enc (withKeys family built.1)
      firstSmall roundSmall nodes capacity radius outcome.1
    let recorded := CheckpointHistoryChain.family_recorded actual outcome.2.2 result.2 retained
      (ExecutedKeySwitchProduct.sourceFamily_recorded (c := c) (lanes := 2) product enc (withKeys family built.1)
        firstSmall roundSmall nodes capacity radius dummy productInitial outcome productSupported)
    DecodedEvaluationKey.key (c+2) psi primitive
      (fun level => PackedCipherSource.familyCipher (c := c) (lanes := 2) (RecordedSourceWorld.family result.2)
        enc dummy (RecordedSourceWorld.slot actual result.2 recorded (.inl (level,true)))) = original ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape H) result.2 := by
  dsimp only
  have recorded := CheckpointHistoryChain.family_recorded
    (ExecutedKeySwitchProduct.sourceFamily (c := c) (lanes := 2) product enc (withKeys family built.1)
      firstSmall roundSmall nodes capacity radius outcome.1) outcome.2.2 result.2 retained
    (ExecutedKeySwitchProduct.sourceFamily_recorded (c := c) (lanes := 2) product enc (withKeys family built.1)
      firstSmall roundSmall nodes capacity radius dummy productInitial outcome productSupported)
  have roots := KeySwitchPaddedProduct.witness_roots product enc (withKeys family built.1)
    firstSmall roundSmall nodes dummy productInitial outcome productSupported
  apply ExecutedHonestEvaluationKey.associated_key_or_bad impl (parameters product capacity radius)
    enc dummy psi primitive original built setupSupported continuation result supported enough margin fits
    (ExecutedKeySwitchProduct.sourceFamily (c := c) (lanes := 2) product enc (withKeys family built.1)
      firstSmall roundSmall nodes capacity radius outcome.1) recorded (fun level => .inl (level,true))
  · intro level
    rfl
  · intro level
    exact congrFun roots (.inl (level,true))

end
end FormalProof4FHE.HasteBoots.ExecutedHonestProductKey
