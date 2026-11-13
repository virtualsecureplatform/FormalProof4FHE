module
public import FormalProof4FHE.HasteBoots.ExecutedHonestProductKey
@[expose] public section

/-! Joint honest setup and native product execution. Analysis snapshots project
exactly to the actual shared-oracle program; all child support is derived. -/
namespace FormalProof4FHE.HasteBoots.ExecutedHonestProductJoint
open OracleSpec OracleComp BinaryTree ExecutedHonestProductKey
open NativeRootMessage (Digest)
noncomputable section
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


/-- The actual setup output becomes the native product's borrowed key roots. -/
def program
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q)))
    (psi : ZMod q) (original : NativeKeySwitch.Key q (2^(c+2)) d)
    (family : PackedPBSOriginalReferences.Family d)
    (firstSmall : 15 ≤ q) (roundSmall : 22 ≤ q) (nodes : 8 ≤ 15) :=
  ExecutedHonestEvaluationKey.joint (base := unifSpec)
    (Result := ((PBSHadamard.Factor d → Digest) × CommitMemory) × PaddedZeroCheck.ActualResult product) (parameters product capacity radius) enc psi original
    (fun roots => PaddedZeroCheck.program
      (KeySwitchPaddedProduct.stage product enc (withKeys family roots) firstSmall roundSmall nodes))

/-- Retain the setup result and native product prefix without adding queries. -/
def witness
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest)
    (psi : ZMod q) (original : NativeKeySwitch.Key q (2^(c+2)) d)
    (family : PackedPBSOriginalReferences.Family d)
    (firstSmall : 15 ≤ q) (roundSmall : 22 ≤ q) (nodes : 8 ≤ 15) :
    ProbComp (((Fin d → Digest) × CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H)) ×
      (PaddedZeroCheck.Prefix (Factor := PBSHadamard.Factor d) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) H ×
        PaddedZeroCheck.RunResult product)) := do
  let built ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy
    (AmbientMatrixSource.Shape H)) (setup product capacity radius enc psi original)).run
      (CheckpointExecution.empty (AmbientMatrixSource.Shape H))
  let outcome ← PaddedZeroCheck.witness
    (KeySwitchPaddedProduct.stage product enc (withKeys family built.1) firstSmall roundSmall nodes) dummy built.2
  pure (built,outcome)

/-- Snapshot erasure is exactly the complete shared-oracle experiment. -/
theorem project
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest)
    (psi : ZMod q) (original : NativeKeySwitch.Key q (2^(c+2)) d)
    (family : PackedPBSOriginalReferences.Family d)
    (firstSmall : 15 ≤ q) (roundSmall : 22 ≤ q) (nodes : 8 ≤ 15) :
    (fun outcome => ((outcome.1.1,(outcome.2.1.1,outcome.2.2.1)),outcome.2.2.2)) <$>
      witness product capacity radius enc dummy psi original family firstSmall roundSmall nodes =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy
      (AmbientMatrixSource.Shape H)) (program product capacity radius enc psi original family
        firstSmall roundSmall nodes)).run (CheckpointExecution.empty (AmbientMatrixSource.Shape H)) := by
  simp only [witness, program, ExecutedHonestEvaluationKey.joint, simulateQ_bind, simulateQ_pure,
    StateT.run_bind, StateT.run_pure, map_bind, map_pure]
  apply bind_congr
  intro built
  have projected := PaddedZeroCheck.project_witness
    (KeySwitchPaddedProduct.stage product enc (withKeys family built.1) firstSmall roundSmall nodes) dummy built.2
  have mapped := congrArg (fun distribution =>
    (fun value => ((built.1,value.1),value.2)) <$> distribution) projected
  simp only [map_eq_bind_pure_comp, bind_assoc] at mapped
  exact mapped

/-- Both supported child executions come from this single supported witness. -/
theorem parts
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest)
    (psi : ZMod q) (original : NativeKeySwitch.Key q (2^(c+2)) d)
    (family : PackedPBSOriginalReferences.Family d)
    (firstSmall : 15 ≤ q) (roundSmall : 22 ≤ q) (nodes : 8 ≤ 15)
    (outcome : ((Fin d → Digest) × CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H)) ×
      (PaddedZeroCheck.Prefix (Factor := PBSHadamard.Factor d) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) H ×
        PaddedZeroCheck.RunResult product))
    (supported : outcome ∈ support (witness product capacity radius enc dummy psi original family
      firstSmall roundSmall nodes)) :
    outcome.1 ∈ support ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy
      (AmbientMatrixSource.Shape H)) (setup product capacity radius enc psi original)).run
        (CheckpointExecution.empty (AmbientMatrixSource.Shape H))) ∧
    outcome.2 ∈ support (PaddedZeroCheck.witness
      (KeySwitchPaddedProduct.stage product enc (withKeys family outcome.1.1) firstSmall roundSmall nodes) dummy outcome.1.2) := by
  simp only [witness, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at supported
  obtain ⟨built, setupSupported, child, childSupported, equal⟩ := supported
  subst outcome
  exact ⟨setupSupported, childSupported⟩

/-- The actual native product's selected key is the original honest key, or
the same final Bad event, on every supported joint execution. -/
theorem key_or_bad
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest)
    (psi : ZMod q) (original : NativeKeySwitch.Key q (2^(c+2)) d)
    (primitive : IsPrimitiveRoot psi (2^(c+3)))
    (family : PackedPBSOriginalReferences.Family d)
    (firstSmall : 15 ≤ q) (roundSmall : 22 ≤ q) (nodes : 8 ≤ 15)
    (outcome : ((Fin d → Digest) × CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H)) ×
      (PaddedZeroCheck.Prefix (Factor := PBSHadamard.Factor d) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) H ×
        PaddedZeroCheck.RunResult product))
    (supported : outcome ∈ support (witness product capacity radius enc dummy psi original family
      firstSmall roundSmall nodes))
    (enough : ∀ level, (parameters product capacity radius level).degree ≤
      2^H (parameters product capacity radius level).tag)
    (margin : ∀ level, 2*(parameters product capacity radius level).radius <
      Code.minDist (BlockCode.code (parameters product capacity radius level).domain
        (parameters product capacity radius level).degree 4 :
        Set (Fin (2^H (parameters product capacity radius level).tag) → Fin 4 → ZMod q)))
    (fits : ∀ level, c+1 ≤ (parameters product capacity radius level).front+
      (parameters product capacity radius level).suffix) :
    let actual := ExecutedKeySwitchProduct.sourceFamily (c := c) (lanes := 2) product enc
      (withKeys family outcome.1.1) firstSmall roundSmall nodes capacity radius outcome.2.1
    let recorded := ExecutedKeySwitchProduct.sourceFamily_recorded (c := c) (lanes := 2) product enc
      (withKeys family outcome.1.1) firstSmall roundSmall nodes capacity radius dummy outcome.1.2
      outcome.2 (parts product capacity radius enc dummy psi original family firstSmall roundSmall nodes outcome supported).2
    DecodedEvaluationKey.key (c+2) psi primitive
      (fun level => PackedCipherSource.familyCipher (c := c) (lanes := 2)
        (RecordedSourceWorld.family outcome.2.2.2) enc dummy
        (RecordedSourceWorld.slot actual outcome.2.2.2 recorded (.inl (level,true)))) = original ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape H) outcome.2.2.2 := by
  dsimp only
  have children := parts product capacity radius enc dummy psi original family firstSmall roundSmall nodes outcome supported
  have runSupported : ((outcome.2.1.1,outcome.2.2.1),outcome.2.2.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy
        (AmbientMatrixSource.Shape H)) (PaddedZeroCheck.program
          (KeySwitchPaddedProduct.stage product enc (withKeys family outcome.1.1) firstSmall roundSmall nodes))).run outcome.1.2) := by
    rw [← PaddedZeroCheck.project_witness
      (KeySwitchPaddedProduct.stage product enc (withKeys family outcome.1.1) firstSmall roundSmall nodes)
      dummy outcome.1.2, support_map, Set.mem_image]
    exact ⟨outcome.2, children.2, rfl⟩
  exact source_key_eq_or_bad product capacity radius (QueryImpl.ofLift unifSpec ProbComp)
    enc dummy psi primitive original outcome.1 children.1
    (PaddedZeroCheck.program (KeySwitchPaddedProduct.stage product enc (withKeys family outcome.1.1) firstSmall roundSmall nodes))
    ((outcome.2.1.1,outcome.2.2.1),outcome.2.2.2) runSupported family firstSmall roundSmall nodes
    outcome.1.2 outcome.2 children.2 (CheckpointHistoryChain.refl _) enough margin fits

end
end FormalProof4FHE.HasteBoots.ExecutedHonestProductJoint
