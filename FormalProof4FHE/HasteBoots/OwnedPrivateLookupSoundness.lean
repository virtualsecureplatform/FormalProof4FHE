module
public import FormalProof4FHE.HasteBoots.StagedPrivateLookupException
public import FormalProof4FHE.HasteBoots.OwnedLookupSources
@[expose] public section

/-! False lookup acceptance on any matching recorded original source family.
Private repeated-pair, native algebra and grouped original-root PCS errors
compose with source reuse using ONE actual complete-run hash charge. -/
namespace FormalProof4FHE.HasteBoots.OwnedPrivateLookupSoundness
open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open InteractiveAuthenticatedOpening HeterogeneousBatchOpening LookupOpeningFamily RepeatedLookupPCSAlgebra
open StagedRepeatedLookup StagedPrivateLookup
noncomputable section
variable {F K L Cfg Input Digest Response Memory SourceMemory HelperMemory Result : Type}
  [Field F] [Field K] [Algebra F K] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {d padding c row count repetitions size : ℕ} {heights : Cfg → ℕ} {tag : Root count repetitions → Cfg}
  {g : Geometry c row count repetitions}
  [SampleableType Digest]

variable [Fintype K] [DecidableEq K] [SampleableType K]

variable [SampleableType (Fin 1 → K)] [SampleableType (Fin (c + row) → K)]
  [∀ root, SampleableType (TestMatrix F (2 ^ (layout g root).front) (d + padding))]
  [∀ root, SampleableType (Fin (layout g root).queries → Fin (2 ^ heights (tag root)))]

variable [Fintype Digest] [Field L] [Algebra F L] [Fintype F] [Fintype L] [DecidableEq L]
  [∀ root, SampleableType ((Fin (2 ^ (layout g root).front) × Fin (d + padding)) → L)]

theorem false_acceptance_bound {active inactive : ℕ} [NeZero (d + padding)] [∀ root, NeZero (layout g root).m]
    (analysisBasis : Module.Basis (Fin (d + padding)) F L)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (mode : Mode) (p : ℕ) [CharP K p] (small : degree mode + 1 ≤ p)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (logicalShape : active + inactive = 2 ^ (c + row)) (fullShape : mode = .full → active = 2 ^ (c + row))
    (table : Fin size → Fin count → F)
    (multiplicities : SourceEmission count Digest SourceMemory → Fin size → F)
    (algebra : Emission count repetitions Digest SourceMemory (LookupPairVectorMiddle.Memory K HelperMemory repetitions) → ScheduleData F K Memory Cfg Input Digest (d + padding) count (c + row) repetitions mode)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (enough : ∀ root, g.m root ≤ Fintype.card (Fin (2 ^ heights (tag root))))
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * (d + padding)) (radius : Root count repetitions → ℕ)
    (fallback : PreparedLookupPair.Packet F K (d + padding) count (c + row))
    (behavior : Emission count repetitions Digest SourceMemory (LookupPairVectorMiddle.Memory K HelperMemory repetitions) →
      RepeatedLookupPCS.Selection (F := F) (K := K) (Memory := Memory) (d := d) (padding := padding) (c := c) (row := row) (count := count) (repetitions := repetitions) →
      (root : Root count repetitions) → Protocol F Input Digest Cfg Response Memory (d + padding) heights tag (layout g) root)
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) (SourceEmission count Digest SourceMemory))
    (pairEnough : size + 1 < Fintype.card K) (lookupSmall : active < p)
    (build : SourceEmission count Digest SourceMemory → (Fin repetitions → Pair K) →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (HelperEmission repetitions Digest HelperMemory))
    (distance : ∀ root, (radius root : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := L) (domain root)) (g.m root) : Set (Fin (2 ^ heights (tag root)) → L)) : ℚ≥0) / 3) :
    let helperCommit := fun first => LookupPairVectorMiddle.program table pairEnough (build first)
    let next := StagedRepeatedLookup.continuation enc mode p small basis shape active (by omega) table multiplicities LookupPairVectorMiddle.pairs algebra domain fallback behavior
    let experiment := StagedCommitmentPrefix.witness enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange count))
      (StagedHeterogeneousBatchOpening.helperRequests tag (List.finRange repetitions)) sourceCommit helperCommit next
      (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg)))
    Pr{let outcome ← experiment}[
      OwnedLookupSources.OriginalFalse enc dummy shape logicalShape table domain capacity radius outcome ∧
      outcome.2.2.1.2.accepted = true] ≤
      TupleLookupPair.error (Fintype.card K) count active size ^ repetitions +
      ((error K mode (c + row) + pcsError (d := d) (padding := padding) (g := g) L domain radius) +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg)))
        (CheckpointCollision.loss unifSpec (fun cfg => Skeleton.perfect (heights cfg)))
        (StagedCommitmentPrefix.program
          (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange count))
          (StagedHeterogeneousBatchOpening.helperRequests tag (List.finRange repetitions)) sourceCommit helperCommit next)
        (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg)))) := by
  dsimp only
  have bound := StagedPrivateLookupException.false_acceptance_or_bad_bound analysisBasis enc dummy mode p small basis shape
    logicalShape fullShape table multiplicities algebra domain enough capacity radius fallback behavior sourceCommit pairEnough lookupSmall build distance
  dsimp only at bound
  apply le_trans (prEvent_mono_of_support _ _ _ ?_) bound
  intro outcome supported event
  rcases OwnedLookupSources.original_false_reduction (d := d) (padding := padding) (c := c) (row := row)
    (count := count) (repetitions := repetitions) (g := g) (heights := heights) (tag := tag)
    enc dummy shape logicalShape table domain capacity radius sourceCommit
    (fun first => LookupPairVectorMiddle.program table pairEnough (build first))
    (StagedRepeatedLookup.continuation enc mode p small basis shape active (by omega) table multiplicities
      LookupPairVectorMiddle.pairs algebra domain fallback behavior) outcome supported event.1 with fresh | bad
  · exact Or.inl ⟨fresh,event.2⟩
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.OwnedPrivateLookupSoundness
