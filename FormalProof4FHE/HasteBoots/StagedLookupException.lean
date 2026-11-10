module
public import FormalProof4FHE.HasteBoots.StagedRepeatedLookup
public import FormalProof4FHE.HasteBoots.StagedCommitmentException
@[expose] public section

/-! The complete staged lookup algebra and grouped native PCS bound includes
the same terminal history exception, with one whole-program hash charge. -/
namespace FormalProof4FHE.HasteBoots.StagedLookupException
open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open scoped Classical
open InteractiveAuthenticatedOpening HeterogeneousBatchOpening LookupOpeningFamily RepeatedLookupPCSAlgebra StagedRepeatedLookup
noncomputable section
variable {F K L Cfg Input Digest Response Memory SourceMemory HelperMemory : Type}
  [Field F] [Field K] [Algebra F K] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {d padding c row count repetitions size : ℕ} {heights : Cfg → ℕ} {tag : Root count repetitions → Cfg}
  {g : Geometry c row count repetitions}
  [SampleableType Digest] [SampleableType (Fin 1 → K)] [SampleableType (Fin (c + row) → K)]
  [∀ root, SampleableType (TestMatrix F (2 ^ (layout g root).front) (d + padding))]
  [∀ root, SampleableType (Fin (layout g root).queries → Fin (2 ^ heights (tag root)))]

variable [Fintype Digest] [Fintype K] [DecidableEq K] [SampleableType K]
  [Field L] [Algebra F L] [Fintype F] [Fintype L] [DecidableEq L]
  [∀ root, SampleableType ((Fin (2 ^ (layout g root).front) × Fin (d + padding)) → L)]

theorem bad_prefix_or_bad_bound {active inactive : ℕ} [NeZero (d + padding)] [∀ root, NeZero (layout g root).m]
    (analysisBasis : Module.Basis (Fin (d + padding)) F L)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (mode : Mode) (p : ℕ) [CharP K p] (small : degree mode + 1 ≤ p)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (logicalShape : active + inactive = 2 ^ (c + row)) (fullShape : mode = .full → active = 2 ^ (c + row))
    (table : Fin size → Fin count → F)
    (multiplicities : SourceEmission count Digest SourceMemory → Fin size → F)
    (pairs : HelperEmission repetitions Digest HelperMemory → Fin repetitions → Pair K)
    (algebra : Emission count repetitions Digest SourceMemory HelperMemory → ScheduleData F K Memory Cfg Input Digest (d + padding) count (c + row) repetitions mode)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (enough : ∀ root, g.m root ≤ Fintype.card (Fin (2 ^ heights (tag root))))
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * (d + padding)) (radius : Root count repetitions → ℕ)
    (fallback : PreparedLookupPair.Packet F K (d + padding) count (c + row))
    (behavior : Emission count repetitions Digest SourceMemory HelperMemory →
      RepeatedLookupPCS.Selection (F := F) (K := K) (Memory := Memory) (d := d) (padding := padding) (c := c) (row := row) (count := count) (repetitions := repetitions) →
      (root : Root count repetitions) → Protocol F Input Digest Cfg Response Memory (d + padding) heights tag (layout g) root)
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) (SourceEmission count Digest SourceMemory))
    (helperCommit : SourceEmission count Digest SourceMemory → OracleComp (SharedSequence.Shared Cfg Input Digest) (HelperEmission repetitions Digest HelperMemory))
    (distance : ∀ root, (radius root : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := L) (domain root)) (g.m root) : Set (Fin (2 ^ heights (tag root)) → L)) : ℚ≥0) / 3) :
    let next := continuation enc mode p small basis shape active (by omega) table multiplicities pairs algebra domain fallback behavior
    Pr{let outcome ← (StagedCommitmentPrefix.witness enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange count))
      (StagedHeterogeneousBatchOpening.helperRequests tag (List.finRange repetitions)) sourceCommit helperCommit next
      (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg))))}[
        (¬AllPass enc dummy basis shape logicalShape table multiplicities pairs domain capacity radius outcome.1 outcome.2.1 ∧
          outcome.2.2.1.2.accepted = true) ∨ CheckpointCollision.Bad (fun cfg => Skeleton.perfect (heights cfg)) outcome.2.2.2] ≤
      (error K mode (c + row) + pcsError (d := d) (padding := padding) (g := g) L domain radius) +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg)))
        (CheckpointCollision.loss unifSpec (fun cfg => Skeleton.perfect (heights cfg)))
        (StagedCommitmentPrefix.program
          (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange count))
          (StagedHeterogeneousBatchOpening.helperRequests tag (List.finRange repetitions)) sourceCommit helperCommit next)
        (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg))) := by
  dsimp only
  apply StagedCommitmentException.event_bound_or_bad enc dummy (fun cfg => Skeleton.perfect (heights cfg))
    (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange count))
    (StagedHeterogeneousBatchOpening.helperRequests tag (List.finRange repetitions)) sourceCommit helperCommit
    (continuation enc mode p small basis shape active (by omega) table multiplicities pairs algebra domain fallback behavior)
    (fun first second last => ¬AllPass enc dummy basis shape logicalShape table multiplicities pairs domain capacity radius first second ∧ last.1.2.accepted = true)
    (ArithmeticEvent enc dummy mode basis shape logicalShape table multiplicities pairs domain capacity radius fallback behavior) _
  · intro first second
    by_cases bad : ¬AllPass enc dummy basis shape logicalShape table multiplicities pairs domain capacity radius first second
    · let selected := badIndex enc dummy basis shape logicalShape table multiplicities pairs domain capacity radius first second bad
      let checkpoint := StagedHeterogeneousBatchOpening.snapshots heights tag first second
      let emission := StagedHeterogeneousBatchOpening.emission first.1 second.1
      have notPasses := Classical.choose_spec (not_forall.mp bad)
      have native := RepeatedLookupPCSAlgebra.facts enc dummy (fun cfg => Skeleton.perfect (heights cfg)) mode p small basis shape
        logicalShape fullShape table (multiplicities first.1) (pairValues (pairs second.1)) (algebra emission)
        (sourceTables domain capacity radius (LookupGroupedOpening.words enc dummy g checkpoint))
        (helperTables domain capacity radius (LookupGroupedOpening.words enc dummy g checkpoint) selected)
        selected (pairs second.1 selected).2.property notPasses
      have bounded := RepeatedLookupPCS.arithmetic_bound analysisBasis enc dummy basis shape domain enough capacity radius fallback
        (verifier mode p small basis shape active (by omega) table multiplicities pairs algebra) (fun emission => (algebra emission).memory)
        behavior emission checkpoint selected
        (RepeatedLookupPCSAlgebra.Arithmetic mode basis shape active (pairValues (pairs second.1) selected).2 (pairValues (pairs second.1) selected).1
          (sourceTables domain capacity radius (LookupGroupedOpening.words enc dummy g checkpoint))
          (helperTables domain capacity radius (LookupGroupedOpening.words enc dummy g checkpoint) selected))
        (error K mode (c + row)) native.2
        (RecordRoots.state _ (StagedHeterogeneousBatchOpening.helperRequests tag (List.finRange repetitions) first.1 second.1) second.2) distance
      refine (prEvent_mono _ _ _ ?_).trans bounded
      intro last event
      unfold ArithmeticEvent at event
      rw [dite_eq_left bad] at event
      exact event
    · have impossible : ∀ last, ¬ArithmeticEvent enc dummy mode basis shape logicalShape table multiplicities pairs domain capacity radius fallback behavior first second last := by
        intro last event
        unfold ArithmeticEvent at event
        rw [dite_eq_right bad] at event
        exact event
      exact (prEvent_eq_zero_of_forall_not _ _ impossible).le.trans zero_le
  · intro first _ second secondSupported last supported accepted
    obtain ⟨bad, passed⟩ := accepted
    let selected := badIndex enc dummy basis shape logicalShape table multiplicities pairs domain capacity radius first second bad
    let checkpoint := StagedHeterogeneousBatchOpening.snapshots heights tag first second
    let emission := StagedHeterogeneousBatchOpening.emission first.1 second.1
    have notPasses := Classical.choose_spec (not_forall.mp bad)
    have native := RepeatedLookupPCSAlgebra.facts enc dummy (fun cfg => Skeleton.perfect (heights cfg)) mode p small basis shape
      logicalShape fullShape table (multiplicities first.1) (pairValues (pairs second.1)) (algebra emission)
      (sourceTables domain capacity radius (LookupGroupedOpening.words enc dummy g checkpoint))
      (helperTables domain capacity radius (LookupGroupedOpening.words enc dummy g checkpoint) selected)
      selected (pairs second.1 selected).2.property notPasses
    have reduction := RepeatedLookupPCS.reduce_acceptance enc dummy basis shape domain capacity radius fallback
      (verifier mode p small basis shape active (by omega) table multiplicities pairs algebra) (fun emission => (algebra emission).memory)
      behavior emission checkpoint (StagedHeterogeneousBatchOpening.snapshots_roots heights tag first second)
      selected
      (RepeatedLookupPCSAlgebra.Arithmetic mode basis shape active (pairValues (pairs second.1) selected).2 (pairValues (pairs second.1) selected).1
        (sourceTables domain capacity radius (LookupGroupedOpening.words enc dummy g checkpoint))
        (helperTables domain capacity radius (LookupGroupedOpening.words enc dummy g checkpoint) selected))
      native.1 _
      (StagedHeterogeneousBatchOpening.snapshots_recorded enc dummy heights tag (List.finRange count) (List.finRange repetitions)
        (fun i => List.mem_finRange i) (fun i => List.mem_finRange i) helperCommit first second secondSupported)
      last supported passed
    simpa only [ArithmeticEvent, dite_eq_left bad, or_assoc] using reduction

end
end FormalProof4FHE.HasteBoots.StagedLookupException
