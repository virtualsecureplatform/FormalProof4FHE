module
public import FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup
public import FormalProof4FHE.HasteBoots.StagedPrefixSafeBound
@[expose] public section

/-! Heterogeneous shared comparison algebra and original-root PCS errors at
an arbitrary audited incoming history, outside its final collision event. -/
open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open scoped Classical
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening
open FormalProof4FHE.HasteBoots.PaddedMixedWidthLookupOpeningFamily
open FormalProof4FHE.HasteBoots.MixedWidthSharedLookupPCSAlgebra
open FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup
namespace FormalProof4FHE.HasteBoots.RectangularLookupConditionalSoundness
noncomputable section
variable {F K Message Memory Cfg Input Digest Response SourceMemory HelperMemory : Type}
  [Field F] [Field K] [Algebra F K] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {d padding helperPadding c row count jobs : ℕ} {columns sizes : Fin jobs → ℕ} {mode : Mode}
  {heights : Cfg → ℕ} {tag : Root count jobs → Cfg} {g : Geometry c row count jobs} {symbolWidth : Root count jobs → ℕ}
  [SampleableType Digest] [SampleableType (Fin 1 → K)] [SampleableType (Fin (c + row) → K)]
  [∀ root, SampleableType (TestMatrix F (2 ^ (layout g root).front) (packedWidth (d + padding) (d + helperPadding) root))]
  [∀ root, SampleableType (Fin (layout g root).queries → Fin (2 ^ heights (tag root)))]
  [Fintype K] [DecidableEq K] [SampleableType K]
    [Fintype F]
  [∀ root, SampleableType ((Fin (2 ^ (layout g root).front) × Fin (packedWidth (d + padding) (d + helperPadding) root)) → F)]

theorem bad_prefix_safe_bound [∀ root : Root count jobs, NeZero (symbolWidth root)] [∀ root, NeZero (layout g root).m]
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (config : Parameters F K Message Memory Cfg Input Digest SourceMemory HelperMemory d padding c row count jobs columns sizes mode)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (enough : ∀ root, g.m root ≤ Fintype.card (Fin (2 ^ heights (tag root))))
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * symbolWidth root) (radius : Root count jobs → ℕ)
    (fallback : Packet F K (d + padding) count (c + row) jobs)
    (behavior : Emission count jobs Digest SourceMemory HelperMemory → RectangularSharedLookupPCS.Selection F K Memory (d + padding) count jobs (c + row) →
      (root : Root count jobs) → Protocol F Input Digest Cfg Response Memory (packedWidth (d + padding) (d + helperPadding)) symbolWidth heights tag (layout g) root)
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) (SourceEmission count Digest SourceMemory))
    (helperCommit : SourceEmission count Digest SourceMemory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (HelperEmission jobs Digest HelperMemory))
    (distanceLarge : ∀ root, radius root < Fintype.card F)
    (distance : ∀ root, 3*radius root < Code.minDist (BlockCode.code (domain root) (g.m root) (symbolWidth root) :
      Set (Fin (2^heights (tag root)) → Fin (symbolWidth root) → F)))
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (audited : CheckpointExecution.Audited enc dummy (fun cfg => Skeleton.perfect (heights cfg)) initial) :
    let next := RectangularStagedSharedLookup.continuation (helperPadding := helperPadding) enc config p small domain fallback behavior
    Pr{let outcome ← (StagedCommitmentPrefix.witness enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (RectangularStagedOpening.sourceRequests tag (List.finRange count))
      (RectangularStagedOpening.helperRequests tag (List.finRange jobs)) sourceCommit helperCommit next
      initial)}[
        (¬AllPass (helperPadding := helperPadding) enc dummy config domain capacity radius outcome.1 outcome.2.1 ∧ outcome.2.2.1.2.accepted = true) ∧
        ¬CheckpointCollision.Bad (fun cfg => Skeleton.perfect (heights cfg)) outcome.2.2.2] ≤
      (error K mode (c + row) + pcsError (d := d) (padding := padding) (helperPadding := helperPadding) (g := g) (symbolWidth := symbolWidth) domain radius) := by
  dsimp only
  apply StagedPrefixSafeBound.event_bound enc dummy (fun cfg => Skeleton.perfect (heights cfg))
    (RectangularStagedOpening.sourceRequests tag (List.finRange count))
    (RectangularStagedOpening.helperRequests tag (List.finRange jobs)) sourceCommit helperCommit
    (RectangularStagedSharedLookup.continuation (helperPadding := helperPadding) enc config p small domain fallback behavior) initial audited
    (fun first second last => ¬AllPass (helperPadding := helperPadding) enc dummy config domain capacity radius first second ∧ last.1.2.accepted = true)
    (ArithmeticEvent (helperPadding := helperPadding) enc dummy config domain capacity radius fallback behavior) _
  · intro first second
    by_cases bad : ¬AllPass (helperPadding := helperPadding) enc dummy config domain capacity radius first second
    · let selected := badIndex (helperPadding := helperPadding) enc dummy config domain capacity radius first second bad
      let checkpoint := RectangularStagedOpening.snapshots heights tag first second
      let emission := RectangularStagedOpening.emission first.1 second.1
      have notPasses := Classical.choose_spec (not_forall.mp bad)
      have native := MixedWidthSharedLookupPCSAlgebra.facts enc dummy (fun cfg => Skeleton.perfect (heights cfg)) mode p small
        config.basis config.shape config.jobsPositive config.slots (pairValues (config.pairs second.1)) config.active
        (fun job => by have := config.logicalShape job; omega) config.tables (config.multiplicities first.1) (config.driver emission)
        (RectangularPaddedLookupOpeningFamily.sourceTables (d := d) (padding := padding) (helperPadding := helperPadding) domain capacity radius (RectangularLookupGroupedOpening.words (d := d) (padding := padding) (helperPadding := helperPadding) enc dummy g checkpoint))
        (RectangularPaddedLookupOpeningFamily.helperTables (d := d) (padding := padding) (helperPadding := helperPadding) domain capacity radius (RectangularLookupGroupedOpening.words (d := d) (padding := padding) (helperPadding := helperPadding) enc dummy g checkpoint)) selected
        (config.logicalShape selected) (fun full => config.fullShape full selected) (config.pairs second.1 selected).2.property
        notPasses (fun points message => config.sumDegree emission points message selected)
        (fun points message => config.identityDegree emission points message selected)
      have bounded := RectangularSharedLookupPCS.arithmetic_bound enc dummy config.basis config.shape domain enough capacity radius fallback
        (verifier config p small) behavior emission checkpoint
        (MixedWidthSharedLookupPCSAlgebra.Arithmetic mode config.basis config.shape config.slots config.active (pairValues (config.pairs second.1))
          (RectangularPaddedLookupOpeningFamily.sourceTables (d := d) (padding := padding) (helperPadding := helperPadding) domain capacity radius (RectangularLookupGroupedOpening.words (d := d) (padding := padding) (helperPadding := helperPadding) enc dummy g checkpoint))
          (RectangularPaddedLookupOpeningFamily.helperTables (d := d) (padding := padding) (helperPadding := helperPadding) domain capacity radius (RectangularLookupGroupedOpening.words (d := d) (padding := padding) (helperPadding := helperPadding) enc dummy g checkpoint)) selected)
        (error K mode (c + row)) native.2
        (RecordRoots.state _ (RectangularStagedOpening.helperRequests tag (List.finRange jobs) first.1 second.1) second.2) distanceLarge distance
      refine (prEvent_mono _ _ _ ?_).trans bounded
      intro last event
      unfold ArithmeticEvent at event
      rw [dite_eq_left bad] at event
      exact event
    · have impossible : ∀ last, ¬ArithmeticEvent (helperPadding := helperPadding) enc dummy config domain capacity radius fallback behavior first second last := by
        intro last event
        unfold ArithmeticEvent at event
        rw [dite_eq_right bad] at event
        exact event
      exact (prEvent_eq_zero_of_forall_not _ _ impossible).le.trans zero_le
  · intro first _ second secondSupported last supported accepted
    obtain ⟨bad,passed⟩ := accepted
    let selected := badIndex (helperPadding := helperPadding) enc dummy config domain capacity radius first second bad
    let checkpoint := RectangularStagedOpening.snapshots heights tag first second
    let emission := RectangularStagedOpening.emission first.1 second.1
    have notPasses := Classical.choose_spec (not_forall.mp bad)
    have native := MixedWidthSharedLookupPCSAlgebra.facts enc dummy (fun cfg => Skeleton.perfect (heights cfg)) mode p small
      config.basis config.shape config.jobsPositive config.slots (pairValues (config.pairs second.1)) config.active
      (fun job => by have := config.logicalShape job; omega) config.tables (config.multiplicities first.1) (config.driver emission)
      (RectangularPaddedLookupOpeningFamily.sourceTables (d := d) (padding := padding) (helperPadding := helperPadding) domain capacity radius (RectangularLookupGroupedOpening.words (d := d) (padding := padding) (helperPadding := helperPadding) enc dummy g checkpoint))
      (RectangularPaddedLookupOpeningFamily.helperTables (d := d) (padding := padding) (helperPadding := helperPadding) domain capacity radius (RectangularLookupGroupedOpening.words (d := d) (padding := padding) (helperPadding := helperPadding) enc dummy g checkpoint)) selected
      (config.logicalShape selected) (fun full => config.fullShape full selected) (config.pairs second.1 selected).2.property
      notPasses (fun points message => config.sumDegree emission points message selected)
      (fun points message => config.identityDegree emission points message selected)
    have reduction := RectangularSharedLookupPCS.reduce_acceptance enc dummy config.basis config.shape config.slots config.coverage
      domain capacity radius fallback (verifier config p small) behavior emission checkpoint
      (RectangularStagedOpening.snapshots_roots heights tag first second)
      (MixedWidthSharedLookupPCSAlgebra.Arithmetic mode config.basis config.shape config.slots config.active (pairValues (config.pairs second.1))
        (RectangularPaddedLookupOpeningFamily.sourceTables (d := d) (padding := padding) (helperPadding := helperPadding) domain capacity radius (RectangularLookupGroupedOpening.words (d := d) (padding := padding) (helperPadding := helperPadding) enc dummy g checkpoint))
        (RectangularPaddedLookupOpeningFamily.helperTables (d := d) (padding := padding) (helperPadding := helperPadding) domain capacity radius (RectangularLookupGroupedOpening.words (d := d) (padding := padding) (helperPadding := helperPadding) enc dummy g checkpoint)) selected)
      native.1 _
      (RectangularStagedOpening.snapshots_recorded enc dummy heights tag (List.finRange count) (List.finRange jobs)
        (fun i => List.mem_finRange i) (fun i => List.mem_finRange i) helperCommit first second secondSupported)
      last supported passed
    simpa only [ArithmeticEvent,dite_eq_left bad,or_assoc] using reduction
end
end FormalProof4FHE.HasteBoots.RectangularLookupConditionalSoundness
