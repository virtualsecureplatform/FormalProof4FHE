module

public import FormalProof4FHE.HasteBoots.StagedRepeatedLookup

@[expose] public section

/-!
# Native lookup facts at fixed source and helper prefixes

Local arithmetic and authentication are discharged by the native selector and
grouped PCS. The middle execution may return arbitrary metadata; source
checkpoints survive that actual execution before the chosen helper roots are
recorded. No concrete helper emission or fallback is required on suspension.
-/

open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open scoped Classical
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.HeterogeneousBatchOpening
open FormalProof4FHE.HasteBoots.LookupOpeningFamily
open FormalProof4FHE.HasteBoots.RepeatedLookupPCSAlgebra
open FormalProof4FHE.HasteBoots.StagedRepeatedLookup

namespace FormalProof4FHE.HasteBoots.StagedLookupPrefixFacts

noncomputable section

section Checkpoints

variable {F Cfg Input Digest SourceMemory HelperMemory Second : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest] {count repetitions : ℕ}

/-- The source snapshot survives an arbitrary real middle program. Recording
its actual completed helper roots supplies the native two-prefix snapshots. -/
theorem snapshots_recorded (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (heights : Cfg → ℕ) (tag : Root count repetitions → Cfg)
    (middle : SourceEmission count Digest SourceMemory → OracleComp (SharedSequence.Shared Cfg Input Digest) Second)
    (first : SourceEmission count Digest SourceMemory ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (second : Second × CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (supported : second ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg)))
      (middle first.1)).run (RecordRoots.state _ (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange count) first.1) first.2)))
    (helper : HelperEmission repetitions Digest HelperMemory) :
    ∀ factor, ⟨tag factor, StagedHeterogeneousBatchOpening.snapshots heights tag first (helper, second.2) factor⟩ ∈
      (RecordRoots.state _ (StagedHeterogeneousBatchOpening.helperRequests tag (List.finRange repetitions) first.1 helper) second.2).checkpoints.checkpoints := by
  intro factor
  cases factor with
  | inl source =>
    have earlier := RecordRoots.recorded (fun cfg => Skeleton.perfect (heights cfg))
      (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange count) first.1) first.2
      (tag (.inl source), first.1.1 source) (List.mem_map_of_mem (List.mem_finRange source))
    have retained := CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy
      (fun cfg => Skeleton.perfect (heights cfg)) (tag (.inl source))
      (StagedHeterogeneousBatchOpening.snapshots heights tag first (helper, second.2) (.inl source))
      (middle first.1) (RecordRoots.state _ (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange count) first.1) first.2)
      earlier second supported
    exact RecordRoots.retains _ _ second.2 _ _ retained
  | inr index =>
    exact RecordRoots.recorded _ (StagedHeterogeneousBatchOpening.helperRequests tag (List.finRange repetitions) first.1 helper) second.2
      (tag (.inr index), helper.1 index) (List.mem_map_of_mem (List.mem_finRange index))

end Checkpoints

variable {F K L Cfg Input Digest Response Memory SourceMemory HelperMemory : Type}
  [Field F] [Field K] [Algebra F K] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {d padding c row count repetitions size : ℕ} {heights : Cfg → ℕ} {tag : Root count repetitions → Cfg}
  {g : Geometry c row count repetitions}
  [SampleableType Digest] [SampleableType (Fin 1 → K)] [SampleableType (Fin (c + row) → K)]
  [∀ root, SampleableType (TestMatrix F (2 ^ (layout g root).front) (d + padding))]
  [∀ root, SampleableType (Fin (layout g root).queries → Fin (2 ^ heights (tag root)))]
  [Fintype K] [DecidableEq K] [SampleableType K]

/-- Fixed-prefix native acceptance reduces to proved arithmetic or the final
availability disagreement, using explicitly recorded original snapshots. -/
theorem reduce_acceptance {active inactive : ℕ}
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (mode : Mode) (p : ℕ) [CharP K p] (small : degree mode + 1 ≤ p)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (logicalShape : active + inactive = 2 ^ (c + row)) (fullShape : mode = .full → active = 2 ^ (c + row))
    (table : Fin size → Fin count → F)
    (multiplicities : SourceEmission count Digest SourceMemory → Fin size → F)
    (pairs : HelperEmission repetitions Digest HelperMemory → Fin repetitions → Pair K)
    (algebra : Emission count repetitions Digest SourceMemory HelperMemory → ScheduleData F K Memory Cfg Input Digest (d + padding) count (c + row) repetitions mode)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * (d + padding)) (radius : Root count repetitions → ℕ)
    (fallback : PreparedLookupPair.Packet F K (d + padding) count (c + row))
    (behavior : Emission count repetitions Digest SourceMemory HelperMemory →
      RepeatedLookupPCS.Selection (F := F) (K := K) (Memory := Memory) (d := d) (padding := padding) (c := c) (row := row) (count := count) (repetitions := repetitions) →
      (root : Root count repetitions) → Protocol F Input Digest Cfg Response Memory (d + padding) heights tag (layout g) root)
    (first : SourceEmission count Digest SourceMemory × CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (second : HelperEmission repetitions Digest HelperMemory × CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (recorded : ∀ root, ⟨tag root, StagedHeterogeneousBatchOpening.snapshots heights tag first second root⟩ ∈ initial.checkpoints.checkpoints)
    (last : RepeatedLookupPCS.Result (F := F) (K := K) (Digest := Digest) (Response := Response) (Memory := Memory) (d := d) (padding := padding) (c := c) (row := row)
      (count := count) (repetitions := repetitions) (heights := heights) (tag := tag) (g := g) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (supported : last ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg)))
      (continuation enc mode p small basis shape active (by omega) table multiplicities pairs algebra domain fallback behavior first.1 second.1)).run initial))
    (bad : ¬AllPass enc dummy basis shape logicalShape table multiplicities pairs domain capacity radius first second)
    (accepted : last.1.2.accepted = true) :
    ArithmeticEvent enc dummy mode basis shape logicalShape table multiplicities pairs domain capacity radius fallback behavior first second last ∨
      CheckpointAvailability.Disagreement enc dummy (fun cfg => Skeleton.perfect (heights cfg)) last.2 := by
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
    behavior emission checkpoint (StagedHeterogeneousBatchOpening.snapshots_roots heights tag first second) selected
    (RepeatedLookupPCSAlgebra.Arithmetic mode basis shape active (pairValues (pairs second.1) selected).2 (pairValues (pairs second.1) selected).1
      (sourceTables domain capacity radius (LookupGroupedOpening.words enc dummy g checkpoint))
      (helperTables domain capacity radius (LookupGroupedOpening.words enc dummy g checkpoint) selected))
    native.1 initial recorded last supported accepted
  simpa only [ArithmeticEvent, dite_eq_left bad, or_assoc] using reduction

variable [Field L] [Algebra F L] [Fintype F] [Fintype L] [DecidableEq L]
  [∀ root, SampleableType ((Fin (2 ^ (layout g root).front) × Fin (d + padding)) → L)]

/-- The native arithmetic exception has the scalar plus per-root PCS bound at
any actual incoming state. No availability or pair certificate is assumed. -/
theorem arithmetic_bound {active inactive : ℕ} [NeZero (d + padding)] [∀ root, NeZero (layout g root).m]
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
    (first : SourceEmission count Digest SourceMemory × CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (second : HelperEmission repetitions Digest HelperMemory × CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (distance : ∀ root, (radius root : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := L) (domain root)) (g.m root) : Set (Fin (2 ^ heights (tag root)) → L)) : ℚ≥0) / 3) :
    Pr{let last ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg)))
      (continuation enc mode p small basis shape active (by omega) table multiplicities pairs algebra domain fallback behavior first.1 second.1)).run initial}[
        ArithmeticEvent enc dummy mode basis shape logicalShape table multiplicities pairs domain capacity radius fallback behavior first second last] ≤
      error K mode (c + row) + pcsError (d := d) (padding := padding) (g := g) L domain radius := by
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
      (error K mode (c + row)) native.2 initial distance
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

end

end FormalProof4FHE.HasteBoots.StagedLookupPrefixFacts
