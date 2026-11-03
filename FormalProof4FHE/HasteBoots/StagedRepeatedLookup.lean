module

public import FormalProof4FHE.HasteBoots.RepeatedLookupPCSAlgebra

@[expose] public section

/-!
# Repeated native lookup algebra and grouped PCS on the two-prefix execution

Original source words and multiplicities precede pair/helper work. Helpers
freeze before all algebra coins. The runtime uses the real repeated selector,
its own successful memory/packets, and computed native grouped opening flags.
The all-pairs-pass term stays explicit until the actual private pair-vector law
is supplied; native rejection/Fiat–Shamir/Rust and full PBS remain separate.
-/

open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open scoped Classical
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.HeterogeneousBatchOpening
open FormalProof4FHE.HasteBoots.LookupOpeningFamily
open FormalProof4FHE.HasteBoots.RepeatedLookupPCSAlgebra

namespace FormalProof4FHE.HasteBoots.StagedRepeatedLookup

noncomputable section

abbrev Pair (K : Type) [Zero K] := K × {r : K // r ≠ 0}
def pairValues {K : Type} [Zero K] {repetitions : ℕ} (pairs : Fin repetitions → Pair K) : Fin repetitions → K × K :=
  fun index => ((pairs index).1, (pairs index).2.val)

variable {F K L Cfg Input Digest Response Memory SourceMemory HelperMemory : Type}
  [Field F] [Field K] [Algebra F K] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {d padding c row count repetitions size : ℕ} {heights : Cfg → ℕ} {tag : Root count repetitions → Cfg}
  {g : Geometry c row count repetitions}
  [SampleableType Digest] [SampleableType (Fin 1 → K)] [SampleableType (Fin (c + row) → K)]
  [∀ root, SampleableType (TestMatrix F (2 ^ (layout g root).front) (d + padding))]
  [∀ root, SampleableType (Fin (layout g root).queries → Fin (2 ^ heights (tag root)))]

abbrev Emission (count repetitions : ℕ) (Digest SourceMemory HelperMemory : Type) :=
  RepeatedLookupPCS.Emission count repetitions Digest SourceMemory HelperMemory
abbrev SourceEmission (count : ℕ) (Digest SourceMemory : Type) := StagedHeterogeneousBatchOpening.SourceEmission (Fin count) Digest SourceMemory
abbrev HelperEmission (repetitions : ℕ) (Digest HelperMemory : Type) := StagedHeterogeneousBatchOpening.HelperEmission (Fin repetitions) Digest HelperMemory

def verifier (mode : Mode) (p : ℕ) [CharP K p] (small : degree mode + 1 ≤ p)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (active : ℕ) (enough : active ≤ 2 ^ (c + row)) (table : Fin size → Fin count → F)
    (multiplicities : SourceEmission count Digest SourceMemory → Fin size → F)
    (pairs : HelperEmission repetitions Digest HelperMemory → Fin repetitions → Pair K)
    (algebra : Emission count repetitions Digest SourceMemory HelperMemory → ScheduleData F K Memory Cfg Input Digest (d + padding) count (c + row) repetitions mode)
    (emission : Emission count repetitions Digest SourceMemory HelperMemory) :=
  RepeatedLookupPCSAlgebra.run mode p small basis shape active enough table (multiplicities emission.2.1)
    (pairValues (pairs emission.2.2)) (algebra emission)

def continuation (enc : MerkleOracle.Encoding Input Digest (List F))
    (mode : Mode) (p : ℕ) [CharP K p] (small : degree mode + 1 ≤ p)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (active : ℕ) (enough : active ≤ 2 ^ (c + row)) (table : Fin size → Fin count → F)
    (multiplicities : SourceEmission count Digest SourceMemory → Fin size → F)
    (pairs : HelperEmission repetitions Digest HelperMemory → Fin repetitions → Pair K)
    (algebra : Emission count repetitions Digest SourceMemory HelperMemory → ScheduleData F K Memory Cfg Input Digest (d + padding) count (c + row) repetitions mode)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (fallback : PreparedLookupPair.Packet F K (d + padding) count (c + row))
    (behavior : Emission count repetitions Digest SourceMemory HelperMemory →
      RepeatedLookupPCS.Selection (F := F) (K := K) (Memory := Memory) (d := d) (padding := padding) (c := c) (row := row) (count := count) (repetitions := repetitions) →
      (root : Root count repetitions) → Protocol F Input Digest Cfg Response Memory (d + padding) heights tag (layout g) root)
    (first : SourceEmission count Digest SourceMemory) (second : HelperEmission repetitions Digest HelperMemory) :=
  RepeatedLookupPCS.program enc basis shape domain fallback
    (verifier mode p small basis shape active enough table multiplicities pairs algebra)
    (fun emission => (algebra emission).memory) behavior (StagedHeterogeneousBatchOpening.emission first second)

/-- The pass predicate uses original pre-pair decoded sources and pre-pair
multiplicities, rather than a source selected at the helper or query prefix. -/
def AllPass {active inactive : ℕ}
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (_basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c) (logicalShape : active + inactive = 2 ^ (c + row))
    (table : Fin size → Fin count → F)
    (multiplicities : SourceEmission count Digest SourceMemory → Fin size → F)
    (pairs : HelperEmission repetitions Digest HelperMemory → Fin repetitions → Pair K)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * (d + padding)) (radius : Root count repetitions → ℕ)
    (first : SourceEmission count Digest SourceMemory × CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (second : HelperEmission repetitions Digest HelperMemory × CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg))) : Prop :=
  ∀ index, TupleLookupPair.Passes
    (LookupPairArithmetic.activeTuples logicalShape (fun i => LookupSourceFlattening.flatten shape
      (sourceTables domain capacity radius (LookupGroupedOpening.words enc dummy g (StagedHeterogeneousBatchOpening.snapshots heights tag first second)) i)))
    table (fun i => algebraMap F K (multiplicities first.1 i)) (pairValues (pairs second.1) index)

/-- Analysis selects a nonpassing index before any algebra coins. The runtime
never receives this index and still runs every pair in native order. -/
def badIndex {active inactive : ℕ}
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c) (logicalShape : active + inactive = 2 ^ (c + row))
    (table : Fin size → Fin count → F)
    (multiplicities : SourceEmission count Digest SourceMemory → Fin size → F)
    (pairs : HelperEmission repetitions Digest HelperMemory → Fin repetitions → Pair K)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * (d + padding)) (radius : Root count repetitions → ℕ)
    (first : SourceEmission count Digest SourceMemory × CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (second : HelperEmission repetitions Digest HelperMemory × CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (bad : ¬AllPass enc dummy basis shape logicalShape table multiplicities pairs domain capacity radius first second) : Fin repetitions :=
  Classical.choose (not_forall.mp bad)

/-- This is only the arithmetic exception predicate, never an operational
acceptance flag or a runtime source-selection rule. -/
def ArithmeticEvent {active inactive : ℕ}
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (mode : Mode)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c) (logicalShape : active + inactive = 2 ^ (c + row))
    (table : Fin size → Fin count → F)
    (multiplicities : SourceEmission count Digest SourceMemory → Fin size → F)
    (pairs : HelperEmission repetitions Digest HelperMemory → Fin repetitions → Pair K)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * (d + padding)) (radius : Root count repetitions → ℕ)
    (fallback : PreparedLookupPair.Packet F K (d + padding) count (c + row))
    (behavior : Emission count repetitions Digest SourceMemory HelperMemory →
      RepeatedLookupPCS.Selection (F := F) (K := K) (Memory := Memory) (d := d) (padding := padding) (c := c) (row := row) (count := count) (repetitions := repetitions) →
      (root : Root count repetitions) → Protocol F Input Digest Cfg Response Memory (d + padding) heights tag (layout g) root)
    (first : SourceEmission count Digest SourceMemory × CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (second : HelperEmission repetitions Digest HelperMemory × CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (last : RepeatedLookupPCS.Result (F := F) (K := K) (Digest := Digest) (Response := Response) (Memory := Memory) (d := d) (padding := padding) (c := c) (row := row)
      (count := count) (repetitions := repetitions) (heights := heights) (tag := tag) (g := g) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg))) : Prop :=
  if bad : ¬AllPass enc dummy basis shape logicalShape table multiplicities pairs domain capacity radius first second then
    let selected := badIndex enc dummy basis shape logicalShape table multiplicities pairs domain capacity radius first second bad
    let checkpoint := StagedHeterogeneousBatchOpening.snapshots heights tag first second
    let emission := StagedHeterogeneousBatchOpening.emission first.1 second.1
    SharedSequence.AnyBad (fun index native => index = selected ∧
      RepeatedLookupPCSAlgebra.Arithmetic mode basis shape active (pairValues (pairs second.1) selected).2 (pairValues (pairs second.1) selected).1
        (sourceTables domain capacity radius (LookupGroupedOpening.words enc dummy g checkpoint))
        (helperTables domain capacity radius (LookupGroupedOpening.words enc dummy g checkpoint) selected) native) last.1.1.results ∨
      SharedSequence.AnyBad (fun _ => RecordedHeterogeneousBatchOpening.Arithmetic enc dummy domain capacity radius
        (LookupGroupedOpening.build basis shape g (RepeatedLookupSelector.packets fallback) behavior) emission checkpoint last.1.1) last.1.2.results
  else False

variable [Fintype Digest] [Fintype K] [DecidableEq K] [SampleableType K]
  [Field L] [Algebra F L] [Fintype F] [Fintype L] [DecidableEq L]
  [∀ root, SampleableType ((Fin (2 ^ (layout g root).front) × Fin (d + padding)) → L)]

def pcsError (L : Type) [Field L] [Algebra F L] [Fintype L] [DecidableEq L]
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F) (radius : Root count repetitions → ℕ) : ENNReal :=
  ((StagedHeterogeneousBatchOpening.factors (List.finRange count) (List.finRange repetitions)).map
    (fun root => JointMatrixOpening.error (K := L) (m := g.m root) (b := d + padding)
      (queries := g.queries root) (domain root) (radius root))).sum

/-- A complete native run accepting outside all-pairs-pass costs one scalar
loss, the native per-root PCS sum, and one complete-run availability charge.
All local algebra, packet and authentication interfaces are discharged. -/
theorem bad_prefix_bound {active inactive : ℕ} [NeZero (d + padding)] [∀ root, NeZero (layout g root).m]
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
        ¬AllPass enc dummy basis shape logicalShape table multiplicities pairs domain capacity radius outcome.1 outcome.2.1 ∧
          outcome.2.2.1.2.accepted = true] ≤
      (error K mode (c + row) + pcsError (d := d) (padding := padding) (g := g) L domain radius) +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg)))
        (CheckpointCollision.loss unifSpec (fun cfg => Skeleton.perfect (heights cfg)))
        (StagedCommitmentPrefix.program
          (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange count))
          (StagedHeterogeneousBatchOpening.helperRequests tag (List.finRange repetitions)) sourceCommit helperCommit next)
        (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg))) := by
  dsimp only
  apply StagedCommitmentPrefix.event_bound enc dummy (fun cfg => Skeleton.perfect (heights cfg))
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

/-- Full native acceptance retains the all-pairs-pass probability explicitly.
It is not replaced by an unproved private-pair or Fiat–Shamir certificate. -/
theorem acceptance_bound {active inactive : ℕ} [NeZero (d + padding)] [∀ root, NeZero (layout g root).m]
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
    let experiment := StagedCommitmentPrefix.witness enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange count))
      (StagedHeterogeneousBatchOpening.helperRequests tag (List.finRange repetitions)) sourceCommit helperCommit next
      (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg)))
    Pr{let outcome ← experiment}[outcome.2.2.1.2.accepted = true] ≤
      Pr{let outcome ← experiment}[AllPass enc dummy basis shape logicalShape table multiplicities pairs domain capacity radius outcome.1 outcome.2.1] +
      ((error K mode (c + row) + pcsError (d := d) (padding := padding) (g := g) L domain radius) +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg)))
        (CheckpointCollision.loss unifSpec (fun cfg => Skeleton.perfect (heights cfg)))
        (StagedCommitmentPrefix.program
          (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange count))
          (StagedHeterogeneousBatchOpening.helperRequests tag (List.finRange repetitions)) sourceCommit helperCommit next)
        (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg)))) := by
  dsimp only
  have bounded := bad_prefix_bound analysisBasis enc dummy mode p small basis shape logicalShape fullShape table multiplicities pairs
    algebra domain enough capacity radius fallback behavior sourceCommit helperCommit distance
  dsimp only at bounded
  refine (prEvent_mono _ _ _ ?_).trans ((prEvent_or_le _ _ _).trans (add_le_add le_rfl bounded))
  intro outcome accepted
  by_cases pass : AllPass enc dummy basis shape logicalShape table multiplicities pairs domain capacity radius outcome.1 outcome.2.1
  · exact Or.inl pass
  · exact Or.inr ⟨pass, accepted⟩

end

end FormalProof4FHE.HasteBoots.StagedRepeatedLookup
