module

public import FormalProof4FHE.HasteBoots.StagedLookupPrefixFacts

@[expose] public section

/-!
# Native lookup acceptance after an optional helper phase

Only an actual completed helper emission starts the native algebra and PCS.
Suspension records no invented root and executes no fallback verifier. The
arithmetic reduction and one availability charge refer to the entire real
source/middle/optional-continuation program, including all sampling work.
-/

open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open scoped Classical
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.HeterogeneousBatchOpening
open FormalProof4FHE.HasteBoots.LookupOpeningFamily
open FormalProof4FHE.HasteBoots.RepeatedLookupPCSAlgebra
open FormalProof4FHE.HasteBoots.StagedRepeatedLookup

namespace FormalProof4FHE.HasteBoots.OptionalStagedLookup

noncomputable section

variable {F K L Cfg Input Digest Response Memory SourceMemory HelperMemory Second : Type}
  [Field F] [Field K] [Algebra F K] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {d padding c row count repetitions size : ℕ} {heights : Cfg → ℕ} {tag : Root count repetitions → Cfg}
  {g : Geometry c row count repetitions}
  [SampleableType Digest] [SampleableType (Fin 1 → K)] [SampleableType (Fin (c + row) → K)]
  [∀ root, SampleableType (TestMatrix F (2 ^ (layout g root).front) (d + padding))]
  [∀ root, SampleableType (Fin (layout g root).queries → Fin (2 ^ heights (tag root)))]

def continuation (enc : MerkleOracle.Encoding Input Digest (List F))
    (mode : Mode) (p : ℕ) [CharP K p] (small : degree mode + 1 ≤ p)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (active : ℕ) (enough : active ≤ 2 ^ (c + row))
    (table : Fin size → Fin count → F)
    (multiplicities : SourceEmission count Digest SourceMemory → Fin size → F)
    (pairs : HelperEmission repetitions Digest HelperMemory → Fin repetitions → Pair K)
    (algebra : Second → Emission count repetitions Digest SourceMemory HelperMemory → ScheduleData F K Memory Cfg Input Digest (d + padding) count (c + row) repetitions mode)
    (completed : Second → Option (HelperEmission repetitions Digest HelperMemory))
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (fallback : PreparedLookupPair.Packet F K (d + padding) count (c + row))
    (behavior : Second → Emission count repetitions Digest SourceMemory HelperMemory →
      RepeatedLookupPCS.Selection (F := F) (K := K) (Memory := Memory) (d := d) (padding := padding) (c := c) (row := row) (count := count) (repetitions := repetitions) →
      (root : Root count repetitions) → Protocol F Input Digest Cfg Response Memory (d + padding) heights tag (layout g) root)
    (first : SourceEmission count Digest SourceMemory) (second : Second) :
    OracleComp (SharedSequence.Shared Cfg Input Digest)
      (Option (RepeatedLookupPCS.Result (F := F) (K := K) (Digest := Digest) (Response := Response) (Memory := Memory)
        (d := d) (padding := padding) (c := c) (row := row) (count := count) (repetitions := repetitions)
        (heights := heights) (tag := tag) (g := g))) :=
  match completed second with
  | none => pure none
  | some helper => some <$> StagedRepeatedLookup.continuation enc mode p small basis shape active enough table multiplicities pairs
      (algebra second) domain fallback (behavior second) first helper

omit [DecidableEq Input] [SampleableType Digest] in
/-- A suspended helper view starts no native algebra or PCS query. -/
theorem continuation_none (enc : MerkleOracle.Encoding Input Digest (List F))
    (mode : Mode) (p : ℕ) [CharP K p] (small : degree mode + 1 ≤ p)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (active : ℕ) (enough : active ≤ 2 ^ (c + row))
    (table : Fin size → Fin count → F)
    (multiplicities : SourceEmission count Digest SourceMemory → Fin size → F)
    (pairs : HelperEmission repetitions Digest HelperMemory → Fin repetitions → Pair K)
    (algebra : Second → Emission count repetitions Digest SourceMemory HelperMemory → ScheduleData F K Memory Cfg Input Digest (d + padding) count (c + row) repetitions mode)
    (completed : Second → Option (HelperEmission repetitions Digest HelperMemory))
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (fallback : PreparedLookupPair.Packet F K (d + padding) count (c + row))
    (behavior : Second → Emission count repetitions Digest SourceMemory HelperMemory →
      RepeatedLookupPCS.Selection (F := F) (K := K) (Memory := Memory) (d := d) (padding := padding) (c := c) (row := row) (count := count) (repetitions := repetitions) →
      (root : Root count repetitions) → Protocol F Input Digest Cfg Response Memory (d + padding) heights tag (layout g) root)
    (first : SourceEmission count Digest SourceMemory) (second : Second)
    (suspended : completed second = none) :
    continuation enc mode p small basis shape active enough table multiplicities pairs algebra completed domain fallback behavior first second = pure none := by
  simp [continuation, suspended]

omit [DecidableEq Input] [SampleableType Digest] in
/-- A completed helper view runs exactly the original native continuation
with that helper, retaining the actual raw-metadata-dependent behavior. -/
theorem continuation_some (enc : MerkleOracle.Encoding Input Digest (List F))
    (mode : Mode) (p : ℕ) [CharP K p] (small : degree mode + 1 ≤ p)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (active : ℕ) (enough : active ≤ 2 ^ (c + row))
    (table : Fin size → Fin count → F)
    (multiplicities : SourceEmission count Digest SourceMemory → Fin size → F)
    (pairs : HelperEmission repetitions Digest HelperMemory → Fin repetitions → Pair K)
    (algebra : Second → Emission count repetitions Digest SourceMemory HelperMemory → ScheduleData F K Memory Cfg Input Digest (d + padding) count (c + row) repetitions mode)
    (completed : Second → Option (HelperEmission repetitions Digest HelperMemory))
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (fallback : PreparedLookupPair.Packet F K (d + padding) count (c + row))
    (behavior : Second → Emission count repetitions Digest SourceMemory HelperMemory →
      RepeatedLookupPCS.Selection (F := F) (K := K) (Memory := Memory) (d := d) (padding := padding) (c := c) (row := row) (count := count) (repetitions := repetitions) →
      (root : Root count repetitions) → Protocol F Input Digest Cfg Response Memory (d + padding) heights tag (layout g) root)
    (first : SourceEmission count Digest SourceMemory) (second : Second)
    (helper : HelperEmission repetitions Digest HelperMemory) (returned : completed second = some helper) :
    continuation enc mode p small basis shape active enough table multiplicities pairs algebra completed domain fallback behavior first second =
      some <$> StagedRepeatedLookup.continuation enc mode p small basis shape active enough table multiplicities pairs
        (algebra second) domain fallback (behavior second) first helper := by
  simp [continuation, returned]

def AllPass {active inactive : ℕ}
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c) (logicalShape : active + inactive = 2 ^ (c + row))
    (table : Fin size → Fin count → F)
    (multiplicities : SourceEmission count Digest SourceMemory → Fin size → F)
    (pairs : HelperEmission repetitions Digest HelperMemory → Fin repetitions → Pair K)
    (completed : Second → Option (HelperEmission repetitions Digest HelperMemory))
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * (d + padding)) (radius : Root count repetitions → ℕ)
    (first : SourceEmission count Digest SourceMemory × CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (second : Second × CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    : Prop := (completed second.1).elim False (fun helper =>
      StagedRepeatedLookup.AllPass enc dummy basis shape logicalShape table multiplicities pairs domain capacity radius first (helper, second.2))

def ArithmeticEvent {active inactive : ℕ}
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (mode : Mode)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c) (logicalShape : active + inactive = 2 ^ (c + row))
    (table : Fin size → Fin count → F)
    (multiplicities : SourceEmission count Digest SourceMemory → Fin size → F)
    (pairs : HelperEmission repetitions Digest HelperMemory → Fin repetitions → Pair K)
    (completed : Second → Option (HelperEmission repetitions Digest HelperMemory))
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * (d + padding)) (radius : Root count repetitions → ℕ)
    (fallback : PreparedLookupPair.Packet F K (d + padding) count (c + row))
    (behavior : Second → Emission count repetitions Digest SourceMemory HelperMemory →
      RepeatedLookupPCS.Selection (F := F) (K := K) (Memory := Memory) (d := d) (padding := padding) (c := c) (row := row) (count := count) (repetitions := repetitions) →
      (root : Root count repetitions) → Protocol F Input Digest Cfg Response Memory (d + padding) heights tag (layout g) root)
    (first : SourceEmission count Digest SourceMemory × CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (second : Second × CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (last : Option (RepeatedLookupPCS.Result (F := F) (K := K) (Digest := Digest) (Response := Response) (Memory := Memory) (d := d) (padding := padding) (c := c) (row := row)
      (count := count) (repetitions := repetitions) (heights := heights) (tag := tag) (g := g)) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    : Prop := (completed second.1).elim False (fun helper => last.1.elim False (fun native =>
      StagedRepeatedLookup.ArithmeticEvent enc dummy mode basis shape logicalShape table multiplicities pairs domain capacity radius fallback
        (behavior second.1) first (helper, second.2) (native, last.2)))

def helperRequests (completed : Second → Option (HelperEmission repetitions Digest HelperMemory))
    (tag : Root count repetitions → Cfg) (first : SourceEmission count Digest SourceMemory) (second : Second) : List (Cfg × Digest) :=
  (completed second).elim [] (StagedHeterogeneousBatchOpening.helperRequests tag (List.finRange repetitions) first)

variable [Fintype Digest] [Fintype K] [DecidableEq K] [SampleableType K]
  [Field L] [Algebra F L] [Fintype F] [Fintype L] [DecidableEq L]
  [∀ root, SampleableType ((Fin (2 ^ (layout g root).front) × Fin (d + padding)) → L)]

/-- Native acceptance outside all-pass on the actual optional helper execution
has its derived scalar/PCS bound and one complete-run availability charge. -/
theorem bad_prefix_bound {active inactive : ℕ} [NeZero (d + padding)] [∀ root, NeZero (layout g root).m]
    (analysisBasis : Module.Basis (Fin (d + padding)) F L)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (mode : Mode) (p : ℕ) [CharP K p] (small : degree mode + 1 ≤ p)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (logicalShape : active + inactive = 2 ^ (c + row)) (fullShape : mode = .full → active = 2 ^ (c + row))
    (table : Fin size → Fin count → F)
    (multiplicities : SourceEmission count Digest SourceMemory → Fin size → F)
    (pairs : HelperEmission repetitions Digest HelperMemory → Fin repetitions → Pair K)
    (algebra : Second → Emission count repetitions Digest SourceMemory HelperMemory → ScheduleData F K Memory Cfg Input Digest (d + padding) count (c + row) repetitions mode)
    (completed : Second → Option (HelperEmission repetitions Digest HelperMemory))
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (enough : ∀ root, g.m root ≤ Fintype.card (Fin (2 ^ heights (tag root))))
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * (d + padding)) (radius : Root count repetitions → ℕ)
    (fallback : PreparedLookupPair.Packet F K (d + padding) count (c + row))
    (behavior : Second → Emission count repetitions Digest SourceMemory HelperMemory →
      RepeatedLookupPCS.Selection (F := F) (K := K) (Memory := Memory) (d := d) (padding := padding) (c := c) (row := row) (count := count) (repetitions := repetitions) →
      (root : Root count repetitions) → Protocol F Input Digest Cfg Response Memory (d + padding) heights tag (layout g) root)
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) (SourceEmission count Digest SourceMemory))
    (middle : SourceEmission count Digest SourceMemory → OracleComp (SharedSequence.Shared Cfg Input Digest) Second)
    (distance : ∀ root, (radius root : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := L) (domain root)) (g.m root) : Set (Fin (2 ^ heights (tag root)) → L)) : ℚ≥0) / 3) :
    let next := continuation enc mode p small basis shape active (by omega) table multiplicities pairs algebra completed domain fallback behavior
    Pr{let outcome ← (StagedCommitmentPrefix.witness enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange count))
      (helperRequests completed tag) sourceCommit middle next (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg))))}[
        ¬AllPass enc dummy basis shape logicalShape table multiplicities pairs completed domain capacity radius outcome.1 outcome.2.1 ∧
          outcome.2.2.1.elim False (fun native => native.2.accepted = true)] ≤
      (error K mode (c + row) + pcsError (d := d) (padding := padding) (g := g) L domain radius) +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg)))
        (CheckpointCollision.loss unifSpec (fun cfg => Skeleton.perfect (heights cfg)))
        (StagedCommitmentPrefix.program
          (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange count))
          (helperRequests completed tag) sourceCommit middle next)
        (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg))) := by
  dsimp only
  apply StagedCommitmentPrefix.event_bound enc dummy (fun cfg => Skeleton.perfect (heights cfg))
    (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange count)) (helperRequests completed tag) sourceCommit middle
    (continuation enc mode p small basis shape active (by omega) table multiplicities pairs algebra completed domain fallback behavior)
    (fun first second last => ¬AllPass enc dummy basis shape logicalShape table multiplicities pairs completed domain capacity radius first second ∧
      last.1.elim False (fun native => native.2.accepted = true))
    (ArithmeticEvent enc dummy mode basis shape logicalShape table multiplicities pairs completed domain capacity radius fallback behavior) _
  · intro first second
    cases tagCompleted : completed second.1 with
    | none =>
      simp [continuation, tagCompleted, ArithmeticEvent, simulateQ_pure, StateT.run_pure, prEvent_norm]
    | some helper =>
      have bounded := StagedLookupPrefixFacts.arithmetic_bound analysisBasis enc dummy mode p small basis shape logicalShape fullShape
        table multiplicities pairs (algebra second.1) domain enough capacity radius fallback (behavior second.1) first (helper, second.2)
        (RecordRoots.state _ (StagedHeterogeneousBatchOpening.helperRequests tag (List.finRange repetitions) first.1 helper) second.2) distance
      simpa only [continuation, tagCompleted, simulateQ_map, StateT.run_map, prEvent_map, ArithmeticEvent,
        Option.elim_some, helperRequests] using bounded
  · intro first _ second secondSupported last supported accepted
    obtain ⟨bad, passed⟩ := accepted
    cases tagCompleted : completed second.1 with
    | none =>
      simp only [continuation, tagCompleted, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst last
      simp at passed
    | some helper =>
      simp only [continuation, tagCompleted, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at supported
      obtain ⟨native, nativeSupported, equal⟩ := supported
      subst last
      have nativeBad : ¬StagedRepeatedLookup.AllPass enc dummy basis shape logicalShape table multiplicities pairs domain capacity radius
          first (helper, second.2) := by
        simpa only [AllPass, tagCompleted, Option.elim_some] using bad
      have recorded := StagedLookupPrefixFacts.snapshots_recorded enc dummy heights tag middle first second secondSupported helper
      have recorded' : ∀ root, ⟨tag root, StagedHeterogeneousBatchOpening.snapshots heights tag first (helper, second.2) root⟩ ∈
          (RecordRoots.state _ (helperRequests completed tag first.1 second.1) second.2).checkpoints.checkpoints := by
        simpa only [helperRequests, tagCompleted, Option.elim_some] using recorded
      have reduction := StagedLookupPrefixFacts.reduce_acceptance enc dummy mode p small basis shape logicalShape fullShape
        table multiplicities pairs (algebra second.1) domain capacity radius fallback (behavior second.1) first (helper, second.2)
        (RecordRoots.state _ (helperRequests completed tag first.1 second.1) second.2) recorded' native nativeSupported nativeBad passed
      simpa only [ArithmeticEvent, tagCompleted, Option.elim_some] using reduction

end

end FormalProof4FHE.HasteBoots.OptionalStagedLookup
