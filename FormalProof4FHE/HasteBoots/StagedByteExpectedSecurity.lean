module

public import FormalProof4FHE.HasteBoots.StagedByteLookupUnboundedSecurity
public import FormalProof4FHE.HasteBoots.OptionalStagedLookup
public import FormalProof4FHE.HasteBoots.StagedByteChargedLimit

@[expose] public section

/-!
# Native staged lookup false acceptance against its actual expected account

The original false-acceptance event uses the original frozen-source witness.
An exact query-program factorization replaces the whole-prefix availability
charge supremum by the mean account of the normalized completed staged
execution. Suspension behavior is derived from the real optional helper and
native continuation. Computational hash/byte work and production FS remain
separate refinements; no PCS/FS/work certificate or query cap is assumed.
-/

open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.HeterogeneousBatchOpening
open FormalProof4FHE.HasteBoots.LookupOpeningFamily
open FormalProof4FHE.HasteBoots.RepeatedLookupPCSAlgebra
open FormalProof4FHE.HasteBoots.StagedRepeatedLookup

namespace FormalProof4FHE.HasteBoots.StagedByteExpectedSecurity

noncomputable section

variable {F K L Cfg Input Digest Response Memory SourceMemory HelperMemory Result : Type}
  [Field F] [Field K] [Algebra F K] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {d padding c row count repetitions size : ℕ} {heights : Cfg → ℕ} {tag : Root count repetitions → Cfg}
  {g : Geometry c row count repetitions}
  [SampleableType Digest]

variable [Fintype K] [DecidableEq K] [SampleableType K]

variable {q sampleDegree : ℕ} [Module (ZMod q) K] [NeZero q]

variable [SampleableType (Fin 1 → K)] [SampleableType (Fin (c + row) → K)]
  [∀ root, SampleableType (TestMatrix F (2 ^ (layout g root).front) (d + padding))]
  [∀ root, SampleableType (Fin (layout g root).queries → Fin (2 ^ heights (tag root)))]

variable [Fintype Digest] [Field L] [Algebra F L] [Fintype F] [Fintype L] [DecidableEq L]
  [∀ root, SampleableType ((Fin (2 ^ (layout g root).front) × Fin (d + padding)) → L)]

/-- Unbounded native lookup false acceptance is bounded by the proved
lookup/algebra/PCS losses plus the actual full staged mean availability account. -/
theorem false_acceptance_bound {active inactive : ℕ} [NeZero (d + padding)] [∀ root, NeZero (layout g root).m]
    (valid : 1 < q) (sampleBasis : Module.Basis (Fin sampleDegree) (ZMod q) K)
    (analysisBasis : Module.Basis (Fin (d + padding)) F L)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (mode : Mode) (p : ℕ) [CharP K p] (small : degree mode + 1 ≤ p)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (logicalShape : active + inactive = 2 ^ (c + row)) (fullShape : mode = .full → active = 2 ^ (c + row))
    (table : Fin size → Fin count → F)
    (multiplicities : SourceEmission count Digest SourceMemory → Fin size → F)
    (algebra : ByteLookupPairMiddle.Emission q sampleDegree K Digest HelperMemory repetitions → Emission count repetitions Digest SourceMemory (LookupPairVectorMiddle.Memory K HelperMemory repetitions) → ScheduleData F K Memory Cfg Input Digest (d + padding) count (c + row) repetitions mode)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (enough : ∀ root, g.m root ≤ Fintype.card (Fin (2 ^ heights (tag root))))
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * (d + padding)) (radius : Root count repetitions → ℕ)
    (fallback : PreparedLookupPair.Packet F K (d + padding) count (c + row))
    (behavior : ByteLookupPairMiddle.Emission q sampleDegree K Digest HelperMemory repetitions → Emission count repetitions Digest SourceMemory (LookupPairVectorMiddle.Memory K HelperMemory repetitions) →
      RepeatedLookupPCS.Selection (F := F) (K := K) (Memory := Memory) (d := d) (padding := padding) (c := c) (row := row) (count := count) (repetitions := repetitions) →
      (root : Root count repetitions) → Protocol F Input Digest Cfg Response Memory (d + padding) heights tag (layout g) root)
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) (SourceEmission count Digest SourceMemory))
    (pairEnough : size + 1 < Fintype.card K) (lookupSmall : active < p)
    (build : SourceEmission count Digest SourceMemory → ByteLookupPairTyped.Raw q sampleDegree K repetitions → (Fin repetitions → Pair K) →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (HelperEmission repetitions Digest HelperMemory))
    (distance : ∀ root, (radius root : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := L) (domain root)) (g.m root) : Set (Fin (2 ^ heights (tag root)) → L)) : ℚ≥0) / 3) :
    let next := OptionalStagedLookup.continuation enc mode p small basis shape active (by omega) table multiplicities LookupPairVectorMiddle.pairs algebra ByteLookupPairMiddle.completed domain fallback behavior
    let fullLaw := StagedByteLookupLimit.measure sampleBasis table enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange count))
      (OptionalStagedLookup.helperRequests ByteLookupPairMiddle.completed tag) sourceCommit build next
      (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg)))
    let accountLaw := StagedByteChargedLimit.measure sampleBasis table enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange count))
      (OptionalStagedLookup.helperRequests ByteLookupPairMiddle.completed tag) sourceCommit build next
      (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg)))
    fullLaw {outcome |
      (∃ i, ∀ j, FrozenLookupSources.tuples enc dummy shape logicalShape domain capacity radius outcome.1 i ≠ table j) ∧
      outcome.2.2.1.elim False (fun native => native.2.accepted = true)} ≤
      TupleLookupPair.error (Fintype.card K) count active size ^ repetitions +
      ((error K mode (c + row) + pcsError (d := d) (padding := padding) (g := g) L domain radius) +
      (∫⁻ outcome, outcome.2.2 ∂accountLaw)) := by
  dsimp only
  have requests_none (first : SourceEmission count Digest SourceMemory)
      (observed : ByteLookupPairTyped.Sample q sampleDegree K repetitions) (suspended : observed.values = none) :
      OptionalStagedLookup.helperRequests (ByteLookupPairMiddle.completed (HelperMemory := HelperMemory)) tag first (observed, none) = [] := by
    simp only [OptionalStagedLookup.helperRequests, ByteLookupPairMiddle.completed, suspended]
    rfl
  have next_none (first : SourceEmission count Digest SourceMemory)
      (observed : ByteLookupPairTyped.Sample q sampleDegree K repetitions) (suspended : observed.values = none) :
      OptionalStagedLookup.continuation enc mode p small basis shape active (by omega) table multiplicities
        LookupPairVectorMiddle.pairs algebra ByteLookupPairMiddle.completed domain fallback behavior first (observed, none) = pure none := by
    simp only [OptionalStagedLookup.continuation, ByteLookupPairMiddle.completed, suspended]
  have mean := StagedByteChargedLimit.expected sampleBasis table enc dummy (fun cfg => Skeleton.perfect (heights cfg))
    (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange count))
    (OptionalStagedLookup.helperRequests ByteLookupPairMiddle.completed tag) sourceCommit build
    (OptionalStagedLookup.continuation enc mode p small basis shape active (by omega) table multiplicities
      LookupPairVectorMiddle.pairs algebra ByteLookupPairMiddle.completed domain fallback behavior)
    (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg))) valid pairEnough requests_none next_none
  have bounded := StagedByteLookupUnboundedSecurity.false_acceptance_bound valid sampleBasis analysisBasis enc dummy mode p small
    basis shape logicalShape fullShape table multiplicities algebra domain enough capacity radius fallback behavior sourceCommit
    pairEnough lookupSmall build distance
  dsimp only at bounded mean
  rw [← mean] at bounded
  exact bounded

end

end FormalProof4FHE.HasteBoots.StagedByteExpectedSecurity
