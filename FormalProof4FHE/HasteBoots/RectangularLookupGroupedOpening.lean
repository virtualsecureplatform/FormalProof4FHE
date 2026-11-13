module

public import FormalProof4FHE.HasteBoots.RectangularPaddedLookupOpeningFamily
public import FormalProof4FHE.HasteBoots.RectangularStagedException

@[expose] public section

/-!
# Accepted original lookup-opening failures have the actual staged PCS bound

The behavior factory's queries and values are overwritten by the exact lookup
family. Source words freeze before pair/helper work, helpers after it. Each source
has one claim; each helper has two ordered claims at the common point. This
bounds job-local original opening failures OR the common history exception,
with one arithmetic loss per original root and one whole-run hash charge. It does not yet
compose the lookup algebra/pair/repetition acceptance bounds or Fiat–Shamir.
-/

open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening
open FormalProof4FHE.HasteBoots.PaddedMixedWidthLookupOpeningFamily

namespace FormalProof4FHE.HasteBoots.RectangularLookupGroupedOpening

noncomputable section

variable {F K Cfg Input Digest Response Memory SourceMemory HelperMemory QueryData : Type}
  [Field F] [Field K] [Algebra F K] [DecidableEq F] [DecidableEq Digest]
  {d padding helperPadding c row count repetitions : ℕ} {heights : Cfg → ℕ} {tag : Root count repetitions → Cfg}
  {g : Geometry c row count repetitions} {symbolWidth : Root count repetitions → ℕ}

abbrev CommitMemory (count repetitions : ℕ) (Digest SourceMemory HelperMemory : Type) :=
  RectangularStagedOpening.CommitMemory (Fin count) (Fin repetitions) Digest SourceMemory HelperMemory

def build (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (g : Geometry c row count repetitions)
    (packets : QueryData → Packet F K (d + padding) count (c + row) repetitions)
    (behavior : ((Root count repetitions → Digest) × CommitMemory count repetitions Digest SourceMemory HelperMemory) →
      QueryData → (root : Root count repetitions) → Protocol F Input Digest Cfg Response Memory (packedWidth (d + padding) (d + helperPadding)) symbolWidth heights tag (layout g) root)
    (emission : (Root count repetitions → Digest) × CommitMemory count repetitions Digest SourceMemory HelperMemory)
    (query : QueryData) (root : Root count repetitions) :=
  RectangularPaddedLookupOpeningFamily.bind (g := g) (heights := heights) (tag := tag) (symbolWidth := symbolWidth) basis shape (packets query) root (behavior emission query root)

/-- Interpret each root in its actual original prefix log, with its actual
layout. These are analysis words, not operational verifier inputs. -/
def words (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (g : Geometry c row count repetitions)
    (checkpoint : RectangularRecordedOpening.Snapshots Input Digest heights tag) :
    ∀ root, Fin (2 ^ heights (tag root)) → (Fin (2 ^ g.front root) × Fin (packedWidth (d + padding) (d + helperPadding) root)) → Fin (symbolWidth root) → F :=
  fun root => AmbientRectangularSource.word enc dummy heights (tag root) (checkpoint root)

/-- Native final accepted wrong values are exactly final acceptance together
with a sum-helper, identity-helper or original-source failure of some pair.
No security certificate and no probability union over pair queries is needed. -/
theorem wrong_iff {columns : Fin repetitions → ℕ}
    (slots : (job : Fin repetitions) → Fin (columns job) → Fin count)
    (coverage : ∀ source, ∃ job column, slots job column = source) (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (packets : QueryData → Packet F K (d + padding) count (c + row) repetitions)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * symbolWidth root) (radius : Root count repetitions → ℕ)
    (behavior : ((Root count repetitions → Digest) × CommitMemory count repetitions Digest SourceMemory HelperMemory) →
      QueryData → (root : Root count repetitions) → Protocol F Input Digest Cfg Response Memory (packedWidth (d + padding) (d + helperPadding)) symbolWidth heights tag (layout g) root)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (emission : (Root count repetitions → Digest) × CommitMemory count repetitions Digest SourceMemory HelperMemory)
    (checkpoint : RectangularRecordedOpening.Snapshots Input Digest heights tag)
    (last : (QueryData × ShortCircuitSequence.Outcome (Root count repetitions)
      (Sigma (Data F Digest Response (packedWidth (d + padding) (d + helperPadding)) symbolWidth heights tag (layout g))) Memory) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg))) :
    RectangularRecordedOpening.Wrong enc dummy domain capacity radius (build basis shape g packets behavior) emission checkpoint last ↔
      last.1.2.accepted = true ∧ ∃ pair,
        PaddedMixedWidthLookupOpeningFamily.WrongOpenings basis shape
          (fun column => RectangularPaddedLookupOpeningFamily.sourceTables (d := d) (padding := padding) (helperPadding := helperPadding) domain capacity radius (words (d := d) (padding := padding) (helperPadding := helperPadding) enc dummy g checkpoint) (slots pair column))
          (RectangularPaddedLookupOpeningFamily.helperTables (d := d) (padding := padding) (helperPadding := helperPadding) domain capacity radius (words (d := d) (padding := padding) (helperPadding := helperPadding) enc dummy g checkpoint) pair)
          (pairPacket slots (packets last.1.1) pair).sumClaim (pairPacket slots (packets last.1.1) pair).zeroClaim
          (pairPacket slots (packets last.1.1) pair).values.sources (pairPacket slots (packets last.1.1) pair).values.helper := by
  change (last.1.2.accepted = true ∧ ∃ root claim,
    RectangularPaddedLookupOpeningFamily.WrongValue (d := d) (padding := padding) (helperPadding := helperPadding) basis shape (packets last.1.1) domain capacity radius (words (d := d) (padding := padding) (helperPadding := helperPadding) enc dummy g checkpoint) root claim) ↔ _
  rw [← RectangularPaddedLookupOpeningFamily.any_job_wrong_iff (d := d) (padding := padding) (helperPadding := helperPadding) basis shape (packets last.1.1) slots coverage domain capacity radius (words (d := d) (padding := padding) (helperPadding := helperPadding) enc dummy g checkpoint)]

variable [DecidableEq Input] [SampleableType Digest] [Fintype Digest]
    [Fintype F]

  [∀ root, SampleableType (TestMatrix F (2 ^ (layout g root).front) (packedWidth (d + padding) (d + helperPadding) root))]
  [∀ root, SampleableType (Fin (layout g root).queries → Fin (2 ^ heights (tag root)))]
  [∀ root, SampleableType ((Fin (2 ^ (layout g root).front) × Fin (packedWidth (d + padding) (d + helperPadding) root)) → F)]

/-- Exact native grouped lookup-opening bound. `K` is the lookup extension;
The independent base-field test rows use the rectangular kernel rate. -/
theorem soundness_from_empty {columns : Fin repetitions → ℕ}
    (slots : (job : Fin repetitions) → Fin (columns job) → Fin count)
    (coverage : ∀ source, ∃ job column, slots job column = source) [∀ root : Root count repetitions, NeZero (symbolWidth root)] [∀ root, NeZero (layout g root).m]
    (lookupBasis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (sources : List (Fin count)) (helpers : List (Fin repetitions))
    (sourceComplete : ∀ source, source ∈ sources) (helperComplete : ∀ helper, helper ∈ helpers)
    (packets : QueryData → Packet F K (d + padding) count (c + row) repetitions)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (enough : ∀ root, g.m root ≤ Fintype.card (Fin (2 ^ heights (tag root))))
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * symbolWidth root) (radius : Root count repetitions → ℕ)
    (behavior : ((Root count repetitions → Digest) × CommitMemory count repetitions Digest SourceMemory HelperMemory) →
      QueryData → (root : Root count repetitions) → Protocol F Input Digest Cfg Response Memory (packedWidth (d + padding) (d + helperPadding)) symbolWidth heights tag (layout g) root)
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest)
      (RectangularStagedOpening.SourceEmission (Fin count) Digest SourceMemory))
    (helperCommit : RectangularStagedOpening.SourceEmission (Fin count) Digest SourceMemory →
      OracleComp (SharedSequence.Shared Cfg Input Digest)
        (RectangularStagedOpening.HelperEmission (Fin repetitions) Digest HelperMemory))
    (selectQuery : ((Root count repetitions → Digest) × CommitMemory count repetitions Digest SourceMemory HelperMemory) →
      OracleComp (SharedSequence.Shared Cfg Input Digest) QueryData)
    (enabled : ((Root count repetitions → Digest) × CommitMemory count repetitions Digest SourceMemory HelperMemory) → QueryData → Bool)
    (start : ((Root count repetitions → Digest) × CommitMemory count repetitions Digest SourceMemory HelperMemory) → QueryData → Memory)
    (smallLarge : ∀ root, radius root < Fintype.card F)
    (small : ∀ root, 3*radius root < Code.minDist (BlockCode.code (domain root) (g.m root) (symbolWidth root) :
      Set (Fin (2^heights (tag root)) → Fin (symbolWidth root) → F))) :
    let next := RectangularStagedOpening.continuation (width := packedWidth (d + padding) (d + helperPadding)) (symbolWidth := symbolWidth) (heights := heights) (tag := tag) (layout := layout g) enc domain
      (build lookupBasis shape g packets behavior) selectQuery enabled start sources helpers
    Pr{let outcome ← (StagedCommitmentPrefix.witness enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (RectangularStagedOpening.sourceRequests tag sources) (RectangularStagedOpening.helperRequests tag helpers)
      sourceCommit helperCommit next (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg))))}[
        (outcome.2.2.1.2.accepted = true ∧ ∃ pair,
          PaddedMixedWidthLookupOpeningFamily.WrongOpenings lookupBasis shape
            (fun column => RectangularPaddedLookupOpeningFamily.sourceTables (d := d) (padding := padding) (helperPadding := helperPadding) domain capacity radius (words (d := d) (padding := padding) (helperPadding := helperPadding) enc dummy g (RectangularStagedOpening.snapshots heights tag outcome.1 outcome.2.1)) (slots pair column))
            (RectangularPaddedLookupOpeningFamily.helperTables (d := d) (padding := padding) (helperPadding := helperPadding) domain capacity radius (words (d := d) (padding := padding) (helperPadding := helperPadding) enc dummy g (RectangularStagedOpening.snapshots heights tag outcome.1 outcome.2.1)) pair)
            (pairPacket slots (packets outcome.2.2.1.1) pair).sumClaim (pairPacket slots (packets outcome.2.2.1.1) pair).zeroClaim
            (pairPacket slots (packets outcome.2.2.1.1) pair).values.sources (pairPacket slots (packets outcome.2.2.1.1) pair).values.helper) ∨
        CheckpointCollision.Bad (fun cfg => Skeleton.perfect (heights cfg)) outcome.2.2.2] ≤
      ((RectangularStagedOpening.factors sources helpers).map (fun root =>
        RectangularVariableWidthOpening.error (domain root) (g.m root) (symbolWidth root) (packedWidth (d + padding) (d + helperPadding) root) (g.queries root) (radius root))).sum +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg)))
        (CheckpointCollision.loss unifSpec (fun cfg => Skeleton.perfect (heights cfg)))
        (StagedCommitmentPrefix.program (RectangularStagedOpening.sourceRequests tag sources)
          (RectangularStagedOpening.helperRequests tag helpers) sourceCommit helperCommit next)
        (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg))) := by
  dsimp only
  have bound := RectangularStagedException.soundness_from_empty (width := packedWidth (d + padding) (d + helperPadding)) (symbolWidth := symbolWidth) (heights := heights) (tag := tag) (layout := layout g) enc dummy sources helpers sourceComplete helperComplete
    domain enough capacity radius (build lookupBasis shape g packets behavior) sourceCommit helperCommit selectQuery enabled start smallLarge small
  dsimp only at bound
  refine (prEvent_mono _ _ _ ?_).trans bound
  intro outcome accepted
  rcases accepted with wrong | bad
  · left
    exact (wrong_iff slots coverage lookupBasis shape packets domain capacity radius behavior enc dummy
      (RectangularStagedOpening.emission outcome.1.1 outcome.2.1.1)
      (RectangularStagedOpening.snapshots heights tag outcome.1 outcome.2.1) outcome.2.2).mpr wrong
  · exact Or.inr bad

end

end FormalProof4FHE.HasteBoots.RectangularLookupGroupedOpening
