module
public import FormalProof4FHE.HasteBoots.AmbientAccumulator
@[expose] public section

/-! Accumulator soundness refers to original recorded owners, even when they
are selected after execution and predate other stages/helper commitments. -/
namespace FormalProof4FHE.HasteBoots.OwnedAmbientAccumulator
open OracleSpec OracleComp BinaryTree Matrix
open InteractiveAuthenticatedOpening
open AmbientAccumulator (Scheme Prefix RunResult tableCast)
noncomputable section
variable {F K Input Digest Cfg Response Memory CommitMemory : Type}
  [Field F] [DecidableEq F] [Fintype F] [DecidableEq Input] [DecidableEq Digest]
  {b c r front suffix m queries height : ℕ}

def originalTables (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor)) :=
  fun factor => tableCast s.layout
    (AmbientMatrixSource.source (front := front) s.encoding dummy heights s.domain capacity radius (s.tag factor) (owner factor))

def originalSources (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor)) :
    AccumulatorMatrixSoundness.Sources F b c r where
  input := originalTables heights s dummy capacity radius owner 0
  product := originalTables heights s dummy capacity radius owner 1
  difference := originalTables heights s dummy capacity radius owner 2
  output := originalTables heights s dummy capacity radius owner 3
  external := originalTables heights s dummy capacity radius owner 4
  duplicateA := originalTables heights s dummy capacity radius owner 5
  duplicateB := originalTables heights s dummy capacity radius owner 6
  initial := s.context.initial
  final := s.context.final
  start := s.context.start
  finish := s.context.finish

def OriginalRisk (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (outcome : Prefix heights (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) ×
      RunResult heights (F := F) (Input := Input) (Digest := Digest) (Response := Response) (Memory := Memory)
        (b := b) (c := c) (r := r) (front := front) (queries := queries) (height := height)) : Prop :=
  ∃ owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor),
    (∀ factor, (owner factor).root = outcome.1.1.1 factor ∧
      ⟨s.tag factor,owner factor⟩ ∈ outcome.2.2.checkpoints.checkpoints) ∧
    ¬AccumulatorEndpointSoundness.FullHolds (originalSources heights s dummy capacity radius owner) ∧
    outcome.2.1.1.accepted = true ∧ outcome.2.1.2.accepted = true

variable [SampleableType Digest] [SampleableType (Fin b → F)]
  [SampleableType (TestMatrix F (2^front) b)] [SampleableType (Fin queries → Fin (2^height))]
  [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
  [SampleableType ((Fin (2^front) × Fin b) → K)]

/-- Original owners and the stage's fresh snapshots agree outside the SAME
final exception. They incur no second availability/collision charge. -/
theorem original_safe_bound [NeZero m] [NeZero b] (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r front suffix m queries height)
    (geometry : ∀ factor, heights (s.tag factor) = height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m : Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (AmbientAccumulator.witness heights s dummy initial)}[
      OriginalRisk heights s dummy capacity radius outcome ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2] ≤
      ((((1+r)+c : ℕ) : ENNReal) * (((((2*b-1 : ℕ) : ENNReal)/Fintype.card F)^b))) +
        7 * JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius := by
  have bound := AmbientAccumulator.false_acceptance_safe_bound heights s geometry basis dummy enough capacity radius small initial audited
  apply le_trans (prEvent_mono_of_support (AmbientAccumulator.witness heights s dummy initial) _
    (fun outcome =>
      (¬AccumulatorEndpointSoundness.FullHolds (AmbientAccumulator.sources heights s dummy capacity radius outcome.1) ∧
        outcome.2.1.1.accepted = true ∧ outcome.2.1.2.accepted = true) ∧
      ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2) ?_) bound
  intro outcome supported event
  obtain ⟨⟨owner,recorded,falseOriginal,arithmetic,opened⟩,clear⟩ := event
  have audit := AmbientAccumulator.audited_witness heights s dummy initial audited outcome supported
  have sameTables : originalTables heights s dummy capacity radius owner =
      AmbientAccumulator.tables heights s dummy capacity radius outcome.1 := by
    funext factor
    rcases AmbientMatrixSource.source_eq_or_bad s.encoding dummy heights (s.tag factor) (geometry factor)
        s.domain capacity radius outcome.2.2 audit (owner factor)
        (AmbientDependentBatchOpening.snapshots heights s.tag outcome.1 factor) (recorded factor).2
        (AmbientAccumulator.fresh_recorded heights s dummy initial outcome supported factor) (recorded factor).1 with equal | bad
    · exact congrArg (tableCast s.layout) equal
    · exact False.elim (clear bad)
  have sameSources : originalSources heights s dummy capacity radius owner =
      AmbientAccumulator.sources heights s dummy capacity radius outcome.1 := by
    simp only [originalSources,AmbientAccumulator.sources,sameTables]
  refine ⟨⟨?_,arithmetic,opened⟩,clear⟩
  intro holds
  exact falseOriginal (sameSources.symm ▸ holds)

end
end FormalProof4FHE.HasteBoots.OwnedAmbientAccumulator
