module
public import FormalProof4FHE.HasteBoots.OwnedNTTSoundness
@[expose] public section

/-! The recorded-owner NTT bound for the concrete negacyclic butterfly map,
expressed as an incorrect coefficient-domain transform at an original row. -/
namespace FormalProof4FHE.HasteBoots.OwnedNTTBinding
open OracleSpec OracleComp BinaryTree Matrix
open InteractiveAuthenticatedOpening
noncomputable section
variable {q log b c r k front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Digest Cfg Response Memory CommitMemory : Type} [DecidableEq Digest]

def WrongTransformRisk (length : 2^c*b = 2^log) (psi : ZMod q)
    (s : AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (outcome : AuthenticatedNTT.Prefix (Digest := Digest) (CommitMemory := CommitMemory)
        (Input := Input) (Cfg := Cfg) (height := height) ×
      AuthenticatedNTT.RunResult (F := ZMod q) (Memory := Memory) (Response := Response) (Input := Input)
        (Digest := Digest) (Cfg := Cfg) (b := b) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height)) : Prop :=
  ∃ owner : ∀ side, RecordedSourceCoherence.Snapshot Input Digest Cfg height (s.tag side),
    (∀ side, (owner side).root = outcome.1.1.1 side ∧ ⟨s.tag side,owner side⟩ ∈ outcome.2.2.checkpoints.checkpoints) ∧
    (∃ row, BlindRotationNTT.transform log psi
      (PackedNTTBinding.row length (OwnedNTTSoundness.originalSources s dummy capacity radius owner false) row) ≠
      PackedNTTBinding.row length (OwnedNTTSoundness.originalSources s dummy capacity radius owner true) row) ∧
    AuthenticatedNTT.accepted outcome.2.1 = true

/-- The fixed butterfly map, rather than a prover/factory-selected transform,
is used by the actual program. All decoded source rows retain their order. -/
theorem original_risk_iff (length : 2^c*b = 2^log) (psi : ZMod q)
    (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (s : AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (outcome : AuthenticatedNTT.Prefix (Digest := Digest) (CommitMemory := CommitMemory)
        (Input := Input) (Cfg := Cfg) (height := height) ×
      AuthenticatedNTT.RunResult (F := ZMod q) (Memory := Memory) (Response := Response) (Input := Input)
        (Digest := Digest) (Cfg := Cfg) (b := b) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height)) :
    OwnedNTTSoundness.OriginalRisk (PackedNTT.scheme length psi primitive s) dummy capacity radius outcome ↔
      WrongTransformRisk length psi s dummy capacity radius outcome := by
  classical
  have semantic (owner : ∀ side, RecordedSourceCoherence.Snapshot Input Digest Cfg height (s.tag side)) :
      NTTRowCheck.Relation (PackedNTT.scheme length psi primitive s).transform
        (NTTCompression.sourceRows c r (OwnedNTTSoundness.originalSources s dummy capacity radius owner false))
        (NTTCompression.sourceRows c r (OwnedNTTSoundness.originalSources s dummy capacity radius owner true)) ↔
      ∀ row, BlindRotationNTT.transform log psi
        (PackedNTTBinding.row length (OwnedNTTSoundness.originalSources s dummy capacity radius owner false) row) =
        PackedNTTBinding.row length (OwnedNTTSoundness.originalSources s dummy capacity radius owner true) row :=
    PackedNTTBinding.relation_iff_transforms length psi primitive _ _
  change (∃ owner, (∀ side, (owner side).root = outcome.1.1.1 side ∧
      ⟨s.tag side,owner side⟩ ∈ outcome.2.2.checkpoints.checkpoints) ∧
    ¬NTTRowCheck.Relation (PackedNTT.scheme length psi primitive s).transform
      (NTTCompression.sourceRows c r (OwnedNTTSoundness.originalSources s dummy capacity radius owner false))
      (NTTCompression.sourceRows c r (OwnedNTTSoundness.originalSources s dummy capacity radius owner true)) ∧
    AuthenticatedNTT.accepted outcome.2.1 = true) ↔ _
  simp only [semantic,not_forall,WrongTransformRisk]

variable {K : Type} [Field K] [Algebra (ZMod q) K] [Fintype K] [DecidableEq K]
  [DecidableEq Input] [Fintype Digest] [SampleableType Digest]
  [SampleableType (ZMod q)] [SampleableType (Fin r → ZMod q)]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin b → ZMod q)]
  [SampleableType (TestMatrix (ZMod q) (2^front) b)] [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType ((Fin (2^front) × Fin b) → K)]

/-- False concrete NTT on any matching original row: row/compression errors,
two PCS errors and ONE actual whole-program hash charge. -/
theorem soundness_from_empty [NeZero m] [NeZero b]
    (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (s : AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (basis : Module.Basis (Fin b) (ZMod q) K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3) :
    Pr{let outcome ← (AuthenticatedNTT.witness (PackedNTT.scheme length psi primitive s) dummy)}[
      WrongTransformRisk length psi s dummy capacity radius outcome] ≤
      ((((r : ENNReal)/q)^k) + (c : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/q)^b)) +
        (JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius +
          JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius)) +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (fun _ : Cfg => Skeleton.perfect height))
        (CheckpointCollision.loss unifSpec (fun _ : Cfg => Skeleton.perfect height))
        (AuthenticatedNTT.program (PackedNTT.scheme length psi primitive s))
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) := by
  have bound := OwnedNTTSoundness.original_soundness_from_empty (PackedNTT.scheme length psi primitive s)
    basis dummy enough capacity radius small
  simp only [ZMod.card] at bound
  apply le_trans (prEvent_mono _ _ _ ?_) bound
  intro outcome risk
  exact (original_risk_iff length psi primitive s dummy capacity radius outcome).mpr risk

end
end FormalProof4FHE.HasteBoots.OwnedNTTBinding
