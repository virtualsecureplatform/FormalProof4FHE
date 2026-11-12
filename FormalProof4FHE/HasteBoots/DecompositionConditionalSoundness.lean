module
public import FormalProof4FHE.HasteBoots.LinearConditionalSoundness
public import FormalProof4FHE.HasteBoots.OwnedDecompositionSoundness
@[expose] public section

/-! Original reconstruction and borrow endpoints inside an inherited shared
execution. The enclosing PBS caller owns the single final collision charge. -/
namespace FormalProof4FHE.HasteBoots.DecompositionConditionalSoundness
open OracleSpec OracleComp BinaryTree
open InteractiveAuthenticatedOpening
noncomputable section
variable {F K Input Digest Cfg Response Memory CommitMemory : Type}
  [Field F] [DecidableEq F] [Fintype F] [DecidableEq Input] [DecidableEq Digest]
  {d b front suffix m queries height : ℕ}
  [SampleableType Digest] [SampleableType (Fin b → F)]
  [SampleableType (TestMatrix F (2^front) b)] [SampleableType (Fin queries → Fin (2^height))]
  [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
  [SampleableType ((Fin (2^front) × Fin b) → K)]

/-- Caller-selected input/digit roots, all original borrow roots and the
native linear relation retain their actual callbacks, state and private memory.
No reconstruction-validity or opening certificate is supplied. -/
theorem native_original_safe_bound [NeZero m] [NeZero b]
    (characteristic : ℕ) [CharP F characteristic] (nodesEnough : 2*b ≤ characteristic)
    (inputRoot : Digest) (digits : Fin d → Digest) (radix : F)
    (s : AuthenticatedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (audited : CheckpointExecution.Audited s.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial) :
    Pr{let outcome ← (LinearConditionalSoundness.witness
      (AuthenticatedLinear.nativeScheme characteristic nodesEnough
        (OwnedDecompositionSoundness.stage inputRoot digits radix s)) dummy initial)}[
      OwnedLinearSoundness.OriginalRisk
        (AuthenticatedLinear.nativeScheme characteristic nodesEnough
          (OwnedDecompositionSoundness.stage inputRoot digits radix s)) dummy capacity radius outcome ∧
      ¬CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) outcome.2.2] ≤
      (((front+suffix : ℕ) : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card F)^b))) +
      ((2*d+2 : ℕ) : ENNReal)*
        JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius := by
  have bound := LinearConditionalSoundness.original_safe_bound
    (AuthenticatedLinear.nativeScheme characteristic nodesEnough
      (OwnedDecompositionSoundness.stage inputRoot digits radix s))
    basis dummy enough capacity radius small initial audited
  simpa only [OwnedDecompositionSoundness.registry_error_sum, AuthenticatedLinear.nativeScheme,
    OwnedDecompositionSoundness.stage, DecompositionLinear.stage] using bound

end
end FormalProof4FHE.HasteBoots.DecompositionConditionalSoundness
