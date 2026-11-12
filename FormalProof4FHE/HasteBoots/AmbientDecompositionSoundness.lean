module
public import FormalProof4FHE.HasteBoots.AmbientLinear
public import FormalProof4FHE.HasteBoots.OwnedDecompositionSoundness
@[expose] public section

/-! Native reconstruction and borrow endpoints on an inherited mixed-height
shared execution. Earlier comparison helpers remain recorded and monitored. -/
namespace FormalProof4FHE.HasteBoots.AmbientDecompositionSoundness
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

omit [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
  [SampleableType ((Fin (2^front) × Fin b) → K)] in
/-- The actual native commitment emits the fixed input/digit roots, retaining
only the borrow roots from its callback on every supported branch. -/
theorem roots (heights : Cfg → ℕ) (characteristic : ℕ) [CharP F characteristic]
    (nodesEnough : 2*b ≤ characteristic)
    (inputRoot : Digest) (digits : Fin d → Digest) (radix : F)
    (s : AuthenticatedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : _) (supported : outcome ∈ support (AmbientLinear.witness heights
      (AuthenticatedLinear.nativeScheme characteristic nodesEnough
        (OwnedDecompositionSoundness.stage inputRoot digits radix s)) dummy initial)) :
    outcome.1.1.1 DecompositionLinear.input = inputRoot ∧
      ∀ level, outcome.1.1.1 (DecompositionLinear.digit level) = digits level := by
  simp only [AmbientLinear.witness,MultiCommitmentPrefix.witness,support_bind,support_pure,
    Set.mem_iUnion,Set.mem_singleton_iff] at supported
  obtain ⟨first,firstSupported,last,_,equal⟩ := supported
  subst outcome
  simp only [AuthenticatedLinear.nativeScheme,OwnedDecompositionSoundness.stage,DecompositionLinear.stage,
    simulateQ_bind,StateT.run_bind,simulateQ_pure,StateT.run_pure,support_bind,support_pure,
    Set.mem_iUnion,Set.mem_singleton_iff] at firstSupported
  obtain ⟨emission,_,same⟩ := firstSupported
  subst first
  exact ⟨OwnedDecompositionSoundness.roots_input inputRoot digits emission.1.1,
    fun level => OwnedDecompositionSoundness.roots_digit inputRoot digits emission.1.1 level⟩

/-- Caller-selected input/digit roots, all original borrow roots and the
native linear relation retain their actual callbacks, state and private memory.
No reconstruction-validity or opening certificate is supplied. -/
theorem native_original_safe_bound [NeZero m] [NeZero b] (heights : Cfg → ℕ)
    (characteristic : ℕ) [CharP F characteristic] (nodesEnough : 2*b ≤ characteristic)
    (inputRoot : Digest) (digits : Fin d → Digest) (radix : F)
    (s : AuthenticatedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (geometry : ∀ factor, heights (s.tag factor) = height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (AmbientLinear.witness heights
      (AuthenticatedLinear.nativeScheme characteristic nodesEnough
        (OwnedDecompositionSoundness.stage inputRoot digits radix s)) dummy initial)}[
      AmbientLinear.OriginalRisk heights
        (AuthenticatedLinear.nativeScheme characteristic nodesEnough
          (OwnedDecompositionSoundness.stage inputRoot digits radix s)) dummy capacity radius outcome ∧
      ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2] ≤
      (((front+suffix : ℕ) : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card F)^b))) +
      ((2*d+2 : ℕ) : ENNReal)*
        JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius := by
  have bound := AmbientLinear.original_safe_bound heights
    (AuthenticatedLinear.nativeScheme characteristic nodesEnough
      (OwnedDecompositionSoundness.stage inputRoot digits radix s))
    geometry basis dummy enough capacity radius small initial audited
  simpa only [OwnedDecompositionSoundness.registry_error_sum, AuthenticatedLinear.nativeScheme,
    OwnedDecompositionSoundness.stage, DecompositionLinear.stage] using bound

end
end FormalProof4FHE.HasteBoots.AmbientDecompositionSoundness
