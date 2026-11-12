module
public import FormalProof4FHE.HasteBoots.ZeroCheckConditionalSoundness
public import FormalProof4FHE.HasteBoots.OwnedHadamardSoundness
@[expose] public section

/-! Typed degree-two Hadamard soundness from any audited incoming state,
outside the caller's one final collision event. Original key openings remain. -/
namespace FormalProof4FHE.HasteBoots.HadamardConditionalSoundness
open OracleSpec OracleComp BinaryTree Matrix
open InteractiveAuthenticatedOpening OwnedHadamardSoundness
noncomputable section
variable {F K FirstMessage Message Input Digest Cfg Response Memory CommitMemory : Type}
  [Field F] [DecidableEq F] {count b n front suffix m queries height : ℕ}

variable [DecidableEq Digest]
variable [DecidableEq Input]
  [SampleableType Digest]
  [SampleableType F] [SampleableType (Fin b → F)] [SampleableType (Fin n → F)]
  [SampleableType (PackedZeroReduction.Points F n b)]
  [SampleableType (Fin b → Fin b → F)] [SampleableType (Fin b → ((Fin b → F) × F))]
  [SampleableType (TestMatrix F (2^front) b)] [SampleableType (Fin queries → Fin (2^height))]
  [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq K]
  [SampleableType ((Fin (2^front) × Fin b) → K)]

/-- Typed native messages supply the degree bounds. All original digit, key
and result openings contribute PCS error outside the final collision event. -/
theorem native_original_safe_bound [NeZero m] [NeZero b]
    (characteristic : ℕ) [CharP F characteristic]
    (firstSmall : (2*b-1)*2+1 ≤ characteristic) (roundSmall : (2*b-1)*3+1 ≤ characteristic)
    (nodesEnough : 2*b ≤ (2*b-1)*2+1)
    (expected : Fin count → Digest)
    (s : AuthenticatedZeroCheck.Scheme F (PBSHadamard.Factor count) (PBSHadamard.Term count)
      (Fin b → Fin ((2*b-1)*2+1) → F) (Fin ((2*b-1)*3+1) → F)
      Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (audited : CheckpointExecution.Audited s.encoding dummy (fun _ : Cfg => Skeleton.perfect height) initial) :
    Pr{let outcome ← (ZeroCheckConditionalSoundness.witness
      (AuthenticatedZeroCheck.nativeScheme characteristic 2 firstSmall roundSmall nodesEnough (stage expected s)) dummy initial)}[
      OriginalFactorExceptionUnion.OriginalRisk
        (AuthenticatedZeroCheck.nativeScheme characteristic 2 firstSmall roundSmall nodesEnough (stage expected s))
        dummy capacity radius outcome ∧
      ¬CheckpointCollision.Bad (fun _ : Cfg => Skeleton.perfect height) outcome.2.2] ≤
      (((n : ENNReal)/Fintype.card F)^b +
        (((((2*b-1)*2+1 : ℕ) : ENNReal)/Fintype.card F)^b) +
        (n : ENNReal)*(((((2*b-1)*3 : ℕ) : ENNReal)/Fintype.card F)^b) +
        ((2*count+1 : ℕ) : ENNReal)*
          JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius) := by
  rw [←factor_error_sum count (JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius)]
  exact ZeroCheckConditionalSoundness.original_safe_bound
    (AuthenticatedZeroCheck.nativeScheme characteristic 2 firstSmall roundSmall nodesEnough (stage expected s))
    basis dummy PBSHadamard.factors_complete enough capacity radius 2 PBSHadamard.degree_bound
    (fun _ _ => NativePackedInterpolation.messagePolynomial_degree _ _)
    (fun _ => NativePackedInterpolation.messagePolynomial_degree _ _) small initial audited

end
end FormalProof4FHE.HasteBoots.HadamardConditionalSoundness
