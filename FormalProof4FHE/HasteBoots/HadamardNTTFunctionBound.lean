module
public import FormalProof4FHE.HasteBoots.HadamardNTTProbability
@[expose] public section

/-! Quantitative enforcement of original Hadamard-factor transforms by the
reached concrete NTT child. Source association and inherited auditing are
derived from the actual short-circuit run; one caller hash charge is paid. -/
namespace FormalProof4FHE.HasteBoots.HadamardNTTFunctionBound
open OracleSpec OracleComp
noncomputable section
variable {q log b c r k n count front suffix m queries height : ℕ} [Fact q.Prime]
  {K Input Digest Cfg Response Memory CommitMemory FirstMessage Message : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest] [Fintype Digest]
  [Field K] [Algebra (ZMod q) K] [Fintype K] [DecidableEq K]
  [SampleableType (ZMod q)] [SampleableType (Fin r → ZMod q)]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points (ZMod q) n b)]
  [SampleableType (Fin b → Fin b → ZMod q)]
  [SampleableType ((Fin (2^front) × Fin b) → K)]

/-- Any accepted false transform at any original row is bounded by one NTT
arithmetic/PCS rate and the actual caller's single shared collision charge.
There is no row-count union or independent source-association certificate. -/
theorem false_transform_bound [NeZero m] [NeZero b]
    (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (coefficient : Digest) (expected : Fin count → Digest)
    (publicRoots : PBSHadamard.Factor count → Digest) (factor : PBSHadamard.Factor count)
    (ns : AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor count) (PBSHadamard.Term count)
      FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (basis : Module.Basis (Fin b) (ZMod q) K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) ns.domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (encoding : hs.encoding = ns.encoding) (domain : hs.domain = ns.domain)
    (tags : ns.tag true = hs.tag factor) :
    Pr{let outcome ← (HadamardNTTComposition.witness coefficient expected publicRoots factor
      (PackedNTT.scheme length psi primitive ns) hs dummy
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      ∃ second, outcome.2 = some second ∧ AuthenticatedNTT.accepted second.2.1 = true ∧
        ∃ row : MatrixFold.Cube r, BlindRotationNTT.transform log psi
          (PackedNTTBinding.row length (AuthenticatedNTT.sources ns dummy capacity radius second.1 false) row) ≠
          PackedNTTBinding.row length (QueryReindex.source (ns.dimensions.trans hs.dimensions.symm)
            (AuthenticatedZeroCheck.sources hs dummy capacity radius outcome.1.1 factor)) row] ≤
    HadamardNTTProbability.rate (K := K) ns radius +
    ExpectedHazard.charge
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height))
      (CheckpointCollision.loss unifSpec (RecordedSourceCoherence.Shape Cfg height))
      (HadamardNTTComposition.program coefficient expected publicRoots factor (PackedNTT.scheme length psi primitive ns) hs)
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)) := by
  apply HadamardNTTProbability.covered_bound coefficient expected publicRoots factor
    (PackedNTT.scheme length psi primitive ns) hs basis dummy enough capacity radius small encoding
  intro outcome supported failed
  rcases outcome with ⟨first,optional⟩
  obtain ⟨second,reached,passes,wrong⟩ := failed
  change optional = some second at reached
  subst optional
  have initial := CheckpointExecution.good_empty hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
  rcases HadamardNTTEnforcement.false_transform_coverage length psi primitive coefficient expected publicRoots factor
      ns hs dummy _ first second supported capacity radius ⟨initial.1,fun _ => initial.2.2⟩
      encoding domain tags wrong passes with risk | bad
  · exact Or.inl ⟨second,rfl,risk⟩
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.HadamardNTTFunctionBound
