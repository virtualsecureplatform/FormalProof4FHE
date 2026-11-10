module
public import FormalProof4FHE.HasteBoots.AuthenticatedExtraction
public import FormalProof4FHE.HasteBoots.AuthenticatedExceptionUnion
@[expose] public section

/-! Accepted false extraction measured on any matching recorded original
source family. The source-reuse and opening exceptions share one hash charge;
the bound contains exactly one private PCS error. -/
namespace FormalProof4FHE.HasteBoots.OwnedExtractionSoundness
open OracleSpec OracleComp BinaryTree Matrix
open InteractiveAuthenticatedOpening AuthenticatedExtraction
noncomputable section
variable {q c lanes dimension front suffix m queries height : ℕ} [Fact q.Prime]
  {FirstMessage Message Input Digest Cfg Response Memory CommitMemory : Type}
  [DecidableEq Input] [DecidableEq Digest]

omit [DecidableEq Input] in
theorem original_vanishes_iff (positive : 0 < dimension)
    (acc : ((Unit → Digest) × CommitMemory) → NativeBlindRotation.Cipher q (2^(c+lanes)))
    (output : ((Unit → Digest) × CommitMemory) → NativePublic.Ciphertext q dimension)
    (s : AuthenticatedPublicZeroCheck.Scheme (ZMod q) Unit Bool (PBSHadamard.Term 1) FirstMessage Message
      Input Digest Cfg Response Memory CommitMemory (2^lanes) c front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (first : AuthenticatedPublicZeroCheck.Prefix (Private := Unit) (Digest := Digest) (CommitMemory := CommitMemory)
      (Input := Input) (Cfg := Cfg) (height := height))
    (owner : ∀ factor, RecordedSourceCoherence.Snapshot Input Digest Cfg height (s.tag factor)) :
    PackedZeroCube.Vanishes PBSHadamard.arity PBSHadamard.coefficient indices
      (AuthenticatedExceptionUnion.originalSources (stage positive acc output s) dummy capacity radius first owner) ↔
    Relation positive (acc first.1) (output first.1)
      (ReusedPrivateSource.atSnapshot s dummy capacity radius (s.tag ()) (owner ())) :=
  vanishes_iff positive (acc first.1) (output first.1)
    (fun factor => ReusedPrivateSource.atSnapshot s dummy capacity radius (s.tag factor) (owner factor))

variable {K : Type} [Field K] [Algebra (ZMod q) K] [Fintype K] [DecidableEq K]
  [Fintype Digest] [SampleableType Digest]
  [SampleableType (ZMod q)] [SampleableType (Fin (2^lanes) → ZMod q)] [SampleableType (Fin c → ZMod q)]
  [SampleableType (PackedZeroReduction.Points (ZMod q) c (2^lanes))]
  [SampleableType (Fin (2^lanes) → Fin (2^lanes) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))]
  [SampleableType (TestMatrix (ZMod q) (2^front) (2^lanes))]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType ((Fin (2^front) × Fin (2^lanes)) → K)]


theorem native_original_soundness_from_empty [NeZero m]
    (positive : 0 < dimension)
    (acc : ((Unit → Digest) × CommitMemory) → NativeBlindRotation.Cipher q (2^(c+lanes)))
    (output : ((Unit → Digest) × CommitMemory) → NativePublic.Ciphertext q dimension)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (nodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (s : AuthenticatedPublicZeroCheck.Scheme (ZMod q) Unit Bool (PBSHadamard.Term 1)
      (Fin (2^lanes) → Fin ((2*(2^lanes)-1)*2+1) → ZMod q)
      (Fin ((2*(2^lanes)-1)*3+1) → ZMod q)
      Input Digest Cfg Response Memory CommitMemory (2^lanes) c front suffix m queries height)
    (basis : Module.Basis (Fin (2^lanes)) (ZMod q) K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3) :
    Pr{let outcome ← (AuthenticatedPublicZeroCheck.witness
      (AuthenticatedPublicZeroCheck.nativeScheme q 2 firstSmall roundSmall nodesEnough (stage positive acc output s)) dummy)}[
      AuthenticatedExceptionUnion.OriginalRisk
        (AuthenticatedPublicZeroCheck.nativeScheme q 2 firstSmall roundSmall nodesEnough (stage positive acc output s))
        dummy capacity radius outcome] ≤
      (KeySwitchExtractionSoundness.error q c (2^lanes) +
        JointMatrixOpening.error (K := K) (m := m) (b := 2^lanes) (queries := queries) s.domain radius) +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (fun _ : Cfg => Skeleton.perfect height))
        (CheckpointCollision.loss unifSpec (fun _ : Cfg => Skeleton.perfect height))
        (AuthenticatedPublicZeroCheck.program (AuthenticatedPublicZeroCheck.nativeScheme q 2 firstSmall roundSmall nodesEnough (stage positive acc output s)))
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) := by
  have complete : ∀ factor, factor ∈ (stage positive acc output s).factors := by
    intro factor
    cases factor
    simp [stage]
  have bound := AuthenticatedExceptionUnion.original_soundness_from_empty
    (AuthenticatedPublicZeroCheck.nativeScheme q 2 firstSmall roundSmall nodesEnough (stage positive acc output s))
    basis dummy complete enough capacity radius 2 PBSHadamard.degree_bound
    (fun _ _ => NativePackedInterpolation.messagePolynomial_degree _ _)
    (fun _ => NativePackedInterpolation.messagePolynomial_degree _ _) small
  simpa only [AuthenticatedPublicZeroCheck.nativeScheme,stage,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
    KeySwitchExtractionSoundness.error,ZMod.card] using bound

end
end FormalProof4FHE.HasteBoots.OwnedExtractionSoundness
