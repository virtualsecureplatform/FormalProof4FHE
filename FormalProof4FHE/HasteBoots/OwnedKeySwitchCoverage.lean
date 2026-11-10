module
public import FormalProof4FHE.HasteBoots.OwnedHadamardSoundness
public import FormalProof4FHE.HasteBoots.PackedKeySwitchStage
@[expose] public section

/-! Connect the signed coefficient-domain key product to the false-relation
event measured by recorded-owner Hadamard soundness. NTT/canonical digit and
original-key bindings are explicit obligations, not acceptance certificates. -/
namespace FormalProof4FHE.HasteBoots.OwnedKeySwitchCoverage
open NativeBlindRotation
open OracleSpec OracleComp
noncomputable section
variable {q log levels b n front suffix m queries height : ℕ} [Fact q.Prime]
  {FirstMessage Message Input Digest Cfg Response Memory CommitMemory : Type} [DecidableEq Digest]

def sourceStage (expected : Fin levels → Digest)
    (s : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor levels) (PBSHadamard.Term levels)
      FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (owner : ∀ factor, RecordedSourceCoherence.Snapshot Input Digest Cfg height (s.tag factor))
    (address : Bool → Fin (2^log) → MatrixFold.Cube (n+1) × Fin b) :
    PackedKeySwitchStage.Stage q log levels (n+1) b :=
  ⟨OriginalFactorExceptionUnion.originalSources (OwnedHadamardSoundness.stage expected s) dummy capacity radius owner,address⟩

/-- A false signed increment with correct bindings of the original sources
is covered by the actual accepted original-owner relation event. -/
theorem accepted_wrong_increment_implies_original
    (expected : Fin levels → Digest)
    (s : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor levels) (PBSHadamard.Term levels)
      FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (outcome : AuthenticatedZeroCheck.Prefix (Factor := PBSHadamard.Factor levels) (Digest := Digest)
        (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) ×
      AuthenticatedZeroCheck.RunResult (F := ZMod q) (Factor := PBSHadamard.Factor levels) (Memory := Memory)
        (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (n := n) (front := front) (queries := queries) (height := height))
    (owner : ∀ factor, RecordedSourceCoherence.Snapshot Input Digest Cfg height (s.tag factor))
    (recorded : ∀ factor, (owner factor).root = outcome.1.1.1 factor ∧
      ⟨s.tag factor,owner factor⟩ ∈ outcome.2.2.checkpoints.checkpoints)
    (address : Bool → Fin (2^log) → MatrixFold.Cube (n+1) × Fin b)
    (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1))) (bits : ℕ)
    (key : NativeKeySwitch.Key q (2^log) levels) (mask : Poly q (2^log)) (result : Cipher q (2^log))
    (digits : ∀ half level, BlindRotationNTT.transform log psi (digit bits level (-mask)) =
      CanonicalKeySwitch.project (sourceStage expected s dummy capacity radius owner address).tables
        (address half) (.inl (level,false)))
    (keys : ∀ half level, BlindRotationNTT.transform log psi (key level half) =
      CanonicalKeySwitch.project (sourceStage expected s dummy capacity radius owner address).tables
        (address half) (.inl (level,true)))
    (output : ∀ half, BlindRotationNTT.transform log psi (result half) =
      CanonicalKeySwitch.project (sourceStage expected s dummy capacity radius owner address).tables
        (address half) (.inr ()))
    (wrong : result ≠ CanonicalKeySwitch.increment bits key mask)
    (passes : AuthenticatedZeroCheck.accepted outcome.2.1 = true) :
    OriginalFactorExceptionUnion.OriginalRisk (OwnedHadamardSoundness.stage expected s) dummy capacity radius outcome := by
  refine ⟨owner,recorded,?_,passes⟩
  intro vanishes
  have relation := (PBSHadamard.vanishes_iff _).mp vanishes
  exact wrong (PackedKeySwitchStage.increment_of_holds psi primitive bits key mask result
    (sourceStage expected s dummy capacity radius owner address) ⟨relation,digits,keys,output⟩)

end
end FormalProof4FHE.HasteBoots.OwnedKeySwitchCoverage
