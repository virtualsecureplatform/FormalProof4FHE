module
public import FormalProof4FHE.HasteBoots.OwnedKeySwitchCoverage
public import FormalProof4FHE.HasteBoots.KeySwitchSourceConstraints
@[expose] public section

/-! Original-owner key-switch coverage with canonical decomposition and NTT
source relations in place of supplied digit/result transform equalities. -/
namespace FormalProof4FHE.HasteBoots.OwnedKeySwitchSourceCoverage
open NativeBlindRotation
open OracleSpec OracleComp
noncomputable section
variable {q log c b levels d dc dw front suffix m queries height : ℕ} [Fact q.Prime]
  {FirstMessage Message Input Digest Cfg Response Memory CommitMemory : Type} [DecidableEq Digest]

/-- Only the total-dimension equality is transported; cube bit order and
lane addresses are unchanged. -/
def tables (expected : Fin levels → Digest)
    (s : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor levels) (PBSHadamard.Term levels)
      FirstMessage Message Input Digest Cfg Response Memory CommitMemory b c front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (owner : ∀ factor, RecordedSourceCoherence.Snapshot Input Digest Cfg height (s.tag factor)) :
    PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor levels) (1+c) b :=
  fun factor => QueryReindex.source (Nat.add_comm 1 c)
    (OriginalFactorExceptionUnion.originalSources (OwnedHadamardSoundness.stage expected s) dummy capacity radius owner factor)

def address (length : 2^c*b = 2^log) (half : Bool) (index : Fin (2^log)) : MatrixFold.Cube (c+1) × Fin b :=
  let position := PackedNTTBinding.address (r := 1) length (half,()) index
  ((Nat.add_comm 1 c) ▸ position.1,position.2)

theorem accepted_wrong_increment_implies_original
    (expected : Fin levels → Digest)
    (s : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor levels) (PBSHadamard.Term levels)
      FirstMessage Message Input Digest Cfg Response Memory CommitMemory b c front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (outcome : AuthenticatedZeroCheck.Prefix (Factor := PBSHadamard.Factor levels) (Digest := Digest)
        (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) ×
      AuthenticatedZeroCheck.RunResult (F := ZMod q) (Factor := PBSHadamard.Factor levels) (Memory := Memory)
        (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (n := c) (front := front) (queries := queries) (height := height))
    (owner : ∀ factor, RecordedSourceCoherence.Snapshot Input Digest Cfg height (s.tag factor))
    (recorded : ∀ factor, (owner factor).root = outcome.1.1.1 factor ∧
      ⟨s.tag factor,owner factor⟩ ∈ outcome.2.2.checkpoints.checkpoints)
    (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1))) (bits : ℕ)
    (radixLarge : 1 < 2^bits) (radixSmall : 2^bits < q) (enough : q-1 < (2^bits)^d) (covered : levels ≤ d)
    (registry : DecompositionBlindRotation.Registry q d dc dw)
    (registryAddress : Fin (2^log) → MatrixFold.Cube dc × Fin dw)
    (key : NativeKeySwitch.Key q (2^log) levels) (mask : Poly q (2^log)) (result : Cipher q (2^log))
    (input : DecompositionBlindRotation.project registry registryAddress DecompositionLinear.input = -mask)
    (linear : DecompositionLinear.Relation ((2^bits : ℕ) : ZMod q) registry)
    (lookup : ∀ index, RadixCanonicity.LookupAt q (2^bits) registry (registryAddress index).1 (registryAddress index).2)
    (coefficients : Fin levels → PackedNTTBinding.Table q (1+c) b)
    (resultCoefficients : PackedNTTBinding.Table q (1+c) b)
    (digitSources : ∀ half level, PackedNTTBinding.row length (coefficients level) (half,()) =
      DecompositionBlindRotation.project registry registryAddress (DecompositionLinear.digit (Fin.castLE covered level)))
    (digitTransforms : ∀ level, PackedNTT.Relation length psi (NTTCompression.sourceRows c 1 (coefficients level))
      (NTTCompression.sourceRows c 1
        (tables expected s dummy capacity radius owner (.inl (level,false)))))
    (resultSource : ∀ half, PackedNTTBinding.row length resultCoefficients (half,()) = result half)
    (resultTransform : PackedNTT.Relation length psi (NTTCompression.sourceRows c 1 resultCoefficients)
      (NTTCompression.sourceRows c 1
        (tables expected s dummy capacity radius owner (.inr ()))))
    (keys : ∀ half level, BlindRotationNTT.transform log psi (key level half) =
      PackedNTTBinding.row length
        (tables expected s dummy capacity radius owner (.inl (level,true))) (half,()))
    (wrong : result ≠ CanonicalKeySwitch.increment bits key mask)
    (passes : AuthenticatedZeroCheck.accepted outcome.2.1 = true) :
    OriginalFactorExceptionUnion.OriginalRisk (OwnedHadamardSoundness.stage expected s) dummy capacity radius outcome := by
  let sourceTables := tables expected s dummy capacity radius owner
  have digits := KeySwitchSourceConstraints.digit_bindings length psi primitive bits radixLarge radixSmall enough covered
    registry registryAddress mask input linear lookup coefficients sourceTables digitSources digitTransforms
  have resultBinding := KeySwitchSourceConstraints.result_bindings length psi primitive result resultCoefficients
    sourceTables resultSource resultTransform
  exact OwnedKeySwitchCoverage.accepted_wrong_increment_implies_original expected s dummy capacity radius outcome owner recorded
    (address length) psi primitive bits key mask result digits keys resultBinding wrong passes

end
end FormalProof4FHE.HasteBoots.OwnedKeySwitchSourceCoverage
