module
public import FormalProof4FHE.HasteBoots.OwnedHadamardSoundness
public import FormalProof4FHE.HasteBoots.DecompositionBlindRotation
@[expose] public section

/-! Blind-rotation external products use the original recorded Hadamard
factor family. Addresses can select a round and ciphertext half inside the
same global sources. Acceptance does not discharge NTT, digit or key bindings.
This is an authenticated-program coverage bridge, not a Rust refinement. -/
namespace FormalProof4FHE.HasteBoots.OwnedBlindRotationCoverage
open NativeBlindRotation
open OracleSpec OracleComp
noncomputable section
variable {q log levels d dc dw b n front suffix m queries height : ℕ} [Fact q.Prime]
  {FirstMessage Message Input Digest Cfg Response Memory CommitMemory : Type} [DecidableEq Digest]

def tables (expected : Fin (2*levels) → Digest)
    (s : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor (2*levels)) (PBSHadamard.Term (2*levels))
      FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (owner : ∀ factor, RecordedSourceCoherence.Snapshot Input Digest Cfg height (s.tag factor)) :
    PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor (2*levels)) (n+1) b :=
  OriginalFactorExceptionUnion.originalSources (OwnedHadamardSoundness.stage expected s) dummy capacity radius owner

/-- A false external product with correct bindings of the original sources
is covered by the actual accepted original-owner relation event. -/
theorem accepted_wrong_external_implies_original
    (expected : Fin (2*levels) → Digest)
    (s : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor (2*levels)) (PBSHadamard.Term (2*levels))
      FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (outcome : AuthenticatedZeroCheck.Prefix (Factor := PBSHadamard.Factor (2*levels)) (Digest := Digest)
        (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) ×
      AuthenticatedZeroCheck.RunResult (F := ZMod q) (Factor := PBSHadamard.Factor (2*levels)) (Memory := Memory)
        (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (n := n) (front := front) (queries := queries) (height := height))
    (owner : ∀ factor, RecordedSourceCoherence.Snapshot Input Digest Cfg height (s.tag factor))
    (recorded : ∀ factor, (owner factor).root = outcome.1.1.1 factor ∧
      ⟨s.tag factor,owner factor⟩ ∈ outcome.2.2.checkpoints.checkpoints)
    (address : Bool → Fin (2^log) → MatrixFold.Cube (n+1) × Fin b)
    (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1))) (bits : ℕ)
    (control : Control q (2^log) levels) (difference result : Cipher q (2^log))
    (digits : ∀ half source level, BlindRotationNTT.transform log psi (digit bits level (difference source)) =
      PBSHadamardBlindRotation.project (tables expected s dummy capacity radius owner)
        (address half) (.inl (PBSHadamardBlindRotation.digitIndex (source,level),false)))
    (keys : ∀ half source level, BlindRotationNTT.transform log psi (control source level half) =
      PBSHadamardBlindRotation.project (tables expected s dummy capacity radius owner)
        (address half) (.inl (PBSHadamardBlindRotation.digitIndex (source,level),true)))
    (output : ∀ half, BlindRotationNTT.transform log psi (result half) =
      PBSHadamardBlindRotation.project (tables expected s dummy capacity radius owner)
        (address half) (.inr ()))
    (wrong : result ≠ NativeBlindRotation.externalProduct bits control difference)
    (passes : AuthenticatedZeroCheck.accepted outcome.2.1 = true) :
    OriginalFactorExceptionUnion.OriginalRisk (OwnedHadamardSoundness.stage expected s) dummy capacity radius outcome := by
  refine ⟨owner,recorded,?_,passes⟩
  intro vanishes
  have relation := (PBSHadamard.vanishes_iff _).mp vanishes
  exact wrong (PBSHadamardBlindRotation.externalProduct_of_relations psi primitive bits control difference result
    (tables expected s dummy capacity radius owner) address relation digits keys output)

/-- No source-binding correctness certificate is needed: each false binding
is exposed at an original half/source/level, or the accepted relation is false. -/
theorem accepted_wrong_external_coverage
    (expected : Fin (2*levels) → Digest)
    (s : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor (2*levels)) (PBSHadamard.Term (2*levels))
      FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (outcome : AuthenticatedZeroCheck.Prefix (Factor := PBSHadamard.Factor (2*levels)) (Digest := Digest)
        (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) ×
      AuthenticatedZeroCheck.RunResult (F := ZMod q) (Factor := PBSHadamard.Factor (2*levels)) (Memory := Memory)
        (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (n := n) (front := front) (queries := queries) (height := height))
    (owner : ∀ factor, RecordedSourceCoherence.Snapshot Input Digest Cfg height (s.tag factor))
    (recorded : ∀ factor, (owner factor).root = outcome.1.1.1 factor ∧
      ⟨s.tag factor,owner factor⟩ ∈ outcome.2.2.checkpoints.checkpoints)
    (address : Bool → Fin (2^log) → MatrixFold.Cube (n+1) × Fin b)
    (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1))) (bits : ℕ)
    (control : Control q (2^log) levels) (difference result : Cipher q (2^log))
    (wrong : result ≠ NativeBlindRotation.externalProduct bits control difference)
    (passes : AuthenticatedZeroCheck.accepted outcome.2.1 = true) :
    (∃ half source level, BlindRotationNTT.transform log psi (digit bits level (difference source)) ≠
      PBSHadamardBlindRotation.project (tables expected s dummy capacity radius owner)
        (address half) (.inl (PBSHadamardBlindRotation.digitIndex (source,level),false))) ∨
    (∃ half source level, BlindRotationNTT.transform log psi (control source level half) ≠
      PBSHadamardBlindRotation.project (tables expected s dummy capacity radius owner)
        (address half) (.inl (PBSHadamardBlindRotation.digitIndex (source,level),true))) ∨
    (∃ half, BlindRotationNTT.transform log psi (result half) ≠
      PBSHadamardBlindRotation.project (tables expected s dummy capacity radius owner)
        (address half) (.inr ())) ∨
    OriginalFactorExceptionUnion.OriginalRisk (OwnedHadamardSoundness.stage expected s) dummy capacity radius outcome := by
  classical
  by_cases digits : ∀ half source level, BlindRotationNTT.transform log psi (digit bits level (difference source)) =
      PBSHadamardBlindRotation.project (tables expected s dummy capacity radius owner)
        (address half) (.inl (PBSHadamardBlindRotation.digitIndex (source,level),false))
  · by_cases keys : ∀ half source level, BlindRotationNTT.transform log psi (control source level half) =
        PBSHadamardBlindRotation.project (tables expected s dummy capacity radius owner)
          (address half) (.inl (PBSHadamardBlindRotation.digitIndex (source,level),true))
    · by_cases output : ∀ half, BlindRotationNTT.transform log psi (result half) =
          PBSHadamardBlindRotation.project (tables expected s dummy capacity radius owner)
            (address half) (.inr ())
      · exact Or.inr (Or.inr (Or.inr (accepted_wrong_external_implies_original expected s dummy capacity
          radius outcome owner recorded address psi primitive bits control difference result digits keys output wrong passes)))
      · exact Or.inr (Or.inr (Or.inl (not_forall.mp output)))
    · push Not at keys
      exact Or.inr (Or.inl keys)
  · push Not at digits
    exact Or.inl digits

/-- Any number of round projections share one original accepted relation
event. This is a pointwise reduction, with no union over round addresses. -/
theorem accepted_wrong_external_family_coverage {I : Type}
    (expected : Fin (2*levels) → Digest)
    (s : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor (2*levels)) (PBSHadamard.Term (2*levels))
      FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (outcome : AuthenticatedZeroCheck.Prefix (Factor := PBSHadamard.Factor (2*levels)) (Digest := Digest)
        (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) ×
      AuthenticatedZeroCheck.RunResult (F := ZMod q) (Factor := PBSHadamard.Factor (2*levels)) (Memory := Memory)
        (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (n := n) (front := front) (queries := queries) (height := height))
    (owner : ∀ factor, RecordedSourceCoherence.Snapshot Input Digest Cfg height (s.tag factor))
    (recorded : ∀ factor, (owner factor).root = outcome.1.1.1 factor ∧
      ⟨s.tag factor,owner factor⟩ ∈ outcome.2.2.checkpoints.checkpoints)
    (address : I → Bool → Fin (2^log) → MatrixFold.Cube (n+1) × Fin b)
    (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1))) (bits : ℕ)
    (control : I → Control q (2^log) levels) (difference result : I → Cipher q (2^log))
    (wrong : ∃ index, result index ≠ NativeBlindRotation.externalProduct bits (control index) (difference index))
    (passes : AuthenticatedZeroCheck.accepted outcome.2.1 = true) :
    (∃ index, (∃ half source level, BlindRotationNTT.transform log psi (digit bits level (difference index source)) ≠
      PBSHadamardBlindRotation.project (tables expected s dummy capacity radius owner)
        (address index half) (.inl (PBSHadamardBlindRotation.digitIndex (source,level),false))) ∨
    (∃ half source level, BlindRotationNTT.transform log psi (control index source level half) ≠
      PBSHadamardBlindRotation.project (tables expected s dummy capacity radius owner)
        (address index half) (.inl (PBSHadamardBlindRotation.digitIndex (source,level),true))) ∨
    (∃ half, BlindRotationNTT.transform log psi (result index half) ≠
      PBSHadamardBlindRotation.project (tables expected s dummy capacity radius owner)
        (address index half) (.inr ()))) ∨
    OriginalFactorExceptionUnion.OriginalRisk (OwnedHadamardSoundness.stage expected s) dummy capacity radius outcome := by
  obtain ⟨index, failed⟩ := wrong
  rcases accepted_wrong_external_coverage expected s dummy capacity radius outcome owner recorded
      (address index) psi primitive bits (control index) (difference index) (result index) failed passes with
    digits | keys | output | risk
  · exact Or.inl ⟨index, Or.inl digits⟩
  · exact Or.inl ⟨index, Or.inr (Or.inl keys)⟩
  · exact Or.inl ⟨index, Or.inr (Or.inr output)⟩
  · exact Or.inr risk

/-- Canonical digits are derived from reconstruction and every original
comparison membership. Only the original coefficient-source NTT binding remains. -/
theorem accepted_wrong_external_of_constraints
    (expected : Fin (2*levels) → Digest)
    (s : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor (2*levels)) (PBSHadamard.Term (2*levels))
      FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (outcome : AuthenticatedZeroCheck.Prefix (Factor := PBSHadamard.Factor (2*levels)) (Digest := Digest)
        (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) ×
      AuthenticatedZeroCheck.RunResult (F := ZMod q) (Factor := PBSHadamard.Factor (2*levels)) (Memory := Memory)
        (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (n := n) (front := front) (queries := queries) (height := height))
    (owner : ∀ factor, RecordedSourceCoherence.Snapshot Input Digest Cfg height (s.tag factor))
    (recorded : ∀ factor, (owner factor).root = outcome.1.1.1 factor ∧
      ⟨s.tag factor,owner factor⟩ ∈ outcome.2.2.checkpoints.checkpoints)
    (address : Bool → Fin (2^log) → MatrixFold.Cube (n+1) × Fin b)
    (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1))) (bits : ℕ)
    (control : Control q (2^log) levels) (difference result : Cipher q (2^log))
    (radixLarge : 1 < 2^bits) (radixSmall : 2^bits < q)
    (enough : q-1 < (2^bits)^d) (covered : levels ≤ d)
    (registries : Bool → DecompositionBlindRotation.Registry q d dc dw)
    (addresses : Bool → Fin (2^log) → MatrixFold.Cube dc × Fin dw)
    (source : ∀ half, DecompositionBlindRotation.project (registries half) (addresses half)
      DecompositionLinear.input = difference half)
    (linear : ∀ half, DecompositionLinear.Relation ((2^bits : ℕ) : ZMod q) (registries half))
    (lookup : ∀ half index, RadixCanonicity.LookupAt q (2^bits) (registries half)
      (addresses half index).1 (addresses half index).2)
    (binding : ∀ half source level, BlindRotationNTT.transform log psi
      (DecompositionBlindRotation.project (registries source) (addresses source)
        (DecompositionLinear.digit (Fin.castLE covered level))) =
      PBSHadamardBlindRotation.project (tables expected s dummy capacity radius owner)
        (address half) (.inl (PBSHadamardBlindRotation.digitIndex (source,level),false)))
    (keys : ∀ half source level, BlindRotationNTT.transform log psi (control source level half) =
      PBSHadamardBlindRotation.project (tables expected s dummy capacity radius owner)
        (address half) (.inl (PBSHadamardBlindRotation.digitIndex (source,level),true)))
    (output : ∀ half, BlindRotationNTT.transform log psi (result half) =
      PBSHadamardBlindRotation.project (tables expected s dummy capacity radius owner)
        (address half) (.inr ()))
    (wrong : result ≠ NativeBlindRotation.externalProduct bits control difference)
    (passes : AuthenticatedZeroCheck.accepted outcome.2.1 = true) :
    OriginalFactorExceptionUnion.OriginalRisk (OwnedHadamardSoundness.stage expected s) dummy capacity radius outcome := by
  have digits := DecompositionBlindRotation.digits_transform_of_constraints psi bits radixLarge radixSmall
    enough covered registries addresses difference source linear lookup
    (tables expected s dummy capacity radius owner) address binding
  exact accepted_wrong_external_implies_original expected s dummy capacity radius outcome owner recorded
    address psi primitive bits control difference result digits keys output wrong passes

end
end FormalProof4FHE.HasteBoots.OwnedBlindRotationCoverage
