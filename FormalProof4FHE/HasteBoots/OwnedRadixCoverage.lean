module
public import FormalProof4FHE.HasteBoots.OwnedDecompositionSoundness
public import FormalProof4FHE.HasteBoots.RadixLookupSources
@[expose] public section

/-! An incorrect original radix digit exposes either the bounded accepted
linear event or a particular original triple outside its literal comparison
table. Actual comparison acceptance still needs its lookup/PCS reduction. -/
namespace FormalProof4FHE.HasteBoots.OwnedRadixCoverage
open OracleSpec OracleComp
noncomputable section
variable {p radix d b front suffix m queries height : ℕ} [Fact p.Prime]
  {Input Digest Cfg Response Memory CommitMemory : Type} [DecidableEq Digest]

theorem accepted_wrong_digit_coverage
    (inputRoot : Digest) (digits : Fin d → Digest)
    (s : AuthenticatedLinear.Scheme (ZMod p) Input Digest Cfg Response Memory CommitMemory (2*d+2) b front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (outcome : AuthenticatedLinear.Prefix (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input)
        (Cfg := Cfg) (height := height) (count := 2*d+2) ×
      AuthenticatedLinear.RunResult (F := ZMod p) (Memory := Memory) (Response := Response) (Input := Input)
        (Digest := Digest) (Cfg := Cfg) (b := b) (count := 2*d+2) (front := front) (suffix := suffix)
        (queries := queries) (height := height))
    (owner : ∀ factor, RecordedSourceCoherence.Snapshot Input Digest Cfg height (s.tag factor))
    (recorded : ∀ factor, (owner factor).root = outcome.1.1.1 factor ∧
      ⟨s.tag factor,owner factor⟩ ∈ outcome.2.2.checkpoints.checkpoints)
    (radixLarge : 1 < radix) (radixSmall : radix < p) (enough : p-1 < radix^d)
    (cell : MatrixFold.Cube (front+suffix)) (lane : Fin b) (digit : Fin d)
    (wrong : ((OwnedLinearSoundness.originalSources
        (OwnedDecompositionSoundness.stage inputRoot digits (radix : ZMod p) s) dummy capacity radius owner)
          (DecompositionLinear.digit digit) cell lane).val ≠
      ((OwnedLinearSoundness.originalSources
        (OwnedDecompositionSoundness.stage inputRoot digits (radix : ZMod p) s) dummy capacity radius owner)
          DecompositionLinear.input cell lane).val / radix^digit.val % radix)
    (passes : AuthenticatedLinear.accepted outcome.2.1 = true) :
    OwnedLinearSoundness.OriginalRisk (OwnedDecompositionSoundness.stage inputRoot digits (radix : ZMod p) s)
      dummy capacity radius outcome ∨
    ∃ limb, ∀ index, RadixLookupSources.tuple
      (OwnedLinearSoundness.originalSources (OwnedDecompositionSoundness.stage inputRoot digits (radix : ZMod p) s)
        dummy capacity radius owner) limb cell lane ≠
      RadixLookupSources.publicTable p radix (RadixCanonicity.modulusDigit p radix limb.val) index := by
  rcases RadixLookupSources.digit_failure_coverage radixLarge radixSmall enough _ cell lane digit wrong with failed | comparison
  · refine Or.inl ⟨owner,recorded,?_,passes⟩
    intro holds
    exact failed ((OwnedDecompositionSoundness.original_relation_iff inputRoot digits (radix : ZMod p) s
      dummy capacity radius owner).mp holds)
  · exact Or.inr comparison

end
end FormalProof4FHE.HasteBoots.OwnedRadixCoverage
