module
public import FormalProof4FHE.HasteBoots.ScalarLifetimeComposition
@[expose] public section

/-! Scalar healing and source/helper PCS families share the same full-history
hash alternative. Global non-root bad events are charged once, before the
adaptive scalar union, with no successful-run mass denominator. -/
namespace FormalProof4FHE.HasteBoots.JointIdentityLifetimeBound
open InputIndexedOracle (World law)
open OracleProgram (Program)
open NativeRootMessage (Digest)
open SingleOpeningLifetimeSoundness (clean SourceBad)
open MeasureTheory
noncomputable section

theorem bound {I A : Type} [Countable I] (HelperMemory SourceMemory : Type) (dummy : Digest) (program : Program A)
    (helper : NativeGoldPcsExecution.Context) (helperOrigin : CacheBackedSingleOpening.Origin helper)
    (source : I → NativeGoldBatchPcsProgram.Context) (sourceOrigin : (i : I) → CacheBackedCodeOrigin.Origin (source i))
    (scalarRadius helperRadius : ℕ) (sourceRadius : I → ℕ)
    (helperWidth : 3 ≤ helper.parameters.width.val) (sourceWidth : ∀ i, 3 ≤ (source i).parameters.width.val)
    (helperSmall : 3*helperRadius < helper.parameters.code.blocks.val-helper.parameters.code.messageBlocks.val+1)
    (sourceSmall : ∀ i, 3*sourceRadius i < (source i).parameters.code.blocks.val-(source i).parameters.code.messageBlocks.val+1) :
    law {world | ScalarLifetimeComposition.Event program dummy scalarRadius world ∨
      SourceBad dummy (clean program) id OracleProgramMachine.step world ∨
      OpeningLifetimeFamily.Failure HelperMemory SourceMemory dummy helper source sourceOrigin helperRadius sourceRadius program OracleProgramMachine.step world} ≤
      ((⨆ fuel : ℕ, NativeRootFamilyLifetime.prefixCharge dummy (.pure program) OracleProgramMachine.step fuel) +
        (SingleOpeningLifetimeSoundness.exposureCharge (clean program) id dummy helper helperOrigin helperRadius OracleProgramMachine.step +
          ∑' i, NativeGoldBatchLifetimeSoundness.exposureCharge (clean program) id dummy (source i) ((sourceOrigin i).primitiveAt _ rfl)
            (sourceRadius i) OracleProgramMachine.step)) +
      (GlobalReferenceBad.otherCharge program + ∫⁻ world, ScalarLifetimeComposition.totalCharge program world ∂law) := by
  have included : {world | ScalarLifetimeComposition.Event program dummy scalarRadius world ∨
        SourceBad dummy (clean program) id OracleProgramMachine.step world ∨
        OpeningLifetimeFamily.Failure HelperMemory SourceMemory dummy helper source sourceOrigin helperRadius sourceRadius program OracleProgramMachine.step world} ⊆
      {world | SourceBad dummy (clean program) id OracleProgramMachine.step world ∨
        OpeningLifetimeFamily.Failure HelperMemory SourceMemory dummy helper source sourceOrigin helperRadius sourceRadius program OracleProgramMachine.step world} ∪
      ({world | GlobalReferenceBad.OtherBad program world} ∪
        {world | ScalarLifetimeComposition.Event program dummy scalarRadius world ∧ ¬GlobalReferenceBad.Bad program dummy world}) := by
    intro world occurred
    rcases occurred with scalar | bad | pcs
    · by_cases bad : GlobalReferenceBad.Bad program dummy world
      · rcases bad with root | other
        · exact Or.inl (Or.inl (ProgramOpeningLifetime.root_bad program world dummy root))
        · exact Or.inr (Or.inl other)
      · exact Or.inr (Or.inr ⟨scalar,bad⟩)
    · exact Or.inl (Or.inl bad)
    · exact Or.inl (Or.inr pcs)
  exact (measure_mono included).trans ((measure_union_le _ _).trans (add_le_add
    (OpeningLifetimeFamily.bound HelperMemory SourceMemory dummy helper helperOrigin source sourceOrigin helperRadius sourceRadius helperWidth sourceWidth
      program OracleProgramMachine.step helperSmall sourceSmall)
    ((measure_union_le _ _).trans (add_le_add (GlobalReferenceBad.other_le program) (ScalarLifetimeComposition.safe_bound program dummy scalarRadius)))))

end
end FormalProof4FHE.HasteBoots.JointIdentityLifetimeBound
