module
public import FormalProof4FHE.HasteBoots.PrivateCoinSharedHash
@[expose] public section

/-! Original helper/source PCS lifetime witnesses and scalar healing share
one actual joint hash ledger. Remaining PCS/non-root probabilities are kept
explicit until their original-execution work calibration is proved. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinJointPcsLedger
open MeasureTheory
open InputIndexedOracle (Input World law)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction)
open InterpreterScalarLifetime (privateProgram)
open NativeRootMessage (Digest)
noncomputable section

variable {I : Type} (HelperMemory SourceMemory : Type) (code : List Instruction) (publicData : Input)
  (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)
  (helper : NativeGoldPcsExecution.Context) (source : I → NativeGoldBatchPcsProgram.Context)
  (sourceOrigin : (i : I) → CacheBackedCodeOrigin.Origin (source i)) (helperRadius : ℕ) (sourceRadius : I → ℕ)

def Pcs (execution : Tape × World) : Prop := ∃ fuel,
  let program := privateProgram code publicData execution.1 privateData fuel
  SingleOpeningLifetimeSoundness.SourceBad dummy (SingleOpeningLifetimeSoundness.clean program) id OracleProgramMachine.step execution.2 ∨
    OpeningLifetimeFamily.Failure HelperMemory SourceMemory dummy helper source sourceOrigin helperRadius sourceRadius program OracleProgramMachine.step execution.2

theorem pcs_outside_hash (execution : Tape × World)
    (safe : ¬∃ fuel, PrivateCoinSharedHash.Root code publicData privateData dummy fuel execution) :
    Pcs HelperMemory SourceMemory code publicData privateData dummy helper source sourceOrigin helperRadius sourceRadius execution ↔
      ∃ fuel, OpeningLifetimeFamily.Failure HelperMemory SourceMemory dummy helper source sourceOrigin helperRadius sourceRadius
        (privateProgram code publicData execution.1 privateData fuel) OracleProgramMachine.step execution.2 := by
  constructor
  · rintro ⟨fuel,bad | failure⟩
    · exact False.elim (safe ⟨fuel,(PrivateCoinSharedHash.source_bad_iff _ dummy execution.2).mp bad⟩)
    · exact ⟨fuel,failure⟩
  · rintro ⟨fuel,failure⟩
    exact ⟨fuel,Or.inr failure⟩

theorem bound (coins : Measure Tape) (scalarRadius : ℕ) :
    (coins.prod law) {execution | (∃ fuel, PrivateCoinScalarProbability.Event code publicData privateData dummy scalarRadius fuel execution) ∨
      Pcs HelperMemory SourceMemory code publicData privateData dummy helper source sourceOrigin helperRadius sourceRadius execution} ≤
      (coins.prod law) {execution | PrivateCoinSharedHash.Other code publicData privateData execution} +
      (coins.prod law) {execution | (∃ fuel, OpeningLifetimeFamily.Failure HelperMemory SourceMemory dummy helper source sourceOrigin helperRadius sourceRadius
        (privateProgram code publicData execution.1 privateData fuel) OracleProgramMachine.step execution.2) ∧
        ¬∃ fuel, PrivateCoinSharedHash.Root code publicData privateData dummy fuel execution} +
      PrivateCoinByteWork.expectedWork coins code publicData privateData * (PrivateCoinSharedHash.rate+ScalarEquationWork.rate) := by
  let root := {execution : Tape × World | ∃ fuel, PrivateCoinSharedHash.Root code publicData privateData dummy fuel execution}
  let other := {execution : Tape × World | PrivateCoinSharedHash.Other code publicData privateData execution}
  let residual := {execution : Tape × World | (∃ fuel, OpeningLifetimeFamily.Failure HelperMemory SourceMemory dummy helper source sourceOrigin helperRadius sourceRadius
    (privateProgram code publicData execution.1 privateData fuel) OracleProgramMachine.step execution.2) ∧ execution ∉ root}
  let scalar := {execution : Tape × World | (∃ fuel, PrivateCoinScalarProbability.Event code publicData privateData dummy scalarRadius fuel execution) ∧
    ¬∃ fuel, PrivateCoinScalarProbability.Bad code publicData privateData dummy fuel execution}
  have included : {execution | (∃ fuel, PrivateCoinScalarProbability.Event code publicData privateData dummy scalarRadius fuel execution) ∨
      Pcs HelperMemory SourceMemory code publicData privateData dummy helper source sourceOrigin helperRadius sourceRadius execution} ⊆
      (other ∪ residual) ∪ (root ∪ scalar) := by
    intro execution occurred
    by_cases hash : execution ∈ root
    · exact Or.inr (Or.inl hash)
    rcases occurred with healing | pcs
    · by_cases bad : PrivateCoinSharedHash.Other code publicData privateData execution
      · exact Or.inl (Or.inl bad)
      · refine Or.inr (Or.inr ⟨healing,?_⟩)
        rw [PrivateCoinSharedHash.bad_split]
        exact not_or_intro hash bad
    · exact Or.inl (Or.inr ⟨(pcs_outside_hash HelperMemory SourceMemory code publicData privateData dummy helper source sourceOrigin helperRadius sourceRadius execution hash).mp pcs,hash⟩)
  apply (measure_mono included).trans
  calc
    _ ≤ ((coins.prod law) other + (coins.prod law) residual) +
        (PrivateCoinByteWork.expectedWork coins code publicData privateData * PrivateCoinSharedHash.rate +
          PrivateCoinByteWork.expectedWork coins code publicData privateData * ScalarEquationWork.rate) :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _)
        ((measure_union_le _ _).trans (add_le_add (PrivateCoinSharedHash.lifetime_bound coins code publicData privateData dummy)
          (PrivateCoinScalarProbability.safe_bound coins code publicData privateData dummy scalarRadius))))
    _ = _ := by rw [mul_add]; rfl

end
end FormalProof4FHE.HasteBoots.PrivateCoinJointPcsLedger
