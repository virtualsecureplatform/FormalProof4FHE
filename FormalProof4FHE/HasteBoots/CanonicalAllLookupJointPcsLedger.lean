module
public import FormalProof4FHE.HasteBoots.PrivateCoinAllLookupChallengeProbability
@[expose] public section

/-! All original lookup challenge events, reference failures and original PCS failures
share one whole-execution root/hash ledger and one set of PCS charges. -/
namespace FormalProof4FHE.HasteBoots.CanonicalAllLookupJointPcsLedger
open MeasureTheory
open InputIndexedOracle (Input World law)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction)
open InterpreterScalarLifetime (privateProgram)
open NativeRootMessage (Digest)
open PrivateCoinJointPcsLedger (Pcs pcs_outside_hash)
noncomputable section

variable {I : Type} (HelperMemory SourceMemory : Type) (code : List Instruction) (publicData : Input)
  (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)
  (helper : NativeGoldPcsExecution.Context) (source : I → NativeGoldBatchPcsProgram.Context)
  (sourceOrigin : (i : I) → CacheBackedCodeOrigin.Origin (source i)) (helperRadius : ℕ) (sourceRadius : I → ℕ)

theorem bound (coins : Measure Tape) :
    (coins.prod law) {execution | (∃ fuel, PrivateCoinAllLookupChallengeProbability.Event code publicData privateData dummy fuel execution) ∨
      (∃ fuel, GlobalReferenceBad.Bad (privateProgram code publicData execution.1 privateData fuel) dummy execution.2) ∨
      Pcs HelperMemory SourceMemory code publicData privateData dummy helper source sourceOrigin helperRadius sourceRadius execution} ≤
      (coins.prod law) {execution | PrivateCoinSharedHash.Other code publicData privateData execution} +
      (coins.prod law) {execution | (∃ fuel, OpeningLifetimeFamily.Failure HelperMemory SourceMemory dummy helper source sourceOrigin helperRadius sourceRadius
        (privateProgram code publicData execution.1 privateData fuel) OracleProgramMachine.step execution.2) ∧
        ¬∃ fuel, PrivateCoinSharedHash.Root code publicData privateData dummy fuel execution} +
      PrivateCoinByteWork.expectedWork coins code publicData privateData * (PrivateCoinSharedHash.rate+PrivateCoinAllLookupChallengeProbability.rate) := by
  let root := {execution : Tape × World | ∃ fuel, PrivateCoinSharedHash.Root code publicData privateData dummy fuel execution}
  let other := {execution : Tape × World | PrivateCoinSharedHash.Other code publicData privateData execution}
  let residual := {execution : Tape × World | (∃ fuel, OpeningLifetimeFamily.Failure HelperMemory SourceMemory dummy helper source sourceOrigin helperRadius sourceRadius
    (privateProgram code publicData execution.1 privateData fuel) OracleProgramMachine.step execution.2) ∧ execution ∉ root}
  let scalar := {execution : Tape × World | (∃ fuel, PrivateCoinAllLookupChallengeProbability.Event code publicData privateData dummy fuel execution) ∧
    ¬∃ fuel, PrivateCoinAllLookupChallengeProbability.Bad code publicData privateData dummy fuel execution}
  have included : {execution | (∃ fuel, PrivateCoinAllLookupChallengeProbability.Event code publicData privateData dummy fuel execution) ∨
      (∃ fuel, GlobalReferenceBad.Bad (privateProgram code publicData execution.1 privateData fuel) dummy execution.2) ∨
      Pcs HelperMemory SourceMemory code publicData privateData dummy helper source sourceOrigin helperRadius sourceRadius execution} ⊆
      (other ∪ residual) ∪ (root ∪ scalar) := by
    intro execution occurred
    by_cases hash : execution ∈ root
    · exact Or.inr (Or.inl hash)
    rcases occurred with healing | reference | pcs
    · by_cases bad : PrivateCoinSharedHash.Other code publicData privateData execution
      · exact Or.inl (Or.inl bad)
      · refine Or.inr (Or.inr ⟨healing,?_⟩)
        change ¬∃ fuel, PrivateCoinScalarProbability.Bad code publicData privateData dummy fuel execution
        rw [PrivateCoinSharedHash.bad_split]
        exact not_or_intro hash bad
    · have split : ∃ fuel, PrivateCoinScalarProbability.Bad code publicData privateData dummy fuel execution := reference
      rw [PrivateCoinSharedHash.bad_split] at split
      exact Or.inl (Or.inl (split.resolve_left hash))
    · exact Or.inl (Or.inr ⟨(pcs_outside_hash HelperMemory SourceMemory code publicData privateData dummy helper source sourceOrigin helperRadius sourceRadius execution hash).mp pcs,hash⟩)
  apply (measure_mono included).trans
  calc
    _ ≤ ((coins.prod law) other + (coins.prod law) residual) +
        (PrivateCoinByteWork.expectedWork coins code publicData privateData * PrivateCoinSharedHash.rate +
          PrivateCoinByteWork.expectedWork coins code publicData privateData * PrivateCoinAllLookupChallengeProbability.rate) :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _)
        ((measure_union_le _ _).trans (add_le_add (PrivateCoinSharedHash.lifetime_bound coins code publicData privateData dummy)
          (PrivateCoinAllLookupChallengeProbability.safe_bound coins code publicData privateData dummy))))
    _ = _ := by rw [mul_add]; rfl

end
end FormalProof4FHE.HasteBoots.CanonicalAllLookupJointPcsLedger
