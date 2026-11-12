module
public import FormalProof4FHE.HasteBoots.PrivateCoinJointPcsLedger
@[expose] public section

/-! Include an original source family in a larger indexed family without a
probability union. Exact source contexts and constructor origins are kept. -/
namespace FormalProof4FHE.HasteBoots.LookupPcsFamilyInclusion
open InputIndexedOracle (Input World)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction)
noncomputable section

theorem include_family {I J : Type} (HelperMemory SourceMemory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : NativeRootMessage.Digest)
    (helper : NativeGoldPcsExecution.Context) (source : J → NativeGoldBatchPcsProgram.Context)
    (origin : (index : J) → CacheBackedCodeOrigin.Origin (source index)) (helperRadius : ℕ) (sourceRadius : J → ℕ)
    (embed : I → J) (execution : Tape × World)
    (failed : PrivateCoinJointPcsLedger.Pcs HelperMemory SourceMemory code publicData privateData dummy helper
      (fun index => source (embed index)) (fun index => origin (embed index)) helperRadius (fun index => sourceRadius (embed index)) execution) :
    PrivateCoinJointPcsLedger.Pcs HelperMemory SourceMemory code publicData privateData dummy helper source origin helperRadius sourceRadius execution := by
  obtain ⟨fuel,hash | helper | ⟨index,batch⟩⟩ := failed
  · exact ⟨fuel,Or.inl hash⟩
  · exact ⟨fuel,Or.inr (Or.inl helper)⟩
  · exact ⟨fuel,Or.inr (Or.inr ⟨embed index,batch⟩)⟩

end
end FormalProof4FHE.HasteBoots.LookupPcsFamilyInclusion
