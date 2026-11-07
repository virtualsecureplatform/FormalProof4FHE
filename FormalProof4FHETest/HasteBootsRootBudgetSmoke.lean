module
import all FormalProof4FHE.HasteBoots.ClosedByteMachineRootBudget
import all FormalProof4FHETest.HasteBootsShapeFamilySmoke
import all FormalProof4FHETest.HasteBootsParentRootFreezeSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World)
open NativeTranscript (Observation)
open OracleSpec OracleComp
namespace HasteBootsRootBudgetSmoke
noncomputable section

open HasteBootsBatchExposureSmoke (dummy input first)
example : (NativeRootFamilyBudget.ledger dummy first).frozen.card = 1 := by
  have counted := NativeRootFamilyBudget.reconstructed_count dummy first
  have concrete : (NativeGoldBatchFamilyAvailability.reconstructed dummy first).checkpoints.checkpoints.length = 64 := by decide +kernel
  rw [concrete] at counted
  omega
example : (NativeGoldBatchFamilyAvailability.reconstructed dummy
    (first ++ [.output input 0 [1,2]])).checkpoints.checkpoints.length =
      64*(NativeRootFamilyBudget.ledger dummy (first ++ [.output input 0 [1,2]])).frozen.card :=
  NativeRootFamilyBudget.reconstructed_count _ _
example : (NativeRootFamilyBudget.ledger dummy (first ++ [.output input 0 [1,2]])).frozen.card = 1 := by
  have counted := NativeRootFamilyBudget.reconstructed_count dummy (first ++ [.output input 0 [1,2]])
  have concrete : (NativeGoldBatchFamilyAvailability.reconstructed dummy
      (first ++ [.output input 0 [1,2]])).checkpoints.checkpoints.length = 64 := by decide +kernel
  rw [concrete] at counted
  omega

-- Both compatible parents remain valid even with an entirely unknown seed.
open HasteBootsParentRootFreezeSmoke (ledger context root child)
def pools : NativeParentLedgerPools.Pools := ⟨{context,root},∅⟩
theorem coherent : NativeParentLedgerPools.Coherent ledger pools := by
  simp [NativeParentLedgerPools.Coherent,HasteBootsParentRootFreezeSmoke.ledger,
    HasteBootsParentRootFreezeSmoke.parent,HasteBootsParentRootFreezeSmoke.other,pools]
example (key : NativeCanonicalLookupWire.Source)
    (resolved : key ∈ NativeParentLedger.resolve ledger NativeShakeCache.empty child) :
    key ∈ NativeParentLedgerPools.sources (NativeParentLedgerPools.grow pools child) :=
  NativeParentLedgerPools.resolve_mem ledger NativeShakeCache.empty pools child coherent key resolved

-- A forged vector count with no serialized source body is not a mention.
example : NativeRootInputView.frameSources ⟨1,NativeCanonicalLookupWire.registryLabel,[1]⟩ = none := by decide +kernel
example (sources : NativePrefixCodec.Vector NativeCanonicalLookupWire.Source) :
    sources.val.length ≤ (NativeCanonicalLookupWire.sourcesCodec.encode sources).length :=
  NativeRootMentionSize.source_vector_size sources

-- Empty-input hashes still cost work and populate a key despite zero input bytes.
example (world : World) : ClosedByteMachineRootBudget.inputWork
    [.hash [] (List.ofFn (InputIndexedOracle.sha512 world []))] = 0 := rfl
example (world : World) : (JointHashCache.project
    [.hash [] (List.ofFn (InputIndexedOracle.sha512 world []))]).keys.card = 1 := by
  simp only [JointHashCache.project,List.foldl_cons,List.foldl_nil,JointHashCache.record,
    CachedHashHandler.observe,CachedHashHandler.empty,Finset.insert_empty,Finset.card_singleton]

example (code : List ClosedByteMachine.Instruction) (publicData : Input) (fuel : ℕ)
    (state : ClosedByteMachine.State) (world : World) (query : Input) :
    let history := (OracleProgram.run (ClosedByteMachine.take code publicData fuel state) world).run.2
    let work := (OracleProgram.run (ClosedByteMachine.take code publicData fuel state) world).run.1.work
    CheckpointCollision.loss unifSpec NativeMerkleShapeFamily.shape (.inr (.inl query))
      (NativeGoldBatchFamilyAvailability.reconstructed dummy history) ≤
        ((3*work+256*work*work : ℕ) : ENNReal)/(2 : ENNReal)^512 :=
  ClosedByteMachineRootBudget.hash_loss_le_work code publicData fuel state world dummy query
end
end HasteBootsRootBudgetSmoke
