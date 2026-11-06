module
import all FormalProof4FHE.HasteBoots.NativeGoldBatchFamilyAvailability
import all FormalProof4FHETest.HasteBootsBatchExposureSmoke
open FormalProof4FHE.HasteBoots
open NativeMerkleShapeFamily
namespace HasteBootsShapeFamilySmoke
noncomputable section
open HasteBootsBatchExposureSmoke (dummy input first)
def key : NativeCanonicalLookupWire.Source :=
  (HasteBootsSourceGroupsSmoke.nativeDigest,HasteBootsSourceGroupsSmoke.nativeRoot)
example : (family key).length = 64 := family_length key
example (index : Height) : ((key.1,index),key.2) ∈ requests [key] :=
  requests_member [key] key (by simp) index
example : height (key.1,⟨63,by decide⟩) = 63 := rfl
example : (requests [key,key]).length = 128 := by rw [requests_length]; rfl
example : (NativeGoldBatchFamilyAvailability.reconstructed dummy [.start input]).checkpoints.checkpoints.length = 0 := by rfl
example : (NativeGoldBatchFamilyAvailability.reconstructed dummy [.output input 7 []]).checkpoints.checkpoints.length = 0 := by rfl
-- The same captured native read now records every height at its original pre-read log.
example : (NativeGoldBatchFamilyAvailability.reconstructed dummy first).checkpoints.checkpoints.length = 64 := by decide +kernel
-- A repeated positive read does not add or reset any height snapshot.
example : (NativeGoldBatchFamilyAvailability.reconstructed dummy
    (first ++ [.output input 0 [1,2]])).checkpoints.checkpoints.length = 64 := by decide +kernel
example : ((NativeGoldBatchFamilyAvailability.reconstructed dummy
    (first ++ [.output input 0 [1,2]])).checkpoints.checkpoints.all
      (fun checkpoint => checkpoint.2.cumulativeLog.length == 1)) = true := by decide +kernel

example (history : List NativeTranscript.Observation) :
    (NativeGoldBatchFamilyAvailability.reconstructed dummy history).hash = JointHashCache.project history :=
  NativeGoldBatchFamilyAvailability.reconstructed_hash dummy history
example (ctx : NativeGoldBatchPcsProgram.Context) (world : InputIndexedOracle.World)
    (work : NativeGoldBatchPcsProgram.Prepared)
    (executed : (OracleProgram.run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) :
    height (tag key.1 work) = work.geometry.height := tag_height key.1 ctx world work executed
end
end HasteBootsShapeFamilySmoke
