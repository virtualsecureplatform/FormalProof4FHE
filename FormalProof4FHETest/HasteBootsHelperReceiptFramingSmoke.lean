module
import all FormalProof4FHE.HasteBoots.ParentDerivedIdentityWork
import all FormalProof4FHETest.HasteBootsHelperFramingSmoke

namespace HasteBootsHelperReceiptFramingSmoke
open FormalProof4FHE.HasteBoots
open HasteBootsCausalPcsSmoke
open HasteBootsHelperFramingSmoke (calls_fit parent_framed)
open NativePcsClaimSmoke (parent blockTables retainedParameters)
noncomputable section

theorem completed_valid : HelperReceiptFramingRecovery.ValidProgress blockTables retainedParameters 18
    (helpers 6 false).1.progress :=
  HelperReceiptFramingRecovery.trace_framed
    (NativeGoldHelperVerification.loop_trace blockTables retainedParameters 18 (select false) 6 calls ⟨parent,(),[]⟩ NativePcsClaimSmoke.Canonical.world)
    calls_fit ⟨parent_framed,by simp⟩

def receipt := (helpers 6 false).1.progress.receipts[0]'(by decide +kernel)

theorem original_receipt_framed : SingleOpeningAvailability.Framed
    (NativeGoldHelperVerification.context blockTables retainedParameters 18 receipt.before receipt.call) :=
  completed_valid.2 receipt (List.getElem_mem (by decide +kernel))

theorem receipt_checked : NativeGoldHelperVerification.Checked blockTables retainedParameters 18 (select false) 6
    NativePcsClaimSmoke.Canonical.world receipt := by
  have trace := NativeGoldHelperVerification.loop_trace blockTables retainedParameters 18 (select false) 6 calls
    ⟨parent,(),[]⟩ NativePcsClaimSmoke.Canonical.world
  rcases trace.receipts receipt (List.getElem_mem (by decide +kernel)) with impossible | ⟨checked,_⟩
  · cases impossible
  · exact checked

theorem metadata_from_actual_prefix :
    (NativeGoldPcsWire.opening receipt.call.root receipt.call.query receipt.call.values).length < TranscriptFrame.lengthLimit :=
  HelperReceiptFramingRecovery.receipt_metadata_fits blockTables retainedParameters 18 (select false) 6
    NativePcsClaimSmoke.Canonical.world receipt receipt_checked (by decide +kernel)

theorem stopped_retains_framing : HelperReceiptFramingRecovery.ValidProgress blockTables retainedParameters 18 repeated.1.progress := by
  apply HelperReceiptFramingRecovery.trace_framed
    (NativeGoldHelperVerification.loop_trace blockTables retainedParameters 18 (select false) 6 (calls++calls)
      ⟨parent,(),[]⟩ NativePcsClaimSmoke.Canonical.world)
  · intro call member
    rcases List.mem_append.mp member with first | second
    · exact calls_fit call first
    · exact calls_fit call second
  · exact ⟨parent_framed,by simp⟩

theorem stopped_has_original_receipt : repeated.1.progress.receipts.length = 1 := by decide +kernel

theorem canceled_valid : HelperReceiptFramingRecovery.ValidProgress blockTables retainedParameters 18
    (helpers 6 true).1.progress :=
  HelperReceiptFramingRecovery.trace_framed
    (NativeGoldHelperVerification.loop_trace blockTables retainedParameters 18 (select true) 6 calls ⟨parent,(),[]⟩ NativePcsClaimSmoke.Canonical.world)
    calls_fit ⟨parent_framed,by simp⟩

theorem canceled_has_no_receipt : (helpers 6 true).1.progress.receipts = [] := by decide +kernel

theorem registry_boundary_arithmetic : 9+128*(2^57-1) < (2^64 : ℕ) ∧ ¬128*2^57 < (2^64 : ℕ) := by decide +kernel

def oversizedMatrix : NativeGoldPcsWire.Matrix := ⟨⟨3,by decide⟩,⟨List.replicate 17 0,by decide⟩⟩

theorem oversized_matrix_rejected : NativeGoldMatrix.validate oversizedMatrix.model 3 = false := by decide +kernel

theorem variable_boundary_rejected : NativeBrakedownParameters.basic
    {retainedParameters with numVariables := ⟨64,by decide⟩} = false := by decide +kernel

end
end HasteBootsHelperReceiptFramingSmoke
