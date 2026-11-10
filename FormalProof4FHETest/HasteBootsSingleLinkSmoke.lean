module
import all FormalProof4FHE.HasteBoots.SingleOpeningPreparedChallenge
import all FormalProof4FHE.HasteBoots.SingleOpeningFirstFieldSource
import all FormalProof4FHETest.HasteBootsSingleChallengeSmoke
import all Init.Data.String.Defs

namespace FormalProof4FHE.HasteBoots.SingleLinkSmoke
open InputIndexedOracle (Input)
open NativeTranscript (Observation)
open SingleChallengeSmoke (zero lazyZero)

def field := SingleChallengeSmoke.view
def opening : NativeGoldPcsOpening.Opening := ⟨lazyZero,zero,⟨[],by decide⟩⟩
def quote : Input := List.replicate 80 0
def nonce (receipt : Input) : Input := SingleOpeningPreparedChallenge.input field (fun _ => 0) opening
  NativeGoldPcsColumns.label ⟨8,by decide⟩ ⟨2,by decide⟩ receipt

def withReceiptFrame (frame : TranscriptFrame.Frame) : Input := SingleOpeningColumnLaw.boundInput
  ⟨TranscriptFrame.encodeMany (field.frames++[frame]),fun _ => 0⟩ NativeGoldPcsColumns.label ⟨8,by decide⟩ ⟨2,by decide⟩ opening

/-- Structural parsing retains the quote; it does not assert receipt truth. -/
example : (SingleOpeningChallengeLink.parse (nonce quote)).map
    (fun parsed => (parsed.field.data.root 0,parsed.field.count.val,parsed.column.index.count.val,
      parsed.receipt.length,parsed.column.opening.evaluation.val.map Fin.val)) = some (7,1,2,80,[0]) := by decide +kernel

example : (SingleOpeningChallengeLink.parse (nonce (List.replicate 79 0))).isNone = true := by decide +kernel
example : (SingleOpeningChallengeLink.parse (nonce (List.replicate 81 0))).isNone = true := by decide +kernel

/-- A batch receipt label cannot stand in for the original single receipt. -/
example : (SingleOpeningChallengeLink.parse (withReceiptFrame ⟨5,NativeGoldBatchPrelude.randomLabel,quote⟩)).isNone = true := by decide +kernel

/-- An earlier receipt is not found by scanning across an intervening frame. -/
example : (SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.boundInput
    ⟨TranscriptFrame.encodeMany (field.frames++[SingleOpeningChallengeLink.receiptFrame quote,⟨1,[],[]⟩]),fun _ => 0⟩
    NativeGoldPcsColumns.label ⟨8,by decide⟩ ⟨2,by decide⟩ opening)).isNone = true := by decide +kernel

example : (SingleOpeningColumnInputView.readResponse {SingleOpeningColumnInputView.responseFrame opening with
    message := (SingleOpeningColumnInputView.responseFrame opening).message++[0]}).isNone = true := by decide +kernel

/-- Off-path exposure at a far offset freezes the earlier source hash log. -/
def before : List Observation := [.hash [9] (List.replicate 64 3)]
def history : List Observation := before ++ [.output (SingleOpeningFirstFieldSource.input field) 63 [1],
  .hash [10] (List.replicate 64 5),.output (SingleOpeningFirstFieldSource.input field) 0 [2]]

example : (SingleOpeningFirstFieldSource.recover (fun _ => 0) history field).map List.length = some 1 := by decide +kernel

/-- Later hashes/reads retain that same original pre-read source. -/
example : (SingleOpeningFirstFieldSource.recover (fun _ => 0)
    (history++[.hash [11] (List.replicate 64 6),.output (SingleOpeningFirstFieldSource.input field) 0 [2]]) field).map List.length = some 1 := by decide +kernel

/-- Starts and empty reads do not freeze the stream before its first byte. -/
def emptyPrefix : List Observation := before++[.start (SingleOpeningFirstFieldSource.input field),
  .output (SingleOpeningFirstFieldSource.input field) 0 [],.hash [10] (List.replicate 64 5)]

example : (SingleOpeningFirstFieldSource.recover (fun _ => 0)
    (emptyPrefix++[.output (SingleOpeningFirstFieldSource.input field) 0 [2]]) field).map List.length = some 2 := by
  have unseen : CausalStreamExposure.seen emptyPrefix (SingleOpeningFirstFieldSource.input field) = false := by
    simp [emptyPrefix,before,CausalStreamExposure.seen,CausalStreamExposure.touches]
  have recovered := SingleOpeningFirstFieldSource.recover_at (fun _ => 0) emptyPrefix [] field 0 [2] unseen (by decide)
  rw [recovered,Option.map_some]
  apply congrArg some
  change (NativeRootFamilySourceSelection.select
    (NativeRootFamilyHistory.reconstruct NativeGoldColumnAuthentication.encoding (fun _ => 0) emptyPrefix)
    (field.data.context,field.data.root)).length = 2
  have fresh : (field.data.context,field.data.root) ∉
      (NativeRootFamilyHistory.reconstruct NativeGoldColumnAuthentication.encoding (fun _ => 0) emptyPrefix).1.1.frozen := by
    simp only [NativeRootFamilyHistory.reconstruct,emptyPrefix,before,List.foldl_append,List.foldl_cons,List.foldl_nil,
      NativeRootFamilyState.record,NativeParentHistory.record,NativeParentLedger.discover_frozen,
      NativeRootFamilyHistory.initial,NativeParentLedger.empty,ite_true,Finset.notMem_empty]
    exact id
  rw [NativeRootFamilySourceSelection.select_new _ _ fresh]
  have hashes : (NativeRootFamilyHistory.reconstruct NativeGoldColumnAuthentication.encoding (fun _ => 0) emptyPrefix).2.hash =
      JointHashCache.project emptyPrefix := NativeGoldBatchFamilyAvailability.reconstructed_hash _ _
  rw [hashes]
  decide +kernel

end FormalProof4FHE.HasteBoots.SingleLinkSmoke
