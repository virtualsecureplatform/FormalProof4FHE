module
import all FormalProof4FHE.HasteBoots.GoldRecoveredSourceTableIdentity
import all FormalProof4FHETest.HasteBootsFieldInputSmoke

namespace FormalProof4FHE.HasteBoots.SourceLogIdentitySmoke
open HasteBootsBatchMeaningSmoke (root usize query zeros)
open NativeTranscript (Observation)
open NativeRootFamilySourceSelection (Log)
noncomputable section

abbrev batch := HasteBootsFieldInputSmoke.view
def another : NativeGoldBatchFieldInputView.View := {batch with count := usize 1}
def single : SingleOpeningFieldInputView.View := ⟨[],⟨batch.data.context,batch.data.root,query,zeros 3 (by decide)⟩,usize 1⟩
def firstInput := NativeGoldBatchFirstFieldSource.input batch
def anotherInput := NativeGoldBatchFirstFieldSource.input another
def singleInput := SingleOpeningFirstFieldSource.input single

theorem batchParsed : NativeGoldBatchFieldInputView.parse firstInput = some batch := by
  have same := (NativeGoldBatchFieldInputView.parse_sound _ batch HasteBootsFieldInputSmoke.decoded root).1
  rw [NativeGoldBatchFieldInputView.phase_input] at same
  change NativeGoldBatchFieldInputView.parse (TranscriptFrame.encodeMany batch.frames) = some batch
  rw [same]
  exact HasteBootsFieldInputSmoke.decoded

theorem anotherParsed : NativeGoldBatchFieldInputView.parse anotherInput = some another := by
  have parsed := NativeGoldBatchFieldInputView.parse_native another root (by decide +kernel) (by
    have originalValid := (NativeGoldBatchFieldInputView.parse_sound _ batch HasteBootsFieldInputSmoke.decoded root).2.2
    intro frame member
    change frame ∈ batch.before ++ [NativeGoldBatchFieldInputView.batchFrame batch.data,NativeGoldBatchFieldInputView.typedFrame,
      NativeGoldBatchFieldInputView.primeFrame,NativeGoldBatchFieldInputView.fieldFrame (usize 1)] at member
    rcases List.mem_append.mp member with earlier | suffix
    · exact originalValid frame (List.mem_append_left _ earlier)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at suffix
      rcases suffix with rfl | rfl | rfl | rfl
      all_goals unfold TranscriptFrame.Valid; decide +kernel)
  rw [NativeGoldBatchFieldInputView.phase_input] at parsed
  exact parsed

theorem singleParsed : SingleOpeningFieldInputView.parse singleInput = some single := by
  have parsed := SingleOpeningFieldInputView.parse_native single root (by decide +kernel) (by
    intro frame member
    change frame ∈ [SingleOpeningFieldInputView.contextFrame single.data,SingleOpeningFieldInputView.openingFrame single.data,
      SingleOpeningFieldInputView.typedFrame,SingleOpeningFieldInputView.primeFrame,SingleOpeningFieldInputView.fieldFrame single.count] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals unfold TranscriptFrame.Valid; decide +kernel)
  rw [SingleOpeningFieldInputView.phase_input] at parsed
  exact parsed

/-- Distinct stream inputs still mention one complete context/root key. -/
example : firstInput ≠ anotherInput ∧ firstInput ≠ singleInput ∧ anotherInput ≠ singleInput := by decide +kernel

def before : List Observation := [.hash [10] (List.ofFn root)]
def middle : List Observation := [.hash [11] (List.ofFn root),.output firstInput 17 []]
def history : List Observation := before ++ [.output firstInput 99 [0]] ++ middle ++
  [.output singleInput 7 [0],.output anotherInput 3 [0],.hash [12] (List.ofFn root)]
def original : Log := [⟨[10],root⟩]

theorem firstRecovered : NativeGoldBatchFirstFieldSource.recover root history batch = some original := by
  have atRead := NativeGoldBatchFirstFieldSource.recover_at root before
    (middle ++ [.output singleInput 7 [0],.output anotherInput 3 [0],.hash [12] (List.ofFn root)]) batch 99 [0]
    (by decide +kernel) (by decide)
  have selected : NativeGoldBatchSelectedSource.log root before batch = original := by
    rw [NativeGoldBatchSelectedSource.log,NativeRootFamilySourceSelection.select_new _ _ (by decide +kernel)]
    change (NativeGoldBatchFamilyAvailability.reconstructed root before).hash.log = original
    rw [NativeGoldBatchFamilyAvailability.reconstructed_hash]
    simp only [before,JointHashCache.project,List.foldl_cons,List.foldl_nil,JointHashCache.record,
      CachedHashHandler.observe,CachedHashHandler.empty,JointHashCache.decode_ofFn,List.nil_append,original]
  simpa only [history,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append,firstInput,selected] using atRead

/-- A later single stream recovers the earlier batch owner's exact old log. -/
example : SingleOpeningFirstFieldSource.recover root history single = some original := by
  obtain ⟨sourceLog,recovered⟩ := SingleOpeningFirstFieldSource.recover_exists root history single (by decide +kernel)
  have same := SourceSnapshotLogIdentity.single_batch root history single batch singleParsed batchParsed rfl rfl
    sourceLog original recovered firstRecovered
  exact recovered.trans (congrArg some same)

/-- A later batch stream with a different request count cannot choose a new
snapshot after the intervening hash. -/
example : NativeGoldBatchFirstFieldSource.recover root history another = some original := by
  obtain ⟨sourceLog,recovered⟩ := NativeGoldBatchFirstFieldSource.recover_exists root history another (by decide +kernel)
  have same := SourceSnapshotLogIdentity.batches root history another batch anotherParsed batchParsed rfl rfl
    sourceLog original recovered firstRecovered
  exact recovered.trans (congrArg some same)

/-- The current hash log contains later work; it is not the selected source. -/
example : (NativeGoldBatchFamilyAvailability.reconstructed root history).hash.log.length = 3 ∧ original.length = 1 := by
  rw [NativeGoldBatchFamilyAvailability.reconstructed_hash]
  decide +kernel

/-- Zero-byte outputs do not supply the first positive field read. -/
example : NativeGoldBatchFirstFieldSource.recover root [ .output anotherInput 3 [] ] another = none := by decide +kernel

/-- Later observations preserve the already recovered exact log. -/
example (suffix : List Observation) : NativeGoldBatchFirstFieldSource.recover root (history++suffix) batch = some original :=
  NativeGoldBatchFirstFieldSource.recover_append root history suffix batch original firstRecovered

end
end FormalProof4FHE.HasteBoots.SourceLogIdentitySmoke
