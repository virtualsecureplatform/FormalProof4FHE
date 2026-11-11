module
public import FormalProof4FHE.HasteBoots.ReceiptFrameView
public import FormalProof4FHE.HasteBoots.NativeFreshReceiptDigest
@[expose] public section

/-! Full receipt-digest targets named by earlier positive transcript-key reads
or hash queries. Starts and empty reads add no targets. Input-length bounds
are finite syntax bounds, not physical attacker-work claims. -/
namespace FormalProof4FHE.HasteBoots.ReceiptDigestTargets
open InputIndexedOracle (Input World)
open NativeTranscript (Observation)
open NativeRootMessage (Digest)
open scoped Classical
noncomputable section

def fromInput (input : Input) : List Digest :=
  (ReceiptFrameView.frames input).filterMap (fun entry =>
    if entry.message.length = 80 then some (NativeFreshReceiptDigest.digest entry.message) else none)

/-- Receipt query keys are outside the framed transcript language, so naming
a receipt key does not manufacture digest targets from its raw payload. -/
theorem from_receipt_key (raw : Input) : fromInput (NativeReceiptPrefixView.key raw) = [] := by
  simp only [fromInput,ReceiptFrameView.frames,
    show NativeReceiptPrefixView.key raw = NativeTranscript.utf8 "HasteBoots consumed field bytes v1" ++ raw from rfl,
    NativeTranscript.receipt_decode_rejected,Option.getD_none,List.filter_nil,List.filterMap_nil]

def candidate : Observation → List Digest
  | .start _ => []
  | .output input _ values => if values = [] then [] else fromInput input
  | .hash input _ => fromInput input

def targets (history : List Observation) : Finset Digest := (history.flatMap candidate).toFinset

theorem native_in_input (input : Input) (world : World) (phase : NativeTranscript.FieldPhase)
    (member : ReceiptFrameView.frame world phase ∈ ReceiptFrameView.frames input) :
    InputIndexedOracle.block world (NativeReceiptPrefixView.key phase.consumed) 0 64 ∈ fromInput input := by
  apply List.mem_filterMap.mpr
  refine ⟨_,member,?_⟩
  rw [show (ReceiptFrameView.frame world phase).message.length = 80 from NativeTranscript.receipt_length world phase.consumed]
  simp only [ite_true,ReceiptFrameView.frame,NativeFreshReceiptDigest.digest_receipt]

theorem observed (input values : Input) (offset : ℕ) (world : World) (phase : NativeTranscript.FieldPhase)
    (history : List Observation) (positive : values ≠ [])
    (present : .output input offset values ∈ history)
    (member : ReceiptFrameView.frame world phase ∈ ReceiptFrameView.frames input) :
    InputIndexedOracle.block world (NativeReceiptPrefixView.key phase.consumed) 0 64 ∈ targets history := by
  apply List.mem_toFinset.mpr
  apply List.mem_flatMap.mpr
  exact ⟨_,present,by simpa only [candidate,positive,ite_false] using native_in_input input world phase member⟩

theorem hashed (input digest : Input) (world : World) (phase : NativeTranscript.FieldPhase)
    (history : List Observation) (present : .hash input digest ∈ history)
    (member : ReceiptFrameView.frame world phase ∈ ReceiptFrameView.frames input) :
    InputIndexedOracle.block world (NativeReceiptPrefixView.key phase.consumed) 0 64 ∈ targets history := by
  apply List.mem_toFinset.mpr
  exact List.mem_flatMap.mpr ⟨_,present,native_in_input input world phase member⟩

theorem append (earlier later : List Observation) : targets (earlier ++ later) = targets earlier ∪ targets later := by
  simp only [targets,List.flatMap_append,List.toFinset_append]

private theorem encoded_length (entries : List TranscriptFrame.Frame) :
    entries.length ≤ (TranscriptFrame.encodeMany entries).length := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp only [List.length_cons,TranscriptFrame.encodeMany,List.length_append,TranscriptFrame.encode_length]
    omega

theorem decoded_length (input : Input) : ((TranscriptFrame.decodeAll input).getD []).length ≤ input.length := by
  cases decoded : TranscriptFrame.decodeAll input with
  | none => simp only [Option.getD_none,List.length_nil]; exact Nat.zero_le _
  | some entries =>
    simp only [Option.getD_some]
    rw [(TranscriptFrame.decodeAll_sound input entries decoded).2]
    exact encoded_length entries

theorem input_length (input : Input) : (fromInput input).length ≤ input.length :=
  (List.length_filterMap_le _ _).trans ((List.length_filter_le _ _).trans (decoded_length input))

def namedBytes : Observation → ℕ
  | .start _ => 0
  | .output input _ values => if values = [] then 0 else input.length
  | .hash input _ => input.length

def inputBytes (history : List Observation) : ℕ := (history.map namedBytes).sum

theorem candidate_length (entry : Observation) : (candidate entry).length ≤ namedBytes entry := by
  cases entry with
  | start input => exact Nat.le_refl _
  | hash input digest => exact input_length input
  | output input offset values =>
    by_cases empty : values = []
    · simp only [candidate,namedBytes,empty,ite_true,List.length_nil,le_refl]
    · simpa only [candidate,namedBytes,empty,ite_false] using input_length input

theorem card (history : List Observation) : (targets history).card ≤ inputBytes history := by
  apply (List.toFinset_card_le _).trans
  induction history with
  | nil => exact Nat.le_refl _
  | cons entry rest ih =>
    simp only [List.flatMap_cons,List.length_append,inputBytes,List.map_cons,List.sum_cons] at *
    exact Nat.add_le_add (candidate_length entry) ih

end
end FormalProof4FHE.HasteBoots.ReceiptDigestTargets
