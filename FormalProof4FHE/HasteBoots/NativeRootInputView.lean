module
public import FormalProof4FHE.HasteBoots.NativeCanonicalLookupWire
public import FormalProof4FHE.HasteBoots.NativeGoldPcsBinding
public import FormalProof4FHE.HasteBoots.NativeExactCodec
public import FormalProof4FHE.HasteBoots.NativeGoldBatchMessage
import all Init.Data.String.Defs
@[expose] public section

/-! Structural context/root mentions in complete native framed inputs.
Canonical bind and registry source vectors retain their original order and
repetitions; single PCS openings pair adjacent context/root frames, and native
batch messages retain their complete context/root tuple.
Mention extraction does not establish trusted-parameter identity, root
availability, helper-parent association or first-exposure registration. -/
namespace FormalProof4FHE.HasteBoots.NativeRootInputView
open InputIndexedOracle (Input)
open NativeCanonicalLookupWire (Binding)

def readBinding (input : Input) : Option (Binding × Input) := do
  let (config,rest) ← NativeLookupRequestWire.configCodec.read input
  let (degree,rest) ← NativePrefixCodec.usize.read rest
  if degree.val = 3 then
    let (helper,rest) ← NativeByteCodec.digest.read rest
    let (sources,rest) ← NativeCanonicalLookupWire.sourcesCodec.read rest
    pure (⟨config,helper,sources⟩,rest)
  else none

theorem readBinding_payload (binding : Binding) (suffix : Input) :
    readBinding (NativeCanonicalLookupWire.payload binding ++ suffix) = some (binding,suffix) := by
  simp only [readBinding,NativeCanonicalLookupWire.payload,List.append_assoc,Option.bind_eq_bind]
  rw [NativeLookupRequestWire.configCodec.read_encode,Option.bind_some]
  dsimp only
  rw [show NativeUsizeMessage.encode (⟨3,by decide⟩ : NativeUsizeMessage.Usize) =
    NativePrefixCodec.usize.encode (⟨3,by decide⟩ : NativeUsizeMessage.Usize) from rfl]
  rw [NativePrefixCodec.usize.read_encode (⟨3,by decide⟩ : NativeUsizeMessage.Usize)
    (NativeByteCodec.digest.encode binding.helper ++ (NativeCanonicalLookupWire.sourcesCodec.encode binding.sources ++ suffix)),Option.bind_some]
  dsimp only
  simp only [ite_true]
  rw [NativeByteCodec.digest.read_encode,Option.bind_some]
  dsimp only
  rw [NativeCanonicalLookupWire.sourcesCodec.read_encode,Option.bind_some]
  rfl

def bindingCodec : NativePrefixCodec.Codec Binding where
  encode := NativeCanonicalLookupWire.payload
  read := readBinding
  read_encode := readBinding_payload

def frameSources (frame : TranscriptFrame.Frame) : Option (List NativeCanonicalLookupWire.Source) :=
  if frame.kind = 1 then
    if frame.label = NativeCanonicalLookupWire.registryLabel then
      (NativeExactCodec.read NativeCanonicalLookupWire.sourcesCodec frame.message).map (fun sources => sources.val)
    else if frame.label = NativeCanonicalLookupWire.label then
      (NativeExactCodec.read bindingCodec frame.message).map (fun binding => binding.sources.val)
    else if frame.label = NativeTranscript.utf8 "mw batched row-code v1" then
      (NativeExactCodec.read NativeGoldBatchMessage.codec frame.message).map (fun data => [(data.context,data.root)])
    else none
  else none

theorem registry_complete (sources : NativePrefixCodec.Vector NativeCanonicalLookupWire.Source) :
    frameSources ⟨1,NativeCanonicalLookupWire.registryLabel,NativeCanonicalLookupWire.sourcesCodec.encode sources⟩ =
      some sources.val := by
  simp only [frameSources,ite_true,NativeExactCodec.read_encode,Option.map_some]

theorem binding_complete (binding : Binding) :
    frameSources ⟨1,NativeCanonicalLookupWire.label,NativeCanonicalLookupWire.payload binding⟩ =
      some binding.sources.val := by
  have labels : NativeCanonicalLookupWire.label ≠ NativeCanonicalLookupWire.registryLabel := by decide +kernel
  simp only [frameSources,ite_true,labels,ite_false]
  change (NativeExactCodec.read bindingCodec (bindingCodec.encode binding)).map _ = _
  rw [NativeExactCodec.read_encode]
  rfl


theorem batch_complete (data : NativeGoldBatchMessage.Data) :
    frameSources ⟨1,NativeTranscript.utf8 "mw batched row-code v1",NativeGoldBatchMessage.codec.encode data⟩ =
      some [(data.context,data.root)] := by
  have registry : NativeTranscript.utf8 "mw batched row-code v1" ≠ NativeCanonicalLookupWire.registryLabel := by decide +kernel
  have binding : NativeTranscript.utf8 "mw batched row-code v1" ≠ NativeCanonicalLookupWire.label := by decide +kernel
  simp only [frameSources,ite_true,registry,binding,ite_false,NativeGoldBatchMessage.read_exact,Option.map_some]


def single (contextFrame openingFrame : TranscriptFrame.Frame) : Option NativeCanonicalLookupWire.Source :=
  if contextFrame.kind = 1 ∧ contextFrame.label = NativeTranscript.utf8 "mw brakedown row-code v2" ∧
      openingFrame.kind = 1 ∧ openingFrame.label = NativeTranscript.utf8 "mw commitment and query" then do
    let context ← NativeExactCodec.read NativeByteCodec.digest contextFrame.message
    let opening ← NativeExactCodec.read NativeGoldPcsWire.openingCodec openingFrame.message
    pure (context,opening.1)
  else none

theorem single_complete (context root : NativeRootMessage.Digest) (query : NativeGoldPcsWire.Query)
    (values : NativeLookupRequestWire.Row) :
    single ⟨1,NativeTranscript.utf8 "mw brakedown row-code v2",List.ofFn context⟩
      ⟨1,NativeTranscript.utf8 "mw commitment and query",NativeGoldPcsWire.opening root query values⟩ =
      some (context,root) := by
  simp only [single,and_self,ite_true,Option.bind_eq_bind]
  rw [show List.ofFn context = NativeByteCodec.digest.encode context from rfl,
    NativeExactCodec.read_encode,Option.bind_some]
  rw [NativeGoldPcsWire.opening,NativeExactCodec.read_encode,Option.bind_some]
  rfl

def mentions : List TranscriptFrame.Frame → List NativeCanonicalLookupWire.Source
  | [] => []
  | frame :: tail => (frameSources frame).getD [] ++
      (match tail with | [] => [] | next :: _ => (single frame next).toList) ++ mentions tail

def raw (input : Input) : Option (List NativeCanonicalLookupWire.Source) :=
  (TranscriptFrame.decodeAll input).map mentions

theorem raw_complete (frames : List TranscriptFrame.Frame)
    (valid : ∀ frame ∈ frames, TranscriptFrame.Valid frame) :
    raw (TranscriptFrame.encodeMany frames) = some (mentions frames) := by
  rw [raw,TranscriptFrame.decodeAll_encodeMany frames valid]
  rfl

theorem head_sources (frame : TranscriptFrame.Frame) (tail : List TranscriptFrame.Frame)
    (sources : List NativeCanonicalLookupWire.Source) (recognized : frameSources frame = some sources) :
    sources.Sublist (mentions (frame::tail)) := by
  simp only [mentions,recognized,Option.getD_some,List.append_assoc]
  exact List.sublist_append_left _ _

theorem tail_mentions (frame : TranscriptFrame.Frame) (tail : List TranscriptFrame.Frame) :
    (mentions tail).Sublist (mentions (frame::tail)) := by
  simp only [mentions]
  exact List.sublist_append_right _ _

theorem recognized_sources (frames : List TranscriptFrame.Frame) (frame : TranscriptFrame.Frame)
    (member : frame ∈ frames) (sources : List NativeCanonicalLookupWire.Source)
    (recognized : frameSources frame = some sources) : sources.Sublist (mentions frames) := by
  induction frames with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst frame
      exact head_sources first rest sources recognized
    · exact (ih later).trans (tail_mentions first rest)


/-- Appending a prefix does not remove the mentions of an existing suffix. -/
theorem suffix_mentions (before later : List TranscriptFrame.Frame) :
    (mentions later).Sublist (mentions (before++later)) := by
  induction before with
  | nil => exact List.Sublist.refl _
  | cons frame before ih => exact ih.trans (tail_mentions frame (before++later))

/-- A recognized adjacent single-opening pair occurs in the ordered mentions. -/
theorem head_single (contextFrame openingFrame : TranscriptFrame.Frame) (tail : List TranscriptFrame.Frame)
    (source : NativeCanonicalLookupWire.Source) (recognized : single contextFrame openingFrame = some source) :
    source ∈ mentions (contextFrame::openingFrame::tail) := by
  simp [mentions,recognized]

theorem recognized_single (before later : List TranscriptFrame.Frame)
    (contextFrame openingFrame : TranscriptFrame.Frame) (source : NativeCanonicalLookupWire.Source)
    (recognized : single contextFrame openingFrame = some source) :
    source ∈ mentions (before++contextFrame::openingFrame::later) :=
  (suffix_mentions before _).subset (head_single contextFrame openingFrame later source recognized)

/-- A successful raw view uses a complete valid frame decomposition of those exact input bytes. -/
theorem raw_sound (input : Input) (sources : List NativeCanonicalLookupWire.Source) (parsed : raw input = some sources) :
    ∃ frames, (∀ frame ∈ frames, TranscriptFrame.Valid frame) ∧ input = TranscriptFrame.encodeMany frames ∧
      sources = mentions frames := by
  unfold raw at parsed
  cases decoded : TranscriptFrame.decodeAll input with
  | none => simp [decoded] at parsed
  | some frames =>
    simp only [decoded,Option.map_some,Option.some.injEq] at parsed
    obtain ⟨valid,bytes⟩ := TranscriptFrame.decodeAll_sound input frames decoded
    exact ⟨frames,valid,bytes,parsed.symm⟩


private theorem encodeMany_append (first later : List TranscriptFrame.Frame) :
    TranscriptFrame.encodeMany (first++later) =
      TranscriptFrame.encodeMany first ++ TranscriptFrame.encodeMany later := by
  induction first with
  | nil => simp [TranscriptFrame.encodeMany]
  | cons entry rest ih => simp [TranscriptFrame.encodeMany,ih,List.append_assoc]

theorem registry_frames (state : NativeTranscript.Transcript) (frames : List TranscriptFrame.Frame)
    (bytes : state.input = TranscriptFrame.encodeMany frames)
    (sources : NativePrefixCodec.Vector NativeCanonicalLookupWire.Source) :
    (NativeCanonicalLookupWire.registry state sources).input = TranscriptFrame.encodeMany
      (frames++[⟨1,NativeCanonicalLookupWire.registryLabel,NativeCanonicalLookupWire.sourcesCodec.encode sources⟩]) := by
  rw [NativeCanonicalLookupWire.registry_input,bytes,encodeMany_append]
  simp [TranscriptFrame.encodeMany]

theorem binding_frames (state : NativeTranscript.Transcript) (frames : List TranscriptFrame.Frame)
    (bytes : state.input = TranscriptFrame.encodeMany frames) (binding : Binding) :
    (NativeCanonicalLookupWire.bind state binding).input = TranscriptFrame.encodeMany
      (frames++[⟨1,NativeCanonicalLookupWire.label,NativeCanonicalLookupWire.payload binding⟩]) := by
  rw [NativeCanonicalLookupWire.bind_input,bytes,encodeMany_append]
  simp [TranscriptFrame.encodeMany]

theorem opening_frames (state : NativeTranscript.Transcript) (frames : List TranscriptFrame.Frame)
    (bytes : state.input = TranscriptFrame.encodeMany frames) (context root : NativeRootMessage.Digest)
    (query : NativeGoldPcsWire.Query) (values : NativeLookupRequestWire.Row) :
    (NativeGoldPcsBinding.appendBound state context root query values).input = TranscriptFrame.encodeMany
      (frames++[⟨1,NativeTranscript.utf8 "mw brakedown row-code v2",List.ofFn context⟩,
        ⟨1,NativeTranscript.utf8 "mw commitment and query",NativeGoldPcsWire.opening root query values⟩]) := by
  change (state.input ++ TranscriptFrame.encode ⟨1,NativeTranscript.utf8 "mw brakedown row-code v2",List.ofFn context⟩) ++
    TranscriptFrame.encode ⟨1,NativeTranscript.utf8 "mw commitment and query",NativeGoldPcsWire.opening root query values⟩ = _
  rw [bytes,encodeMany_append]
  simp [TranscriptFrame.encodeMany,List.append_assoc]

theorem raw_registry (state : NativeTranscript.Transcript) (frames : List TranscriptFrame.Frame)
    (bytes : state.input = TranscriptFrame.encodeMany frames)
    (sources : NativePrefixCodec.Vector NativeCanonicalLookupWire.Source)
    (valid : ∀ frame ∈ frames++[⟨1,NativeCanonicalLookupWire.registryLabel,NativeCanonicalLookupWire.sourcesCodec.encode sources⟩],
      TranscriptFrame.Valid frame) :
    ∃ found, raw (NativeCanonicalLookupWire.registry state sources).input = some found ∧ sources.val.Sublist found := by
  rw [registry_frames state frames bytes sources]
  refine ⟨_,raw_complete _ valid,?_⟩
  exact recognized_sources _ _ (by simp) sources.val (registry_complete sources)

theorem raw_binding (state : NativeTranscript.Transcript) (frames : List TranscriptFrame.Frame)
    (bytes : state.input = TranscriptFrame.encodeMany frames) (binding : Binding)
    (valid : ∀ frame ∈ frames++[⟨1,NativeCanonicalLookupWire.label,NativeCanonicalLookupWire.payload binding⟩],
      TranscriptFrame.Valid frame) :
    ∃ found, raw (NativeCanonicalLookupWire.bind state binding).input = some found ∧ binding.sources.val.Sublist found := by
  rw [binding_frames state frames bytes binding]
  refine ⟨_,raw_complete _ valid,?_⟩
  exact recognized_sources _ _ (by simp) binding.sources.val (binding_complete binding)

theorem raw_opening (state : NativeTranscript.Transcript) (frames : List TranscriptFrame.Frame)
    (bytes : state.input = TranscriptFrame.encodeMany frames) (context root : NativeRootMessage.Digest)
    (query : NativeGoldPcsWire.Query) (values : NativeLookupRequestWire.Row)
    (valid : ∀ frame ∈ frames++[⟨1,NativeTranscript.utf8 "mw brakedown row-code v2",List.ofFn context⟩,
        ⟨1,NativeTranscript.utf8 "mw commitment and query",NativeGoldPcsWire.opening root query values⟩],
      TranscriptFrame.Valid frame) :
    ∃ found, raw (NativeGoldPcsBinding.appendBound state context root query values).input = some found ∧
      (context,root) ∈ found := by
  rw [opening_frames state frames bytes context root query values]
  refine ⟨_,raw_complete _ valid,?_⟩
  exact recognized_single frames [] _ _ _ (single_complete context root query values)

end FormalProof4FHE.HasteBoots.NativeRootInputView
