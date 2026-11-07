module
public import FormalProof4FHE.HasteBoots.StoredRegistrySourcesCost
@[expose] public section

/-! Strict measured decoding of the terminal original registry packet. Earlier
registry frames are not merged or used as a fallback. Native allocation/framing
premises remain explicit; physical deserializer refinement is separate. -/
namespace FormalProof4FHE.HasteBoots.StoredRegistryPacketCost
open InputIndexedOracle (Input World)
open TranscriptFrame (Frame)
open SolverOperationCost (Run)
open StoredSourceVectorReadCost (Sources view)

private theorem encodeMany_append (first last : List Frame) :
    TranscriptFrame.encodeMany (first ++ last) = TranscriptFrame.encodeMany first ++ TranscriptFrame.encodeMany last := by
  induction first with
  | nil => rfl
  | cons head tail ih => simp only [List.cons_append,TranscriptFrame.encodeMany,ih,List.append_assoc]

def fromFrames (frames : List Frame) : Run (Option Sources) :=
  let reversed := ParentSeedRequestCost.reverseAux frames []
  match reversed.value with
  | [] => ⟨none,reversed.cost+2⟩
  | last::_ =>
    let parsed := StoredRegistrySourcesCost.frameSources last
    ⟨parsed.value,reversed.cost+parsed.cost+3⟩

def decode (input : Input) : Run (Option Sources) :=
  let frames := TranscriptFrameStreamCost.decodeAll input
  match frames.value with
  | none => ⟨none,frames.cost+2⟩
  | some values =>
    let parsed := fromFrames values
    ⟨parsed.value,frames.cost+parsed.cost+3⟩

theorem frameSources_sound (frame : Frame) (sources : Sources)
    (accepted : (StoredRegistrySourcesCost.frameSources frame).value = some sources) :
    frame.kind = 1 ∧ frame.label = NativeCanonicalLookupWire.registryLabel ∧
      (StoredSourceVectorCost.decode frame.message).value = some sources := by
  simp only [StoredRegistrySourcesCost.frameSources] at accepted
  split at accepted
  · rename_i kind
    split at accepted
    · rename_i named
      rw [BytePrefixMatchCost.equal_value] at named
      exact ⟨kind,(of_decide_eq_true named).symm,accepted⟩
    · contradiction
  · contradiction

theorem fromFrames_sound (frames : List Frame) (sources : Sources)
    (accepted : (fromFrames frames).value = some sources) :
    ∃ before, frames = before ++ [⟨1,NativeCanonicalLookupWire.registryLabel,
      NativeCanonicalLookupWire.sourcesCodec.encode (view sources)⟩] := by
  simp only [fromFrames,ParentSeedRequestCost.reverseAux_value,List.append_nil] at accepted
  cases reversed : frames.reverse with
  | nil => simp only [reversed] at accepted; contradiction
  | cons last rest =>
    simp only [reversed] at accepted
    obtain ⟨kind,named,decoded⟩ := frameSources_sound last sources accepted
    have bytes := StoredSourceVectorCost.decode_sound last.message sources decoded
    have original := congrArg List.reverse reversed
    simp only [List.reverse_reverse,List.reverse_cons] at original
    refine ⟨rest.reverse,original.trans ?_⟩
    congr 2
    cases last
    simp_all

theorem decode_sound (input : Input) (sources : Sources)
    (accepted : (decode input).value = some sources) :
    ∃ before, (∀ frame ∈ before, TranscriptFrame.Valid frame) ∧
      input = TranscriptFrame.encodeMany (before ++ [⟨1,NativeCanonicalLookupWire.registryLabel,
        NativeCanonicalLookupWire.sourcesCodec.encode (view sources)⟩]) := by
  simp only [decode] at accepted
  split at accepted
  · contradiction
  · rename_i frames parsed
    obtain ⟨valid,encoded⟩ := TranscriptFrameStreamCost.decodeAll_sound input frames parsed
    obtain ⟨before,same⟩ := fromFrames_sound frames sources accepted
    refine ⟨before,?_,?_⟩
    · intro frame member
      exact valid frame (by rw [same]; exact List.mem_append_left _ member)
    · exact encoded.trans (congrArg TranscriptFrame.encodeMany same)

theorem last_message_le (frames : List Frame) (last : Frame) (rest : List Frame)
    (reversed : frames.reverse = last::rest) : last.message.length ≤ (TranscriptFrame.encodeMany frames).length := by
  have member : last ∈ frames := List.mem_reverse.mp (reversed ▸ List.mem_cons_self)
  have messages := StoredRegistrySourcesCost.messageBytes_le_encoded frames
  have own : last.message.length ≤ StoredRegistrySourcesCost.messageBytes frames := by
    clear reversed messages
    induction frames with
    | nil => simp only [List.not_mem_nil] at member
    | cons head tail ih =>
      simp only [StoredRegistrySourcesCost.messageBytes]
      rcases List.mem_cons.mp member with rfl | later
      · omega
      · have prior := ih later; omega
  exact own.trans messages

theorem fromFrames_cost (frames : List Frame) :
    (fromFrames frames).cost ≤ 3*frames.length + 1770*(TranscriptFrame.encodeMany frames).length +
      6*StoredRegistrySourcesCost.label.length+1783 := by
  have reversedCost := ParentSeedRequestCost.reverseAux_cost frames []
  simp only [fromFrames,ParentSeedRequestCost.reverseAux_value,List.append_nil]
  cases reversed : frames.reverse with
  | nil => dsimp only; omega
  | cons last rest =>
    have parsed := StoredRegistrySourcesCost.frameSources_cost last
    have size := last_message_le frames last rest reversed
    have divided := Nat.div_le_self last.message.length 128
    dsimp only
    simp only [ParentSeedRequestCost.reverseAux_cost]
    omega

theorem decode_cost (input : Input) :
    (decode input).cost ≤ 1797*input.length+6*StoredRegistrySourcesCost.label.length+1787 := by
  have parsed := TranscriptFrameStreamCost.decodeAll_cost input
  simp only [decode]
  split
  · dsimp only; omega
  · rename_i frames found
    have encoded := (TranscriptFrameStreamCost.decodeAll_sound input frames found).2
    have count := ParentSeedRequestCost.frameCount_le_encoded frames
    have selected := fromFrames_cost frames
    rw [← encoded] at count selected
    dsimp only; omega

theorem fromFrames_registry (before : List Frame) (sources : Sources) :
    (fromFrames (before ++ [⟨1,NativeCanonicalLookupWire.registryLabel,
      (StoredSourceVectorCost.encode sources).value⟩])).value = some sources := by
  simp only [fromFrames,ParentSeedRequestCost.reverseAux_value,List.append_nil,List.reverse_append,
    List.reverse_singleton,List.singleton_append]
  exact StoredRegistrySourcesCost.frameSources_encode sources


theorem frameSources_native (native : NativePrefixCodec.Vector NativeCanonicalLookupWire.Source) :
    ∃ sources : Sources,
      (StoredRegistrySourcesCost.frameSources ⟨1,NativeCanonicalLookupWire.registryLabel,
        NativeCanonicalLookupWire.sourcesCodec.encode native⟩).value = some sources ∧ view sources = native := by
  have reference := StoredRegistrySourcesCost.frameSources_value
    ⟨1,NativeCanonicalLookupWire.registryLabel,NativeCanonicalLookupWire.sourcesCodec.encode native⟩
  have nativeView : StoredRegistrySourcesCost.registryView
      ⟨1,NativeCanonicalLookupWire.registryLabel,NativeCanonicalLookupWire.sourcesCodec.encode native⟩ = some native.val := by
    rw [StoredRegistrySourcesCost.registryView_eq_decode]
    simp only [StoredRegistrySourcesCost.label,and_self,ite_true,NativeExactCodec.read_encode,Option.map_some]
  obtain ⟨sources,parsed,same⟩ := Option.map_eq_some_iff.mp (reference.trans nativeView)
  exact ⟨sources,parsed,Subtype.ext same⟩

theorem decode_native_complete (parent : NativeTranscript.Transcript)
    (native : NativePrefixCodec.Vector NativeCanonicalLookupWire.Source)
    (before : List Frame) (parentBytes : parent.input = TranscriptFrame.encodeMany before)
    (framed : ∀ frame ∈ before ++ [⟨1,NativeCanonicalLookupWire.registryLabel,
      NativeCanonicalLookupWire.sourcesCodec.encode native⟩], TranscriptFrame.Valid frame) :
    ∃ sources : Sources, (decode (NativeCanonicalLookupWire.registry parent native).input).value = some sources ∧
      view sources = native := by
  obtain ⟨sources,parsed,same⟩ := frameSources_native native
  refine ⟨sources,?_,same⟩
  have inputEq : (NativeCanonicalLookupWire.registry parent native).input =
      TranscriptFrame.encodeMany (before ++ [⟨1,NativeCanonicalLookupWire.registryLabel,
        NativeCanonicalLookupWire.sourcesCodec.encode native⟩]) := by
    rw [NativeCanonicalLookupWire.registry_input,parentBytes,encodeMany_append]
    simp only [TranscriptFrame.encodeMany,List.append_nil]
  simpa only [decode,TranscriptFrameStreamCost.decodeAll_value,inputEq,
    TranscriptFrame.decodeAll_encodeMany _ framed,fromFrames,ParentSeedRequestCost.reverseAux_value,
    List.append_nil,List.reverse_append,List.reverse_singleton,List.singleton_append] using parsed

theorem decoded_native_sources (parent : NativeTranscript.Transcript)
    (native : NativePrefixCodec.Vector NativeCanonicalLookupWire.Source) (sources : Sources)
    (before : List Frame) (parentBytes : parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (labelFits : NativeCanonicalLookupWire.registryLabel.length < TranscriptFrame.lengthLimit)
    (messageFits : (NativeCanonicalLookupWire.sourcesCodec.encode native).length < TranscriptFrame.lengthLimit)
    (decoded : (decode (NativeCanonicalLookupWire.registry parent native).input).value = some sources) :
    view sources = native := by
  have allValid : ∀ frame ∈ before ++ [⟨1,NativeCanonicalLookupWire.registryLabel,
      NativeCanonicalLookupWire.sourcesCodec.encode native⟩], TranscriptFrame.Valid frame := by
    intro frame member
    rcases List.mem_append.mp member with old | added
    · exact valid frame old
    · obtain rfl := List.mem_singleton.mp added
      exact ⟨labelFits,messageFits⟩
  have inputEq : (NativeCanonicalLookupWire.registry parent native).input =
      TranscriptFrame.encodeMany (before ++ [⟨1,NativeCanonicalLookupWire.registryLabel,
        NativeCanonicalLookupWire.sourcesCodec.encode native⟩]) := by
    rw [NativeCanonicalLookupWire.registry_input,parentBytes,encodeMany_append]
    simp only [TranscriptFrame.encodeMany,List.append_nil]
  simp only [decode,TranscriptFrameStreamCost.decodeAll_value,inputEq,
    TranscriptFrame.decodeAll_encodeMany _ allValid,fromFrames,ParentSeedRequestCost.reverseAux_value,
    List.append_nil,List.reverse_append,List.reverse_singleton,List.singleton_append] at decoded
  have raw := (frameSources_sound _ sources decoded).2.2
  have reference := StoredSourceVectorCost.decode_value (NativeCanonicalLookupWire.sourcesCodec.encode native)
  rw [raw,Option.map_some,NativeExactCodec.read_encode] at reference
  exact Option.some.inj reference

end FormalProof4FHE.HasteBoots.StoredRegistryPacketCost
