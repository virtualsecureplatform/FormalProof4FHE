module

public import FormalProof4FHE.HasteBoots.NativeSeedAncestry
public import FormalProof4FHE.HasteBoots.NativeSharedLookupChild
public import FormalProof4FHE.HasteBoots.OracleProgramMachine
import all Init.Data.String.Defs

@[expose] public section

/-! Native fork execution supplies source/helper ancestry certificates from
its actual seed read. Shared-lookup preparation and typed identity retain
the canonical binding and seed header. Exact causal-machine interpretation
then derives chronological metadata for the complete native program log.
This is not native accepted-run coverage, availability, receipt entropy,
physical attacker-work accounting, or Rust refinement. -/
namespace FormalProof4FHE.HasteBoots.NativeForkAncestry
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeTranscript (Transcript Observation utf8)
open TranscriptFrame (Frame)
open OracleProgram (Program run bind)
open NativeSeedAncestry (Fact Realized)
noncomputable section

def seedInput (parent : Transcript) (label context : Input) : Input :=
  NativeTranscript.requestInput (NativeTranscript.absorb parent 6 label context) (utf8 "classical child seed") 64

def seedFrames (before : List Frame) (label context : Input) : List Frame :=
  before++[⟨6,label,context⟩,⟨2,utf8 "classical child seed",TranscriptFrame.littleEndian 8 64⟩]

theorem seedFrames_valid (before : List Frame) (label context : Input)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (labelFits : label.length < TranscriptFrame.lengthLimit)
    (contextFits : context.length < TranscriptFrame.lengthLimit) :
    ∀ frame ∈ seedFrames before label context, TranscriptFrame.Valid frame := by
  intro frame member
  rcases List.mem_append.mp member with old | added
  · exact valid frame old
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at added
    rcases added with rfl | rfl
    · exact ⟨labelFits,contextFits⟩
    · constructor <;> decide +kernel

theorem seedInput_parsed (parent : Transcript) (before : List Frame) (label context : Input)
    (bytes : parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (labelFits : label.length < TranscriptFrame.lengthLimit)
    (contextFits : context.length < TranscriptFrame.lengthLimit) :
    NativeParentInputView.parseParent (seedInput parent label context) = some (seedFrames before label context) :=
  NativeParentInputView.parseParent_request parent before bytes label context
    (seedFrames_valid before label context valid labelFits contextFits)

/-- The native fork itself performs this positive read, even on a cache hit. -/
theorem fork_read (world : World) (parent : Transcript) (label context : Input) :
    Observation.output (seedInput parent label context) 0
      (InputIndexedOracle.bytes world (seedInput parent label context) 0 64) ∈
      (run (NativeTranscriptProgram.forkChild parent label context) world).run.2 := by
  change Observation.output _ _ _ ∈ [Observation.start _,Observation.output _ _ _]
  exact List.mem_cons_of_mem _ List.mem_cons_self

theorem fork_direct (world : World) (log : List Observation) (parent : Transcript) (before : List Frame)
    (label context : Input) (bytes : parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (labelFits : label.length < TranscriptFrame.lengthLimit) (contextFits : context.length < TranscriptFrame.lengthLimit)
    (observed : (run (NativeTranscriptProgram.forkChild parent label context) world).run.2.Sublist log)
    (fact : Fact) (direct : NativeSeedAncestry.Direct (seedInput parent label context) fact) :
    ∃ index, Realized world log (seedInput parent label context) index fact := by
  exact NativeSeedAncestry.direct_of_read world log _ _
    (seedInput_parsed parent before label context bytes valid labelFits contextFits) fact direct 0 _
    (by simp [InputIndexedOracle.bytes]) (by decide)
    (observed.subset (fork_read world parent label context))

/-- Header preservation supplies the seed link; callers do not supply a quote equality. -/
theorem fork_inherit {world : World} {log : List Observation} {producer : Input} {producerIndex : ℕ} {fact : Fact}
    (previous : Realized world log producer producerIndex fact)
    (parent : Transcript) (label context : Input)
    (labelFits : label.length < TranscriptFrame.lengthLimit) (contextFits : context.length < TranscriptFrame.lengthLimit)
    (profile : Digest) (childLabel childContext : Input)
    (header : NativeChildSeedView.HasHeader parent profile childLabel childContext (InputIndexedOracle.block world producer 0 64))
    (observed : (run (NativeTranscriptProgram.forkChild parent label context) world).run.2.Sublist log) :
    ∃ index, Realized world log (seedInput parent label context) index fact := by
  obtain ⟨suffix,valid,bytes⟩ := header
  have retained : NativeChildSeedView.HasHeader parent profile childLabel childContext (InputIndexedOracle.block world producer 0 64) :=
    ⟨suffix,valid,bytes⟩
  have forkHeader := retained.absorb 6 label context ⟨labelFits,contextFits⟩
  exact NativeSeedAncestry.inherit_of_read previous _ _
    (seedInput_parsed parent _ label context bytes valid labelFits contextFits)
    (forkHeader.request (utf8 "classical child seed") 64 (by decide +kernel)) 0 _
    (by simp [InputIndexedOracle.bytes]) (by decide)
    (observed.subset (fork_read world parent label context))

/-- Any executed segment remains in the enclosing program's complete ordered log. -/
theorem segment_log {A B C : Type} (world : World) (prelude : Program A) (segment : A → Program B)
    (next : A → B → Program C) :
    (run (segment (run prelude world).run.1) world).run.2.Sublist
      (run (bind prelude (fun value => bind (segment value) (next value))) world).run.2 := by
  rw [OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run_bind,ObservationReplay.run_bind]
  exact (List.sublist_append_left _ _).trans (List.sublist_append_right _ _)

/-- The real shared-lookup initializer retains its native fork before checkpoint and type identity. -/
theorem start_fork (world : World) (parent : Transcript) (packet : NativeLookupMultiplicityWire.Packet) :
    (run (NativeTranscriptProgram.forkChild (NativeSharedLookupChild.prepare parent packet)
      NativeSharedLookupChild.childLabel NativeSharedLookupChild.childContext) world).run.2.Sublist
      (run (NativeSharedLookupChild.start parent packet) world).run.2 := by
  rw [NativeSharedLookupChild.run_start]
  change (NativeTranscript.forkChild world (NativeSharedLookupChild.prepare parent packet)
    NativeSharedLookupChild.childLabel NativeSharedLookupChild.childContext).run.2.Sublist ((_ ++ _) ++ _)
  exact (List.sublist_append_left _ _).trans (List.sublist_append_left _ _)


def prepareFrames (before : List Frame) (packet : NativeLookupMultiplicityWire.Packet) : List Frame :=
  before++[⟨1,NativeSharedLookupChild.groupedLabel,NativeLookupMultiplicityWire.grouped packet⟩,
    ⟨1,NativeSharedLookupChild.flatLabel,NativeLookupMultiplicityWire.flattened packet⟩]

private theorem encodeMany_append (before later : List Frame) :
    TranscriptFrame.encodeMany (before++later) = TranscriptFrame.encodeMany before ++ TranscriptFrame.encodeMany later := by
  induction before with
  | nil => simp [TranscriptFrame.encodeMany]
  | cons frame rest ih => simp [TranscriptFrame.encodeMany,ih,List.append_assoc]

theorem prepare_frames (parent : Transcript) (before : List Frame) (packet : NativeLookupMultiplicityWire.Packet)
    (bytes : parent.input = TranscriptFrame.encodeMany before) :
    (NativeSharedLookupChild.prepare parent packet).input = TranscriptFrame.encodeMany (prepareFrames before packet) := by
  rw [NativeSharedLookupChild.prepare_input,bytes,prepareFrames,encodeMany_append]
  simp only [TranscriptFrame.encodeMany,List.append_nil,List.append_assoc]

theorem prepareFrames_valid (before : List Frame) (packet : NativeLookupMultiplicityWire.Packet)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (groupedFits : (NativeLookupMultiplicityWire.grouped packet).length < TranscriptFrame.lengthLimit)
    (flatFits : (NativeLookupMultiplicityWire.flattened packet).length < TranscriptFrame.lengthLimit) :
    ∀ frame ∈ prepareFrames before packet, TranscriptFrame.Valid frame := by
  intro frame member
  rcases List.mem_append.mp member with old | added
  · exact valid frame old
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at added
    rcases added with rfl | rfl
    · exact ⟨by change NativeSharedLookupChild.groupedLabel.length < _; decide +kernel,groupedFits⟩
    · exact ⟨by change NativeSharedLookupChild.flatLabel.length < _; decide +kernel,flatFits⟩

/-- A canonical source in the original bind survives all preparation frames and is realized by the actual start. -/
theorem start_source (world : World) (log : List Observation) (parent : Transcript) (before : List Frame)
    (packet : NativeLookupMultiplicityWire.Packet) (bytes : parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (groupedFits : (NativeLookupMultiplicityWire.grouped packet).length < TranscriptFrame.lengthLimit)
    (flatFits : (NativeLookupMultiplicityWire.flattened packet).length < TranscriptFrame.lengthLimit)
    (observed : (run (NativeSharedLookupChild.start parent packet) world).run.2.Sublist log)
    (binding : NativeCanonicalLookupWire.Binding)
    (bound : (⟨1,NativeCanonicalLookupWire.label,NativeCanonicalLookupWire.payload binding⟩ : Frame) ∈ before)
    (key : NativeCanonicalLookupWire.Source) (member : key ∈ binding.sources.val) :
    ∃ index, Realized world log (seedInput (NativeSharedLookupChild.prepare parent packet)
      NativeSharedLookupChild.childLabel NativeSharedLookupChild.childContext) index (.source key) := by
  have parsed := seedInput_parsed (NativeSharedLookupChild.prepare parent packet) (prepareFrames before packet)
    NativeSharedLookupChild.childLabel NativeSharedLookupChild.childContext (prepare_frames parent before packet bytes)
    (prepareFrames_valid before packet valid groupedFits flatFits) (by decide +kernel) (by decide +kernel)
  apply fork_direct world log (NativeSharedLookupChild.prepare parent packet) (prepareFrames before packet)
    NativeSharedLookupChild.childLabel NativeSharedLookupChild.childContext (prepare_frames parent before packet bytes)
    (prepareFrames_valid before packet valid groupedFits flatFits) (by decide +kernel) (by decide +kernel)
    ((start_fork world parent packet).trans observed) (.source key)
  exact NativeSourceLineage.binding_source _ _ parsed binding
    (List.mem_append_left _ (List.mem_append_left _ bound)) key member

/-- The helper context comes from the same canonical binding, rather than a supplied context table. -/
theorem start_helper (world : World) (log : List Observation) (parent : Transcript) (before : List Frame)
    (packet : NativeLookupMultiplicityWire.Packet) (bytes : parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (groupedFits : (NativeLookupMultiplicityWire.grouped packet).length < TranscriptFrame.lengthLimit)
    (flatFits : (NativeLookupMultiplicityWire.flattened packet).length < TranscriptFrame.lengthLimit)
    (observed : (run (NativeSharedLookupChild.start parent packet) world).run.2.Sublist log)
    (binding : NativeCanonicalLookupWire.Binding)
    (bound : (⟨1,NativeCanonicalLookupWire.label,NativeCanonicalLookupWire.payload binding⟩ : Frame) ∈ before) :
    ∃ index, Realized world log (seedInput (NativeSharedLookupChild.prepare parent packet)
      NativeSharedLookupChild.childLabel NativeSharedLookupChild.childContext) index (.helper binding.helper) := by
  have parsed := seedInput_parsed (NativeSharedLookupChild.prepare parent packet) (prepareFrames before packet)
    NativeSharedLookupChild.childLabel NativeSharedLookupChild.childContext (prepare_frames parent before packet bytes)
    (prepareFrames_valid before packet valid groupedFits flatFits) (by decide +kernel) (by decide +kernel)
  apply fork_direct world log (NativeSharedLookupChild.prepare parent packet) (prepareFrames before packet)
    NativeSharedLookupChild.childLabel NativeSharedLookupChild.childContext (prepare_frames parent before packet bytes)
    (prepareFrames_valid before packet valid groupedFits flatFits) (by decide +kernel) (by decide +kernel)
    ((start_fork world parent packet).trans observed) (.helper binding.helper)
  exact NativeParentCoverage.binding_helper _ _ parsed binding
    (List.mem_append_left _ (List.mem_append_left _ bound))


/-- The typed zero-count identity keeps the header through its actual receipt frame. -/
theorem identity_header (p degree w : ℕ) (world : World) (child : Transcript)
    (profile : Digest) (label context : Input) (seed : Digest)
    (header : NativeChildSeedView.HasHeader child profile label context seed)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit) :
    NativeChildSeedView.HasHeader (TypedTranscriptChild.identityExecute p degree w world child).1
      profile label context seed := by
  have kind := header.absorb 1 (utf8 "field challenge kind") (utf8 "extension vector")
    ⟨by decide +kernel,by decide +kernel⟩
  have basis := kind.absorb 1 (utf8 "extension basis") (NativeExtensionDescriptor.descriptor degree w)
    ⟨by change (utf8 "extension basis").length < _; decide +kernel,descriptorFits⟩
  have requested := basis.absorb 4 (utf8 "typed extension identity")
    (TranscriptFrame.littleEndian 16 p ++ TranscriptFrame.littleEndian 8 0)
    ⟨by change (utf8 "typed extension identity").length < _; decide +kernel,by simp only [List.length_append,TranscriptFrame.littleEndian_length]; decide +kernel⟩
  have finished := requested.absorb 5 (utf8 "typed extension identity")
    (TranscriptFrame.littleEndian 16 0 ++ InputIndexedOracle.bytes world (utf8 "HasteBoots consumed field bytes v1" ++ []) 0 64)
    ⟨by change (utf8 "typed extension identity").length < _; decide +kernel,by simp only [List.length_append,TranscriptFrame.littleEndian_length,InputIndexedOracle.bytes,List.length_ofFn]; decide +kernel⟩
  exact finished

/-- The initializer's returned typed child has the executed fork's actual seed. -/
theorem start_header (world : World) (parent : Transcript) (packet : NativeLookupMultiplicityWire.Packet) :
    NativeChildSeedView.HasHeader (NativeSharedLookupChild.startExecute world parent packet).1.2 parent.profile
      NativeSharedLookupChild.childLabel NativeSharedLookupChild.childContext
      (InputIndexedOracle.block world (seedInput (NativeSharedLookupChild.prepare parent packet)
        NativeSharedLookupChild.childLabel NativeSharedLookupChild.childContext) 0 64) := by
  exact identity_header NativeFields.goldilocksModulus 3 7 world _ _ _ _ _
    (NativeChildSeedView.forkChild_header world (NativeSharedLookupChild.prepare parent packet)
      NativeSharedLookupChild.childLabel NativeSharedLookupChild.childContext (by decide +kernel) (by decide +kernel))
    (by decide +kernel)


/-- Exact program-to-machine agreement transfers derived chronology to the native program log. -/
theorem program_chronological {A : Type} (program : Program A) (world : World)
    (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world)
    {input : Input} {index : ℕ} {fact : Fact}
    (realized : Realized world (run program world).run.2 input index fact) :
    NativeSeedAncestry.Known world ((run program world).run.2.take (index+1)) input fact := by
  obtain ⟨fuel,completed⟩ := OracleProgramMachine.complete program world
  have logs := congrArg Prod.snd completed
  have native : Realized world (run (OracleMachine.take OracleProgramMachine.step fuel program) world).run.2 input index fact := by
    rw [logs]
    exact realized
  simpa only [logs] using native.chronological OracleProgramMachine.step fuel program world safe

/-- All earlier raw activity is retained when deriving metadata before a quoted observation. -/
theorem program_before_quote {A : Type} (program : Program A) (world : World)
    (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world)
    {input : Input} {index : ℕ} {fact : Fact}
    (realized : Realized world (run program world).run.2 input index fact)
    (position : ℕ) (entry : Observation) (positioned : (run program world).run.2[position]? = some entry)
    (quoted : NativeChildSeedView.candidate entry = some (InputIndexedOracle.block world input 0 64)) :
    NativeSeedAncestry.Known world ((run program world).run.2.take position) input fact := by
  obtain ⟨fuel,completed⟩ := OracleProgramMachine.complete program world
  have logs := congrArg Prod.snd completed
  have native : Realized world (run (OracleMachine.take OracleProgramMachine.step fuel program) world).run.2 input index fact := by
    rw [logs]
    exact realized
  have positioned' : (run (OracleMachine.take OracleProgramMachine.step fuel program) world).run.2[position]? = some entry := by
    rw [logs]
    exact positioned
  simpa only [logs] using native.before_quote OracleProgramMachine.step fuel program world safe position entry positioned' quoted

end
end FormalProof4FHE.HasteBoots.NativeForkAncestry

