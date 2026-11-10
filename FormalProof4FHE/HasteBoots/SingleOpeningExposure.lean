module
public import FormalProof4FHE.HasteBoots.NativeGoldPcsProgram
public import FormalProof4FHE.HasteBoots.NativePrimeReadExposure
public import FormalProof4FHE.HasteBoots.NativeRootFamilyHistory
public import FormalProof4FHE.HasteBoots.NativeRootInputView
import all Init.Data.String.Defs
@[expose] public section

/-! The actual single-opening binding exposes its context/root at the first
random-test byte read, including a rejected first candidate. Adjacent original
single frames are retained. The history monitor records the same immutable log
for every supported height; later mentions do not reset it. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningExposure
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open NativeGoldBlockCode (description)
open NativeRootMessage (Digest)
open InputIndexedOracle (Input World bytes)
open NativeTranscript (Transcript Observation utf8)
open OracleProgram (run)
noncomputable section

def contextFrame (context : Digest) : TranscriptFrame.Frame :=
  ⟨1,utf8 "mw brakedown row-code v2",List.ofFn context⟩
def openingFrame (root : Digest) (query : NativeGoldPcsWire.Query) (claimed : NativeLookupRequestWire.Row) : TranscriptFrame.Frame :=
  ⟨1,utf8 "mw commitment and query",NativeGoldPcsWire.opening root query claimed⟩
def frames (before after : List TranscriptFrame.Frame) (context root : Digest)
    (query : NativeGoldPcsWire.Query) (claimed : NativeLookupRequestWire.Row) : List TranscriptFrame.Frame :=
  before ++ contextFrame context :: openingFrame root query claimed :: after
def input (before after : List TranscriptFrame.Frame) (context root : Digest)
    (query : NativeGoldPcsWire.Query) (claimed : NativeLookupRequestWire.Row) : Input :=
  TranscriptFrame.encodeMany (frames before after context root query claimed)

/-- Recognition uses the original adjacent context/opening frames, including
raw query/value words. It does not reinterpret them as a batch packet. -/
theorem mentioned (before after : List TranscriptFrame.Frame) (context root : Digest)
    (query : NativeGoldPcsWire.Query) (claimed : NativeLookupRequestWire.Row)
    (valid : ∀ entry ∈ frames before after context root query claimed, TranscriptFrame.Valid entry) :
    (context,root) ∈ NativeParentLedger.direct (input before after context root query claimed) := by
  have parsed := NativeRootInputView.raw_complete _ valid
  have present := NativeRootInputView.recognized_single before after (contextFrame context) (openingFrame root query claimed)
    (context,root) (NativeRootInputView.single_complete context root query claimed)
  unfold NativeParentLedger.direct input
  rw [parsed]
  exact present

theorem history_snapshot (dummy : Digest) (history : List Observation)
    (before after : List TranscriptFrame.Frame) (context root : Digest)
    (query : NativeGoldPcsWire.Query) (claimed : NativeLookupRequestWire.Row)
    (valid : ∀ entry ∈ frames before after context root query claimed, TranscriptFrame.Valid entry)
    (offset : ℕ) (values : Input) (positive : values ≠ [])
    (observed : .output (input before after context root query claimed) offset values ∈ history) :
    ∃ log : MerkleTreeExtractor.QueryLog Input Digest, ∀ index : NativeMerkleShapeFamily.Height,
      ⟨(context,index),⟨root,log⟩⟩ ∈
        (NativeRootFamilyHistory.reconstruct NativeGoldColumnAuthentication.encoding dummy history).2.checkpoints.checkpoints :=
  NativeRootFamilyHistory.direct_snapshot NativeGoldColumnAuthentication.encoding dummy history _ offset values positive observed
    (context,root) (mentioned before after context root query claimed valid)

theorem binding_origin (ctx : Context) (world : World) (bound : Transcript)
    (executed : (run (NativeGoldPcsBinding.protocol description.row ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed) world).run.1 = some bound) :
    ∃ context : Digest,
      (run (NativeBrakedownContext.context description.row ctx.parameters) world).run.1 = some context ∧
      bound = NativeGoldPcsBinding.appendBound ctx.transcript context ctx.root ctx.query ctx.claimed := by
  simp only [NativeGoldPcsBinding.protocol] at executed
  split at executed
  · simp only [OracleProgram.run_bind,ObservationReplay.run_bind] at executed
    cases hashed : (run (NativeBrakedownContext.context description.row ctx.parameters) world).run.1 with
    | none => simp only [hashed,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed; contradiction
    | some context =>
      simp only [hashed,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed
      exact ⟨context,rfl,(Option.some.inj executed).symm⟩
  · contradiction

def suffix (count : NativeUsizeMessage.Usize) : List TranscriptFrame.Frame :=
  [⟨1,utf8 "typed request kind",TypedFieldRequest.kindBytes .vector⟩,
   ⟨1,utf8 "field challenge kind",utf8 "prime vector"⟩,
   ⟨4,NativeGoldPcsPrelude.randomLabel,TranscriptFrame.littleEndian 16 NativeFields.goldilocksModulus ++
     TranscriptFrame.littleEndian 8 count.val⟩]

theorem suffix_valid (count : NativeUsizeMessage.Usize) : ∀ frame ∈ suffix count, TranscriptFrame.Valid frame := by
  intro frame member
  simp only [suffix,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · unfold TranscriptFrame.Valid; decide +kernel
  · unfold TranscriptFrame.Valid; decide +kernel
  · constructor
    · change NativeGoldPcsPrelude.randomLabel.length < TranscriptFrame.lengthLimit
      decide +kernel
    · simp only [List.length_append,TranscriptFrame.littleEndian_length]
      decide +kernel

theorem frames_valid (ctx : Context) (context : Digest) (before : List TranscriptFrame.Frame)
    (count : NativeUsizeMessage.Usize) (valid : ∀ entry ∈ before, TranscriptFrame.Valid entry)
    (fits : (NativeGoldPcsWire.opening ctx.root ctx.query ctx.claimed).length < TranscriptFrame.lengthLimit) :
    ∀ entry ∈ frames before (suffix count) context ctx.root ctx.query ctx.claimed, TranscriptFrame.Valid entry := by
  intro entry member
  rcases List.mem_append.mp member with old | added
  · exact valid entry old
  · rcases List.mem_cons.mp added with rfl | added
    · constructor
      · change (utf8 "mw brakedown row-code v2").length < _; decide +kernel
      · change (List.ofFn context).length < _
        simp only [List.length_ofFn]; decide +kernel
    · rcases List.mem_cons.mp added with rfl | added
      · exact ⟨by change (utf8 "mw commitment and query").length < _; decide +kernel,fits⟩
      · exact suffix_valid count entry added

theorem encodeMany_append (first last : List TranscriptFrame.Frame) :
    TranscriptFrame.encodeMany (first++last) = TranscriptFrame.encodeMany first ++ TranscriptFrame.encodeMany last := by
  induction first with
  | nil => rfl
  | cons frame rest ih => simp only [List.cons_append,TranscriptFrame.encodeMany,ih,List.append_assoc]

theorem phase_input (ctx : Context) (context : Digest) (before : List TranscriptFrame.Frame)
    (count : NativeUsizeMessage.Usize) (parent : ctx.transcript.input = TranscriptFrame.encodeMany before) :
    (NativePrimeRequest.phase NativeFields.goldilocksModulus
      (NativeGoldPcsBinding.appendBound ctx.transcript context ctx.root ctx.query ctx.claimed)
      .vector NativeGoldPcsPrelude.randomLabel count).pending.input =
      input before (suffix count) context ctx.root ctx.query ctx.claimed := by
  change (NativePrimeRequest.prepare _ .vector).input ++ TranscriptFrame.encode
    ⟨4,NativeGoldPcsPrelude.randomLabel,TranscriptFrame.littleEndian 16 NativeFields.goldilocksModulus ++
      TranscriptFrame.littleEndian 8 count.val⟩ = _
  rw [NativePrimeRequest.prepare_input,NativeGoldPcsBinding.appendBound_input,parent]
  simp only [input,frames,encodeMany_append,contextFrame,openingFrame,suffix,
    TranscriptFrame.encodeMany,List.append_nil,List.append_assoc]

/-- The first nonempty read precedes every random-test answer. Parent frame
validity and the original opening message allocation bound remain explicit. -/
theorem prepared_exposure (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work)
    (before : List TranscriptFrame.Frame) (parent : ctx.transcript.input = TranscriptFrame.encodeMany before)
    (valid : ∀ entry ∈ before, TranscriptFrame.Valid entry)
    (fits : (NativeGoldPcsWire.opening ctx.root ctx.query ctx.claimed).length < TranscriptFrame.lengthLimit) :
    ∃ context : Digest,
      (run (NativeBrakedownContext.context description.row ctx.parameters) world).run.1 = some context ∧
      (∀ entry ∈ frames before (suffix work.geometry.randomCount) context ctx.root ctx.query ctx.claimed, TranscriptFrame.Valid entry) ∧
      .output (input before (suffix work.geometry.randomCount) context ctx.root ctx.query ctx.claimed) 0
        (bytes world (input before (suffix work.geometry.randomCount) context ctx.root ctx.query ctx.claimed) 0 8) ∈
        (run ctx.prefix world).run.2 := by
  obtain ⟨geometry,state,weights,sample,planRoot,test,evaluation,jobs,encoded,_,rfl⟩ :=
    NativeGoldPcsWorkers.prepared_origin ctx.tables ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed ctx.opening ctx.fieldFuel world work prepared
  have original := (NativeGoldPcsEncoding.encoded_origin ctx.tables ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed
    ctx.opening ctx.fieldFuel world geometry state weights sample planRoot test evaluation encoded).1
  obtain ⟨next,prior,columnsLog⟩ := NativeGoldPcsColumns.columns_observations description ctx.parameters ctx.transcript ctx.root ctx.query
    ctx.claimed ctx.opening ctx.fieldFuel world geometry state weights sample original
  obtain ⟨built,shape,bound,boundRead,sampled⟩ := NativeGoldPcsPrelude.sampling_origin description ctx.parameters ctx.transcript ctx.root
    ctx.query ctx.claimed ctx.opening ctx.fieldFuel world geometry (.finished state next) prior
  obtain ⟨context,hashed,binding⟩ := binding_origin ctx world bound boundRead
  have spec := NativeBrakedownParameters.build_spec description ctx.parameters geometry built
  have positive : geometry.randomCount.val ≠ 0 := by
    rw [spec.computed]
    change 2^ctx.parameters.leftVariables.val * ctx.parameters.width.val * ctx.parameters.width.val ≠ 0
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (by positivity) spec.basic.1) spec.basic.1
  have read := NativePrimeReadExposure.finished_read NativeFields.goldilocksModulus ctx.fieldFuel bound .vector
    NativeGoldPcsPrelude.randomLabel geometry.randomCount positive world state next sampled
  have width : CanonicalByteSampler.byteCount NativeFields.goldilocksModulus = 8 := by decide +kernel
  have sameInput : (NativePrimeRequest.phase NativeFields.goldilocksModulus bound .vector
      NativeGoldPcsPrelude.randomLabel geometry.randomCount).pending.input =
      input before (suffix geometry.randomCount) context ctx.root ctx.query ctx.claimed := by
    rw [binding]
    exact phase_input ctx context before geometry.randomCount parent
  rw [width,sameInput] at read
  refine ⟨context,hashed,frames_valid ctx context before geometry.randomCount valid fits,?_⟩
  have preludeLog : (run (NativeGoldPcsPrelude.protocol description ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed ctx.opening ctx.fieldFuel) world).run.2 =
      (run (NativeGoldPcsBinding.protocol description.row ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed) world).run.2 ++
        (run (NativeGoldPcsPrelude.sample geometry ctx.fieldFuel bound) world).run.2 := by
    rw [NativeGoldPcsPrelude.run_protocol]
    simp only [built,ite_eq_left shape,boundRead]
  change _ ∈ (run (NativeGoldPcsWorkers.protocol ctx.tables ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed ctx.opening ctx.fieldFuel) world).run.2
  rw [NativeGoldPcsWorkers.run_protocol,NativeGoldPcsEncoding.run_protocol,columnsLog,preludeLog]
  exact List.mem_append_left _ (List.mem_append_right _ read)

end
end FormalProof4FHE.HasteBoots.SingleOpeningExposure
