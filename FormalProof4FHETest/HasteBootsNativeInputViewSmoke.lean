module
import all FormalProof4FHE.HasteBoots.NativeChildSeedView
import all FormalProof4FHE.HasteBoots.NativeRootInputView
import all Mathlib.Data.List.Sort
import all Init.Data.String.Defs
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Byte Input World)
namespace HasteBootsNativeInputViewSmoke

def profile : NativeRootMessage.Digest := fun _ => 0
def seed : NativeRootMessage.Digest := fun _ => 41
def otherSeed : NativeRootMessage.Digest := fun _ => 99
def label : Input := [7]
def context : Input := [9]
def header := NativeChildSeedView.seededFrames profile label context seed

def quoted := TranscriptFrame.encodeMany header

def suffix : List TranscriptFrame.Frame := [⟨1,NativeTranscript.utf8 "parent seed",List.ofFn otherSeed⟩]

example : (NativeChildSeedView.quote quoted).map (fun value => value 0) = some 41 := by decide +kernel
example : (NativeChildSeedView.quote (TranscriptFrame.encodeMany (header++suffix))).map (fun value => value 0) = some 41 := by decide +kernel
example : NativeChildSeedView.quote [] = none := by decide +kernel
example : NativeChildSeedView.quote (TranscriptFrame.encodeMany [⟨1,NativeTranscript.utf8 "parent seed",List.ofFn seed⟩]) = none := by
  decide +kernel
example : NativeChildSeedView.quote (quoted++[255]) = none := by decide +kernel
example : NativeChildSeedView.quote (TranscriptFrame.encodeMany
    [⟨0,[],[]⟩,⟨0,[],[]⟩,⟨0,[],[]⟩,⟨0,[],[]⟩,⟨0,[],[]⟩,⟨1,NativeTranscript.utf8 "parent seed",[41]⟩]) = none := by decide +kernel

example : (NativeChildSeedView.guesses [.start quoted,.output quoted 0 [],.output quoted 3 [0],.hash quoted (List.replicate 64 0)]).card = 1 := by
  decide +kernel
example : (NativeChildSeedView.guesses [.start quoted,.output quoted 0 []]).card = 0 := by decide +kernel
example : (NativeChildSeedView.guesses [.output (quoted++[255]) 0 [0]]).card = 0 := by decide +kernel

example : NativeExactCodec.read NativeByteCodec.digest (List.ofFn seed ++ [0]) = none := by decide +kernel

-- A real registry vector with a repeated original source followed by another source.
def sources : NativePrefixCodec.Vector NativeCanonicalLookupWire.Source :=
  ⟨[(profile,seed),(profile,seed),(seed,otherSeed)],by decide⟩
def registryFrame : TranscriptFrame.Frame :=
  ⟨1,NativeCanonicalLookupWire.registryLabel,NativeCanonicalLookupWire.sourcesCodec.encode sources⟩

example : (NativeRootInputView.frameSources registryFrame).map List.length = some 3 := by decide +kernel
example : (NativeRootInputView.frameSources registryFrame).map (List.map (fun pair => (pair.1 0,pair.2 0))) =
    some [(0,41),(0,41),(41,99)] := by decide +kernel
example : NativeRootInputView.frameSources { registryFrame with message := registryFrame.message++[0] } = none := by decide +kernel
example : (NativeRootInputView.raw (TranscriptFrame.encodeMany [registryFrame])).map List.length = some 3 := by decide +kernel
example : NativeRootInputView.raw [255] = none := by decide +kernel

def config : NativeLookupRequestWire.Config := ⟨⟨0,by decide⟩,⟨[],by decide⟩,⟨1,by decide⟩⟩
def binding : NativeCanonicalLookupWire.Binding := ⟨config,profile,sources⟩
def bindingFrame : TranscriptFrame.Frame :=
  ⟨1,NativeCanonicalLookupWire.label,NativeCanonicalLookupWire.payload binding⟩

example : (NativeRootInputView.frameSources bindingFrame).map List.length = some 3 := by decide +kernel
example : NativeRootInputView.frameSources { bindingFrame with message := bindingFrame.message++[0] } = none := by decide +kernel
example : NativeRootInputView.frameSources ⟨1,NativeCanonicalLookupWire.label,
    NativeLookupRequestWire.configCodec.encode config ++ NativeUsizeMessage.encode ⟨4,by decide⟩ ++
      NativeByteCodec.digest.encode profile ++ NativeCanonicalLookupWire.sourcesCodec.encode sources⟩ = none := by decide +kernel
example : (NativeRootInputView.raw (TranscriptFrame.encodeMany [bindingFrame,registryFrame])).map List.length = some 6 := by decide +kernel

def query : NativeGoldPcsWire.Query := ⟨[],by decide⟩
def values : NativeLookupRequestWire.Row := ⟨[],by decide⟩
def contextFrame : TranscriptFrame.Frame := ⟨1,NativeTranscript.utf8 "mw brakedown row-code v2",List.ofFn profile⟩
def openingFrame : TranscriptFrame.Frame :=
  ⟨1,NativeTranscript.utf8 "mw commitment and query",NativeGoldPcsWire.opening seed query values⟩

example : (NativeRootInputView.single contextFrame openingFrame).map (fun pair => (pair.1 0,pair.2 0)) = some (0,41) := by decide +kernel
example : NativeRootInputView.single openingFrame contextFrame = none := by decide +kernel
example : NativeRootInputView.single contextFrame { openingFrame with message := openingFrame.message++[0] } = none := by decide +kernel
example : (NativeRootInputView.raw (TranscriptFrame.encodeMany [registryFrame,contextFrame,openingFrame])).map
    (List.map (fun pair => (pair.1 0,pair.2 0))) = some [(0,41),(0,41),(41,99),(0,41)] := by decide +kernel

noncomputable section
example : sources.val.Sublist (NativeRootInputView.mentions [contextFrame,registryFrame,openingFrame]) := by
  apply NativeRootInputView.recognized_sources _ registryFrame (by simp)
  exact NativeRootInputView.registry_complete sources

def parent : NativeTranscript.Transcript := NativeTranscript.new [1,2] profile

def parentSeedInput : Input := NativeTranscript.requestInput (NativeTranscript.absorb parent 6 label context)
  (NativeTranscript.utf8 "classical child seed") 64

def childQuery : Input := NativeTranscript.requestInput ⟨quoted,profile⟩ [3] 1

def orphanStep (state : ℕ) : OracleMachine.Command ℕ Unit :=
  if state = 0 then .read childQuery 0 1 (fun _ => 1) else
  if state = 1 then .read (NativeTranscript.utf8 "HasteBoots consumed field bytes v1") 0 1 (fun _ => 2) else
  if state = 2 then .read parentSeedInput 63 1 (fun _ => 3) else .done ()

def world : World := fun _ => 0

example : OracleFirstExposure.locate (OracleProgram.run (OracleMachine.take orphanStep 3 0) world).run.2
    (OracleFirstExposure.seedCoordinates parentSeedInput) = some 2 := by decide +kernel
example : (NativeChildSeedView.guesses (OracleProgram.run (OracleMachine.take orphanStep 2 0) world).run.2).card = 1 := by decide +kernel


example : NativeChildSeedView.quote (NativeTranscript.forkChild world parent label context).run.1.2.input =
    some (InputIndexedOracle.block world parentSeedInput 0 64) :=
  NativeChildSeedView.quote_forkChild world parent label context (by decide +kernel) (by decide +kernel)

example : NativeChildSeedView.quote (NativeTranscript.beginField
    (NativeTranscript.forkChild world parent label context).run.1.2 [4] 17 0).run.1.pending.input =
    some (InputIndexedOracle.block world parentSeedInput 0 64) :=
  (NativeChildSeedView.forkChild_header world parent label context (by decide +kernel) (by decide +kernel)).beginField
    [4] 17 0 (by decide +kernel)

open MeasureTheory ProbabilityTheory
example : (InputIndexedOracle.law[|{other | (OracleProgram.run (OracleMachine.take orphanStep 2 0) other).run =
    (OracleProgram.run (OracleMachine.take orphanStep 2 0) world).run}]) {other |
      InputIndexedOracle.block other parentSeedInput 0 64 ∈
        NativeChildSeedView.guesses (OracleProgram.run (OracleMachine.take orphanStep 2 0) other).run.2} =
    1/(2 : ENNReal)^512 := by
  have found : OracleFirstExposure.locate (OracleProgram.run (OracleMachine.take orphanStep 3 0) world).run.2
    (OracleFirstExposure.seedCoordinates parentSeedInput) = some 2 := by decide +kernel
  have result := NativeChildSeedView.orphan_probability orphanStep 3 2 0 world parentSeedInput found
  have count : (NativeChildSeedView.guesses (OracleProgram.run (OracleMachine.take orphanStep 2 0) world).run.2).card = 1 := by
    decide +kernel
  simpa only [count,Nat.cast_one] using result

end
end HasteBootsNativeInputViewSmoke

/-- info: 'FormalProof4FHE.HasteBoots.NativeExactCodec.read_encode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeExactCodec.read_encode

/-- info: 'FormalProof4FHE.HasteBoots.NativeExactCodec.read_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeExactCodec.read_sound

/-- info: 'FormalProof4FHE.HasteBoots.NativeExactCodec.read_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeExactCodec.read_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativeChildSeedView.frameSeed_native' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeChildSeedView.frameSeed_native

/-- info: 'FormalProof4FHE.HasteBoots.NativeChildSeedView.quote_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeChildSeedView.quote_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeChildSeedView.guesses_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeChildSeedView.guesses_card_le

/-- info: 'FormalProof4FHE.HasteBoots.NativeChildSeedView.guesses_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeChildSeedView.guesses_append

/-- info: 'FormalProof4FHE.HasteBoots.NativeChildSeedView.forkChild_input' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeChildSeedView.forkChild_input

/-- info: 'FormalProof4FHE.HasteBoots.NativeChildSeedView.seededFrames_valid' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeChildSeedView.seededFrames_valid

/-- info: 'FormalProof4FHE.HasteBoots.NativeChildSeedView.quote_forkChild' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeChildSeedView.quote_forkChild

/-- info: 'FormalProof4FHE.HasteBoots.NativeChildSeedView.frameSeed_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeChildSeedView.frameSeed_sound

/-- info: 'FormalProof4FHE.HasteBoots.NativeChildSeedView.quote_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeChildSeedView.quote_sound

/-- info: 'FormalProof4FHE.HasteBoots.NativeChildSeedView.quote_receipt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeChildSeedView.quote_receipt

/-- info: 'FormalProof4FHE.HasteBoots.NativeChildSeedView.HasHeader.quote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeChildSeedView.HasHeader.quote

/-- info: 'FormalProof4FHE.HasteBoots.NativeChildSeedView.HasHeader.absorb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeChildSeedView.HasHeader.absorb

/-- info: 'FormalProof4FHE.HasteBoots.NativeChildSeedView.forkChild_header' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeChildSeedView.forkChild_header

/-- info: 'FormalProof4FHE.HasteBoots.NativeChildSeedView.HasHeader.request' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeChildSeedView.HasHeader.request

/-- info: 'FormalProof4FHE.HasteBoots.NativeChildSeedView.HasHeader.beginField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeChildSeedView.HasHeader.beginField

/-- info: 'FormalProof4FHE.HasteBoots.NativeChildSeedView.orphan_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeChildSeedView.orphan_probability

/-- info: 'FormalProof4FHE.HasteBoots.NativeRootInputView.readBinding_payload' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRootInputView.readBinding_payload

/-- info: 'FormalProof4FHE.HasteBoots.NativeRootInputView.registry_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRootInputView.registry_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeRootInputView.binding_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRootInputView.binding_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeRootInputView.single_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRootInputView.single_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeRootInputView.raw_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRootInputView.raw_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeRootInputView.head_sources' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRootInputView.head_sources

/-- info: 'FormalProof4FHE.HasteBoots.NativeRootInputView.tail_mentions' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRootInputView.tail_mentions

/-- info: 'FormalProof4FHE.HasteBoots.NativeRootInputView.recognized_sources' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRootInputView.recognized_sources

/-- info: 'FormalProof4FHE.HasteBoots.NativeRootInputView.suffix_mentions' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRootInputView.suffix_mentions

/-- info: 'FormalProof4FHE.HasteBoots.NativeRootInputView.head_single' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRootInputView.head_single

/-- info: 'FormalProof4FHE.HasteBoots.NativeRootInputView.recognized_single' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRootInputView.recognized_single

/-- info: 'FormalProof4FHE.HasteBoots.NativeRootInputView.raw_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRootInputView.raw_sound

/-- info: 'FormalProof4FHE.HasteBoots.NativeRootInputView.registry_frames' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRootInputView.registry_frames

/-- info: 'FormalProof4FHE.HasteBoots.NativeRootInputView.binding_frames' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRootInputView.binding_frames

/-- info: 'FormalProof4FHE.HasteBoots.NativeRootInputView.opening_frames' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRootInputView.opening_frames

/-- info: 'FormalProof4FHE.HasteBoots.NativeRootInputView.raw_registry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRootInputView.raw_registry

/-- info: 'FormalProof4FHE.HasteBoots.NativeRootInputView.raw_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRootInputView.raw_binding

/-- info: 'FormalProof4FHE.HasteBoots.NativeRootInputView.raw_opening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRootInputView.raw_opening
