module
import all FormalProof4FHE.HasteBoots.NativeRegistryAncestry
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input Byte World)
open NativeRootMessage (Digest)
open NativeTranscript (Transcript Observation utf8)
open OracleProgram (Program run bind)
namespace HasteBootsRegistryAncestrySmoke
noncomputable section

def usize (value : ℕ) : NativeUsizeMessage.Usize := ⟨value % 2^64,Nat.mod_lt _ (by decide)⟩
def digest (value : Byte) : Digest := fun _ => value
def root : Digest := digest 7
def description : NativeBrakedownContext.RowDescription (Fin 2) :=
  ⟨fun _ => usize 2,fun _ => usize 32,fun _ => ⟨[],by decide⟩,
    fun code => some [if code.val = 0 then 0 else 1]⟩
def sourceA : NativeBrakedownContext.Parameters (Fin 2) := ⟨usize 1,usize 4,usize 0,usize 3,0⟩
def sourceB : NativeBrakedownContext.Parameters (Fin 2) := ⟨usize 1,usize 4,usize 1,usize 5,1⟩
def helper : NativeBrakedownContext.Parameters (Fin 2) := ⟨usize 3,usize 3,usize 0,usize 7,0⟩
def registry : NativePrefixCodec.Vector (NativeSharedLookupParent.Oracle (Fin 2)) :=
  ⟨[⟨sourceA,root⟩,⟨sourceA,root⟩,⟨sourceB,root⟩],by decide⟩
def expected : NativePrefixCodec.Vector NativeCanonicalLookupWire.Source :=
  ⟨[(digest 0,root),(digest 0,root),(digest 1,root)],by decide⟩
def world : World
  | .inl _ => 9
  | .inr (input,_) => input.getLast?.getD 0
private theorem contexts_computed : (run (NativeSharedLookupParent.contexts description registry.val) world).run.1 = some expected.val := by decide +kernel

def row : NativeLookupRequestWire.Row := ⟨[usize 0],by decide⟩
def config : NativeLookupRequestWire.Config := ⟨usize 1,⟨[row],by decide⟩,usize 1⟩
-- Only duplicate slot1 is used. Earlier slot0 and different-context slot2 still belong to the registry.
def request : NativeLookupRequestWire.Request := ⟨config,⟨[usize 1],by decide⟩⟩
def requests : NativePrefixCodec.Vector NativeLookupRequestWire.Request := ⟨[request],by decide⟩
def parent := NativeTranscript.new [] (digest 0)
def preparation := (run (NativeSharedLookupParent.prepare description registry helper parent requests) world).run
def preflightParent := (run (NativeSharedLookupParent.preflight description registry.val helper parent requests) world).run.1.1
private theorem prepared_exists : ∃ geometry, preparation.1.2 = some geometry := by
  have accepted : preparation.1.2.isSome = true := by decide +kernel
  cases selected : preparation.1.2 with
  | none => simp only [selected,Option.isSome_none,Bool.false_eq_true] at accepted
  | some geometry => exact ⟨geometry,rfl⟩
private theorem registered : preparation.1.1 = NativeCanonicalLookupWire.registry preflightParent expected := by
  obtain ⟨geometry,success⟩ := prepared_exists
  obtain ⟨sources,computed,bytes⟩ := NativeRegistryAncestry.prepare_registered description registry helper parent requests world geometry success
  have same : sources = expected := Subtype.ext (Option.some.inj (computed.symm.trans contexts_computed))
  subst sources
  exact bytes

def frames := (TranscriptFrame.decodeAll preflightParent.input).getD []
private theorem decoded : TranscriptFrame.decodeAll preflightParent.input = some frames := by decide +kernel
private theorem framed : (∀ frame ∈ frames, TranscriptFrame.Valid frame) ∧
    preflightParent.input = TranscriptFrame.encodeMany frames := TranscriptFrame.decodeAll_sound preflightParent.input frames decoded

def packet : NativeLookupMultiplicityWire.Packet := ⟨⟨[],by decide⟩,by decide⟩
def program := bind (NativeSharedLookupParent.prepare description registry helper parent requests)
  (fun pair => NativeSharedLookupChild.start pair.1 packet)
def log := (run program world).run.2
def producer := NativeForkAncestry.seedInput (NativeSharedLookupChild.prepare preparation.1.1 packet)
  NativeSharedLookupChild.childLabel NativeSharedLookupChild.childContext
private theorem observed : (run (NativeSharedLookupChild.start preparation.1.1 packet) world).run.2.Sublist log := by
  unfold log
  rw [program,OracleProgram.run_bind,ObservationReplay.run_bind]
  exact List.sublist_append_right _ _
private theorem realized (key : NativeCanonicalLookupWire.Source) (member : key ∈ expected.val) :
    ∃ index, NativeSeedAncestry.Realized world log producer index (.source key) := by
  have seen := observed
  unfold producer
  rw [registered] at seen ⊢
  exact NativeRegistryAncestry.registered_start_source world log preflightParent frames framed.2 framed.1 expected
    (by decide +kernel) packet (by decide +kernel) (by decide +kernel) seen key member

example : expected.val.length = registry.val.length := rfl
example : expected.val[0]? = expected.val[1]? := rfl
example : expected.val[0]?.map Prod.snd = expected.val[2]?.map Prod.snd := rfl
example : expected.val[0]?.map Prod.fst ≠ expected.val[2]?.map Prod.fst := by decide +kernel
example : request.sourceSlots.val.map Fin.val = [1] := rfl
example : List.Forall₂ (fun entry source =>
    (run (NativeBrakedownContext.context description entry.parameters) world).run.1 = some source.1 ∧ source.2 = entry.root)
    registry.val expected.val := NativeRegistryAncestry.contexts_order description registry.val world expected.val contexts_computed
example : ∃ source, expected.val[2]? = some source ∧
    (run (NativeBrakedownContext.context description registry.val[2].parameters) world).run.1 = some source.1 ∧
    source.2 = registry.val[2].root := NativeRegistryAncestry.contexts_slot description registry.val world expected.val contexts_computed ⟨2,by decide⟩
example : ∃ sources : NativePrefixCodec.Vector NativeCanonicalLookupWire.Source,
    (run (NativeSharedLookupParent.contexts description registry.val) world).run.1 = some sources.val ∧
    preparation.1.1 = NativeCanonicalLookupWire.registry preflightParent sources := by
  obtain ⟨geometry,success⟩ := prepared_exists
  exact NativeRegistryAncestry.prepare_registered description registry helper parent requests world geometry success
example : ∃ index, NativeSeedAncestry.Realized world log producer index (.source (digest 0,root)) := realized _ (by simp [expected])
example : ∃ index, NativeSeedAncestry.Realized world log producer index (.source (digest 1,root)) := realized _ (by simp [expected])
example : preparation.2.IsPrefix log := by
  unfold log
  rw [program,OracleProgram.run_bind,ObservationReplay.run_bind]
  exact ⟨_,rfl⟩

def failingDescription : NativeBrakedownContext.RowDescription (Fin 2) :=
  {description with serialize := fun code => if code.val = 0 then some [0] else none}
example : (run (NativeSharedLookupParent.register failingDescription registry parent) world).run.1 = none := by decide +kernel
example : (run (NativeSharedLookupParent.register failingDescription registry parent) world).run.2.length = 2 := by decide +kernel
example : (run (NativeSharedLookupParent.register description ⟨[],by decide⟩ parent) world).run = (none,[]) := rfl
end
end HasteBootsRegistryAncestrySmoke

/-- info: 'FormalProof4FHE.HasteBoots.NativeRegistryAncestry.contexts_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRegistryAncestry.contexts_order

/-- info: 'FormalProof4FHE.HasteBoots.NativeRegistryAncestry.register_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRegistryAncestry.register_spec

/-- info: 'FormalProof4FHE.HasteBoots.NativeRegistryAncestry.prepare_registered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRegistryAncestry.prepare_registered

/-- info: 'FormalProof4FHE.HasteBoots.NativeRegistryAncestry.launch_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRegistryAncestry.launch_start

/-- info: 'FormalProof4FHE.HasteBoots.NativeRegistryAncestry.bound_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRegistryAncestry.bound_start

/-- info: 'FormalProof4FHE.HasteBoots.NativeRegistryAncestry.contexts_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRegistryAncestry.contexts_slot

/-- info: 'FormalProof4FHE.HasteBoots.NativeRegistryAncestry.bound_registration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRegistryAncestry.bound_registration

/-- info: 'FormalProof4FHE.HasteBoots.NativeRegistryAncestry.registered_start_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRegistryAncestry.registered_start_source

/-- info: 'FormalProof4FHE.HasteBoots.NativeRegistryAncestry.bound_registered_sources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRegistryAncestry.bound_registered_sources
