module

public import FormalProof4FHE.HasteBoots.NativeSharedLookupProofData
public import FormalProof4FHE.HasteBoots.NativeSharedLookupMetadata
public import FormalProof4FHE.HasteBoots.TypedTranscriptChild
import all Init.Data.String.Defs

@[expose] public section

/-!
# Actual classical shared lookup child initialization and lineage

Grouped and flattened multiplicities are absorbed in native order before
the typed detached extension fork. The computed parent/checkpoint binding
is retained alongside the child. The initializer is behind the native
shape/value gates and all fields come from one proof object. Parent context
preflight, full child-body orchestration and PCS authentication remain open.
-/

namespace FormalProof4FHE.HasteBoots.NativeSharedLookupChild

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeTranscript (Transcript Observation utf8)
open InputIndexedOracle (Input World)
open OracleProgram (Program bind run)
open NativeLookupMultiplicityWire (Packet)
open NativeSharedLookupProofData (Proof)
open NativeSharedLookupValues (Policy)
open NativeSharedLookupStatement (Request)
open NativeLookupBindGeometry (Parameters)

def groupedLabel : Input := utf8 "shared lookup grouped multiplicities"
def flatLabel : Input := utf8 "extension lookup multiplicities"
def childLabel : Input := utf8 "classical extension lookup child v1"
def childContext : Input := utf8 "packed extension tuple lookup"
def terminalLabel : Input := utf8 "shared lookup terminal values"

def prepare (parent : Transcript) (packet : Packet) : Transcript :=
  NativeTranscript.appendBytes (NativeTranscript.appendBytes parent groupedLabel (NativeLookupMultiplicityWire.grouped packet))
    flatLabel (NativeLookupMultiplicityWire.flattened packet)

theorem prepare_input (parent : Transcript) (packet : Packet) :
    (prepare parent packet).input = parent.input ++
      TranscriptFrame.encode ⟨1,groupedLabel,NativeLookupMultiplicityWire.grouped packet⟩ ++
      TranscriptFrame.encode ⟨1,flatLabel,NativeLookupMultiplicityWire.flattened packet⟩ := rfl

/-- Native frame allocation domains make the complete seed prefix bind the
grouped data, even when two different groupings have the same flattening. -/
theorem prepare_injective (parent : Transcript) (left right : Packet)
    (leftGrouped : (NativeLookupMultiplicityWire.grouped left).length < TranscriptFrame.lengthLimit)
    (rightGrouped : (NativeLookupMultiplicityWire.grouped right).length < TranscriptFrame.lengthLimit)
    (leftFlat : (NativeLookupMultiplicityWire.flattened left).length < TranscriptFrame.lengthLimit)
    (rightFlat : (NativeLookupMultiplicityWire.flattened right).length < TranscriptFrame.lengthLimit)
    (same : (prepare parent left).input = (prepare parent right).input) : left.groups.values = right.groups.values := by
  rw [prepare_input,prepare_input] at same
  have encoded := List.append_cancel_left (by simpa only [List.append_assoc] using same)
  have groupedFits : groupedLabel.length < TranscriptFrame.lengthLimit := by decide +kernel
  have flatFits : flatLabel.length < TranscriptFrame.lengthLimit := by decide +kernel
  have frames := TranscriptFrame.encodeMany_injective
    [⟨1,groupedLabel,NativeLookupMultiplicityWire.grouped left⟩,⟨1,flatLabel,NativeLookupMultiplicityWire.flattened left⟩]
    [⟨1,groupedLabel,NativeLookupMultiplicityWire.grouped right⟩,⟨1,flatLabel,NativeLookupMultiplicityWire.flattened right⟩]
    (by intro frame member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with same | same
        · subst frame; exact ⟨groupedFits,leftGrouped⟩
        · subst frame; exact ⟨flatFits,leftFlat⟩)
    (by intro frame member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with same | same
        · subst frame; exact ⟨groupedFits,rightGrouped⟩
        · subst frame; exact ⟨flatFits,rightFlat⟩)
    (by simpa only [TranscriptFrame.encodeMany,List.append_nil] using encoded)
  exact NativeLookupMultiplicityWire.grouped_injective left right
    (congrArg TranscriptFrame.Frame.message (List.cons.inj frames).1)

structure State where
  parent : Transcript
  binding : TypedTranscriptChild.Binding

def start (parent : Transcript) (packet : Packet) : Program (State × Transcript) :=
  bind (NativeTranscriptProgram.forkChild (prepare parent packet) childLabel childContext) (fun (parent,child) =>
    bind (NativeTranscriptProgram.checkpoint parent) (fun checkpoint =>
      bind (TypedTranscriptChild.identity goldilocksModulus 3 7 child) (fun bytes =>
        .pure (⟨parent,⟨parent.profile,checkpoint,childLabel⟩⟩,bytes))))

def startExecute (world : World) (parent : Transcript) (packet : Packet) : (State × Transcript) × List Observation :=
  let seeded := (NativeTranscript.forkChild world (prepare parent packet) childLabel childContext).run
  let checkpoint := (NativeTranscript.checkpoint world seeded.1.1).run
  let child := TypedTranscriptChild.identityExecute goldilocksModulus 3 7 world seeded.1.2
  ((⟨seeded.1.1,⟨seeded.1.1.profile,checkpoint.1,childLabel⟩⟩,child.1),seeded.2 ++ checkpoint.2 ++ child.2)

theorem run_start (world : World) (parent : Transcript) (packet : Packet) :
    (run (start parent packet) world).run = startExecute world parent packet := by
  simp only [start,startExecute,OracleProgram.run_bind,ObservationReplay.run_bind,NativeTranscriptProgram.run_forkChild,
    NativeTranscriptProgram.run_checkpoint,TypedTranscriptChild.run_identity,OracleProgram.run,CanonicalTranscriptSampler.run_pure,
    List.append_nil,List.append_assoc]

/-- Erasing the concrete retained state gives the existing detached typed
fork result and exactly the same observations, not merely the same law. -/
theorem start_projection (world : World) (parent : Transcript) (packet : Packet) :
    let result := startExecute world parent packet
    ((result.1.1.parent,TypedTranscriptChild.Child.mk (some result.1.2) (some result.1.1.binding)),result.2) =
      TypedTranscriptChild.forkCoreExecute goldilocksModulus 3 7 world (prepare parent packet) childLabel childContext := rfl

theorem start_profiles (world : World) (parent : Transcript) (packet : Packet) :
    (startExecute world parent packet).1.1.parent.profile = parent.profile ∧
      (startExecute world parent packet).1.2.profile = parent.profile ∧
      (startExecute world parent packet).1.1.binding.profile = parent.profile := ⟨rfl,rfl,rfl⟩

theorem start_binding (world : World) (parent : Transcript) (packet : Packet) :
    (startExecute world parent packet).1.1.binding.checkpoint =
      (NativeTranscript.checkpoint world (startExecute world parent packet).1.1.parent).run.1 ∧
      (startExecute world parent packet).1.1.binding.label = childLabel := ⟨rfl,rfl⟩

theorem start_log_length (world : World) (parent : Transcript) (packet : Packet) :
    (startExecute world parent packet).2.length = 7 := rfl

def finish (state : State) (child : Transcript) : Program TypedTranscriptChild.FinishResult :=
  TypedTranscriptChild.finish (some state.parent) ⟨some child,some state.binding⟩

def bindTerminal {S B : Type} (child : Transcript) (proof : Proof S B) : Transcript :=
  NativeTranscript.appendBytes child terminalLabel (NativeSharedLookupProofData.terminal proof)

theorem terminal_bind_injective {S B T C : Type} (child : Transcript) (left : Proof S B) (right : Proof T C)
    (leftFits : (NativeSharedLookupProofData.terminal left).length < TranscriptFrame.lengthLimit)
    (rightFits : (NativeSharedLookupProofData.terminal right).length < TranscriptFrame.lengthLimit)
    (same : (bindTerminal child left).input = (bindTerminal child right).input) : left.sources = right.sources ∧ left.helpers = right.helpers := by
  change child.input ++ TranscriptFrame.encode ⟨1,terminalLabel,NativeSharedLookupProofData.terminal left⟩ =
    child.input ++ TranscriptFrame.encode ⟨1,terminalLabel,NativeSharedLookupProofData.terminal right⟩ at same
  have encoded := List.append_cancel_left same
  have labelFits : terminalLabel.length < TranscriptFrame.lengthLimit := by decide +kernel
  have frames := TranscriptFrame.encodeMany_injective
    [⟨1,terminalLabel,NativeSharedLookupProofData.terminal left⟩] [⟨1,terminalLabel,NativeSharedLookupProofData.terminal right⟩]
    (by intro frame member; obtain rfl := List.mem_singleton.mp member; exact ⟨labelFits,leftFits⟩)
    (by intro frame member; obtain rfl := List.mem_singleton.mp member; exact ⟨labelFits,rightFits⟩)
    (by simpa only [TranscriptFrame.encodeMany,List.append_nil] using encoded)
  exact NativeSharedLookupProofData.terminal_injective left right
    (congrArg TranscriptFrame.Frame.message (List.cons.inj frames).1)

theorem finish_started_iff (world : World) (parent : Transcript) (packet : Packet) (child : Transcript) :
    (run (finish (startExecute world parent packet).1.1 child) world).run.1.outcome = .ok () ↔ child.profile = parent.profile := by
  rw [finish,TypedTranscriptChild.run_finish,TypedTranscriptChild.finish_accepts_iff]
  simp only [startExecute]
  constructor
  · intro accepted; exact accepted.2.1
  · intro profile; exact ⟨True.intro,profile,True.intro⟩

theorem finish_initial (world : World) (parent : Transcript) (packet : Packet) :
    (run (finish (startExecute world parent packet).1.1 (startExecute world parent packet).1.2) world).run.1.outcome = .ok () :=
  (finish_started_iff world parent packet _).mpr (start_profiles world parent packet).2.1

theorem finish_terminal_iff {S B : Type} (world : World) (parent child : Transcript) (proof : Proof S B) :
    (run (finish (startExecute world parent proof.multiplicities).1.1 (bindTerminal child proof)) world).run.1.outcome = .ok () ↔
      child.profile = parent.profile := finish_started_iff world parent proof.multiplicities (bindTerminal child proof)

noncomputable section

/-- The complete proof is the sole source of grouped/flat multiplicities,
opening counts and values. The concrete initializer is inside both gates. -/
def launch {S B : Type} {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (policy : Policy) (registry : List Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (proof : Proof S B) (lookupFuel equalityFuel : ℕ) (parent : Transcript) :
    Program (Option (State × NativeSharedLookupPrelude.Ready geometry.geometry.1.val)) :=
  NativeSharedLookupValidated.withChildState fits requests policy registry geometry proof.helperOpenings.val.length proof.values proof.roots.property
    7 lookupFuel equalityFuel (start parent proof.multiplicities)

theorem launch_rejected {S B : Type} {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (policy : Policy) (registry : List Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (proof : Proof S B) (lookupFuel equalityFuel : ℕ) (parent : Transcript) (world : World)
    (rejected : NativeSharedLookupValidated.checks policy registry (List.ofFn requests) geometry proof.helperOpenings.val.length proof.values = false) :
    (run (launch fits requests policy registry geometry proof lookupFuel equalityFuel parent) world).run = (none,[]) :=
  NativeSharedLookupValidated.withChildState_rejected fits requests policy registry geometry proof.helperOpenings.val.length proof.values proof.roots.property
    7 lookupFuel equalityFuel (start parent proof.multiplicities) world rejected

theorem launch_spec {S B : Type} {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (policy : Policy) (registry : List Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (proof : Proof S B) (lookupFuel equalityFuel : ℕ) (parent : Transcript) (world : World)
    (state : State) (ready : NativeSharedLookupPrelude.Ready geometry.geometry.1.val)
    (success : (run (launch fits requests policy registry geometry proof lookupFuel equalityFuel parent) world).run.1 = some (state,ready)) :
    state = (startExecute world parent proof.multiplicities).1.1 ∧
      NativeSharedLookupProofShape.Accepted registry (List.ofFn requests) geometry proof.helperOpenings.val.length proof.values ∧
      NativeSharedLookupValues.Accepted policy registry.length (List.ofFn requests) proof.values ∧
      (run (NativeSharedLookupPrelude.protocol fits requests geometry.geometry.1 proof.values.multiplicities proof.values.roots proof.roots.property
        7 lookupFuel equalityFuel (startExecute world parent proof.multiplicities).1.2) world).run.1 = some ready := by
  have actual := NativeSharedLookupValidated.withChildState_spec fits requests policy registry geometry proof.helperOpenings.val.length proof.values proof.roots.property
    7 lookupFuel equalityFuel (start parent proof.multiplicities) world state ready success
  simpa only [run_start] using actual

/-- The concrete initializer, sole proof object and rebuilt original
configuration now feed scalar preflight without a metadata certificate. -/
theorem launch_beginVerify {S B : Type} {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (policy : Policy) (original : List Request)
    (rebuilt : NativeSharedLookupConfig.rebuild policy original = some (List.ofFn requests))
    (registry : List Parameters) (helper : Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (preflight : NativeSharedLookupPreflight.preflight registry helper (List.ofFn requests) = some geometry)
    (proof : Proof S B) (lookupFuel equalityFuel : ℕ) (parent : Transcript) (world : World)
    (state : State) (ready : NativeSharedLookupPrelude.Ready geometry.geometry.1.val)
    (success : (run (launch fits requests policy registry geometry proof lookupFuel equalityFuel parent) world).run.1 = some (state,ready))
    (shape : NativeScalarBatchPreflight.proofShape ready.statement proof.algebra = true) :
    NativeScalarBatchPreflight.beginVerify ready.equality.transcript ready.statement proof.algebra =
      .ok (NativeScalarBatchWire.bindStatement ready.equality.transcript ready.statement) :=
  NativeSharedLookupMetadata.validated_beginVerify fits requests policy original rebuilt registry helper geometry preflight
    proof.helperOpenings.val.length proof.values proof.roots.property 7 lookupFuel equalityFuel (start parent proof.multiplicities)
    world state ready success proof.algebra shape

end

end FormalProof4FHE.HasteBoots.NativeSharedLookupChild
