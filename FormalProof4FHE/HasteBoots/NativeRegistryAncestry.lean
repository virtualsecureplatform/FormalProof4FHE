module

public import FormalProof4FHE.HasteBoots.NativeForkAncestry
public import FormalProof4FHE.HasteBoots.NativeSharedLookupExecution
import all Init.Data.String.Defs

@[expose] public section

/-! Complete native registry provenance and source ancestry from executed
shared-lookup branches. All original slots, including duplicates and unused
entries, remain in the computed registry. Bound protocol results retain the
actual initializer and realize the registered source facts under explicit
native frame/allocation domains. This does not establish PCS availability,
first-original aliases, full application soundness or physical work bounds. -/
namespace FormalProof4FHE.HasteBoots.NativeRegistryAncestry
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeTranscript (Transcript Observation)
open NativeSharedLookupParent (Oracle)
open NativeBrakedownContext (RowDescription Parameters)
open NativeLookupRequestWire (Request)
open NativeSharedLookupProofData (Proof)
open NativeSharedLookupBody (Bound)
open NativePrefixCodec (Vector)
open OracleProgram (Program bind run)
noncomputable section

/-- Successful contexts retain every original position and its actual context computation. -/
theorem contexts_order {C : Type} (row : RowDescription C) (registry : List (Oracle C)) (world : World)
    (sources : List NativeCanonicalLookupWire.Source)
    (success : (run (NativeSharedLookupParent.contexts row registry) world).run.1 = some sources) :
    List.Forall₂ (fun entry source => (run (NativeBrakedownContext.context row entry.parameters) world).run.1 = some source.1 ∧
      source.2 = entry.root) registry sources := by
  induction registry generalizing sources with
  | nil => have same := Option.some.inj success; subst sources; exact .nil
  | cons entry tail ih =>
    simp only [NativeSharedLookupParent.contexts,OracleProgram.run_bind,ObservationReplay.run_bind] at success
    cases computed : (run (NativeBrakedownContext.context row entry.parameters) world).run.1 with
    | none => simp only [computed,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
    | some digest =>
      simp only [computed,OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success
      obtain ⟨rest,remaining,same⟩ := Option.map_eq_some_iff.mp success
      rw [← same]
      exact .cons ⟨computed,rfl⟩ (ih rest remaining)

/-- A successful register appends the complete computed source vector, including unused/duplicate slots. -/
theorem register_spec {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (parent : Transcript)
    (world : World) (registered : Transcript)
    (success : (run (NativeSharedLookupParent.register row registry parent) world).run.1 = some registered) :
    ∃ sources : Vector NativeCanonicalLookupWire.Source,
      (run (NativeSharedLookupParent.contexts row registry.val) world).run.1 = some sources.val ∧
      registered = NativeCanonicalLookupWire.registry parent sources := by
  unfold NativeSharedLookupParent.register at success
  split at success
  · change none = some registered at success
    contradiction
  · simp only [OracleProgram.run_bind,ObservationReplay.run_bind] at success
    cases computed : (run (NativeSharedLookupParent.contexts row registry.val) world).run.1 with
    | none => simp only [computed,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
    | some sources =>
      simp only [computed] at success
      split at success
      next fits => exact ⟨⟨sources,fits⟩,rfl,(Option.some.inj success).symm⟩
      next tooLong => change none = some registered at success; contradiction

/-- The final registry is derived from the actual preflight and registration branches. -/
theorem prepare_registered {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : Vector Request) (world : World) (geometry : NativeSharedLookupPreflight.Output)
    (success : (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.2 = some geometry) :
    ∃ sources : Vector NativeCanonicalLookupWire.Source,
      (run (NativeSharedLookupParent.contexts row registry.val) world).run.1 = some sources.val ∧
      (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.1 =
        NativeCanonicalLookupWire.registry
          (run (NativeSharedLookupParent.preflight row registry.val helper parent requests) world).run.1.1 sources := by
  change (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.2 = some geometry at success
  simp only [NativeSharedLookupParent.prepare,OracleProgram.run_bind,ObservationReplay.run_bind] at success ⊢
  cases numeric : (run (NativeSharedLookupParent.preflight row registry.val helper parent requests) world).run.1.2 with
  | none => simp only [numeric,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
  | some result =>
    cases registered : (run (NativeSharedLookupParent.register row registry
        (run (NativeSharedLookupParent.preflight row registry.val helper parent requests) world).run.1.1) world).run.1 with
    | none => simp only [numeric,registered,OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
    | some finalParent =>
      obtain ⟨sources,computed,bytes⟩ := register_spec row registry _ world finalParent registered
      refine ⟨sources,computed,?_⟩
      simp only [registered,OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure]
      exact bytes

/-- Passing gates preserves the initializer log even when the later sampling prefix is unfinished. -/
theorem launch_start {S B : Type} {count : ℕ} (fits : count ≤ 2^64)
    (requests : Fin count → NativeSharedLookupStatement.Request) (policy : NativeSharedLookupValues.Policy)
    (registry : List NativeLookupBindGeometry.Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (proof : Proof S B) (lookupFuel equalityFuel : ℕ) (parent : Transcript) (world : World)
    (accepted : NativeSharedLookupValidated.checks policy registry (List.ofFn requests) geometry proof.helperOpenings.val.length proof.values = true) :
    (run (NativeSharedLookupChild.start parent proof.multiplicities) world).run.2.IsPrefix
      (run (NativeSharedLookupChild.launch fits requests policy registry geometry proof lookupFuel equalityFuel parent) world).run.2 := by
  rw [NativeSharedLookupChild.launch,NativeSharedLookupValidated.withChildState_accepted fits requests policy registry geometry
    proof.helperOpenings.val.length proof.values proof.roots.property 7 lookupFuel equalityFuel _ world accepted]
  exact ⟨_,rfl⟩

/-- An accepted protocol branch retains preparation, the gated initializer, and the subsequent body in one log. -/
theorem bound_start {C S B : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : Vector Request) (proof : Proof S B) (lookupFuel equalityFuel scalarFuel : ℕ)
    (world : World) (result : Bound)
    (success : (run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.1 = some (.bound result)) :
    (run (NativeSharedLookupChild.start
      (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.1 proof.multiplicities) world).run.2.Sublist
      (run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.2 := by
  obtain ⟨geometry,launched,began,numeric,executed,body⟩ :=
    NativeSharedLookupExecution.bound_origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result success
  have checked : NativeSharedLookupValidated.checks .retain (registry.val.map Oracle.geometry) (List.ofFn (NativeSharedLookupParent.models requests))
      geometry proof.helperOpenings.val.length proof.values = true := by
    cases check : NativeSharedLookupValidated.checks .retain (registry.val.map Oracle.geometry) (List.ofFn (NativeSharedLookupParent.models requests))
        geometry proof.helperOpenings.val.length proof.values with
    | true => rfl
    | false =>
      rw [NativeSharedLookupChild.launch_rejected requests.property.le (NativeSharedLookupParent.models requests) .retain
        (registry.val.map Oracle.geometry) geometry proof lookupFuel equalityFuel _ world check] at executed
      contradiction
  have start := launch_start requests.property.le (NativeSharedLookupParent.models requests) .retain (registry.val.map Oracle.geometry)
    geometry proof lookupFuel equalityFuel (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.1 world checked
  have prep := NativeSharedLookupParent.begin_spec row registry helper parent requests proof lookupFuel equalityFuel world _ began
  obtain ⟨g,l,same,prepared,_,launch⟩ := prep
  have aligned : g = geometry := by
    have pair := Sigma.mk.inj_iff.mp same
    exact pair.1.symm
  subst g
  have beginLog : (run (NativeSharedLookupParent.begin row registry helper parent requests proof lookupFuel equalityFuel) world).run.2 =
      (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.2 ++
      (run (NativeSharedLookupChild.launch requests.property.le (NativeSharedLookupParent.models requests) .retain (registry.val.map Oracle.geometry)
        geometry proof lookupFuel equalityFuel (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.1) world).run.2 := by
    simp only [NativeSharedLookupParent.begin,OracleProgram.run_bind,ObservationReplay.run_bind,prepared,
      OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]
  have inBegin : (run (NativeSharedLookupChild.start
      (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.1 proof.multiplicities) world).run.2.Sublist
      (run (NativeSharedLookupParent.begin row registry helper parent requests proof lookupFuel equalityFuel) world).run.2 := by
    rw [beginLog]
    exact start.sublist.trans (List.sublist_append_right _ _)
  simp only [NativeSharedLookupExecution.run_protocol,began]
  exact inBegin.trans (List.sublist_append_left _ _)


/-- The context/root pair at each original slot comes from that exact original registry entry. -/
theorem contexts_slot {C : Type} (row : RowDescription C) (registry : List (Oracle C)) (world : World)
    (sources : List NativeCanonicalLookupWire.Source)
    (success : (run (NativeSharedLookupParent.contexts row registry) world).run.1 = some sources)
    (slot : Fin registry.length) :
    ∃ source, sources[slot.val]? = some source ∧
      (run (NativeBrakedownContext.context row registry[slot.val].parameters) world).run.1 = some source.1 ∧
      source.2 = registry[slot.val].root := by
  have order := contexts_order row registry world sources success
  have bounded : slot.val < sources.length := by rw [← order.length_eq]; exact slot.isLt
  refine ⟨sources[slot.val],List.getElem?_eq_getElem bounded,?_⟩
  simpa only [List.get_eq_getElem] using order.get slot.isLt bounded

/-- Success of the real protocol determines its appended complete registry. -/
theorem bound_registration {C S B : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : Vector Request) (proof : Proof S B) (lookupFuel equalityFuel scalarFuel : ℕ)
    (world : World) (result : Bound)
    (success : (run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.1 = some (.bound result)) :
    ∃ sources : Vector NativeCanonicalLookupWire.Source,
      (run (NativeSharedLookupParent.contexts row registry.val) world).run.1 = some sources.val ∧
      (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.1 =
        NativeCanonicalLookupWire.registry
          (run (NativeSharedLookupParent.preflight row registry.val helper parent requests) world).run.1.1 sources := by
  obtain ⟨geometry,launched,began,_,_,_⟩ :=
    NativeSharedLookupExecution.bound_origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result success
  obtain ⟨g,l,_,prepared,_,_⟩ := NativeSharedLookupParent.begin_spec row registry helper parent requests proof lookupFuel equalityFuel world _ began
  exact prepare_registered row registry helper parent requests world g prepared

/-- Complete registry entries become producer facts in the executed native initializer. -/
theorem registered_start_source (world : World) (log : List Observation) (parent : Transcript)
    (before : List TranscriptFrame.Frame) (bytes : parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame) (sources : Vector NativeCanonicalLookupWire.Source)
    (registryFits : (NativeCanonicalLookupWire.sourcesCodec.encode sources).length < TranscriptFrame.lengthLimit)
    (packet : NativeLookupMultiplicityWire.Packet)
    (groupedFits : (NativeLookupMultiplicityWire.grouped packet).length < TranscriptFrame.lengthLimit)
    (flatFits : (NativeLookupMultiplicityWire.flattened packet).length < TranscriptFrame.lengthLimit)
    (observed : (run (NativeSharedLookupChild.start (NativeCanonicalLookupWire.registry parent sources) packet) world).run.2.Sublist log)
    (key : NativeCanonicalLookupWire.Source) (member : key ∈ sources.val) :
    ∃ index, NativeSeedAncestry.Realized world log
      (NativeForkAncestry.seedInput (NativeSharedLookupChild.prepare (NativeCanonicalLookupWire.registry parent sources) packet)
        NativeSharedLookupChild.childLabel NativeSharedLookupChild.childContext) index (.source key) := by
  let registryFrame : TranscriptFrame.Frame := ⟨1,NativeCanonicalLookupWire.registryLabel,NativeCanonicalLookupWire.sourcesCodec.encode sources⟩
  let framed := before++[registryFrame]
  have framedValid : ∀ frame ∈ framed, TranscriptFrame.Valid frame := by
    intro frame member
    rcases List.mem_append.mp member with old | added
    · exact valid frame old
    · obtain rfl := List.mem_singleton.mp added
      exact ⟨by change NativeCanonicalLookupWire.registryLabel.length < _; decide +kernel,registryFits⟩
  have framedBytes := NativeRootInputView.registry_frames parent before bytes sources
  have preparedBytes := NativeForkAncestry.prepare_frames (NativeCanonicalLookupWire.registry parent sources) framed packet framedBytes
  have preparedValid := NativeForkAncestry.prepareFrames_valid framed packet framedValid groupedFits flatFits
  have parsed := NativeForkAncestry.seedInput_parsed _ _ NativeSharedLookupChild.childLabel NativeSharedLookupChild.childContext
    preparedBytes preparedValid (by decide +kernel) (by decide +kernel)
  apply NativeForkAncestry.fork_direct world log _ _ NativeSharedLookupChild.childLabel NativeSharedLookupChild.childContext
    preparedBytes preparedValid (by decide +kernel) (by decide +kernel)
    ((NativeForkAncestry.start_fork world _ packet).trans observed) (.source key)
  change key ∈ NativeParentLedger.direct _
  unfold NativeParentLedger.direct NativeRootInputView.raw
  rw [NativeParentCoverage.parseParent_decode _ _ parsed]
  apply (NativeRootInputView.recognized_sources _ registryFrame _ sources.val (NativeRootInputView.registry_complete sources)).subset member
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self))

/-- Runs reaching the native PCS boundary supply source ancestry for the full original registry;
only the explicit native byte-allocation/framing domain remains as an input. -/
theorem bound_registered_sources {C S B : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : Vector Request) (proof : Proof S B) (lookupFuel equalityFuel scalarFuel : ℕ)
    (world : World) (result : Bound)
    (success : (run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.1 = some (.bound result)) :
    ∃ sources : Vector NativeCanonicalLookupWire.Source,
      (run (NativeSharedLookupParent.contexts row registry.val) world).run.1 = some sources.val ∧
      ∀ frames : List TranscriptFrame.Frame,
        (run (NativeSharedLookupParent.preflight row registry.val helper parent requests) world).run.1.1.input = TranscriptFrame.encodeMany frames →
        (∀ frame ∈ frames, TranscriptFrame.Valid frame) →
        (NativeCanonicalLookupWire.sourcesCodec.encode sources).length < TranscriptFrame.lengthLimit →
        (NativeLookupMultiplicityWire.grouped proof.multiplicities).length < TranscriptFrame.lengthLimit →
        (NativeLookupMultiplicityWire.flattened proof.multiplicities).length < TranscriptFrame.lengthLimit →
        ∀ key ∈ sources.val, ∃ index, NativeSeedAncestry.Realized world
          (run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.2
          (NativeForkAncestry.seedInput (NativeSharedLookupChild.prepare
            (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.1 proof.multiplicities)
            NativeSharedLookupChild.childLabel NativeSharedLookupChild.childContext) index (.source key) := by
  obtain ⟨sources,computed,registered⟩ := bound_registration row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result success
  refine ⟨sources,computed,?_⟩
  intro frames bytes valid registryFits groupedFits flatFits key member
  have observed := bound_start row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result success
  rw [registered] at observed ⊢
  exact registered_start_source world _ _ frames bytes valid sources registryFits proof.multiplicities groupedFits flatFits observed key member

end
end FormalProof4FHE.HasteBoots.NativeRegistryAncestry
