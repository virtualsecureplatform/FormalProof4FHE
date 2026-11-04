module

public import FormalProof4FHE.HasteBoots.NativeSharedLookupBody

@[expose] public section

/-! Full Goldilocks Brakedown parent/child execution up to the native PCS
boundary, for already rebuilt requests. No ready transcript, statement,
challenge trace, terminal query or lineage certificate is supplied as input.
A bound result still requires helper and source PCS authentication. -/
namespace FormalProof4FHE.HasteBoots.NativeSharedLookupExecution

open NativeTranscript (Transcript)
open InputIndexedOracle (World)
open NativeBrakedownContext (RowDescription Parameters)
open NativeSharedLookupParent (Oracle models)
open NativeLookupRequestWire (Request)
open NativeSharedLookupBody (Outcome Bound)
open OracleProgram (Program bind run)

abbrev Preparation := Σ geometry : NativeSharedLookupPreflight.Output,
  NativeSharedLookupChild.State × NativeSharedLookupPrelude.Ready geometry.geometry.1.val

noncomputable section

def continueBody {C S B : Type} (registry : NativePrefixCodec.Vector (Oracle C)) (requests : NativePrefixCodec.Vector Request)
    (proof : NativeSharedLookupProofData.Proof S B) (fuel : ℕ) (prepared : Preparation) : Program Outcome :=
  NativeSharedLookupBody.body (models requests) (registry.val.map Oracle.geometry) prepared.1.geometry.2.val prepared.2.1 prepared.2.2 proof fuel

def protocol {C S B : Type} (row : RowDescription C) (registry : NativePrefixCodec.Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : NativePrefixCodec.Vector Request) (proof : NativeSharedLookupProofData.Proof S B)
    (lookupFuel equalityFuel scalarFuel : ℕ) : Program (Option Outcome) :=
  bind (NativeSharedLookupParent.begin row registry helper parent requests proof lookupFuel equalityFuel) (fun prepared =>
    match prepared with
    | none => .pure none
    | some prepared => bind (continueBody registry requests proof scalarFuel prepared) (fun result => .pure (some result)))

/-- Parent/lookup/equality observations precede the scalar/finish body in
one execution. Analysis-prefix unavailability is distinct from body errors. -/
theorem run_protocol {C S B : Type} (row : RowDescription C) (registry : NativePrefixCodec.Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : NativePrefixCodec.Vector Request) (proof : NativeSharedLookupProofData.Proof S B)
    (lookupFuel equalityFuel scalarFuel : ℕ) (world : World) :
    (run (protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run =
      let earlier := (run (NativeSharedLookupParent.begin row registry helper parent requests proof lookupFuel equalityFuel) world).run
      match earlier.1 with
      | none => (none,earlier.2)
      | some prepared =>
        let later := (run (continueBody registry requests proof scalarFuel prepared) world).run
        (some later.1,earlier.2 ++ later.2) := by
  simp only [protocol,OracleProgram.run_bind,ObservationReplay.run_bind]
  cases (run (NativeSharedLookupParent.begin row registry helper parent requests proof lookupFuel equalityFuel) world).run.1 <;>
    simp only [OracleProgram.run,CanonicalTranscriptSampler.run_pure,OracleProgram.run_bind,ObservationReplay.run_bind,List.append_nil]

theorem bound_origin {C S B : Type} (row : RowDescription C) (registry : NativePrefixCodec.Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : NativePrefixCodec.Vector Request) (proof : NativeSharedLookupProofData.Proof S B)
    (lookupFuel equalityFuel scalarFuel : ℕ) (world : World) (result : Bound)
    (success : (run (protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.1 = some (.bound result)) :
    ∃ geometry launched,
      (run (NativeSharedLookupParent.begin row registry helper parent requests proof lookupFuel equalityFuel) world).run.1 = some ⟨geometry,launched⟩ ∧
      NativeSharedLookupPreflight.preflight (registry.val.map Oracle.geometry) helper.geometry (List.ofFn (models requests)) = some geometry ∧
      (run (NativeSharedLookupChild.launch requests.property.le (models requests) .retain (registry.val.map Oracle.geometry)
        geometry proof lookupFuel equalityFuel (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.1) world).run.1 = some launched ∧
      (run (NativeSharedLookupBody.body (models requests) (registry.val.map Oracle.geometry) geometry.geometry.2.val
        launched.1 launched.2 proof scalarFuel) world).run.1 = .bound result := by
  rw [run_protocol] at success
  cases began : (run (NativeSharedLookupParent.begin row registry helper parent requests proof lookupFuel equalityFuel) world).run.1 with
  | none => simp only [began] at success; contradiction
  | some prepared =>
    simp only [began] at success
    have completed := Option.some.inj success
    obtain ⟨geometry,launched,same,_,numeric,executed⟩ := NativeSharedLookupParent.begin_spec row registry helper parent requests proof lookupFuel equalityFuel world prepared began
    subst prepared
    exact ⟨geometry,launched,rfl,numeric,executed,completed⟩

/-- All terminal prefix bounds and equality draw records are derived from
one actual completed execution, using the same proof and original requests. -/
theorem bound_terminal {C S B : Type} (row : RowDescription C) (registry : NativePrefixCodec.Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : NativePrefixCodec.Vector Request) (proof : NativeSharedLookupProofData.Proof S B)
    (lookupFuel equalityFuel scalarFuel : ℕ) (world : World) (result : Bound)
    (success : (run (protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.1 = some (.bound result)) :
    result.terminal.point.length < 64 ∧ result.child.binding = none ∧
      ∀ checked ∈ result.terminal.checked, checked.request.logicalLength.val ≤ 2^result.terminal.point.length ∧
        ∃ draw : NativeLookupEquality.Draw result.terminal.point.length NativeExtensionFields.Goldilocks3, NativeGoldLookupEquality.DrawEvidence draw checked.equalityPoint := by
  obtain ⟨geometry,launched,_,numeric,executed,body⟩ := bound_origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result success
  have launch := NativeSharedLookupChild.launch_spec requests.property.le (models requests) .retain (registry.val.map Oracle.geometry)
    geometry proof lookupFuel equalityFuel (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.1 world launched.1 launched.2 executed
  have bodyContract := NativeSharedLookupBody.body_bound (models requests) (registry.val.map Oracle.geometry) geometry.geometry.2.val
    launched.1 launched.2 proof scalarFuel world result body
  have completed := bodyContract.2.scalar
  rw [bodyContract.1] at completed
  obtain ⟨bound,first,accepted,head⟩ := NativeSharedLookupBody.finished_preflight launched.2.equality.transcript launched.2.statement proof.algebra scalarFuel world result.claims completed
  have bounds := NativeSharedLookupPreflightLink.terminal_bounds requests.property.le (models requests) (registry.val.map Oracle.geometry)
    helper.geometry geometry numeric proof.values proof.roots.property 7 lookupFuel equalityFuel _ world launched.2 launch.2.2.2
    proof.algebra first bound accepted head scalarFuel result.claims completed result.sourceVariables result.terminal bodyContract.2.guarded
  have linked := NativeSharedLookupPrelude.protocol_scalar_link requests.property.le (models requests) geometry.geometry.1 proof.values.multiplicities
    proof.values.roots proof.roots.property 7 lookupFuel equalityFuel _ world launched.2 launch.2.2.2 proof.values.sources proof.values.helpers
    proof.algebra first bound accepted head scalarFuel result.claims completed result.sourceVariables geometry.geometry.2.val result.terminal bodyContract.2.guarded
  refine ⟨bounds.1,NativeSharedLookupBody.bound_spent _ _ _ _ _ _ world result bodyContract.2,?_⟩
  intro checked member
  obtain ⟨draw,_,evidence⟩ := linked.2.2 checked member
  refine ⟨bounds.2 checked member,?_⟩
  rw [linked.2.1]
  exact ⟨draw,evidence⟩

end

end FormalProof4FHE.HasteBoots.NativeSharedLookupExecution
