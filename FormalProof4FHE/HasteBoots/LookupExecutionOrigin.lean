module
public import FormalProof4FHE.HasteBoots.LookupIdentityProtocol
public import FormalProof4FHE.HasteBoots.NativeSharedLookupExecution
@[expose] public section

/-! Recover identity-reduction prerequisites from one completed native caller.
Preflight, proof checking, child start, scalar completion and guard success are
outputs of the recovery, not independent certificates supplied by the caller. -/
namespace FormalProof4FHE.HasteBoots.LookupExecutionOrigin
open NativeBrakedownContext (RowDescription Parameters)
open NativeSharedLookupParent (Oracle models)
open NativePrefixCodec (Vector)
open NativeLookupRequestWire (Request)
open NativeTranscript (Transcript)
open InputIndexedOracle (World)
open NativeSharedLookupBody (Bound)
open OracleProgram (run)
noncomputable section

theorem shape_complete (registry : List NativeLookupBindGeometry.Parameters)
    (requests : List NativeSharedLookupStatement.Request) (geometry : NativeSharedLookupPreflight.Output)
    (openingCount : ℕ) (values : NativeSharedLookupProofShape.Values)
    (accepted : NativeSharedLookupProofShape.Accepted registry requests geometry openingCount values) :
    NativeSharedLookupProofShape.check registry requests geometry openingCount values = true := by
  have pairs := List.forall₂_iff_zip.mp accepted.multiplicities
  simp only [NativeSharedLookupProofShape.check,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,and_assoc]
  exact ⟨accepted.openings,pairs.1,(fun pair member => pairs.2 member),accepted.roots,accepted.helpers,accepted.sources,accepted.width⟩

def childStart {C S B : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : Vector Request) (proof : NativeSharedLookupProofData.Proof S B) (world : World) : Transcript :=
  (NativeSharedLookupChild.startExecute world
    (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.1 proof.multiplicities).1.2

structure Origin {C S B : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : Vector Request) (proof : NativeSharedLookupProofData.Proof S B)
    (lookupFuel equalityFuel scalarFuel : ℕ) (world : World) (result : Bound) where
  geometry : NativeSharedLookupPreflight.Output
  preflight : NativeSharedLookupPreflight.preflight (registry.val.map Oracle.geometry) helper.geometry (List.ofFn (models requests)) = some geometry
  ready : NativeSharedLookupPrelude.Ready geometry.geometry.1.val
  prepared : (run (NativeSharedLookupPrelude.protocol requests.property.le (models requests) geometry.geometry.1
    proof.values.multiplicities proof.values.roots proof.roots.property 7 lookupFuel equalityFuel
    (childStart row registry helper parent requests proof world)) world).run.1 = some ready
  shape : NativeSharedLookupProofShape.check (registry.val.map Oracle.geometry) (List.ofFn (models requests)) geometry
    proof.helperOpenings.val.length proof.values = true
  scalar : (NativeScalarBatchVerifier.execute ready.statement proof.algebra scalarFuel
    (NativeScalarBatchVerifier.initial ready.equality.transcript ready.statement proof.algebra) world).1.control = .finished result.claims
  guarded : NativeSharedLookupGuard.guard (NativeSharedLookupPrelude.guardInputs (models requests) ready proof.values.sources proof.values.helpers)
    result.claims result.sourceVariables geometry.geometry.2.val = some result.terminal
  source : ∃ first, (registry.val.map Oracle.geometry).head? = some first ∧ result.sourceVariables = first.numVariables.val

theorem recover {C S B : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : Vector Request) (proof : NativeSharedLookupProofData.Proof S B)
    (lookupFuel equalityFuel scalarFuel : ℕ) (world : World) (result : Bound)
    (success : (run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.1 = some (.bound result)) :
    Nonempty (Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result) := by
  obtain ⟨geometry,launched,_,preflight,executed,body⟩ := NativeSharedLookupExecution.bound_origin row registry helper parent requests proof
    lookupFuel equalityFuel scalarFuel world result success
  have launch := NativeSharedLookupChild.launch_spec requests.property.le (models requests) .retain (registry.val.map Oracle.geometry)
    geometry proof lookupFuel equalityFuel (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.1
    world launched.1 launched.2 executed
  have bodyContract := NativeSharedLookupBody.body_bound (models requests) (registry.val.map Oracle.geometry) geometry.geometry.2.val
    launched.1 launched.2 proof scalarFuel world result body
  have completed := bodyContract.2.scalar
  rw [bodyContract.1] at completed
  exact ⟨⟨geometry,preflight,launched.2,launch.2.2.2,shape_complete _ _ _ _ _ launch.2.1,completed,bodyContract.2.guarded,bodyContract.2.source⟩⟩

variable {C S B : Type} {row : RowDescription C} {registry : Vector (Oracle C)} {helper : Parameters C}
  {parent : Transcript} {requests : Vector Request} {proof : NativeSharedLookupProofData.Proof S B}
  {lookupFuel equalityFuel scalarFuel : ℕ} {world : World} {result : Bound}

def Origin.padding (origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result) : ℕ :=
  origin.geometry.geometry.2.val-3

theorem Origin.width (origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result) :
    origin.geometry.geometry.2.val = 3+origin.padding := by
  have guarded := NativeSharedLookupGuard.guard_spec _ result.claims result.sourceVariables origin.geometry.geometry.2.val result.terminal origin.guarded
  have shape := NativeGoldScalarQuery.scalarQuery_checked _ _ _ _ guarded.query
  have lower := ((NativeGoldProjection.dimensions_iff _).mp (NativeScalarQueryShape.checked_dimensions _ _ _ shape)).1
  unfold Origin.padding
  omega

/-- All original slots, including unused slots and aliases, share the actual
source dimension/width. Full code parameters are not identified with one another. -/
theorem Origin.registry_dimensions (origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result)
    (slot : Fin registry.val.length) :
    (registry.val.get slot).parameters.numVariables.val = result.sourceVariables ∧
      (registry.val.get slot).parameters.width.val = 3+origin.padding := by
  obtain ⟨first,head,uniform,width,_,_,_⟩ := NativeSharedLookupPreflight.registry_geometry _ _ _ _ origin.preflight
  obtain ⟨source,sourceHead,sourceDimension⟩ := origin.source
  have same : source = first := Option.some.inj (sourceHead.symm.trans head)
  subst source
  have selected := uniform (registry.val.get slot).geometry (List.mem_map.mpr ⟨registry.val.get slot,List.get_mem _ _,rfl⟩)
  have dimensions := congrArg NativeLookupBindGeometry.Parameters.numVariables selected
  have widths := congrArg NativeLookupBindGeometry.Parameters.width selected
  refine ⟨(congrArg Fin.val dimensions).trans sourceDimension.symm,?_⟩
  exact (congrArg Fin.val (widths.trans width.symm)).trans origin.width

/-- The native helper dimension is already the full scalar dimension, while
its packing width is independently allowed to be source width or three. -/
theorem Origin.helper_dimensions (origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result) :
    helper.numVariables = origin.geometry.geometry.1 ∧
      (helper.width.val = 3+origin.padding ∨ helper.width.val = 3) := by
  obtain ⟨_,_,_,_,_,variablesEq,widths⟩ := NativeSharedLookupPreflight.registry_geometry _ _ _ _ origin.preflight
  refine ⟨variablesEq,?_⟩
  rcases widths with equal | degree
  · exact Or.inl ((congrArg Fin.val equal).trans origin.width)
  · exact Or.inr degree

end
end FormalProof4FHE.HasteBoots.LookupExecutionOrigin
