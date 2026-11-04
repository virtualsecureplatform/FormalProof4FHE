module

public import FormalProof4FHE.HasteBoots.NativeSharedLookupProofShape

@[expose] public section

/-!
# Original shared preflight data bounds the actual strict terminal

The same original requests determine checked repetition totals, prepared
jobs, proof dimensions, the scalar statement and terminal request lookup.
Every accepted terminal prefix uses its original request's logical length
and the actual scalar point. No independent logical-prefix or point-length
certificate is supplied. Context/value validation and PCS remain open.
-/

namespace FormalProof4FHE.HasteBoots.NativeSharedLookupPreflightLink

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeSharedLookupStatement (Request)
open NativeLookupBindGeometry (Parameters)
open NativeSharedLookupProofShape (Values)
open NativeTranscript (Transcript)
open InputIndexedOracle (World)

noncomputable section

theorem protocol_counts {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (registry : List Parameters) (helper : Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (preflight : NativeSharedLookupPreflight.preflight registry helper (List.ofFn requests) = some geometry)
    (openingCount : ℕ) (values : Values)
    (shape : NativeSharedLookupProofShape.check registry (List.ofFn requests) geometry openingCount values = true)
    (rootFits : values.roots.length < 2^64) (w lookupFuel equalityFuel : ℕ) (transcript : Transcript) (world : World)
    (ready : NativeSharedLookupPrelude.Ready geometry.geometry.1.val)
    (finished : (OracleProgram.run (NativeSharedLookupPrelude.protocol fits requests geometry.geometry.1 values.multiplicities
      values.roots rootFits w lookupFuel equalityFuel transcript) world).run.1 = some ready) :
    ready.jobs.length = geometry.repetitions.val ∧ ready.equality.points.length = geometry.repetitions.val ∧
      ready.statement.infos.val.length = 2 * geometry.repetitions.val ∧
      values.helpers.length = ready.jobs.length ∧ openingCount = ready.jobs.length := by
  have contract := NativeSharedLookupPrelude.protocol_contract fits requests geometry.geometry.1 values.multiplicities values.roots rootFits
    w lookupFuel equalityFuel transcript world ready finished
  have length := NativeSharedLookupProofShape.prepared_count fits requests registry helper geometry preflight _ ready.jobs contract.prepared
  have dimensions := NativeSharedLookupProofShape.prepared_dimensions fits requests registry helper geometry preflight openingCount values shape
    _ ready.jobs contract.prepared
  exact ⟨length,contract.pointCount.trans length,contract.dimensions.1.trans (contract.dimensions.2.trans (congrArg (2 * ·) length)),
    dimensions.2.1,dimensions.2.2⟩

private theorem get_mem {α : Type} (values : List α) (index : ℕ) (value : α) (found : values[index]? = some value) : value ∈ values := by
  obtain ⟨bound,same⟩ := List.getElem?_eq_some_iff.mp found
  rw [← same]
  exact List.getElem_mem bound

/-- Native numeric preflight plus actual lookup/equality/scalar executions
discharge all logical-prefix bounds of accepted original request lookups. -/
theorem terminal_bounds {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (registry : List Parameters) (helper : Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (preflight : NativeSharedLookupPreflight.preflight registry helper (List.ofFn requests) = some geometry)
    (values : Values) (rootFits : values.roots.length < 2^64)
    (w lookupFuel equalityFuel : ℕ) (transcript : Transcript) (world : World)
    (ready : NativeSharedLookupPrelude.Ready geometry.geometry.1.val)
    (prepared : (OracleProgram.run (NativeSharedLookupPrelude.protocol fits requests geometry.geometry.1 values.multiplicities
      values.roots rootFits w lookupFuel equalityFuel transcript) world).run.1 = some ready)
    (proof : NativeScalarBatchPreflight.Proof) (first : NativeScalarBatchWire.Info) (resultTranscript : Transcript)
    (accepted : NativeScalarBatchPreflight.beginVerify ready.equality.transcript ready.statement proof = .ok resultTranscript)
    (head : ready.statement.infos.val.head? = some first) (fuel : ℕ) (claims : List NativeScalarBatchVerifier.SubClaim)
    (finished : (NativeScalarBatchVerifier.execute ready.statement proof fuel
      (NativeScalarBatchVerifier.initial ready.equality.transcript ready.statement proof) world).1.control = .finished claims)
    (sourceVars : ℕ) (result : NativeSharedLookupGuard.Result)
    (passed : NativeSharedLookupGuard.guard (NativeSharedLookupPrelude.guardInputs requests ready values.sources values.helpers)
      claims sourceVars geometry.geometry.2.val = some result) :
    result.point.length < 64 ∧ ∀ checked ∈ result.checked,
      checked.request.logicalLength.val ≤ 2^result.point.length := by
  have linked := NativeSharedLookupPrelude.protocol_scalar_link fits requests geometry.geometry.1 values.multiplicities values.roots rootFits
    w lookupFuel equalityFuel transcript world ready prepared values.sources values.helpers proof first resultTranscript accepted head
    fuel claims finished sourceVars geometry.geometry.2.val result passed
  have bounds := NativeSharedLookupPreflight.geometry_bounds registry helper (List.ofFn requests) geometry preflight
  refine ⟨by rw [linked.2.1]; exact bounds.1,?_⟩
  intro checked member
  have found := (linked.1.guard.checked checked member).request
  change ((List.ofFn requests).map Request.terminal)[checked.job.request]? = some checked.request at found
  obtain ⟨request,present,same⟩ := List.mem_map.mp (get_mem _ _ _ found)
  rw [← same,linked.2.1]
  exact bounds.2 request present

end

end FormalProof4FHE.HasteBoots.NativeSharedLookupPreflightLink
