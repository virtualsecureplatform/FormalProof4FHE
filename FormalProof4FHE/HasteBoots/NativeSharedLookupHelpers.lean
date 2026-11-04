module

public import FormalProof4FHE.HasteBoots.NativeSharedLookupExecution
public import FormalProof4FHE.HasteBoots.NativeGoldPcsWire
public import FormalProof4FHE.HasteBoots.NativeGoldHelper

@[expose] public section

/-! The native helper-opening handoff after child finishing. All coefficient
vectors are computed before the literal ordered zip. Brakedown normalization
retains their original raw words. The handoff is not PCS acceptance. -/
namespace FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers

open NativeUsizeMessage (Usize)
open NativeFieldWire (GoldExtension)
open NativeLookupRequestWire (Row)
open NativeRootMessage (Digest)
open NativeGoldPcsWire (Query)
open NativeTranscript (Transcript)
open InputIndexedOracle (World)
open NativeBrakedownContext (RowDescription Parameters)
open NativeSharedLookupParent (Oracle models)
open NativeSharedLookupBody (Bound Outcome)
open OracleProgram (Program bind run)

structure Call (S : Type) where
  root : Digest
  query : Query
  values : Row
  opening : S

structure Plan (S : Type) where
  query : Query
  values : NativePrefixCodec.Vector Row
  calls : List (Call S)

def vector (width : Usize) (value : GoldExtension) : Row :=
  ⟨NativeGoldHelper.vector width.val value,by rw [NativeGoldHelper.vector_length]; exact width.isLt⟩

def values (width : Usize) (helpers : NativePrefixCodec.Vector GoldExtension) : NativePrefixCodec.Vector Row :=
  ⟨helpers.val.map (vector width),by rw [List.length_map]; exact helpers.property⟩

def calls {S : Type} (query : Query) (roots : List Digest) (claimed : List Row) (openings : List S) : List (Call S) :=
  ((roots.zip claimed).zip openings).map (fun entry => ⟨entry.1.1,query,entry.1.2,entry.2⟩)

def build {S B : Type} (width : Usize) (point : List GoldExtension) (proof : NativeSharedLookupProofData.Proof S B) : Option (Plan S) :=
  (NativeGoldPcsWire.coefficientsQuery width.val point).map (fun query =>
    let claimed := values width proof.helpers
    ⟨query,claimed,calls query proof.roots.val claimed.val proof.helperOpenings.val⟩)

theorem vector_raw (width : Usize) (value : GoldExtension) :
    (vector width value).val = NativeGoldHelper.vector width.val value := rfl

theorem values_length (width : Usize) (helpers : NativePrefixCodec.Vector GoldExtension) :
    (values width helpers).val.length = helpers.val.length := List.length_map _

theorem calls_length {S : Type} (query : Query) (roots : List Digest) (claimed : List Row) (openings : List S) :
    (calls query roots claimed openings).length = min (min roots.length claimed.length) openings.length := by
  simp only [calls,List.length_map,List.length_zip]

/-- Each original index reads all three original vectors, in order. -/
theorem calls_get {S : Type} (query : Query) (roots : List Digest) (claimed : List Row) (openings : List S)
    (index : ℕ) (root : Digest) (value : Row) (opening : S)
    (atRoot : roots[index]? = some root) (atValue : claimed[index]? = some value) (atOpening : openings[index]? = some opening) :
    (calls query roots claimed openings)[index]? = some ⟨root,query,value,opening⟩ := by
  obtain ⟨rootBound,rootEq⟩ := List.getElem?_eq_some_iff.mp atRoot
  obtain ⟨valueBound,valueEq⟩ := List.getElem?_eq_some_iff.mp atValue
  obtain ⟨openingBound,openingEq⟩ := List.getElem?_eq_some_iff.mp atOpening
  have inside : index < (calls query roots claimed openings).length := by rw [calls_length]; omega
  rw [List.getElem?_eq_getElem inside]
  simp only [calls,List.getElem_map,List.getElem_zip,rootEq,valueEq,openingEq]

structure Spec {S B : Type} (width : Usize) (point : List GoldExtension)
    (proof : NativeSharedLookupProofData.Proof S B) (plan : Plan S) : Prop where
  packed : NativeGoldPcsWire.coefficientsQuery width.val point = some plan.query
  vectors : plan.values = values width proof.helpers
  ordered : plan.calls = calls plan.query proof.roots.val plan.values.val proof.helperOpenings.val

theorem build_spec {S B : Type} (width : Usize) (point : List GoldExtension)
    (proof : NativeSharedLookupProofData.Proof S B) (plan : Plan S) (success : build width point proof = some plan) :
    Spec width point proof plan := by
  obtain ⟨query,packed,same⟩ := Option.map_eq_some_iff.mp success
  subst plan
  exact ⟨packed,rfl,rfl⟩

theorem build_complete {S B : Type} (width : Usize) (point : List GoldExtension)
    (proof : NativeSharedLookupProofData.Proof S B) (shape : NativeGoldProjection.dimensions width.val = true)
    (count : point.length < 2^64) : ∃ plan, build width point proof = some plan := by
  obtain ⟨query,packed,_⟩ := NativeGoldPcsWire.coefficientsQuery_complete width.val point shape count
  refine ⟨⟨query,values width proof.helpers,calls query proof.roots.val (values width proof.helpers).val proof.helperOpenings.val⟩,?_⟩
  simp only [build,packed,Option.map_some]

/-- The actual query has one pair per original scalar point coordinate. -/
theorem query_length {S B : Type} (width : Usize) (point : List GoldExtension)
    (proof : NativeSharedLookupProofData.Proof S B) (plan : Plan S) (success : build width point proof = some plan)
    (shape : NativeGoldProjection.dimensions width.val = true) : plan.query.val.length = point.length := by
  have model := NativeGoldPcsWire.coefficientsQuery_models _ _ _ shape (build_spec _ _ _ _ success).packed
  have length := congrArg List.length model
  simpa only [NativeGoldPcsWire.Query.models,List.length_map,NativeGoldCoefficientsQuery.built_length] using length

/-- A helper call carries the root, raw coefficient vector and opening at the
same original index, with the common query computed by the handoff. -/
theorem packet_at {S B : Type} (width : Usize) (point : List GoldExtension)
    (proof : NativeSharedLookupProofData.Proof S B) (plan : Plan S) (success : build width point proof = some plan)
    (index : ℕ) (root : Digest) (value : GoldExtension) (opening : S)
    (atRoot : proof.roots.val[index]? = some root) (atValue : proof.helpers.val[index]? = some value)
    (atOpening : proof.helperOpenings.val[index]? = some opening) :
    plan.calls[index]? = some ⟨root,plan.query,vector width value,opening⟩ := by
  have spec := build_spec width point proof plan success
  rw [spec.ordered,spec.vectors]
  apply calls_get _ _ _ _ _ _ _ _ atRoot _ atOpening
  simp only [values,List.getElem?_map,atValue,Option.map_some]

/-- Shape checks upstream make the literal native zip lossless. -/
theorem no_truncation {S B : Type} (width : Usize) (point : List GoldExtension)
    (proof : NativeSharedLookupProofData.Proof S B) (plan : Plan S) (success : build width point proof = some plan)
    (helpers : proof.helpers.val.length = proof.roots.val.length)
    (openings : proof.helperOpenings.val.length = proof.roots.val.length) : plan.calls.length = proof.roots.val.length := by
  have spec := build_spec width point proof plan success
  rw [spec.ordered,calls_length,spec.vectors,values_length,helpers,openings,Nat.min_self,Nat.min_self]

/-- Numeric preflight computes the helper's actual dimensions from the common
binding, rather than accepting a caller-supplied helper-geometry certificate. -/
theorem preflight_helper (registry : List NativeLookupBindGeometry.Parameters) (helper : NativeLookupBindGeometry.Parameters)
    (requests : List NativeSharedLookupStatement.Request) (output : NativeSharedLookupPreflight.Output)
    (success : NativeSharedLookupPreflight.preflight registry helper requests = some output) :
    helper.numVariables = output.geometry.1 ∧ (helper.width = output.geometry.2 ∨ helper.width.val = 3) ∧
      output.geometry.1.val ≠ 0 := by
  have spec := NativeSharedLookupPreflight.preflight_spec registry helper requests output success
  have nonempty : output.bindings ≠ [] := by
    intro empty
    exact spec.dimensions.2.1 (by rw [← spec.order,empty]; rfl)
  cases entries : output.bindings with
  | nil => exact (nonempty entries).elim
  | cons first rest =>
    have member : first ∈ output.bindings := by rw [entries]; exact List.mem_cons_self
    have bound := NativeLookupBindGeometry.bind_spec _ _ _ _ _ (spec.bound first member).geometry
    have common := spec.common first member
    have vars := congrArg Prod.fst common
    have width := congrArg Prod.snd common
    change first.geometry.numVariables = output.geometry.1 at vars
    change first.geometry.width = output.geometry.2 at width
    rw [← vars,← width]
    exact ⟨bound.helperVariables,bound.helperWidth,bound.positive⟩

noncomputable section

/-- All dimensions and original packet counts follow from one completed run. -/
theorem completed_geometry {C S B : Type} (row : RowDescription C) (registry : NativePrefixCodec.Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : NativePrefixCodec.Vector NativeLookupRequestWire.Request) (proof : NativeSharedLookupProofData.Proof S B)
    (lookupFuel equalityFuel scalarFuel : ℕ) (world : World) (result : Bound)
    (success : (run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.1 = some (.bound result)) :
    NativeGoldProjection.dimensions helper.width.val = true ∧ result.terminal.point.length = helper.numVariables.val ∧
      result.terminal.point.length ≠ 0 ∧ proof.helpers.val.length = proof.roots.val.length ∧
      proof.helperOpenings.val.length = proof.roots.val.length := by
  obtain ⟨geometry,launched,_,numeric,executed,body⟩ := NativeSharedLookupExecution.bound_origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result success
  have launch := NativeSharedLookupChild.launch_spec requests.property.le (models requests) .retain (registry.val.map Oracle.geometry)
    geometry proof lookupFuel equalityFuel (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.1 world launched.1 launched.2 executed
  have contract := NativeSharedLookupBody.body_bound (models requests) (registry.val.map Oracle.geometry) geometry.geometry.2.val
    launched.1 launched.2 proof scalarFuel world result body
  have guarded := NativeSharedLookupGuard.guard_spec _ _ _ _ _ contract.2.guarded
  have checked := NativeGoldScalarQuery.scalarQuery_checked _ _ _ _ guarded.query
  have sourceShape := NativeScalarQueryShape.checked_dimensions _ _ _ checked
  have helperGeometry := preflight_helper _ _ _ _ numeric
  have helperShape : NativeGoldProjection.dimensions helper.width.val = true := by
    rcases helperGeometry.2.1 with same | three
    · change helper.width = geometry.geometry.2 at same
      rw [same]; exact sourceShape
    · change helper.width.val = 3 at three
      rw [three]; decide
  have completed := contract.2.scalar
  rw [contract.1] at completed
  obtain ⟨bound,first,accepted,head⟩ := NativeSharedLookupBody.finished_preflight launched.2.equality.transcript launched.2.statement proof.algebra scalarFuel world result.claims completed
  have linked := NativeSharedLookupPrelude.protocol_scalar_link requests.property.le (models requests) geometry.geometry.1 proof.values.multiplicities
    proof.values.roots proof.roots.property 7 lookupFuel equalityFuel _ world launched.2 launch.2.2.2 proof.values.sources proof.values.helpers
    proof.algebra first bound accepted head scalarFuel result.claims completed result.sourceVariables geometry.geometry.2.val result.terminal contract.2.guarded
  have dimension := linked.2.1
  have helperVariables : helper.numVariables = geometry.geometry.1 := helperGeometry.1
  refine ⟨helperShape,dimension.trans (congrArg Fin.val helperVariables).symm,?_,?_,?_⟩
  · rw [dimension]; exact helperGeometry.2.2
  · exact launch.2.1.helpers.trans launch.2.1.roots.symm
  · exact launch.2.1.openings.trans launch.2.1.roots.symm

/-- No transcript/hash operation is introduced by constructing the handoff. -/
def handoff {S B : Type} (width : Usize) (proof : NativeSharedLookupProofData.Proof S B) : Option Outcome → Option (Plan S)
  | some (.bound result) => build width result.terminal.point proof
  | _ => none

def protocol {C S B : Type} (row : RowDescription C) (registry : NativePrefixCodec.Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : NativePrefixCodec.Vector NativeLookupRequestWire.Request) (proof : NativeSharedLookupProofData.Proof S B)
    (lookupFuel equalityFuel scalarFuel : ℕ) : Program (Option Outcome × Option (Plan S)) :=
  bind (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel)
    (fun result => .pure (result,handoff helper.width proof result))

theorem run_protocol {C S B : Type} (row : RowDescription C) (registry : NativePrefixCodec.Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : NativePrefixCodec.Vector NativeLookupRequestWire.Request) (proof : NativeSharedLookupProofData.Proof S B)
    (lookupFuel equalityFuel scalarFuel : ℕ) (world : World) :
    (run (protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run =
      let original := (run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run
      ((original.1,handoff helper.width proof original.1),original.2) := by
  simp only [protocol,OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]

/-- The completed entry point always constructs all original helper calls;
no point, prepared query, packet count or ready-state certificate is supplied. -/
theorem completed_handoff {C S B : Type} (row : RowDescription C) (registry : NativePrefixCodec.Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : NativePrefixCodec.Vector NativeLookupRequestWire.Request) (proof : NativeSharedLookupProofData.Proof S B)
    (lookupFuel equalityFuel scalarFuel : ℕ) (world : World) (result : Bound)
    (success : (run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.1 = some (.bound result)) :
    ∃ plan, (run (protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.1 = (some (.bound result),some plan) ∧
      Spec helper.width result.terminal.point proof plan ∧ plan.calls.length = proof.roots.val.length ∧
      plan.query.models = (NativeGoldCoefficientsQuery.built helper.width.val result.terminal.point).pairs := by
  have geometry := completed_geometry row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result success
  obtain ⟨plan,built⟩ := build_complete helper.width result.terminal.point proof geometry.1 (by rw [geometry.2.1]; exact helper.numVariables.isLt)
  have spec := build_spec _ _ _ _ built
  refine ⟨plan,?_,spec,no_truncation _ _ _ _ built geometry.2.2.2.1 geometry.2.2.2.2,?_⟩
  · rw [run_protocol]
    simp only [success,handoff,built]
  · exact NativeGoldPcsWire.coefficientsQuery_models _ _ _ geometry.1 spec.packed

end
end FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers
