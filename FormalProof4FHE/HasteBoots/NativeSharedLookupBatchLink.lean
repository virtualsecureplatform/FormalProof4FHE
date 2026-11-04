module

public import FormalProof4FHE.HasteBoots.NativeSharedLookupGuard
public import FormalProof4FHE.HasteBoots.NativeScalarBatchContract

@[expose] public section

/-!
# Shared lookup guards consume actual scalar-verifier outputs

The strict caller reads the common point from claims[0], not from an
independently supplied identity point. The initialized scalar verifier's
existing contract supplies every indexed claim's identical computed point
and every sampled coefficient record. The guard records supply the exact
sum/helper equality and original registry-slot copies. Full statement/job
schedule alignment, equality-point draw composition, caller geometry and
PCS authentication remain separate obligations.
-/

namespace FormalProof4FHE.HasteBoots.NativeSharedLookupBatchLink

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeGoldExtensionArithmetic (Word)
open NativeScalarBatchWire NativeScalarBatchPreflight NativeScalarBatchVerifier
open NativeSharedLookupGuard
open NativeTranscript (Transcript)
open InputIndexedOracle (World)

noncomputable section

structure Linked (data : Inputs) (statement : Statement) (proof : Proof) (first : Info) (machine : Machine)
    (claims : List SubClaim) (sourceVars width : ℕ) (result : Result) : Prop where
  batch : NativeScalarBatchContract.Contract statement proof first machine claims
  guard : Accepted data claims sourceVars width result
  point : result.point = machine.completed.map (fun entry => entry.challenge)
  length : result.point.length = first.numVariables.val
  claims : ∀ entry ∈ result.checked,
    entry.sumClaim ∈ claims ∧ entry.identityClaim ∈ claims ∧
      entry.sumClaim.point = result.point ∧ entry.identityClaim.point = result.point ∧
      goldExtensionValue entry.sumClaim.expected = goldExtensionValue entry.helper ∧
      List.Forall₂ (fun slot value => data.sourceValues[slot]? = some value) entry.request.sourceSlots entry.values

private theorem get_mem {a : Type} (values : List a) (index : ℕ) (value : a) (found : values[index]? = some value) : value ∈ values := by
  obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp found
  rw [← same]
  exact List.getElem_mem bound

private theorem head_mem {a : Type} (values : List a) (value : a) (found : values.head? = some value) : value ∈ values := by
  cases values with
  | nil => contradiction
  | cons head tail =>
    have same : head = value := Option.some.inj found
    rw [← same]
    exact List.mem_cons_self

/-- The common-point and sum/helper links are derived from the actual returned
claim list and actual guard run, rather than supplied per-equation certificates. -/
theorem link_contract (data : Inputs) (statement : Statement) (proof : Proof) (first : Info) (machine : Machine)
    (claims : List SubClaim) (contract : NativeScalarBatchContract.Contract statement proof first machine claims)
    (sourceVars width : ℕ) (result : Result) (success : NativeSharedLookupGuard.guard data claims sourceVars width = some result) :
    Linked data statement proof first machine claims sourceVars width result := by
  have checked := guard_spec data claims sourceVars width result success
  have output := NativeScalarBatchContract.contract_output statement proof first machine claims contract
  obtain ⟨head, headGet, headPoint⟩ := checked.head
  have samePoint : result.point = machine.completed.map (fun entry => entry.challenge) :=
    headPoint.trans (output.2.2 head (head_mem claims head headGet)).1
  refine ⟨contract, checked, samePoint, ?_, ?_⟩
  · exact headPoint ▸ (output.2.2 head (head_mem claims head headGet)).2
  · intro entry member
    have evidence := checked.checked entry member
    have sumMember := get_mem claims (2 * entry.ordinal) entry.sumClaim evidence.sum
    have identityMember := get_mem claims (2 * entry.ordinal + 1) entry.identityClaim evidence.identity
    have matched := evidence.matched
    rw [NativeGoldInterpolation.equal_value] at matched
    have sameHelper : goldExtensionValue entry.sumClaim.expected = goldExtensionValue entry.helper := by
      simpa only [NativeInterpolationField.arithmetic, decide_eq_true_eq] using matched
    exact ⟨sumMember, identityMember, (output.2.2 entry.sumClaim sumMember).1.trans samePoint.symm,
      (output.2.2 entry.identityClaim identityMember).1.trans samePoint.symm, sameHelper,
      gather_related data.sourceValues entry.request.sourceSlots entry.values evidence.values⟩

/-- Full entry point: the initialized, executed scalar verifier supplies the
contract itself. No completed-draw, common-point or polynomial trace is input. -/
theorem initialized_link (data : Inputs) (transcript resultTranscript : Transcript) (statement : Statement) (proof : Proof)
    (first : Info) (accepted : beginVerify transcript statement proof = .ok resultTranscript)
    (head : statement.infos.val.head? = some first) (fuel : ℕ) (world : World) (claims : List SubClaim)
    (finished : (execute statement proof fuel (initial transcript statement proof) world).1.control = .finished claims)
    (sourceVars width : ℕ) (result : Result) (success : NativeSharedLookupGuard.guard data claims sourceVars width = some result) :
    Linked data statement proof first (execute statement proof fuel (initial transcript statement proof) world).1
      claims sourceVars width result := by
  exact link_contract data statement proof first _ claims
    (NativeScalarBatchContract.finished_contract transcript resultTranscript statement proof first accepted head fuel world claims finished)
    sourceVars width result success

/-- Successful query construction derives the source/lane geometry from the
actual completed point, without an independent geometry certificate. -/
theorem source_geometry (data : Inputs) (statement : Statement) (proof : Proof) (first : Info) (machine : Machine)
    (claims : List SubClaim) (sourceVars width : ℕ) (result : Result)
    (linked : Linked data statement proof first machine claims sourceVars width result) :
    NativeScalarQueryShape.check sourceVars width result.point.length = true ∧
      width = 2 ^ NativeScalarQueryShape.laneBits width ∧
      NativeScalarQueryShape.laneBits width + sourceVars = first.numVariables.val ∧
      NativeScalarQueryShape.laneBits width < 64 ∧ width * width < 2 ^ 64 := by
  have accepted := NativeGoldScalarQuery.scalarQuery_checked sourceVars width result.point result.pulled linked.guard.query
  refine ⟨accepted, NativeScalarQueryShape.checked_power _ _ _ accepted, ?_,
    NativeScalarQueryShape.checked_shift _ _ _ accepted, ?_⟩
  · rw [← linked.length]
    exact NativeScalarQueryShape.checked_length _ _ _ accepted
  · exact (NativeGoldProjection.dimensions_iff width).mp (NativeScalarQueryShape.checked_dimensions _ _ _ accepted) |>.2

/-- Actual successful claim getters and the original statement's usize vector
bound derive safe native even/odd addresses for every executed guard. -/
theorem claim_addresses (data : Inputs) (statement : Statement) (proof : Proof) (first : Info) (machine : Machine)
    (claims : List SubClaim) (sourceVars width : ℕ) (result : Result)
    (linked : Linked data statement proof first machine claims sourceVars width result) (entry : Checked) (member : entry ∈ result.checked) :
    2 * entry.ordinal < claims.length ∧ 2 * entry.ordinal + 1 < claims.length ∧ 2 * entry.ordinal + 1 < 2 ^ 64 := by
  have evidence := linked.guard.checked entry member
  obtain ⟨sumBound, _⟩ := List.getElem?_eq_some_iff.mp evidence.sum
  obtain ⟨identityBound, _⟩ := List.getElem?_eq_some_iff.mp evidence.identity
  have length := (NativeScalarBatchContract.contract_output statement proof first machine claims linked.batch).2.1
  have capacity := statement.claims.property
  exact ⟨sumBound, identityBound, by omega⟩

/-- Every original guarded point coordinate comes from the actual retained
scalar-challenge draw and its original coefficient vector. -/
theorem point_coordinate (data : Inputs) (statement : Statement) (proof : Proof) (first : Info) (machine : Machine)
    (claims : List SubClaim) (sourceVars width : ℕ) (result : Result)
    (linked : Linked data statement proof first machine claims sourceVars width result) (index : ℕ) (inside : index < result.point.length) :
    ∃ entry, machine.completed[index]? = some entry ∧ result.point[index]? = some entry.challenge ∧
      goldExtensionValue entry.challenge = TypedFieldRequest.scalarValue goldilocksBasis entry.coefficients.values := by
  have bound : index < machine.completed.length := by
    have length := congrArg List.length linked.point
    rw [List.length_map] at length
    omega
  let entry := machine.completed[index]'bound
  refine ⟨entry, List.getElem?_eq_getElem bound, ?_, ?_⟩
  · rw [linked.point, List.getElem?_map, List.getElem?_eq_getElem bound, Option.map_some]
  · exact (linked.batch.2.2.2.2.2 entry (List.getElem_mem bound)).2.2

end

end FormalProof4FHE.HasteBoots.NativeSharedLookupBatchLink
