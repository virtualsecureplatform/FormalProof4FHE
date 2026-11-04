module

public import FormalProof4FHE.HasteBoots.NativeSharedLookupStatement
public import FormalProof4FHE.HasteBoots.NativeLookupBindGeometry

@[expose] public section

/-!
# Terminal bounds from actual binding, statement construction and scalar run

The infos builder fixes the actual scalar dimension. The numeric binding
prefix supplies the machine shift and active-prefix bound. Combining those
with the initialized scalar-verifier/guard linkage derives the terminal's
bounds at its computed point, rather than assuming them independently.
Context hashing, shared-request geometry agreement and PCS remain open.
-/

namespace FormalProof4FHE.HasteBoots.NativeSharedLookupGeometryLink

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeScalarBatchWire NativeScalarBatchPreflight NativeScalarBatchVerifier
open NativeSharedLookupGuard
open NativeTranscript (Transcript)
open InputIndexedOracle (World)
open NativeUsizeMessage (Usize)

noncomputable section

private theorem head_mem {a : Type} (values : List a) (value : a) (found : values.head? = some value) : value ∈ values := by
  cases values with
  | nil => contradiction
  | cons head tail => have same : head = value := Option.some.inj found; rw [← same]; exact List.mem_cons_self

theorem statement_head (n : Usize) (requests : List NativeSharedLookupStatement.Request)
    (jobs : List NativeSharedLookupStatement.Prepared) (multiplicities : List (List GoldWord))
    (statement : Statement) (built : NativeSharedLookupStatement.build n requests jobs multiplicities = some statement)
    (first : Info) (head : statement.infos.val.head? = some first) : first.numVariables = n := by
  have member := head_mem statement.infos.val first head
  rw [(NativeSharedLookupStatement.build_spec n requests jobs multiplicities statement built).1] at member
  exact NativeSharedLookupStatement.infos_numVariables n requests first member

/-- The prefix bounds are consequences of native numeric checks and the exact
compiled statement, at the actual computed scalar-verifier point. -/
theorem linked_terminal_bounds (columns : ℕ) (logicalLength : Usize) (helper : NativeLookupBindGeometry.Parameters)
    (sources : List NativeLookupBindGeometry.Parameters) (geometry : NativeLookupBindGeometry.Output)
    (bound : NativeLookupBindGeometry.bind columns logicalLength helper sources = some geometry)
    (requests : List NativeSharedLookupStatement.Request) (jobs : List NativeSharedLookupStatement.Prepared)
    (multiplicities : List (List GoldWord)) (data : Inputs) (statement : Statement)
    (built : NativeSharedLookupStatement.build geometry.numVariables requests jobs multiplicities = some statement)
    (proof : Proof) (first : Info) (head : statement.infos.val.head? = some first) (machine : Machine)
    (claims : List SubClaim) (sourceVars : ℕ) (result : Result)
    (linked : NativeSharedLookupBatchLink.Linked data statement proof first machine claims sourceVars geometry.width.val result) :
    result.point.length < 64 ∧ logicalLength.val ≤ 2 ^ result.point.length := by
  have dimension := congrArg Fin.val (statement_head geometry.numVariables requests jobs multiplicities statement built first head)
  have same : result.point.length = geometry.numVariables.val := linked.length.trans dimension
  rw [same]
  exact NativeLookupBindGeometry.terminal_bounds columns logicalLength helper sources geometry bound

/-- End-to-end initialized-run form, with neither a point nor a prefix-bound
certificate supplied by the caller. -/
theorem initialized_terminal_bounds (columns : ℕ) (logicalLength : Usize) (helper : NativeLookupBindGeometry.Parameters)
    (sources : List NativeLookupBindGeometry.Parameters) (geometry : NativeLookupBindGeometry.Output)
    (bound : NativeLookupBindGeometry.bind columns logicalLength helper sources = some geometry)
    (requests : List NativeSharedLookupStatement.Request) (jobs : List NativeSharedLookupStatement.Prepared)
    (multiplicities : List (List GoldWord)) (data : Inputs) (transcript resultTranscript : Transcript)
    (statement : Statement) (built : NativeSharedLookupStatement.build geometry.numVariables requests jobs multiplicities = some statement)
    (proof : Proof) (first : Info) (accepted : beginVerify transcript statement proof = .ok resultTranscript)
    (head : statement.infos.val.head? = some first) (fuel : ℕ) (world : World) (claims : List SubClaim)
    (finished : (execute statement proof fuel (initial transcript statement proof) world).1.control = .finished claims)
    (sourceVars : ℕ) (result : Result)
    (passed : NativeSharedLookupGuard.guard data claims sourceVars geometry.width.val = some result) :
    result.point.length < 64 ∧ logicalLength.val ≤ 2 ^ result.point.length := by
  exact linked_terminal_bounds columns logicalLength helper sources geometry bound requests jobs multiplicities data statement built
    proof first head _ claims sourceVars result
    (NativeSharedLookupBatchLink.initialized_link data transcript resultTranscript statement proof first accepted head fuel world claims
      finished sourceVars geometry.width.val result passed)

end

end FormalProof4FHE.HasteBoots.NativeSharedLookupGeometryLink
