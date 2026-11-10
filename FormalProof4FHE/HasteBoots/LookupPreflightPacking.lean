module
public import FormalProof4FHE.HasteBoots.NativeSharedLookupPreflight
public import FormalProof4FHE.HasteBoots.MixedWidthLookupOpeningFamily
@[expose] public section

/-! Packing dimensions are computed from successful native Goldilocks shared
preflight. Compact helpers retain width three; power-of-two source packing is
independent. No geometry decoder or replacement commitment is assumed. Native
field/byte, PCS row-code and complete verifier refinement remain separate. -/
namespace FormalProof4FHE.HasteBoots.LookupPreflightPacking
open NativeLookupBindGeometry (Parameters)
open NativeSharedLookupStatement (Request)
open NativeSharedLookupPreflight (Output)

structure Packing where
  sourcePadding : ℕ
  helperPadding : ℕ
  lanes : ℕ
  rows : ℕ
  deriving DecidableEq

def packing (helper : Parameters) (out : Output) : Packing :=
  ⟨out.geometry.2.val - 3, helper.width.val - 3,
    NativeScalarQueryShape.laneBits out.geometry.2.val,
    out.geometry.1.val - NativeScalarQueryShape.laneBits out.geometry.2.val⟩

/-- Native checked binding supplies the lower bound and power-of-two property
of the actual registry width, including every used and unused registry entry. -/
theorem source_width (registry : List Parameters) (helper : Parameters) (requests : List Request) (out : Output)
    (success : NativeSharedLookupPreflight.preflight registry helper requests = some out) :
    3 ≤ out.geometry.2.val ∧ NativeScalarQueryShape.powerOfTwo out.geometry.2.val = true := by
  have accepted := NativeSharedLookupPreflight.preflight_spec registry helper requests out success
  obtain ⟨request,member⟩ := List.exists_mem_of_ne_nil requests accepted.dimensions.2.1
  obtain ⟨binding,present,_,_,_,widthEq,_,_⟩ :=
    NativeSharedLookupPreflight.request_geometry registry helper requests out success request member
  have bound := accepted.bound binding present
  have native := NativeLookupBindGeometry.bind_spec _ _ _ _ _ bound.geometry
  obtain ⟨first,_,localWidth,lower,power,_,_⟩ := native.first
  rw [← widthEq,localWidth]
  exact ⟨lower,power⟩

structure Spec (registry : List Parameters) (helper : Parameters) (requests : List Request)
    (out : Output) (p : Packing) : Prop where
  sourceShape : 3 + p.sourcePadding = 2 ^ p.lanes
  sourceWidth : 3 + p.sourcePadding = out.geometry.2.val
  helperShape : 3 + p.helperPadding = helper.width.val
  helperAlternatives : p.helperPadding = 0 ∨ p.helperPadding = p.sourcePadding
  sourceRows : ∀ source ∈ registry, source.numVariables.val = p.rows
  sourceWidths : ∀ source ∈ registry, source.width.val = 3 + p.sourcePadding
  helperRows : helper.numVariables.val = p.lanes + p.rows
  terminalArity : p.lanes + p.rows = out.geometry.1.val
  shift : p.lanes + p.rows < 64
  logical : ∀ request ∈ requests, request.terminal.logicalLength.val ≤ 2 ^ (p.lanes + p.rows)

/-- Every dimension here is obtained from the accepted native computation.
The two allowed helper branches are preserved without padding helper payloads. -/
theorem packing_spec (registry : List Parameters) (helper : Parameters) (requests : List Request) (out : Output)
    (success : NativeSharedLookupPreflight.preflight registry helper requests = some out) :
    Spec registry helper requests out (packing helper out) := by
  obtain ⟨first,_,uniform,width,arityEq,helperVariables,helperWidth⟩ :=
    NativeSharedLookupPreflight.registry_geometry registry helper requests out success
  have source := source_width registry helper requests out success
  have power := NativeScalarQueryShape.power_eq_laneBits out.geometry.2.val source.2
  have sourceShape : 3 + (out.geometry.2.val - 3) = out.geometry.2.val := by omega
  have helperLower : 3 ≤ helper.width.val := by
    rcases helperWidth with same | degree
    · have equal := congrArg Fin.val same
      omega
    · omega
  have helperShape : 3 + (helper.width.val - 3) = helper.width.val := by omega
  have arity : NativeScalarQueryShape.laneBits out.geometry.2.val +
      (out.geometry.1.val - NativeScalarQueryShape.laneBits out.geometry.2.val) = out.geometry.1.val := by
    rw [width] at ⊢
    omega
  have bounds := NativeSharedLookupPreflight.geometry_bounds registry helper requests out success
  refine ⟨sourceShape.trans power,sourceShape,helperShape,?_,?_,?_,?_,arity,?_,?_⟩
  · rcases helperWidth with same | degree
    · right
      exact congrArg (fun value : NativeUsizeMessage.Usize => value.val - 3) same
    · left
      change helper.width.val - 3 = 0
      omega
  · intro source member
    rw [uniform source member]
    dsimp only [packing]
    rw [width,arityEq]
    omega
  · intro source member
    rw [uniform source member,← width]
    exact sourceShape.symm
  · dsimp only [packing]
    rw [arity,helperVariables]
  · simpa only [packing,arity] using bounds.1
  · intro request member
    simpa only [packing,arity] using bounds.2 request member

/-- The per-root widths used by the mixed PCS family are the actual native
registry/helper widths. This does not change payloads or commitments. -/
theorem root_widths {count jobs : ℕ} (registry : Fin count → Parameters) (helper : Parameters)
    (requests : List Request) (out : Output)
    (success : NativeSharedLookupPreflight.preflight (List.ofFn registry) helper requests = some out) :
    ∀ root : MixedWidthLookupOpeningFamily.Root count jobs,
      MixedWidthLookupOpeningFamily.packedWidth (3 + (packing helper out).sourcePadding)
        (3 + (packing helper out).helperPadding) root =
      Sum.elim (fun source => (registry source).width.val) (fun _ => helper.width.val) root := by
  have spec := packing_spec (List.ofFn registry) helper requests out success
  intro root
  cases root with
  | inl source =>
    exact (spec.sourceWidths (registry source) (List.mem_ofFn.mpr ⟨source,rfl⟩)).symm
  | inr helperIndex => exact spec.helperShape

/-- The literal native active length gives a valid mathematical active/inactive
split; no stronger range restriction or supplied prefix-bound certificate is used. -/
theorem logical_shape (registry : List Parameters) (helper : Parameters) (requests : List Request) (out : Output)
    (success : NativeSharedLookupPreflight.preflight registry helper requests = some out)
    (request : Request) (member : request ∈ requests) :
    request.terminal.logicalLength.val +
      (2 ^ ((packing helper out).lanes + (packing helper out).rows) - request.terminal.logicalLength.val) =
      2 ^ ((packing helper out).lanes + (packing helper out).rows) := by
  have bound := (packing_spec registry helper requests out success).logical request member
  omega

end FormalProof4FHE.HasteBoots.LookupPreflightPacking
