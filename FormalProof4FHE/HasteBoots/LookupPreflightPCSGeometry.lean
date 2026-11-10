module
public import FormalProof4FHE.HasteBoots.LookupPreflightPacking
public import FormalProof4FHE.HasteBoots.NativeGoldBlockCode
@[expose] public section

/-! Original native Goldilocks parameter objects determine the mixed-width
PCS tensor splits and query counts. Constructor and preflight success derive
arity obligations; no independent geometry certificate is assumed. Encoder,
code-distance, field/byte and whole-verifier refinement remain separate. -/
namespace FormalProof4FHE.HasteBoots.LookupPreflightPCSGeometry
open NativeGoldBlockCode (Stored description)
open NativeBrakedownContext (Parameters)
open NativeSharedLookupStatement (Request)
open NativeSharedLookupPreflight (Output)
open MixedWidthLookupOpeningFamily (Root Geometry)

/-- The numeric fields inspected by the existing native binding prefix. -/
def numeric (parameters : Parameters Stored) : NativeLookupBindGeometry.Parameters :=
  ⟨parameters.numVariables,parameters.width⟩

def parameters {count jobs : ℕ} (sources : Fin count → Parameters Stored) (helper : Parameters Stored) :
    Root count jobs → Parameters Stored := Sum.elim sources (fun _ => helper)

/-- Tensor and query metadata come from the original objects. The row-code
message-block degree is retained; its RS semantics are a later obligation. -/
def geometry {count jobs : ℕ} (sources : Fin count → Parameters Stored) (helper : Parameters Stored)
    (requests : List Request) (out : Output)
    (accepted : NativeSharedLookupPreflight.preflight (List.ofFn (fun source => numeric (sources source)))
      (numeric helper) requests = some out)
    (sourceGeometry : Fin count → NativeBrakedownParameters.Geometry)
    (sourcesBuilt : ∀ source, NativeBrakedownParameters.build description (sources source) = some (sourceGeometry source))
    (helperGeometry : NativeBrakedownParameters.Geometry)
    (helperBuilt : NativeBrakedownParameters.build description helper = some helperGeometry) :
    Geometry (LookupPreflightPacking.packing (numeric helper) out).lanes
      (LookupPreflightPacking.packing (numeric helper) out).rows count jobs where
  front root := (parameters sources helper root).leftVariables.val
  suffix root := (parameters sources helper root).numVariables.val - (parameters sources helper root).leftVariables.val
  m root := (parameters sources helper root).code.messageBlocks.val
  queries root := (parameters sources helper root).queries.val
  sourceArity source := by
    have native := NativeBrakedownParameters.build_spec description (sources source) (sourceGeometry source) (sourcesBuilt source)
    have split := native.basic.2.1
    have rows := (LookupPreflightPacking.packing_spec _ _ requests out accepted).sourceRows
      (numeric (sources source)) (List.mem_ofFn.mpr ⟨source,rfl⟩)
    change (sources source).numVariables.val = _ at rows
    change (sources source).leftVariables.val +
      ((sources source).numVariables.val - (sources source).leftVariables.val) = _
    omega
  helperArity job := by
    have native := NativeBrakedownParameters.build_spec description helper helperGeometry helperBuilt
    have split := native.basic.2.1
    have rows := (LookupPreflightPacking.packing_spec _ _ requests out accepted).helperRows
    change helper.numVariables.val = _ at rows
    change helper.leftVariables.val + (helper.numVariables.val - helper.leftVariables.val) = _
    omega

/-- The packed width for each original root is its original parameter width,
including compact width-three helpers. No context or commitment is rewritten. -/
theorem root_widths {count jobs : ℕ} (sources : Fin count → Parameters Stored) (helper : Parameters Stored)
    (requests : List Request) (out : Output)
    (accepted : NativeSharedLookupPreflight.preflight (List.ofFn (fun source => numeric (sources source)))
      (numeric helper) requests = some out) :
    ∀ root : Root count jobs,
      MixedWidthLookupOpeningFamily.packedWidth
        (3 + (LookupPreflightPacking.packing (numeric helper) out).sourcePadding)
        (3 + (LookupPreflightPacking.packing (numeric helper) out).helperPadding) root =
      (parameters sources helper root).width.val := by
  intro root
  have native := LookupPreflightPacking.root_widths (jobs := jobs)
    (fun source => numeric (sources source)) (numeric helper) requests out accepted root
  cases root <;> exact native

end FormalProof4FHE.HasteBoots.LookupPreflightPCSGeometry
