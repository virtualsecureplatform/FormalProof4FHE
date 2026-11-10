module
public import FormalProof4FHE.HasteBoots.LookupPCSCodeCapacity
@[expose] public section

/-! Original native source/helper constructor results supply the capacity,
positive degree, leaf count and nonzero query conditions of the mixed PCS
layout. No bound is supplied independently from the original objects. -/
namespace FormalProof4FHE.HasteBoots.LookupPCSLayoutBounds
open NativeGoldBlockCode (Stored Tables description)
open NativeBrakedownContext (Parameters)
open NativeSharedLookupStatement (Request)
open NativeSharedLookupPreflight (Output)
open NativeUsizeMessage (Usize)
open MixedWidthLookupOpeningFamily (Root)
open LookupPreflightPCSGeometry (parameters numeric)

def nativeGeometry {count jobs : ℕ} (sources : Fin count → NativeBrakedownParameters.Geometry)
    (helper : NativeBrakedownParameters.Geometry) : Root count jobs → NativeBrakedownParameters.Geometry :=
  Sum.elim sources (fun _ => helper)

/-- Parameter and code constructor results, together with the actual numeric
shared preflight, derive the PCS layout's original-root size conditions. -/
theorem bounds {count jobs : ℕ} (sources : Fin count → Parameters Stored) (helper : Parameters Stored)
    (requests : List Request) (out : Output)
    (accepted : NativeSharedLookupPreflight.preflight (List.ofFn (fun source => numeric (sources source)))
      (numeric helper) requests = some out)
    (sourceGeometry : Fin count → NativeBrakedownParameters.Geometry)
    (sourcesBuilt : ∀ source, NativeBrakedownParameters.build description (sources source) = some (sourceGeometry source))
    (helperGeometry : NativeBrakedownParameters.Geometry)
    (helperBuilt : NativeBrakedownParameters.build description helper = some helperGeometry)
    (tables : Root count jobs → Tables) (messages blowups : Root count jobs → Usize)
    (constructed : ∀ root, NativeGoldBlockCode.build (tables root) (messages root)
      (parameters sources helper root).width (blowups root) = .ok (parameters sources helper root).code) :
    let g := LookupPreflightPCSGeometry.geometry (jobs := jobs) sources helper requests out accepted
      sourceGeometry sourcesBuilt helperGeometry helperBuilt
    ∀ root,
      2 ^ g.suffix root ≤ g.m root * MixedWidthLookupOpeningFamily.packedWidth
        (3 + (LookupPreflightPacking.packing (numeric helper) out).sourcePadding)
        (3 + (LookupPreflightPacking.packing (numeric helper) out).helperPadding) root ∧
      0 < g.m root ∧ g.m root ≤ 2 ^ (nativeGeometry sourceGeometry helperGeometry root).height ∧
      g.queries root ≠ 0 ∧
      (nativeGeometry sourceGeometry helperGeometry root).height = NativeGoldBlockCode.logSize (parameters sources helper root).code := by
  dsimp only
  intro root
  have built : NativeBrakedownParameters.build description (parameters sources helper root) =
      some (nativeGeometry sourceGeometry helperGeometry root) := by
    cases root with
    | inl source => exact sourcesBuilt source
    | inr job => exact helperBuilt
  have spec := LookupPCSCodeCapacity.code_spec (tables root) (messages root) (blowups root)
    (parameters sources helper root) (constructed root) (nativeGeometry sourceGeometry helperGeometry root) built
  have width := LookupPreflightPCSGeometry.root_widths sources helper requests out accepted root
  have queries := (NativeBrakedownParameters.build_spec description _ _ built).basic.2.2.2
  change 2 ^ ((parameters sources helper root).numVariables.val - (parameters sources helper root).leftVariables.val) ≤
      (parameters sources helper root).code.messageBlocks.val * _ ∧
    0 < (parameters sources helper root).code.messageBlocks.val ∧
    (parameters sources helper root).code.messageBlocks.val ≤ _ ∧
    (parameters sources helper root).queries.val ≠ 0 ∧ _
  rw [width]
  exact ⟨spec.capacity,spec.degreePositive,spec.degreeLeaves,queries,spec.height⟩

end FormalProof4FHE.HasteBoots.LookupPCSLayoutBounds
