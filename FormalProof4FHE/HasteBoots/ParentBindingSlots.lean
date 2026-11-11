module
public import FormalProof4FHE.HasteBoots.OriginalParentBindings
@[expose] public section

/-! Literal binding sources are gathered from the complete original registry
at the original request addresses. Repeated addresses remain repeated, and
unused registry positions remain in the recovered registry. -/
namespace FormalProof4FHE.HasteBoots.ParentBindingSlots
open NativeSharedLookupParent (Oracle)
open NativeBrakedownContext (RowDescription Parameters)
open NativeCanonicalLookupWire (Source Binding)
open NativeLookupRequestWire (Request)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

def gather (sources : List Source) : List ℕ → Option (List Source)
  | [] => some []
  | index :: rest => sources[index]?.bind (fun source => (gather sources rest).map (source :: ·))

theorem contexts {C : Type} (row : RowDescription C) (registry : List (Oracle C)) (sources : List Source) (world : World)
    (computed : (run (NativeSharedLookupParent.contexts row registry) world).run.1 = some sources)
    (slots : List ℕ) (selected : List (Oracle C)) (found : NativeSharedLookupParent.gather registry slots = some selected) :
    gather sources slots = (run (NativeSharedLookupParent.contexts row selected) world).run.1 := by
  induction slots generalizing selected with
  | nil =>
    have same : [] = selected := Option.some.inj found
    subst selected
    rfl
  | cons index rest ih =>
    simp only [NativeSharedLookupParent.gather] at found
    cases atIndex : registry[index]? with
    | none => simp only [atIndex,Option.bind_none] at found; contradiction
    | some entry =>
      simp only [atIndex,Option.bind_some] at found
      obtain ⟨remaining,remainingFound,same⟩ := Option.map_eq_some_iff.mp found
      obtain ⟨bound,sameEntry⟩ := List.getElem?_eq_some_iff.mp atIndex
      obtain ⟨source,sourceAt,context,root⟩ := NativeRegistryAncestry.contexts_slot row registry world sources computed ⟨index,bound⟩
      rw [sameEntry] at context root
      rw [← same]
      simp only [gather,sourceAt,Option.bind_some,NativeSharedLookupParent.contexts,OracleProgram.run_bind,ObservationReplay.run_bind,context]
      rw [ih remaining remainingFound]
      rw [← root]
      cases (run (NativeSharedLookupParent.contexts row remaining) world).run.1 <;> rfl

theorem binding {C : Type} (row : RowDescription C) (registry : List (Oracle C)) (helper : Parameters C)
    (sources : List Source) (world : World)
    (computed : (run (NativeSharedLookupParent.contexts row registry) world).run.1 = some sources)
    (request : Request) (binding : Binding) (related : ParentBindingTrace.ForRequest row registry helper world request binding) :
    gather sources request.toModel.terminal.sourceSlots = some binding.sources.val := by
  obtain ⟨selected,found,_,_,selectedComputed⟩ := related
  exact (contexts row registry sources world computed request.toModel.terminal.sourceSlots selected found).trans selectedComputed

end
end FormalProof4FHE.HasteBoots.ParentBindingSlots
