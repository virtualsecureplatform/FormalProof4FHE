module

public import FormalProof4FHE.HasteBoots.BatchGrouping
public import FormalProof4FHE.HasteBoots.NativeRegistryAncestry
public import FormalProof4FHE.HasteBoots.NativeGoldHelperVerification
@[expose] public section

/-! Original native source-registry ownership, computed from the contexts of
all original slots before filtering unused groups. Alias identity includes
both the complete computed context digest and the root. Retaining this
metadata erases to the existing registry execution with identical oracle
observations. Ownership does not imply parameter equality without a context
collision argument, nor availability, authenticated claims, or final source
verification. Rust/refinement and security composition remain open. -/
namespace FormalProof4FHE.HasteBoots.NativeSourceRegistry
open InputIndexedOracle (World)
open NativeCanonicalLookupWire (Source)
open NativePrefixCodec (Vector)
open NativeTranscript (Transcript)
open NativeSharedLookupParent (Oracle)
open NativeBrakedownContext (RowDescription)
open OracleProgram (Program bind run)
noncomputable section
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq

abbrev groupCount (sources : Vector Source) := (BatchGrouping.compute sources.val).1.length
abbrev group (sources : Vector Source) (position : Fin sources.val.length) : Fin (groupCount sources) :=
  BatchGrouping.groupOf sources.val position
abbrev representative (sources : Vector Source) (index : Fin (groupCount sources)) : Fin sources.val.length :=
  BatchGrouping.representative sources.val index
/-- Ownership comes from all original registry slots, without a used-slot filter. -/
def owner (sources : Vector Source) (position : Fin sources.val.length) : Fin sources.val.length :=
  representative sources (group sources position)

theorem owner_key (sources : Vector Source) (position : Fin sources.val.length) :
    sources.val.get (owner sources position) = sources.val.get position :=
  BatchGrouping.representative_group_key sources.val position

theorem representative_first (sources : Vector Source) (index : Fin (groupCount sources))
    (earlier : Fin sources.val.length) (before : earlier.val < (representative sources index).val) :
    sources.val.get earlier ≠ sources.val.get (representative sources index) := by
  rw [BatchGrouping.representative_key]
  exact BatchGrouping.representative_first sources.val index earlier before

theorem owner_first (sources : Vector Source) (position earlier : Fin sources.val.length)
    (before : earlier.val < (owner sources position).val) : sources.val.get earlier ≠ sources.val.get position := by
  rw [← owner_key sources position]
  exact representative_first sources (group sources position) earlier before

theorem owner_le (sources : Vector Source) (position : Fin sources.val.length) :
    (owner sources position).val ≤ position.val := by
  by_contra later
  exact owner_first sources position position (Nat.lt_of_not_ge later) rfl

theorem owner_eq_iff (sources : Vector Source) (left right : Fin sources.val.length) :
    owner sources left = owner sources right ↔ sources.val.get left = sources.val.get right := by
  constructor
  · intro same
    rw [← owner_key sources left,← owner_key sources right,same]
  · intro same
    have grouped := (BatchGrouping.groupOf_eq_iff sources.val left right).mpr same
    exact congrArg (representative sources) grouped

theorem owner_idempotent (sources : Vector Source) (position : Fin sources.val.length) :
    owner sources (owner sources position) = owner sources position :=
  (owner_eq_iff sources (owner sources position) position).mpr (owner_key sources position)

/-- Context digest AND root identify an alias; equal roots alone are insufficient. -/
theorem group_eq_iff (sources : Vector Source) (left right : Fin sources.val.length) :
    group sources left = group sources right ↔
      (sources.val.get left).1 = (sources.val.get right).1 ∧ (sources.val.get left).2 = (sources.val.get right).2 := by
  rw [BatchGrouping.groupOf_eq_iff,Prod.ext_iff]

structure Initialized where
  sources : Vector Source
  parent : Transcript

/-- The original native registry initializer, retaining its computed alias keys. -/
def startRegistry {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (parent : Transcript) : Program (Option Initialized) :=
  if registry.val = [] then .pure none else
    bind (NativeSharedLookupParent.contexts row registry.val) (fun sources => match sources with
      | none => .pure none
      | some sources => if fits : sources.length < 2^64 then
          .pure (some ⟨⟨sources,fits⟩,NativeCanonicalLookupWire.registry parent ⟨sources,fits⟩⟩)
        else .pure none)

/-- Retaining alias metadata changes neither the registered parent nor any oracle observation. -/
theorem initialize_erasure {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (parent : Transcript) (world : World) :
    ((run (startRegistry row registry parent) world).run.1.map Initialized.parent,
      (run (startRegistry row registry parent) world).run.2) =
      (run (NativeSharedLookupParent.register row registry parent) world).run := by
  simp only [startRegistry,NativeSharedLookupParent.register]
  split
  · rfl
  · simp only [OracleProgram.run_bind,ObservationReplay.run_bind]
    cases (run (NativeSharedLookupParent.contexts row registry.val) world).run.1 with
    | none => rfl
    | some sources =>
      dsimp only
      split <;> rfl

theorem initialized_origin {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (parent : Transcript)
    (world : World) (initialized : Initialized)
    (executed : (run (startRegistry row registry parent) world).run.1 = some initialized) :
    registry.val ≠ [] ∧ (run (NativeSharedLookupParent.contexts row registry.val) world).run.1 = some initialized.sources.val ∧
      initialized.parent = NativeCanonicalLookupWire.registry parent initialized.sources ∧
      (run (startRegistry row registry parent) world).run.2 = (run (NativeSharedLookupParent.contexts row registry.val) world).run.2 := by
  unfold startRegistry at executed ⊢
  split at executed
  · contradiction
  next nonempty =>
    simp only [ite_eq_right nonempty,OracleProgram.run_bind,ObservationReplay.run_bind] at executed ⊢
    cases computed : (run (NativeSharedLookupParent.contexts row registry.val) world).run.1 with
    | none => simp only [computed,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed; contradiction
    | some sources =>
      simp only [computed] at executed ⊢
      split at executed
      next fits =>
        have same := Option.some.inj executed
        cases same
        exact ⟨nonempty,rfl,rfl,by simp only [dite_eq_left fits,OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]⟩
      next rejected => contradiction

theorem initialized_sources {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (parent : Transcript)
    (world : World) (initialized : Initialized)
    (executed : (run (startRegistry row registry parent) world).run.1 = some initialized) :
    List.Forall₂ (fun entry source => (run (NativeBrakedownContext.context row entry.parameters) world).run.1 = some source.1 ∧
      source.2 = entry.root) registry.val initialized.sources.val :=
  NativeRegistryAncestry.contexts_order row registry.val world initialized.sources.val
    (initialized_origin row registry parent world initialized executed).2.1

/-- Each computed owner refers to an original parameter object, including an earlier unused slot. -/
theorem initialized_owner {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (parent : Transcript)
    (world : World) (initialized : Initialized)
    (executed : (run (startRegistry row registry parent) world).run.1 = some initialized)
    (position : Fin initialized.sources.val.length) :
    ∃ original : Fin registry.val.length,
      original.val = (owner initialized.sources position).val ∧ original.val ≤ position.val ∧
      (run (NativeBrakedownContext.context row (registry.val.get original).parameters) world).run.1 =
        some (initialized.sources.val.get position).1 ∧
      (registry.val.get original).root = (initialized.sources.val.get position).2 := by
  have corresponding := initialized_sources row registry parent world initialized executed
  let selected := owner initialized.sources position
  let original : Fin registry.val.length := ⟨selected.val,by rw [corresponding.length_eq]; exact selected.isLt⟩
  have described := corresponding.get original.isLt selected.isLt
  have same := owner_key initialized.sources position
  refine ⟨original,rfl,owner_le initialized.sources position,?_,?_⟩
  · exact described.1.trans (congrArg (fun source : Source => some source.1) same)
  · exact described.2.symm.trans (congrArg Prod.snd same)

/-- Every successful old initializer has the same computed metadata-bearing result. -/
theorem registered_metadata {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (parent : Transcript)
    (world : World) (registered : Transcript)
    (executed : (run (NativeSharedLookupParent.register row registry parent) world).run.1 = some registered) :
    ∃ initialized, (run (startRegistry row registry parent) world).run.1 = some initialized ∧ initialized.parent = registered := by
  have erased := congrArg Prod.fst (initialize_erasure row registry parent world)
  rw [executed] at erased
  exact Option.map_eq_some_iff.mp erased

/-- Annotation is recovered from the actual registration inside preparation, with its original log. -/
theorem prepared_metadata {C : Type} (row : RowDescription C) (registry : Vector (Oracle C))
    (helper : NativeBrakedownContext.Parameters C) (parent : Transcript)
    (requests : Vector NativeLookupRequestWire.Request) (world : World) (geometry : NativeSharedLookupPreflight.Output)
    (executed : (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.2 = some geometry) :
    ∃ initialized,
      (run (startRegistry row registry (run (NativeSharedLookupParent.preflight row registry.val helper parent requests) world).run.1.1) world).run.1 = some initialized ∧
      initialized.parent = (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.1 ∧
      (run (startRegistry row registry (run (NativeSharedLookupParent.preflight row registry.val helper parent requests) world).run.1.1) world).run.2.Sublist
        (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.2 := by
  simp only [NativeSharedLookupParent.prepare,OracleProgram.run_bind,ObservationReplay.run_bind] at executed ⊢
  cases numeric : (run (NativeSharedLookupParent.preflight row registry.val helper parent requests) world).run.1.2 with
  | none => simp only [numeric,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed; contradiction
  | some geometry =>
    simp only [numeric,OracleProgram.run_bind,ObservationReplay.run_bind] at executed ⊢
    cases registered : (run (NativeSharedLookupParent.register row registry
        (run (NativeSharedLookupParent.preflight row registry.val helper parent requests) world).run.1.1) world).run.1 with
    | none => simp only [registered,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed; contradiction
    | some finalParent =>
      obtain ⟨initialized,annotated,same⟩ := registered_metadata row registry _ world finalParent registered
      refine ⟨initialized,annotated,?_,?_⟩
      · simpa only [registered,OracleProgram.run,CanonicalTranscriptSampler.run_pure] using same
      · have logs := congrArg Prod.snd (initialize_erasure row registry
          (run (NativeSharedLookupParent.preflight row registry.val helper parent requests) world).run.1.1 world)
        rw [logs]
        simp only [OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]
        exact List.sublist_append_right _ _

/-- A completed native lookup body retains metadata from its actual original registry initializer. -/
theorem bound_metadata {C S B : Type} (row : RowDescription C) (registry : Vector (Oracle C))
    (helper : NativeBrakedownContext.Parameters C) (parent : Transcript) (requests : Vector NativeLookupRequestWire.Request)
    (proof : NativeSharedLookupProofData.Proof S B) (lookupFuel equalityFuel scalarFuel : ℕ) (world : World)
    (result : NativeSharedLookupBody.Bound)
    (upstream : (run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.1 = some (.bound result)) :
    ∃ initialized,
      (run (startRegistry row registry (run (NativeSharedLookupParent.preflight row registry.val helper parent requests) world).run.1.1) world).run.1 = some initialized ∧
      initialized.parent = (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.1 ∧
      List.Forall₂ (fun entry source => (run (NativeBrakedownContext.context row entry.parameters) world).run.1 = some source.1 ∧
        source.2 = entry.root) registry.val initialized.sources.val := by
  obtain ⟨geometry,launched,began,_,_,_⟩ := NativeSharedLookupExecution.bound_origin row registry helper
    parent requests proof lookupFuel equalityFuel scalarFuel world result upstream
  obtain ⟨prepared,ready,_,computed,_,_⟩ := NativeSharedLookupParent.begin_spec row registry helper
    parent requests proof lookupFuel equalityFuel world ⟨geometry,launched⟩ began
  obtain ⟨initialized,annotated,parent,_⟩ := prepared_metadata row registry helper parent requests world prepared computed
  exact ⟨initialized,annotated,parent,initialized_sources row registry _ world initialized annotated⟩

/-- The actual completed helper pipeline determines the original registry metadata; none is supplied by its caller. -/
theorem helpers_metadata {B Memory : Type} (ctx : NativeGoldHelperVerification.Context B)
    (choose : NativeGoldPcsProgram.Scheduler Memory) (memory : Memory) (world : World)
    (result : NativeSharedLookupBody.Bound) (plan : NativeSharedLookupHelpers.Plan NativeGoldPcsOpening.Opening)
    (status : NativeGoldHelperVerification.Result Memory)
    (executed : (run (NativeGoldHelperVerification.program ctx choose memory) world).run.1 = .helpers result plan status) :
    ∃ initialized,
      (run (startRegistry NativeGoldBlockCode.description.row ctx.registry
        (run (NativeSharedLookupParent.preflight NativeGoldBlockCode.description.row ctx.registry.val ctx.helper ctx.parent ctx.requests) world).run.1.1) world).run.1 = some initialized ∧
      initialized.parent = (run (NativeSharedLookupParent.prepare NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests) world).run.1.1 ∧
      List.Forall₂ (fun entry source => (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row entry.parameters) world).run.1 = some source.1 ∧
        source.2 = entry.root) ctx.registry.val initialized.sources.val := by
  have origin := NativeGoldHelperVerification.helpers_origin ctx choose memory world result plan status executed
  have upstream := congrArg Prod.fst origin.native
  simp only [NativeGoldHelperVerification.Context.native,NativeSharedLookupHelpers.run_protocol] at upstream
  exact bound_metadata NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
    ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel world result upstream

end
end FormalProof4FHE.HasteBoots.NativeSourceRegistry
