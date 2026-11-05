module

public import FormalProof4FHE.HasteBoots.NativeParentInputView
@[expose] public section

/-! Causal parent association using the old observed byte cache. Every compatible
parent is retained, including partially observed seeds. Discovery never freezes
a root or revises an earlier checkpoint; only a subsequent nonempty read can
freeze a newly resolved key. Structural association is not authentication. -/
namespace FormalProof4FHE.HasteBoots.NativeParentLedger
open InputIndexedOracle (Input)
open NativeRootMessage (Digest)
open NativeCanonicalLookupWire (Source)
open TranscriptFrame (Frame)
open scoped Classical
noncomputable section

structure Parent where
  input : Input
  sources : List Source
  helpers : List Digest

structure State where
  parents : List Parent
  frozen : Finset Source

def empty : State := ⟨[],∅⟩

def frames (input : Input) : List Frame := (TranscriptFrame.decodeAll input).getD []
def direct (input : Input) : List Source := (NativeRootInputView.raw input).getD []
def helpers (input : Input) : List Digest := (frames input).filterMap NativeParentInputView.frameHelper

def roots (input : Input) : List Digest := (frames input).flatMap (fun frame => (NativeParentInputView.helperRoots frame).getD [])

def active (state : State) (cache : NativeShakeCache.Cache) (input : Input) : List Parent :=
  match NativeChildSeedView.quote input with
  | none => []
  | some seed => state.parents.filter (fun parent => NativeParentInputView.compatible cache parent.input seed)

def resolve (state : State) (cache : NativeShakeCache.Cache) (input : Input) : List Source :=
  direct input ++ (active state cache input).flatMap (fun parent =>
    parent.sources ++ parent.helpers.flatMap (fun context => (roots input).map (fun root => (context,root))))

def contexts (state : State) (cache : NativeShakeCache.Cache) (input : Input) : List Digest :=
  helpers input ++ (active state cache input).flatMap (fun parent => parent.helpers)

def discover (state : State) (cache : NativeShakeCache.Cache) (input : Input) : State :=
  match NativeParentInputView.parseParent input with
  | none => state
  | some _ => { state with parents := ⟨input,resolve state cache input,contexts state cache input⟩ :: state.parents }

structure Plan where
  requests : List Source
  next : State

def prepare (state : State) (cache : NativeShakeCache.Cache) (input : Input) : Plan :=
  let requests := (resolve state cache input).eraseDups.filter (fun key => key ∉ state.frozen)
  ⟨requests,{ discover state cache input with frozen := state.frozen ∪ requests.toFinset }⟩

theorem discover_frozen (state : State) (cache : NativeShakeCache.Cache) (input : Input) :
    (discover state cache input).frozen = state.frozen := by
  unfold discover
  split <;> rfl

theorem prepare_mem (state : State) (cache : NativeShakeCache.Cache) (input : Input) (key : Source) :
    key ∈ (prepare state cache input).requests ↔ key ∈ resolve state cache input ∧ key ∉ state.frozen := by
  simp [prepare]

theorem prepare_frozen (state : State) (cache : NativeShakeCache.Cache) (input : Input) :
    (prepare state cache input).next.frozen = state.frozen ∪ (resolve state cache input).toFinset := by
  ext key
  simp [prepare]
  tauto

theorem prepare_keeps (state : State) (cache : NativeShakeCache.Cache) (input : Input) :
    state.frozen ⊆ (prepare state cache input).next.frozen := by
  rw [prepare_frozen]
  exact Finset.subset_union_left

theorem prepare_remembers (state : State) (cache : NativeShakeCache.Cache) (input : Input) (key : Source)
    (resolved : key ∈ resolve state cache input) : key ∈ (prepare state cache input).next.frozen := by
  rw [prepare_frozen]
  exact Finset.mem_union_right _ (List.mem_toFinset.mpr resolved)

theorem prepare_no_repeat (state : State) (cache : NativeShakeCache.Cache) (later : Input) (key : Source)
    (registered : key ∈ state.frozen) : key ∉ (prepare state cache later).requests := by
  simp only [prepare_mem]
  exact fun member => member.2 registered

theorem active_member (state : State) (cache : NativeShakeCache.Cache) (input : Input) (seed : Digest)
    (quoted : NativeChildSeedView.quote input = some seed) (parent : Parent) (present : parent ∈ state.parents)
    (compatible : NativeParentInputView.compatible cache parent.input seed) : parent ∈ active state cache input := by
  simp [active,quoted,present,compatible]

theorem resolve_source (state : State) (cache : NativeShakeCache.Cache) (input : Input) (parent : Parent)
    (present : parent ∈ active state cache input) (key : Source) (source : key ∈ parent.sources) :
    key ∈ resolve state cache input := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  exact ⟨parent,present,List.mem_append_left _ source⟩

theorem resolve_helper (state : State) (cache : NativeShakeCache.Cache) (input : Input) (parent : Parent)
    (present : parent ∈ active state cache input) (context root : Digest)
    (helper : context ∈ parent.helpers) (committed : root ∈ roots input) :
    (context,root) ∈ resolve state cache input := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨parent,present,List.mem_append_right _ ?_⟩
  apply List.mem_flatMap.mpr
  exact ⟨context,helper,List.mem_map.mpr ⟨root,committed,rfl⟩⟩


theorem resolve_actual_helper (state : State) (log : List NativeTranscript.Observation)
    (world : InputIndexedOracle.World) (input : Input) (parent : Parent)
    (present : parent ∈ state.parents)
    (quoted : NativeChildSeedView.quote input = some (InputIndexedOracle.block world parent.input 0 64))
    (context root : Digest) (helper : context ∈ parent.helpers) (committed : root ∈ roots input) :
    (context,root) ∈ resolve state (NativeShakeKernel.observed log world) input :=
  resolve_helper state _ input parent
    (active_member state _ input _ quoted parent present (NativeParentInputView.compatible_observed log world parent.input))
    context root helper committed

theorem discover_parents (state : State) (cache : NativeShakeCache.Cache) (input : Input) :
    state.parents.Sublist (discover state cache input).parents := by
  unfold discover
  split
  · exact List.Sublist.refl _
  · exact List.Sublist.cons _ (List.Sublist.refl _)

theorem prepare_parents (state : State) (cache : NativeShakeCache.Cache) (input : Input) :
    state.parents.Sublist (prepare state cache input).next.parents := discover_parents state cache input

/-- Discovery attaches metadata to the selected parent input, using only the old table. -/
theorem discover_entry (state : State) (cache : NativeShakeCache.Cache) (input : Input)
    (decoded : List Frame) (parsed : NativeParentInputView.parseParent input = some decoded) :
    (⟨input,resolve state cache input,contexts state cache input⟩ : Parent) ∈ (discover state cache input).parents := by
  simp [discover,parsed]

theorem helpers_frame (input : Input) (decoded : List Frame)
    (parsed : TranscriptFrame.decodeAll input = some decoded) (frame : Frame) (present : frame ∈ decoded)
    (context : Digest) (recognized : NativeParentInputView.frameHelper frame = some context) :
    context ∈ helpers input := by
  simp only [helpers,frames,parsed,Option.getD_some,List.mem_filterMap]
  exact ⟨frame,present,recognized⟩

theorem roots_frame (input : Input) (decoded : List Frame)
    (parsed : TranscriptFrame.decodeAll input = some decoded) (frame : Frame) (present : frame ∈ decoded)
    (values : List Digest) (recognized : NativeParentInputView.helperRoots frame = some values)
    (root : Digest) (committed : root ∈ values) : root ∈ roots input := by
  simp only [roots,frames,parsed,Option.getD_some,List.mem_flatMap]
  exact ⟨frame,present,by simpa only [recognized,Option.getD_some] using committed⟩

/-- A raw child read before parent discovery does not acquire a snapshot retroactively. -/
theorem discover_no_backdate (state : State) (cache : NativeShakeCache.Cache) (input : Input)
    (key : Source) : key ∈ (discover state cache input).frozen ↔ key ∈ state.frozen := by
  rw [discover_frozen]

end
end FormalProof4FHE.HasteBoots.NativeParentLedger
