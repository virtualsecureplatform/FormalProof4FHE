module
public import FormalProof4FHE.HasteBoots.ExecutableParentInputView
public import FormalProof4FHE.HasteBoots.NativeParentLedger
public import FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication
@[expose] public section
/-! This reference ledger preserves the analysis lists, including duplicates.
A compact representation and a polynomial cost bound remain separate proof
obligations; executable equality alone does not establish efficient extraction. -/
namespace FormalProof4FHE.HasteBoots.ExecutableParentLedger
open InputIndexedOracle (Input)
open NativeRootMessage (Digest)
open NativeCanonicalLookupWire (Source)
open NativeParentLedger (State Parent Plan)
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

def empty : State := ⟨[],∅⟩
def frames (input : Input) : List TranscriptFrame.Frame := (TranscriptFrame.decodeAll input).getD []
def direct (input : Input) : List Source := (NativeRootInputView.raw input).getD []
def helpers (input : Input) : List Digest := (frames input).filterMap ExecutableParentInputView.frameHelper
def roots (input : Input) : List Digest := (frames input).flatMap (fun frame => (ExecutableParentInputView.helperRoots frame).getD [])

def active (state : State) (cache : NativeShakeCache.Cache) (input : Input) : List Parent :=
  match NativeChildSeedView.quote input with
  | none => []
  | some seed => state.parents.filter (fun parent => ExecutableParentInputView.compatible cache parent.input seed)

def resolve (state : State) (cache : NativeShakeCache.Cache) (input : Input) : List Source :=
  direct input ++ (active state cache input).flatMap (fun parent =>
    parent.sources ++ parent.helpers.flatMap (fun context => (roots input).map (fun root => (context,root))))

def contexts (state : State) (cache : NativeShakeCache.Cache) (input : Input) : List Digest :=
  helpers input ++ (active state cache input).flatMap (fun parent => parent.helpers)

def discover (state : State) (cache : NativeShakeCache.Cache) (input : Input) : State :=
  match ExecutableParentInputView.parseParent input with
  | none => state
  | some _ => { state with parents := ⟨input,resolve state cache input,contexts state cache input⟩ :: state.parents }

def prepare (state : State) (cache : NativeShakeCache.Cache) (input : Input) : Plan :=
  let requests := (resolve state cache input).eraseDups.filter (fun key => key ∉ state.frozen)
  ⟨requests,{ discover state cache input with frozen := state.frozen ∪ requests.toFinset }⟩

theorem empty_eq : empty = NativeParentLedger.empty := rfl
theorem frames_eq : frames = NativeParentLedger.frames := rfl
theorem direct_eq : direct = NativeParentLedger.direct := rfl
theorem helpers_eq : helpers = NativeParentLedger.helpers := by
  funext input
  simp only [helpers,NativeParentLedger.helpers,frames_eq,ExecutableParentInputView.frameHelper_eq]
theorem roots_eq : roots = NativeParentLedger.roots := by
  funext input
  simp only [roots,NativeParentLedger.roots,frames_eq,ExecutableParentInputView.helperRoots_eq]

theorem active_eq (state : State) (cache : NativeShakeCache.Cache) (input : Input) :
    active state cache input = NativeParentLedger.active state cache input := by
  cases quoted : NativeChildSeedView.quote input with
  | none => simp only [active,NativeParentLedger.active,quoted]
  | some seed =>
    simp only [active,NativeParentLedger.active,quoted]
    apply List.filter_congr
    intro parent _
    apply Bool.eq_iff_iff.mpr
    simp only [ExecutableParentInputView.compatible_iff,decide_eq_true_eq]

theorem resolve_eq (state : State) (cache : NativeShakeCache.Cache) (input : Input) :
    resolve state cache input = NativeParentLedger.resolve state cache input := by
  simp only [resolve,NativeParentLedger.resolve,direct_eq,active_eq,roots_eq]

theorem contexts_eq (state : State) (cache : NativeShakeCache.Cache) (input : Input) :
    contexts state cache input = NativeParentLedger.contexts state cache input := by
  simp only [contexts,NativeParentLedger.contexts,helpers_eq,active_eq]

theorem discover_eq (state : State) (cache : NativeShakeCache.Cache) (input : Input) :
    discover state cache input = NativeParentLedger.discover state cache input := by
  simp only [discover,NativeParentLedger.discover,ExecutableParentInputView.parseParent_eq,resolve_eq,contexts_eq]
  rfl

theorem prepare_eq (state : State) (cache : NativeShakeCache.Cache) (input : Input) :
    prepare state cache input = NativeParentLedger.prepare state cache input := by
  have decisions : (fun first second : Digest => Fintype.decidablePiFintype first second) = (inferInstance : DecidableEq Digest) := Subsingleton.elim _ _
  simp only [prepare,NativeParentLedger.prepare,resolve_eq,discover_eq]
  rw [decisions]
end FormalProof4FHE.HasteBoots.ExecutableParentLedger
