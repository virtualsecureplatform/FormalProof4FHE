module

public import FormalProof4FHE.HasteBoots.NativeDeferredOpeningBatch
@[expose] public section

/-! Source claims traverse every original slot in order. Every used slot computes
its context before alias comparison; equal aliases compare modulo the field,
while only the first used occurrence appends the original raw claim. -/
namespace FormalProof4FHE.HasteBoots.NativeSharedSourceClaims
open NativePrefixCodec (Vector)
open NativeSharedLookupParent (Oracle)
open NativeBrakedownContext (RowDescription)
open NativeLookupRequestWire (Request Row)
open NativeGoldPcsWire (Query)
open NativeCanonicalLookupWire (Source)
open InputIndexedOracle (World)
open OracleProgram (Program bind run)
noncomputable section
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq

def used {count : ℕ} (requests : Vector Request) (slot : Fin count) : Bool :=
  requests.val.any (fun request => request.sourceSlots.val.any (fun source => source.val == slot.val))

structure Seen where
  slot : ℕ
  key : Source
  values : Row
structure Progress where
  state : NativeDeferredOpeningBatch.State
  seen : List Seen
inductive Error where
  | context | alias | indexingUnavailable
  | push (reason : NativeDeferredOpeningBatch.Error)
  deriving DecidableEq
inductive Result where
  | done (progress : Progress)
  | stopped (progress : Progress) (reason : Error)

def Result.progress : Result → Progress
  | .done progress => progress
  | .stopped progress _ => progress

def afterContext {C : Type} (registry : Vector (Oracle C)) (query : Query) (values : Vector Row)
    (slot : Fin registry.val.length) (before : Progress) : Option NativeRootMessage.Digest → Result
  | none => .stopped before .context
  | some digest =>
    let key : Source := (digest,(registry.val.get slot).root)
    match values.val[slot.val]? with
    | none => .stopped before .indexingUnavailable
    | some row => match before.seen.find? (fun previous => decide (previous.key = key)) with
      | some previous => if NativeGoldPcsClaim.equal previous.values.val row.val then .done before else .stopped before .alias
      | none =>
        let pushed := NativeDeferredOpeningBatch.push registry before.state ⟨slot.val,lt_of_lt_of_le slot.isLt registry.property.le⟩ query row
        match pushed.2 with
        | .error reason => .stopped ⟨pushed.1,before.seen⟩ (.push reason)
        | .ok () => .done ⟨pushed.1,before.seen++[⟨slot.val,key,row⟩]⟩

/-- Every used original slot recomputes its context before any alias/value decision. -/
def step {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (query : Query) (values : Vector Row) (slot : Fin registry.val.length) (before : Progress) : Program Result :=
  if used requests slot then bind (NativeBrakedownContext.context row (registry.val.get slot).parameters)
    (fun context => .pure (afterContext registry query values slot before context))
  else .pure (.done before)

def loop {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (query : Query) (values : Vector Row) : List (Fin registry.val.length) → Progress → Program Result
  | [],before => .pure (.done before)
  | slot::rest,before => bind (step row registry requests query values slot before) (fun result => match result with
    | .stopped progress reason => .pure (.stopped progress reason)
    | .done after => loop row registry requests query values rest after)

def program {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (query : Query) (values : Vector Row) (state : NativeDeferredOpeningBatch.State) : Program Result :=
  loop row registry requests query values (List.finRange registry.val.length) ⟨state,[]⟩

theorem used_iff {count : ℕ} (requests : Vector Request) (slot : Fin count) :
    used requests slot = true ↔ ∃ request ∈ requests.val, ∃ source ∈ request.sourceSlots.val, source.val = slot.val := by
  simp only [used,List.any_eq_true,beq_iff_eq]

theorem skipped {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (query : Query) (values : Vector Row) (slot : Fin registry.val.length) (before : Progress) (world : World)
    (unused : used requests slot ≠ true) : (run (step row registry requests query values slot before) world).run = (.done before,[]) := by
  simp only [step,ite_eq_right unused,OracleProgram.run,CanonicalTranscriptSampler.run_pure]

theorem step_observations {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (query : Query) (values : Vector Row) (slot : Fin registry.val.length) (before : Progress) (world : World) :
    (run (step row registry requests query values slot before) world).run.2 =
      if used requests slot then (run (NativeBrakedownContext.context row (registry.val.get slot).parameters) world).run.2 else [] := by
  unfold step
  split
  · simp only [OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]
  · rfl

theorem afterContext_sources {C : Type} (registry : Vector (Oracle C)) (query : Query) (values : Vector Row)
    (slot : Fin registry.val.length) (before : Progress) (context : Option NativeRootMessage.Digest) :
    (afterContext registry query values slot before context).progress.state.sources = before.state.sources := by
  cases context with
  | none => rfl
  | some digest =>
    simp only [afterContext]
    split
    · rfl
    · split
      · split <;> rfl
      · split <;> exact NativeDeferredOpeningBatch.push_sources _ _ _ _ _

theorem step_sources {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (query : Query) (values : Vector Row) (slot : Fin registry.val.length) (before : Progress) (world : World) :
    (run (step row registry requests query values slot before) world).run.1.progress.state.sources = before.state.sources := by
  unfold step
  split
  · simp only [OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure]
    exact afterContext_sources _ _ _ _ _ _
  · rfl

theorem loop_sources {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (query : Query) (values : Vector Row) (slots : List (Fin registry.val.length)) (before : Progress) (world : World) :
    (run (loop row registry requests query values slots before) world).run.1.progress.state.sources = before.state.sources := by
  induction slots generalizing before with
  | nil => rfl
  | cons slot rest ih =>
    simp only [loop,OracleProgram.run_bind,ObservationReplay.run_bind]
    have same := step_sources row registry requests query values slot before world
    cases current : (run (step row registry requests query values slot before) world).run.1 with
    | stopped progress reason => simpa only [current,OracleProgram.run,CanonicalTranscriptSampler.run_pure] using same
    | done after => exact (ih after).trans (by simpa only [current,Result.progress] using same)
end
end FormalProof4FHE.HasteBoots.NativeSharedSourceClaims
