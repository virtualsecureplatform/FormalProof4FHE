module

public import FormalProof4FHE.HasteBoots.NativeSourceClaimInvariant
@[expose] public section

/-! Source-loop indexing and claim-counter domains follow from original
registry/value-vector lengths and the remaining finite source slots.
No retry cap, lifetime cap or caller-supplied successful-push certificate
is used. Native context, dimension and alias rejection remain explicit. -/
namespace FormalProof4FHE.HasteBoots.NativeSourceClaimDomain
open NativePrefixCodec (Vector)
open NativeSharedLookupParent (Oracle)
open NativeBrakedownContext (RowDescription)
open NativeLookupRequestWire (Request Row)
open NativeGoldPcsWire (Query)
open NativeSharedSourceClaims (Progress Result afterContext step loop)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq

def PushAvailable : Except NativeDeferredOpeningBatch.Error Unit → Prop
  | .error .unknownSource | .error .indexingUnavailable | .error .allocationUnavailable => False
  | _ => True

def Available : Result → Prop
  | .stopped _ .indexingUnavailable => False
  | .stopped _ (.push reason) => PushAvailable (.error reason)
  | _ => True

theorem push_available {C : Type} (registry : Vector (Oracle C)) (state : NativeDeferredOpeningBatch.State)
    (slot : Fin registry.val.length) (query : Query) (values : Row)
    (sources : state.sources.val.length = registry.val.length) (fits : state.claims.val.length+1 < 2^64) :
    PushAvailable (NativeDeferredOpeningBatch.push registry state ⟨slot.val,lt_of_lt_of_le slot.isLt registry.property.le⟩ query values).2 := by
  unfold NativeDeferredOpeningBatch.push
  split
  next missing =>
    have outside := List.getElem?_eq_none_iff.mp missing
    have inside := slot.isLt
    dsimp only at outside inside
    omega
  next oracle found =>
    split
    · have bounded : slot.val < state.sources.val.length := by rw [sources]; exact slot.isLt
      simp only [dite_eq_left bounded,PushAvailable]
    · trivial

theorem afterContext_available {C : Type} (registry : Vector (Oracle C)) (query : Query) (values : Vector Row)
    (slot : Fin registry.val.length) (before : Progress) (context : Option NativeRootMessage.Digest)
    (sources : before.state.sources.val.length = registry.val.length) (fits : before.state.claims.val.length+1 < 2^64)
    (valueCount : registry.val.length ≤ values.val.length) : Available (afterContext registry query values slot before context) := by
  cases context with
  | none => trivial
  | some digest =>
    simp only [afterContext]
    split
    next missing =>
      have outside := List.getElem?_eq_none_iff.mp missing
      have inside := slot.isLt
      omega
    next row found =>
      split
      · split <;> trivial
      · have available := push_available registry before.state slot query row sources fits
        split
        next reason failed =>
          change PushAvailable (.error reason)
          simpa only [failed] using available
        next passed => trivial

theorem afterContext_count {C : Type} (registry : Vector (Oracle C)) (query : Query) (values : Vector Row)
    (slot : Fin registry.val.length) (before : Progress) (context : Option NativeRootMessage.Digest) :
    (afterContext registry query values slot before context).progress.state.claims.val.length ≤ before.state.claims.val.length+1 := by
  rcases NativeSourceClaimInvariant.afterContext_change registry query values slot before context with same | ⟨digest,row,_,_,_,passed,same⟩
  · rw [same]; omega
  · rw [same]
    exact (NativeDeferredOpeningBatch.push_count registry before.state _ query row passed).1.le

theorem step_available {C : Type} (description : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (query : Query) (values : Vector Row) (slot : Fin registry.val.length) (before : Progress) (world : World)
    (sources : before.state.sources.val.length = registry.val.length) (fits : before.state.claims.val.length+1 < 2^64)
    (valueCount : registry.val.length ≤ values.val.length) :
    Available (run (step description registry requests query values slot before) world).run.1 := by
  unfold step
  split
  · simp only [OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure]
    exact afterContext_available registry query values slot before _ sources fits valueCount
  · trivial

def Count (result : Result) : ℕ := result.progress.state.claims.val.length

theorem step_count {C : Type} (description : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (query : Query) (values : Vector Row) (slot : Fin registry.val.length) (before : Progress) (world : World) :
    Count (run (step description registry requests query values slot before) world).run.1 ≤ before.state.claims.val.length+1 := by
  by_cases used : NativeSharedSourceClaims.used requests slot = true
  · simp only [step,ite_eq_left used,OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure]
    exact afterContext_count registry query values slot before _
  · simp only [step,ite_eq_right used,OracleProgram.run,CanonicalTranscriptSampler.run_pure]
    change before.state.claims.val.length ≤ before.state.claims.val.length+1
    omega

/-- Remaining slots pay for possible local insertions. No retry/lifetime bound is used. -/
theorem loop_available {C : Type} (description : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (query : Query) (values : Vector Row) (slots : List (Fin registry.val.length)) (before : Progress) (world : World)
    (sources : before.state.sources.val.length = registry.val.length)
    (capacity : before.state.claims.val.length+slots.length ≤ registry.val.length)
    (valueCount : registry.val.length ≤ values.val.length) :
    Available (run (loop description registry requests query values slots before) world).run.1 := by
  induction slots generalizing before with
  | nil => trivial
  | cons slot rest ih =>
    have nativeSize := registry.property
    have fits : before.state.claims.val.length+1 < 2^64 := by simp only [List.length_cons] at capacity; omega
    have one := step_available description registry requests query values slot before world sources fits valueCount
    have count := step_count description registry requests query values slot before world
    have same := NativeSharedSourceClaims.step_sources description registry requests query values slot before world
    simp only [loop,OracleProgram.run_bind,ObservationReplay.run_bind]
    cases current : (run (step description registry requests query values slot before) world).run.1 with
    | stopped progress reason => simpa only [current,OracleProgram.run,CanonicalTranscriptSampler.run_pure] using one
    | done after =>
      simp only [current,Result.progress] at count same
      have afterSources : after.state.sources.val.length = registry.val.length := by rw [same]; exact sources
      have countAfter : after.state.claims.val.length ≤ before.state.claims.val.length+1 := count
      have afterCapacity : after.state.claims.val.length+rest.length ≤ registry.val.length := by
        simp only [List.length_cons] at capacity
        omega
      exact ih after afterSources afterCapacity

theorem program_available {C : Type} (description : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (query : Query) (values : Vector Row) (state : NativeDeferredOpeningBatch.State) (world : World)
    (sources : state.sources.val.length = registry.val.length) (empty : state.claims.val = [])
    (valueCount : registry.val.length ≤ values.val.length) :
    Available (run (NativeSharedSourceClaims.program description registry requests query values state) world).run.1 := by
  exact loop_available description registry requests query values (List.finRange registry.val.length) ⟨state,[]⟩ world sources
    (by simp only [empty,List.length_nil,List.length_finRange,Nat.zero_add,le_refl]) valueCount
end
end FormalProof4FHE.HasteBoots.NativeSourceClaimDomain
