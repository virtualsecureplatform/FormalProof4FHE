module

public import FormalProof4FHE.HasteBoots.NativeSharedLookupValues

@[expose] public section

/-!
# Proof shape and backend value gates before actual lookup sampling

The backend's trusted value policy is explicit. Both native proof-dimension
and value checks gate the existing lookup/equality prelude. Rejection emits
no prelude observations. The state-based entry takes a child state; the child-program entry gates
its creation as well. Exact child construction and earlier PCS contexts
remain to instantiate.
-/

namespace FormalProof4FHE.HasteBoots.NativeSharedLookupValidated

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeSharedLookupStatement (Request)
open NativeLookupBindGeometry (Parameters)
open NativeSharedLookupProofShape (Values)
open NativeSharedLookupValues (Policy)
open NativeTranscript (Transcript)
open InputIndexedOracle (World)
open OracleProgram (Program run)

noncomputable section

def checks (policy : Policy) (registry : List Parameters) (requests : List Request)
    (geometry : NativeSharedLookupPreflight.Output) (openingCount : ℕ) (values : Values) : Bool :=
  NativeSharedLookupProofShape.check registry requests geometry openingCount values &&
    NativeSharedLookupValues.check policy registry.length requests values

def protocol {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (policy : Policy) (registry : List Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (openingCount : ℕ) (values : Values) (rootFits : values.roots.length < 2^64)
    (w lookupFuel equalityFuel : ℕ) (transcript : Transcript) : Program (Option (NativeSharedLookupPrelude.Ready geometry.geometry.1.val)) :=
  if checks policy registry (List.ofFn requests) geometry openingCount values then
    NativeSharedLookupPrelude.protocol fits requests geometry.geometry.1 values.multiplicities values.roots rootFits
      w lookupFuel equalityFuel transcript
  else .pure none

theorem checks_iff (policy : Policy) (registry : List Parameters) (requests : List Request)
    (geometry : NativeSharedLookupPreflight.Output) (openingCount : ℕ) (values : Values) :
    checks policy registry requests geometry openingCount values = true ↔
      NativeSharedLookupProofShape.check registry requests geometry openingCount values = true ∧
      NativeSharedLookupValues.check policy registry.length requests values = true := by
  simp only [checks,Bool.and_eq_true]

theorem run_accepted {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (policy : Policy) (registry : List Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (openingCount : ℕ) (values : Values) (rootFits : values.roots.length < 2^64)
    (w lookupFuel equalityFuel : ℕ) (transcript : Transcript) (world : World)
    (accepted : checks policy registry (List.ofFn requests) geometry openingCount values = true) :
    (run (protocol fits requests policy registry geometry openingCount values rootFits w lookupFuel equalityFuel transcript) world).run =
      (run (NativeSharedLookupPrelude.protocol fits requests geometry.geometry.1 values.multiplicities values.roots rootFits
        w lookupFuel equalityFuel transcript) world).run := by
  rw [protocol,ite_eq_left accepted]

theorem run_rejected {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (policy : Policy) (registry : List Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (openingCount : ℕ) (values : Values) (rootFits : values.roots.length < 2^64)
    (w lookupFuel equalityFuel : ℕ) (transcript : Transcript) (world : World)
    (rejected : checks policy registry (List.ofFn requests) geometry openingCount values = false) :
    (run (protocol fits requests policy registry geometry openingCount values rootFits w lookupFuel equalityFuel transcript) world).run =
      (none,[]) := by
  simp only [protocol,rejected,Bool.false_eq_true,ite_false,OracleProgram.run,CanonicalTranscriptSampler.run_pure]

/-- Every successful actual gated execution supplies its shape and value
checks and the original full prelude execution, including its observations. -/
theorem protocol_spec {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (policy : Policy) (registry : List Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (openingCount : ℕ) (values : Values) (rootFits : values.roots.length < 2^64)
    (w lookupFuel equalityFuel : ℕ) (transcript : Transcript) (world : World)
    (ready : NativeSharedLookupPrelude.Ready geometry.geometry.1.val)
    (success : (run (protocol fits requests policy registry geometry openingCount values rootFits w lookupFuel equalityFuel transcript) world).run.1 = some ready) :
    NativeSharedLookupProofShape.Accepted registry (List.ofFn requests) geometry openingCount values ∧
      NativeSharedLookupValues.Accepted policy registry.length (List.ofFn requests) values ∧
      (run (NativeSharedLookupPrelude.protocol fits requests geometry.geometry.1 values.multiplicities values.roots rootFits
        w lookupFuel equalityFuel transcript) world).run.1 = some ready := by
  cases accepted : checks policy registry (List.ofFn requests) geometry openingCount values with
  | false => rw [run_rejected fits requests policy registry geometry openingCount values rootFits w lookupFuel equalityFuel transcript world accepted] at success; contradiction
  | true =>
    have checked := (checks_iff policy registry (List.ofFn requests) geometry openingCount values).mp accepted
    rw [run_accepted fits requests policy registry geometry openingCount values rootFits w lookupFuel equalityFuel transcript world accepted] at success
    exact ⟨NativeSharedLookupProofShape.check_spec registry (List.ofFn requests) geometry openingCount values checked.1,
      NativeSharedLookupValues.check_spec policy registry.length (List.ofFn requests) values checked.2,success⟩

/-- No policy/shape gate silently blocks a valid completed operational run.
Native vector domains remain explicit; no sampler/attacker-work cap is added. -/
theorem protocol_complete {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (policy : Policy) (registry : List Parameters) (helper : Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (preflight : NativeSharedLookupPreflight.preflight registry helper (List.ofFn requests) = some geometry)
    (openingCount : ℕ) (values : Values) (accepted : checks policy registry (List.ofFn requests) geometry openingCount values = true)
    (rootFits : values.roots.length < 2^64) (vectorFits : 2 * geometry.repetitions.val < 2^64)
    (w lookupFuel equalityFuel : ℕ) (transcript : Transcript) (world : World) (child : Transcript)
    (finished : (NativeLookupBatch.execute goldilocksBasis w lookupFuel
      (NativeLookupBatch.initial (NativeLookupBatch.schedule fits (fun i => (requests i).sampling)) transcript) world).1.control = .finished child)
    (complete : (run (NativeLookupEquality.request goldilocksBasis w geometry.geometry.1.val equalityFuel
      child values.roots rootFits) world).run.1.remaining = 0) :
    ∃ ready, (run (protocol fits requests policy registry geometry openingCount values rootFits w lookupFuel equalityFuel transcript) world).run.1 = some ready := by
  have checked := (checks_iff policy registry (List.ofFn requests) geometry openingCount values).mp accepted
  obtain ⟨ready,success⟩ := NativeSharedLookupProofShape.protocol_complete fits requests registry helper geometry preflight openingCount values
    checked.1 rootFits vectorFits w lookupFuel equalityFuel transcript world child finished complete
  exact ⟨ready,by rw [run_accepted fits requests policy registry geometry openingCount values rootFits w lookupFuel equalityFuel transcript world accepted]; exact success⟩

/-- Native value rejection precedes child creation. The startChildr is a
program, so its actual observations occur only on the accepted branch. -/
def withChild {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (policy : Policy) (registry : List Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (openingCount : ℕ) (values : Values) (rootFits : values.roots.length < 2^64)
    (w lookupFuel equalityFuel : ℕ) (startChild : Program Transcript) : Program (Option (NativeSharedLookupPrelude.Ready geometry.geometry.1.val)) :=
  if checks policy registry (List.ofFn requests) geometry openingCount values then
    OracleProgram.bind startChild (fun transcript => NativeSharedLookupPrelude.protocol fits requests geometry.geometry.1 values.multiplicities
      values.roots rootFits w lookupFuel equalityFuel transcript)
  else .pure none

theorem withChild_accepted {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (policy : Policy) (registry : List Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (openingCount : ℕ) (values : Values) (rootFits : values.roots.length < 2^64)
    (w lookupFuel equalityFuel : ℕ) (startChild : Program Transcript) (world : World)
    (accepted : checks policy registry (List.ofFn requests) geometry openingCount values = true) :
    (run (withChild fits requests policy registry geometry openingCount values rootFits w lookupFuel equalityFuel startChild) world).run =
      let child := (run startChild world).run
      let later := (run (NativeSharedLookupPrelude.protocol fits requests geometry.geometry.1 values.multiplicities values.roots rootFits
        w lookupFuel equalityFuel child.1) world).run
      (later.1,child.2 ++ later.2) := by
  simp only [withChild,accepted,ite_true,OracleProgram.run_bind,ObservationReplay.run_bind]

theorem withChild_rejected {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (policy : Policy) (registry : List Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (openingCount : ℕ) (values : Values) (rootFits : values.roots.length < 2^64)
    (w lookupFuel equalityFuel : ℕ) (startChild : Program Transcript) (world : World)
    (rejected : checks policy registry (List.ofFn requests) geometry openingCount values = false) :
    (run (withChild fits requests policy registry geometry openingCount values rootFits w lookupFuel equalityFuel startChild) world).run = (none,[]) := by
  simp only [withChild,rejected,Bool.false_eq_true,ite_false,OracleProgram.run,CanonicalTranscriptSampler.run_pure]

/-- The same executed startChildr supplies the child state of the complete
prelude contract. No parent/child transcript-equality certificate is input. -/
theorem withChild_spec {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (policy : Policy) (registry : List Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (openingCount : ℕ) (values : Values) (rootFits : values.roots.length < 2^64)
    (w lookupFuel equalityFuel : ℕ) (startChild : Program Transcript) (world : World)
    (ready : NativeSharedLookupPrelude.Ready geometry.geometry.1.val)
    (success : (run (withChild fits requests policy registry geometry openingCount values rootFits w lookupFuel equalityFuel startChild) world).run.1 = some ready) :
    NativeSharedLookupProofShape.Accepted registry (List.ofFn requests) geometry openingCount values ∧
      NativeSharedLookupValues.Accepted policy registry.length (List.ofFn requests) values ∧
      NativeSharedLookupPrelude.Contract fits requests geometry.geometry.1 values.multiplicities values.roots rootFits w equalityFuel
        (NativeLookupBatch.execute goldilocksBasis w lookupFuel
          (NativeLookupBatch.initial (NativeLookupBatch.schedule fits (fun i => (requests i).sampling))
            (run startChild world).run.1) world).1 world ready := by
  cases accepted : checks policy registry (List.ofFn requests) geometry openingCount values with
  | false => rw [withChild_rejected fits requests policy registry geometry openingCount values rootFits w lookupFuel equalityFuel startChild world accepted] at success; contradiction
  | true =>
    rw [withChild_accepted fits requests policy registry geometry openingCount values rootFits w lookupFuel equalityFuel startChild world accepted] at success
    have checked := (checks_iff policy registry (List.ofFn requests) geometry openingCount values).mp accepted
    exact ⟨NativeSharedLookupProofShape.check_spec registry (List.ofFn requests) geometry openingCount values checked.1,
      NativeSharedLookupValues.check_spec policy registry.length (List.ofFn requests) values checked.2,
      NativeSharedLookupPrelude.protocol_contract fits requests geometry.geometry.1 values.multiplicities values.roots rootFits w lookupFuel equalityFuel
        (run startChild world).run.1 world ready success⟩

/-- Retain the initializer's parent/private state for child finishing and
later authentication. It is computed output, not a supplied state certificate. -/
def withChildState {A : Type} {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (policy : Policy) (registry : List Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (openingCount : ℕ) (values : Values) (rootFits : values.roots.length < 2^64)
    (w lookupFuel equalityFuel : ℕ) (startChild : Program (A × Transcript)) : Program (Option (A × NativeSharedLookupPrelude.Ready geometry.geometry.1.val)) :=
  if checks policy registry (List.ofFn requests) geometry openingCount values then
    OracleProgram.bind startChild (fun (state,transcript) =>
      OracleProgram.bind (NativeSharedLookupPrelude.protocol fits requests geometry.geometry.1 values.multiplicities values.roots rootFits
        w lookupFuel equalityFuel transcript) (fun result => .pure (result.map (fun ready => (state,ready)))))
  else .pure none

theorem withChildState_accepted {A : Type} {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (policy : Policy) (registry : List Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (openingCount : ℕ) (values : Values) (rootFits : values.roots.length < 2^64)
    (w lookupFuel equalityFuel : ℕ) (startChild : Program (A × Transcript)) (world : World)
    (accepted : checks policy registry (List.ofFn requests) geometry openingCount values = true) :
    (run (withChildState fits requests policy registry geometry openingCount values rootFits w lookupFuel equalityFuel startChild) world).run =
      let child := (run startChild world).run
      let later := (run (NativeSharedLookupPrelude.protocol fits requests geometry.geometry.1 values.multiplicities values.roots rootFits
        w lookupFuel equalityFuel child.1.2) world).run
      (later.1.map (fun ready => (child.1.1,ready)),child.2 ++ later.2) := by
  simp only [withChildState,accepted,ite_true,OracleProgram.run_bind,ObservationReplay.run_bind,
    OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]

theorem withChildState_rejected {A : Type} {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (policy : Policy) (registry : List Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (openingCount : ℕ) (values : Values) (rootFits : values.roots.length < 2^64)
    (w lookupFuel equalityFuel : ℕ) (startChild : Program (A × Transcript)) (world : World)
    (rejected : checks policy registry (List.ofFn requests) geometry openingCount values = false) :
    (run (withChildState fits requests policy registry geometry openingCount values rootFits w lookupFuel equalityFuel startChild) world).run = (none,[]) := by
  simp only [withChildState,rejected,Bool.false_eq_true,ite_false,OracleProgram.run,CanonicalTranscriptSampler.run_pure]

theorem withChildState_spec {A : Type} {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (policy : Policy) (registry : List Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (openingCount : ℕ) (values : Values) (rootFits : values.roots.length < 2^64)
    (w lookupFuel equalityFuel : ℕ) (startChild : Program (A × Transcript)) (world : World)
    (state : A) (ready : NativeSharedLookupPrelude.Ready geometry.geometry.1.val)
    (success : (run (withChildState fits requests policy registry geometry openingCount values rootFits w lookupFuel equalityFuel startChild) world).run.1 = some (state,ready)) :
    state = (run startChild world).run.1.1 ∧
      NativeSharedLookupProofShape.Accepted registry (List.ofFn requests) geometry openingCount values ∧
      NativeSharedLookupValues.Accepted policy registry.length (List.ofFn requests) values ∧
      (run (NativeSharedLookupPrelude.protocol fits requests geometry.geometry.1 values.multiplicities values.roots rootFits
        w lookupFuel equalityFuel (run startChild world).run.1.2) world).run.1 = some ready := by
  cases accepted : checks policy registry (List.ofFn requests) geometry openingCount values with
  | false => rw [withChildState_rejected fits requests policy registry geometry openingCount values rootFits w lookupFuel equalityFuel startChild world accepted] at success; contradiction
  | true =>
    rw [withChildState_accepted fits requests policy registry geometry openingCount values rootFits w lookupFuel equalityFuel startChild world accepted] at success
    obtain ⟨result,done,same⟩ := Option.map_eq_some_iff.mp success
    have retained := (congrArg Prod.fst same).symm
    have output := congrArg Prod.snd same
    change result = ready at output
    subst result
    have checked := (checks_iff policy registry (List.ofFn requests) geometry openingCount values).mp accepted
    exact ⟨retained,NativeSharedLookupProofShape.check_spec registry (List.ofFn requests) geometry openingCount values checked.1,
      NativeSharedLookupValues.check_spec policy registry.length (List.ofFn requests) values checked.2,done⟩

end

end FormalProof4FHE.HasteBoots.NativeSharedLookupValidated
