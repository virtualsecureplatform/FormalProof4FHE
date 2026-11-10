module
import FormalProof4FHE.HasteBoots.ConstructedGoldRegisteredSecurity
open FormalProof4FHE.HasteBoots MeasureTheory
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open ConstructedGoldRegisteredSecurity

-- The event quantifies over candidate contexts, schedulers and all execution
-- prefixes; no enumeration or measurability of those candidate types is needed.
example (registered : Registry) (profile dummy : Digest) (Memory : Type)
    (code : List PrivateCoinByteMachine.Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) :
    MeasurableSet {execution | Failure Memory code publicData privateData dummy registered profile execution} :=
  failure_measurable Memory code publicData privateData dummy registered profile

-- No per-slot contexts, independent primitive-root certificate or separate
-- expected-work allowance is supplied for the registered family.
example (registered : Registry) (profile dummy : Digest) (Memory : Type)
    (code : List PrivateCoinByteMachine.Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (coins : Measure PrivateCoinReplay.Tape)
    (bounded : registered.registry.val.length ≤ 256) :
    (2 : ENNReal)^128 * (coins.prod InputIndexedOracle.law)
      {execution | Failure Memory code publicData privateData dummy registered profile execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData :=
  work_bound coins Memory code publicData privateData dummy registered profile bounded

-- The extraction owner's actual entry determines both the original slot and
-- role, without assuming a second parameter-to-context association.
example (registered : Registry) (ctx : NativeGoldBatchPcsProgram.Context)
    (bound : ConstructedGoldRegistryTargets.Binding registered.entries registered.references ctx) :
    ∃ index : Fin registered.registry.val.length, bound.original = index.val ∧
      ctx.parameters = (registered.registry.val.get index).parameters ∧ bound.role = role registered index :=
  binding_registered registered ctx bound

-- Reanchoring analysis does not replace the accepted candidate with the empty
-- representative or execute a different verifier/scheduler.
example (Memory : Type) (dummy : Digest) (first second : NativeGoldBatchPcsProgram.Context)
    (radius : ℕ) (world : World) (history : List NativeTranscript.Observation)
    (parameters : first.parameters = second.parameters) (profile : first.parent.profile = second.parent.profile)
    (witness : ClosedByteMachineExecutableSoundness.Witness Memory dummy first radius world history) :
    (rebase parameters profile witness).candidate = witness.candidate ∧
      (rebase parameters profile witness).choose = witness.choose ∧
      (rebase parameters profile witness).verifierFuel = witness.verifierFuel := ⟨rfl, rfl, rfl⟩
