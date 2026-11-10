module
import all FormalProof4FHE.HasteBoots.ConstructedGoldObjectSetup
import all FormalProof4FHE.HasteBoots.ConstructedGoldRegistryTargets
import all FormalProof4FHETest.HasteBootsConstructedTargetsSmoke
open FormalProof4FHE.HasteBoots MeasureTheory
open InputIndexedOracle (Input law)
open NativeRootMessage (Digest)
open PrivateCoinReplay (Tape)
open HasteBootsConstructedTargetsSmoke (request header advance)
namespace HasteBootsObjectSecuritySmoke

def job (role : NativeBrakedownCalibration.Role) (queries : ℕ) : ConstructedGoldObjectSetup.Job :=
  ⟨request role, header role queries, advance (request role) 6 {}⟩

-- Actual four-role constructor execution, followed by 1024 original source
-- slots with repeated object handles and many distinct roots. No slot is filtered.
/-- info: true -/
#guard_msgs in
#eval match ConstructedGoldObjectSetup.allocate []
    [job .source 544, job .helper 544, job .finalSource 544, job .finalHelper 544] with
  | some (.ok entries) =>
    let references : List NativeGoldParameterStore.Reference := (List.range 1024).map fun index =>
      ⟨index % 4, fun position => Fin.ofNat 256 (index+position.val)⟩
    match NativeGoldParameterStore.collect entries references with
    | some registry => entries.length == 4 && registry.length == 1024 &&
        ConstructedGoldRegistryTargets.checkReferences entries references &&
        entries.map (fun entry : NativeGoldParameterStore.Entry => entry.initialized.parameters.width.val) == [4,3,4,3] &&
        registry.all (fun source : NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored => source.parameters.code.blockWidth.val == 4 && source.parameters.queries.val == 544)
    | none => false
  | _ => false

-- Pending or rejected roles propagate through the sequential setup. They are
-- never discarded to produce a smaller successful object family.
/-- info: true -/
#guard_msgs in
#eval
  let good := job .finalSource 544
  let pending := {good with config := {}}
  let rejected := job .finalSource 0
  (ConstructedGoldObjectSetup.allocate [] [good,pending,good]).isNone &&
    match ConstructedGoldObjectSetup.allocate [] [good,rejected,good] with
    | some (.error _) => true
    | _ => false

noncomputable section
-- No limit on registry slots appears in the arena-based work interface.
example (coins : Measure Tape) (Memory : Type) (code : List PrivateCoinByteMachine.Instruction)
    (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)
    (registered : ConstructedGoldRegisteredSecurity.Registry) (bounded : registered.entries.length ≤ 256) :
    (2 : ENNReal)^128 * (coins.prod law)
      {execution | ConstructedGoldAnyProfileSecurity.Failure Memory code publicData privateData dummy registered execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData :=
  ConstructedGoldObjectSecurity.arena_work_bound coins Memory code publicData privateData dummy registered bounded

-- Four actual allocation receipts derive the count premise automatically.
example (coins : Measure Tape) (Memory : Type) (code : List PrivateCoinByteMachine.Instruction)
    (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)
    (registered : ConstructedGoldRegisteredSecurity.Registry) (source helper finalSource finalHelper : ConstructedGoldObjectSetup.Job)
    (executed : ConstructedGoldObjectSetup.allocate [] [source,helper,finalSource,finalHelper] = some (.ok registered.entries)) :
    (2 : ENNReal)^128 * (coins.prod law)
      {execution | ConstructedGoldAnyProfileSecurity.Failure Memory code publicData privateData dummy registered execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData :=
  ConstructedGoldObjectSetup.four_role_work_bound coins Memory code publicData privateData dummy registered
    source helper finalSource finalHelper executed

-- Unrelated unadmitted entries are permitted, and selected profile metadata
-- may depend on the same oracle world as the failure event.
example (coins : Measure Tape) (Memory : Type) (code : List PrivateCoinByteMachine.Instruction)
    (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)
    (registered : ConstructedGoldRegisteredSecurity.Registry) (descriptor : Input)
    (bounded : Fintype.card (ConstructedGoldObjectSecurity.Admitted registered) ≤ 256) :
    (2 : ENNReal)^128 * (coins.prod law) {execution : Tape × InputIndexedOracle.World |
      ConstructedGoldRegisteredSecurity.Failure Memory code publicData privateData dummy registered
        (InputIndexedOracle.sha512 execution.2 descriptor) execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData :=
  ConstructedGoldObjectSecurity.selected_work_bound coins Memory code publicData privateData dummy registered _ bounded
end
end HasteBootsObjectSecuritySmoke
