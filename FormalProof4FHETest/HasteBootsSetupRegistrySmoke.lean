module
import all FormalProof4FHE.HasteBoots.ConstructedGoldConstructorSetup
import all FormalProof4FHE.HasteBoots.ConstructedGoldObjectSetup
import all FormalProof4FHE.HasteBoots.ConstructedGoldRegistryTargets
import all FormalProof4FHETest.HasteBootsConstructedTargetsSmoke
open FormalProof4FHE.HasteBoots MeasureTheory
open InputIndexedOracle (Input law)
open NativeRootMessage (Digest)
open PrivateCoinReplay (Tape)
open NativePrefixCodec (Vector)
open NativeGoldParameterStore (Entry Reference)
open NativeSharedLookupParent (Oracle)
open ConstructedGoldConstructorSetup
open HasteBootsConstructedTargetsSmoke (request header)
namespace HasteBootsSetupRegistrySmoke

def invocation (role : NativeBrakedownCalibration.Role) (queries steps : ℕ) : Invocation :=
  ⟨request role, header role queries, steps⟩

def references (count : NativeUsizeMessage.Usize) : Vector Reference :=
  ⟨(List.range count.val).map (fun index => ⟨index % 4, fun position => Fin.ofNat 256 (index+position.val)⟩),
    by simp only [List.length_map, List.length_range]; exact count.isLt⟩

-- Literal constructor runs, security admission and complete typed collection
-- compose on all four roles, keeping all 1024 original source positions.
/-- info: true -/
#guard_msgs in
#eval
  let invocations := [.source,.helper,.finalSource,.finalHelper].map fun role => invocation role 544 6
  admitted invocations &&
    match ConstructedGoldObjectSetup.allocate [] (jobs invocations) with
    | some (.ok entries) =>
      match NativeGoldParameterStore.registry entries (references 1024) with
      | some registry => entries.length == 4 && registry.val.length == 1024 &&
          ConstructedGoldRegistryTargets.checkReferences entries (references 1024).val
      | none => false
    | _ => false

-- Constructor success is not security qualification. An unfinished run also
-- supplies no allocation receipt, even if its request/header are admitted.
/-- info: true -/
#guard_msgs in
#eval
  let below := [invocation .finalSource 543 6]
  let pending := [invocation .finalSource 544 0]
  !admitted below && admitted pending && (ConstructedGoldObjectSetup.allocate [] (jobs pending)).isNone &&
    match ConstructedGoldObjectSetup.allocate [] (jobs below) with
    | some (.ok entries) => entries.length == 1
    | _ => false

noncomputable section

-- No supplied reference-check or constructor-reachability certificate.
example (invocations : List Invocation) (accepted : admitted invocations = true)
    (entries : List Entry) (allocated : ConstructedGoldObjectSetup.allocate [] (jobs invocations) = some (.ok entries))
    (refs : Vector Reference) (registry : Vector (Oracle NativeGoldBlockCode.Stored))
    (collected : NativeGoldParameterStore.registry entries refs = some registry) :
    ConstructedGoldRegistryTargets.checkReferences entries refs.val = true :=
  (registered invocations accepted entries allocated refs registry collected).checked

-- The resulting event is measurable for the same runtime-coin execution.
example (Memory : Type) (code : List PrivateCoinByteMachine.Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)
    (invocations : List Invocation) (accepted : admitted invocations = true)
    (entries : List Entry) (allocated : ConstructedGoldObjectSetup.allocate [] (jobs invocations) = some (.ok entries))
    (refs : Vector Reference) (registry : Vector (Oracle NativeGoldBlockCode.Stored))
    (collected : NativeGoldParameterStore.registry entries refs = some registry) :
    MeasurableSet {execution | ConstructedGoldAnyProfileSecurity.Failure Memory code publicData privateData dummy
      (registered invocations accepted entries allocated refs registry collected) execution} :=
  ConstructedGoldAnyProfileSecurity.failure_measurable Memory code publicData privateData dummy _

-- Four successful executed constructor/allocation runs and collection derive
-- the work theorem without a separately assembled Registry/Target certificate.
example (coins : Measure Tape) (Memory : Type) (code : List PrivateCoinByteMachine.Instruction)
    (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)
    (source helper finalSource finalHelper : Invocation) (accepted : admitted [source,helper,finalSource,finalHelper] = true)
    (entries : List Entry) (allocated : ConstructedGoldObjectSetup.allocate [] (jobs [source,helper,finalSource,finalHelper]) = some (.ok entries))
    (refs : Vector Reference) (registry : Vector (Oracle NativeGoldBlockCode.Stored))
    (collected : NativeGoldParameterStore.registry entries refs = some registry) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | ConstructedGoldAnyProfileSecurity.Failure Memory code publicData privateData dummy
      (registered [source,helper,finalSource,finalHelper] accepted entries allocated refs registry collected) execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData :=
  four_role_work_bound coins Memory code publicData privateData dummy source helper finalSource finalHelper
    accepted entries allocated refs registry collected
end
end HasteBootsSetupRegistrySmoke
