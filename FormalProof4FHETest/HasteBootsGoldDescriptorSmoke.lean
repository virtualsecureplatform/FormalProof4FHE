module
import all FormalProof4FHE.HasteBoots.ClassicalGoldDescriptor
import all FormalProof4FHE.HasteBoots.ClassicalGoldDescriptorSetup
import all FormalProof4FHE.HasteBoots.ConstructedGoldConstructorSetup
import all FormalProof4FHE.HasteBoots.ConstructedGoldObjectSetup
import all FormalProof4FHETest.HasteBootsSetupRegistrySmoke
open FormalProof4FHE.HasteBoots MeasureTheory
open ClassicalGoldDescriptor
open InputIndexedOracle (Input law)
open NativeRootMessage (Digest)
open PrivateCoinReplay (Tape)
open NativePrefixCodec (Vector)
open NativeGoldParameterStore (Entry Reference)
open NativeSharedLookupParent (Oracle)
open HasteBootsConstructedTargetsSmoke (usize)
namespace HasteBootsGoldDescriptorSmoke

def specification (quota : ℕ) : Specification where
  backend := .brakedown
  roles := fun index =>
    let role := calibrationRole index
    ⟨usize (NativeBrakedownCalibration.roleVariables .goldilocks role),
      usize (NativeBrakedownCalibration.testWidth .goldilocks role), usize quota,
      some (usize (NativeBrakedownCalibration.left .goldilocks role)), some (usize 4)⟩
  blowup := usize 2
  fragmentVariables := none

def update (before : Specification) (index : Fin 4) (change : RoleDescription → RoleDescription) : Specification :=
  {before with roles := fun position => if position = index then change (before.roles position) else before.roles position}

-- One descriptor supplies all request/header data, followed by actual logical
-- constructors, allocations and complete collection of 1024 original sources.
/-- info: true -/
#guard_msgs in
#eval admitted (specification 544) &&
  match prepare (specification 544) with
  | .error _ => false
  | .ok plans =>
    let runs := invocations plans (fun _ => 6)
    (runs.map fun value : ConstructedGoldConstructorSetup.Invocation => value.request.message.val) == [1024,2048,32,64] &&
      match ConstructedGoldObjectSetup.allocate [] (ConstructedGoldConstructorSetup.jobs runs) with
      | some (.ok entries) =>
        match NativeGoldParameterStore.registry entries (HasteBootsSetupRegistrySmoke.references 1024) with
        | some registry => entries.length == 4 && registry.val.length == 1024 &&
            entries.map (fun value : Entry => value.initialized.parameters.width.val) == [4,3,4,3]
        | none => false
      | _ => false

-- Supported projection errors include descriptor-only missing/invalid fields;
-- no subtraction truncation or machine-shift wrap is accepted.
/-- info: true -/
#guard_msgs in
#eval
  let base := specification 544
  [ {base with backend := .polyfrim}, {base with fragmentVariables := some (usize 1)},
    update base 0 (fun role => {role with leftVariables := none}),
    update base 1 (fun role => {role with blockWidth := none}),
    update base 2 (fun role => {role with numVariables := usize 64}),
    update base 3 (fun role => {role with leftVariables := some (usize 64)}) ].all fun changed =>
      match prepare changed with | .error _ => true | .ok _ => false

-- Qualification is canonical-role-specific and configurable above the quota.
-- Alternative helper packing may project, but is outside this calibration.
/-- info: true -/
#guard_msgs in
#eval
  let base := specification 544
  let swapped := {base with roles := fun index => base.roles (if index = 0 then 1 else if index = 1 then 0 else index)}
  [544,545,600,1024].all (fun quota => admitted (specification quota)) &&
    !admitted (specification 543) && !admitted swapped &&
    !admitted (update base 1 (fun role => {role with width := usize 4})) &&
    !admitted (update base 0 (fun role => {role with blockWidth := some (usize 8)}))

noncomputable section

example (spec : Specification) (plans : Plans) (prepared : prepare spec = .ok plans)
    (accepted : admitted spec = true) (index : Fin 4) :
    544 ≤ (spec.roles index).queries.val ∧
      (spec.roles index).width.val = NativeBrakedownCalibration.testWidth .goldilocks (calibrationRole index) := by
  have geometry := descriptor_geometry spec plans prepared accepted index
  exact ⟨geometry.2.2.1, geometry.2.1⟩

example (spec : Specification) (index : Fin 4) (plan : Plan) (prepared : projectRole spec index = .ok plan) :
    plan.request.message.val = 2^(plan.header.numVariables.val-plan.header.leftVariables.val) ∧ plan.header.numVariables.val < 64 := by
  obtain ⟨_,_,_,_,_,_,power,small,_⟩ := project_fields spec index plan prepared
  exact ⟨power,small⟩

-- No independent request/header, constructor reachability, registry check or
-- target calibration certificate is supplied to the work interface.
example (coins : Measure Tape) (Memory : Type) (code : List PrivateCoinByteMachine.Instruction)
    (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)
    (spec : Specification) (plans : Plans) (prepared : prepare spec = .ok plans)
    (accepted : admitted spec = true) (steps : Fin 4 → ℕ)
    (entries : List Entry) (allocated : ConstructedGoldObjectSetup.allocate []
      (ConstructedGoldConstructorSetup.jobs (invocations plans steps)) = some (.ok entries))
    (refs : Vector Reference) (registry : Vector (Oracle NativeGoldBlockCode.Stored))
    (collected : NativeGoldParameterStore.registry entries refs = some registry) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | ConstructedGoldAnyProfileSecurity.Failure Memory code publicData privateData dummy
      (ClassicalGoldDescriptorSetup.registered spec plans prepared accepted steps entries allocated refs registry collected) execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData :=
  ClassicalGoldDescriptorSetup.work_bound coins Memory code publicData privateData dummy spec plans prepared accepted steps
    entries allocated refs registry collected
end
end HasteBootsGoldDescriptorSmoke
