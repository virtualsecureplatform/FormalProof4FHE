module
import all FormalProof4FHE.HasteBoots.ConstructedGoldRegistrySoundness
import all FormalProof4FHE.HasteBoots.ConstructedGoldTargets
import all FormalProof4FHE.HasteBoots.ConstructedGoldRegistryTargets
import all FormalProof4FHE.HasteBoots.NativeBrakedownCalibration
import all FormalProof4FHETest.HasteBootsNativeGoldParametersSmoke
open FormalProof4FHE.HasteBoots MeasureTheory
open NativeBrakedownCalibration (Role)
open InputIndexedOracle (Input)
namespace HasteBootsConstructedTargetsSmoke
noncomputable section

def usize (n : ℕ) : NativeUsizeMessage.Usize := Fin.ofNat (2^64) n
def request (role : Role) : NativeGoldBlockCodeProgram.Request :=
  ⟨usize (2^(NativeBrakedownCalibration.roleVariables .goldilocks role-NativeBrakedownCalibration.left .goldilocks role)),
    usize 4, usize 2⟩
def header (role : Role) (queries : ℕ) : NativeGoldEncodedParameters.Header :=
  ⟨usize (NativeBrakedownCalibration.roleVariables .goldilocks role),
    usize (NativeBrakedownCalibration.testWidth .goldilocks role),
    usize (NativeBrakedownCalibration.left .goldilocks role), usize queries⟩

example : ConstructedGoldTargets.admitted .helper (request .helper) (header .helper 544) = true := by decide +kernel
example : ConstructedGoldTargets.admitted .source (request .source) (header .source 543) = false := by decide +kernel
example : ConstructedGoldTargets.admitted .helper {request .helper with block := usize 3} (header .helper 544) = false := by decide +kernel
example : ConstructedGoldRegistryTargets.classify (request .helper) {header .helper 544 with width := usize 4} = none := by decide +kernel

-- Quotas may exceed the minimum, and the helper test width remains distinct
-- from the independently selected code packing width.
/-- info: true -/
#guard_msgs in
#eval [.source, .helper, .finalSource, .finalHelper].all fun role =>
  [544, 545, 600, 1024].all fun queries =>
    ConstructedGoldTargets.admitted role (request role) (header role queries) &&
      ConstructedGoldRegistryTargets.classify (request role) (header role queries) == some role

-- Actual constructor execution, not a separately supplied primitive root.
def advance (req : NativeGoldBlockCodeProgram.Request) : ℕ → NativeGoldBlockCodeProgram.Config → NativeGoldBlockCodeProgram.Config
  | 0, config => config
  | n+1, config => advance req n (NativeGoldBlockCodeProgram.tick req config)

theorem advance_reachable (req : NativeGoldBlockCodeProgram.Request) (n : ℕ)
    (config : NativeGoldBlockCodeProgram.Config) (reachable : NativeGoldBlockCodeProgram.Reachable req config) :
    NativeGoldBlockCodeProgram.Reachable req (advance req n config) := by
  induction n generalizing config with
  | zero => exact reachable
  | succ n ih => exact ih _ (.tick reachable)

def completed := advance (request .finalSource) 6 {}

-- The generic native constructor may succeed at 543 queries. It therefore
-- cannot by itself discharge the 544-query security-admission obligation.
/-- info: true -/
#guard_msgs in
#eval match NativeGoldParameterInitialization.finish (header .finalSource 543) completed with
  | some (.ok result) => result.parameters.queries.val == 543 &&
      !ConstructedGoldTargets.admitted .finalSource (request .finalSource) (header .finalSource 543)
  | _ => false

-- Duplicated references preserve both original objects and slot ordering.
/-- info: true -/
#guard_msgs in
#eval match NativeGoldParameterStore.allocate [] (request .finalSource) (header .finalSource 544) completed with
  | some (.ok first) =>
    match NativeGoldParameterStore.allocate first.entries (request .finalSource) (header .finalSource 600) completed with
    | some (.ok second) =>
      let root : NativeRootMessage.Digest := fun _ => 7
      match NativeGoldParameterStore.collect second.entries [⟨0,root⟩,⟨1,root⟩,⟨0,root⟩] with
      | some registry => (registry.map fun source : NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored => source.parameters.queries.val) == [544,600,544]
      | none => false
    | _ => false
  | _ => false

-- Admission covers registered slots, including aliases, while unrelated
-- objects in the same arena do not narrow the admitted family.
/-- info: true -/
#guard_msgs in
#eval match NativeGoldParameterStore.allocate [] (request .finalSource) (header .finalSource 543) completed with
  | some (.ok first) =>
    match NativeGoldParameterStore.allocate first.entries (request .finalSource) (header .finalSource 544) completed with
    | some (.ok second) =>
      let root : NativeRootMessage.Digest := fun _ => 7
      ConstructedGoldRegistryTargets.checkReferences second.entries [⟨1,root⟩,⟨1,root⟩] &&
        !ConstructedGoldRegistryTargets.checkReferences second.entries [⟨1,root⟩,⟨0,root⟩,⟨1,root⟩] &&
        !ConstructedGoldRegistryTargets.checkReferences second.entries [⟨2,root⟩]
    | _ => false
  | _ => false

-- Certificates below need the actual logical constructor/arena evidence and
-- checked policy. No independent code, root or Matches certificate is passed.
example (family : ConstructedGoldRegistrySoundness.Family) (index : Fin family.registry.val.length) :
    544 ≤ (family.contexts index).parameters.queries.val :=
  (ConstructedGoldRegistrySoundness.targets family index).compatible.queries
example (family : ConstructedGoldRegistrySoundness.Family) (index : Fin family.registry.val.length) :
    IsPrimitiveRoot (NativeFieldRepresentation.goldValue (family.contexts index).parameters.code.domainRoot)
      (2^(NativeGoldBlockCode.logSize (family.contexts index).parameters.code+1)) :=
  (ConstructedGoldRegistrySoundness.targets family index).primitive
example (family : ConstructedGoldRegistrySoundness.Family) (index : Fin family.registry.val.length) :
    family.references.val[index.val]? = some (ConstructedGoldRegistrySoundness.binding family index).reference := by
  have selected := (ConstructedGoldRegistrySoundness.binding family index).atReference
  rwa [ConstructedGoldRegistrySoundness.binding_original] at selected

example (family : ConstructedGoldRegistrySoundness.Family) (coins : Measure PrivateCoinReplay.Tape)
    (code : List PrivateCoinByteMachine.Instruction) (publicData : InputIndexedOracle.Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : NativeRootMessage.Digest) :
    (2 : ENNReal)^128 * (coins.prod InputIndexedOracle.law)
      {execution | ConstructedGoldRegistrySoundness.Failure Unit code publicData privateData dummy family execution} ≤
        ((family.registry.val.length : ENNReal)*(9/4096)) * PrivateCoinByteWork.expectedWork coins code publicData privateData :=
  ConstructedGoldRegistrySoundness.scaled_bound coins Unit code publicData privateData dummy family
end
end HasteBootsConstructedTargetsSmoke
