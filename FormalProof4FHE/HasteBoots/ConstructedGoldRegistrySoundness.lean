module
public import FormalProof4FHE.HasteBoots.ConstructedGoldRegistryTargets
@[expose] public section

/-! Registry-indexed calibrated families derived from original retained
objects. Context-to-parameter association and trusted configuration admission
are explicit. Native context/profile registration and physical refinement
are not established by this logical family wrapper. -/
namespace FormalProof4FHE.HasteBoots.ConstructedGoldRegistrySoundness
open MeasureTheory
open InputIndexedOracle (Input World law)
open NativePrefixCodec (Vector)
open NativeGoldParameterStore (Entry Reference)
open NativeGoldBatchPcsProgram (Context)
open ConstructedGoldRegistryTargets (Binding checkReferences checked_registry_binding)
open PrivateCoinReplay (Tape)
open NativeRootMessage (Digest)
noncomputable section

structure Family where
  entries : List Entry
  reachable : NativeGoldParameterStore.Reachable entries
  references : Vector Reference
  checked : checkReferences entries references.val = true
  registry : Vector (NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored)
  retained : NativeGoldParameterStore.registry entries references = some registry
  contexts : Fin registry.val.length → Context
  associated : ∀ index, (contexts index).parameters = (registry.val.get index).parameters

def binding (family : Family) (index : Fin family.registry.val.length) :
    Binding family.entries family.references (family.contexts index) :=
  Classical.choose (checked_registry_binding family.entries family.reachable family.references family.checked
    family.registry family.retained index (family.contexts index) (family.associated index))

theorem binding_original (family : Family) (index : Fin family.registry.val.length) :
    (binding family index).original = index.val :=
  Classical.choose_spec (checked_registry_binding family.entries family.reachable family.references family.checked
    family.registry family.retained index (family.contexts index) (family.associated index))

def targets (family : Family) (index : Fin family.registry.val.length) : PrivateCoinExecutableSoundness.Target :=
  (binding family index).target

theorem targets_context (family : Family) (index : Fin family.registry.val.length) :
    (targets family index).ctx = family.contexts index := rfl

def Failure (Memory : Type) (code : List PrivateCoinByteMachine.Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (family : Family) (execution : Tape × World) : Prop :=
  ∃ index, PrivateCoinByteFailure.Failure Memory code publicData privateData dummy (targets family index) execution

theorem failure_measurable (Memory : Type) (code : List PrivateCoinByteMachine.Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (family : Family) :
    MeasurableSet {execution | Failure Memory code publicData privateData dummy family execution} :=
  PrivateCoinByteConfigurationUnion.failure_measurable Memory code publicData privateData dummy (targets family)

/-- The target count is the original registry size: aliases and unused
positions have not been filtered to manufacture a smaller loss budget. -/
theorem scaled_bound (coins : Measure Tape) (Memory : Type) (code : List PrivateCoinByteMachine.Instruction)
    (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (family : Family) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | Failure Memory code publicData privateData dummy family execution} ≤
      ((family.registry.val.length : ENNReal)*(9/4096)) * PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  simpa only [Fintype.card_fin, Failure, PrivateCoinByteConfigurationUnion.familyFailure] using
    PrivateCoinByteConfigurationUnion.scaled_family_le_work coins Memory code publicData privateData dummy (targets family)

theorem configured_bound (coins : Measure Tape) (Memory : Type) (code : List PrivateCoinByteMachine.Instruction)
    (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (family : Family)
    (bounded : family.registry.val.length ≤ 256) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | Failure Memory code publicData privateData dummy family execution} ≤
      (9/16 : ENNReal) * PrivateCoinByteWork.expectedWork coins code publicData privateData :=
  PrivateCoinByteConfigurationUnion.configured_allowance coins Memory code publicData privateData dummy (targets family)
    (by simpa only [Fintype.card_fin] using bounded)
end
end FormalProof4FHE.HasteBoots.ConstructedGoldRegistrySoundness
