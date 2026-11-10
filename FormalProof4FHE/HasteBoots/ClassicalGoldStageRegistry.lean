module
public import FormalProof4FHE.HasteBoots.ClassicalGoldRoleBundle
@[expose] public section

/-! Build every original stage/root source reference from its actual retained
role object. Collection succeeds by construction without a supplied registry
receipt. This is logical stage-parameter routing, not whole native PBS/heap
refinement or accepted-false-PBS coverage. -/
namespace FormalProof4FHE.HasteBoots.ClassicalGoldStageRegistry
open ClassicalGoldRoleBundle (Bundle Stage roleIndex parameters entry_spec)
open NativeRootMessage (Digest)
open NativeGoldParameterStore (Reference)
open NativeSharedLookupParent (Oracle)
open InputIndexedOracle (Input law)
open PrivateCoinReplay (Tape)
open MeasureTheory
noncomputable section

abbrev Sources := NativePrefixCodec.Vector (Stage × Digest)

def reference (source : Stage × Digest) : Reference := ⟨(roleIndex source.1).val,source.2⟩
def oracle (bundle : Bundle) (source : Stage × Digest) : Oracle NativeGoldBlockCode.Stored :=
  ⟨parameters bundle source.1,source.2⟩

def references (sources : Sources) : NativePrefixCodec.Vector Reference :=
  ⟨sources.val.map reference, by simpa only [List.length_map] using sources.property⟩

def oracles (bundle : Bundle) (sources : Sources) : NativePrefixCodec.Vector (Oracle NativeGoldBlockCode.Stored) :=
  ⟨sources.val.map (oracle bundle), by simpa only [List.length_map] using sources.property⟩

theorem collect (bundle : Bundle) (sources : List (Stage × Digest)) :
    NativeGoldParameterStore.collect bundle.entries (sources.map reference) = some (sources.map (oracle bundle)) := by
  induction sources with
  | nil => rfl
  | cons source rest ih =>
    simp only [List.map_cons, NativeGoldParameterStore.collect, reference,
      (entry_spec bundle (roleIndex source.1)).1, ih, Option.map_some]
    rfl

theorem collected (bundle : Bundle) (sources : Sources) :
    NativeGoldParameterStore.registry bundle.entries (references sources) = some (oracles bundle sources) := by
  have actual : NativeGoldParameterStore.collect bundle.entries (references sources).val =
      some (oracles bundle sources).val := collect bundle sources.val
  unfold NativeGoldParameterStore.registry
  split
  · rename_i missing
    rw [missing] at actual
    cases actual
  · rename_i output found
    have same : output = (oracles bundle sources).val := Option.some.inj (found.symm.trans actual)
    subst output
    rfl

def registered (bundle : Bundle) (sources : Sources) : ConstructedGoldRegisteredSecurity.Registry :=
  ClassicalGoldDescriptorSetup.registered bundle.specification bundle.plans bundle.prepared bundle.accepted bundle.steps
    bundle.entries bundle.allocated (references sources) (oracles bundle sources) (collected bundle sources)

theorem source_count (bundle : Bundle) (sources : Sources) :
    (registered bundle sources).registry.val.length = sources.val.length := List.length_map (oracle bundle)

theorem oracle_get (bundle : Bundle) (sources : Sources) (index : Fin sources.val.length) :
    (oracles bundle sources).val[index.val]? =
      some ⟨parameters bundle (sources.val.get index).1,(sources.val.get index).2⟩ := by
  simp only [oracles, List.getElem?_map, List.getElem?_eq_getElem index.isLt, Option.map_some]
  rfl

theorem parameter_geometry (bundle : Bundle) (sources : Sources) (index : Fin sources.val.length) :
    (oracle bundle (sources.val.get index)).parameters.numVariables.val =
        NativeBrakedownCalibration.roleVariables .goldilocks (ClassicalGoldDescriptor.calibrationRole (roleIndex (sources.val.get index).1)) ∧
    (oracle bundle (sources.val.get index)).parameters.width.val =
        NativeBrakedownCalibration.testWidth .goldilocks (ClassicalGoldDescriptor.calibrationRole (roleIndex (sources.val.get index).1)) ∧
    544 ≤ (oracle bundle (sources.val.get index)).parameters.queries.val := by
  have geometry := ClassicalGoldRoleBundle.stage_geometry bundle (sources.val.get index).1
  exact ⟨geometry.1,geometry.2.1,geometry.2.2.2⟩

theorem failure_measurable (Memory : Type) (code : List PrivateCoinByteMachine.Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (bundle : Bundle) (sources : Sources) :
    MeasurableSet {execution | ConstructedGoldAnyProfileSecurity.Failure Memory code publicData privateData dummy (registered bundle sources) execution} :=
  ConstructedGoldAnyProfileSecurity.failure_measurable Memory code publicData privateData dummy _

/-- The caller supplies neither stage-specific parameters nor a collection,
reference-check, target or object-count certificate. Every source slot remains. -/
theorem work_bound (coins : Measure Tape) (Memory : Type) (code : List PrivateCoinByteMachine.Instruction)
    (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (bundle : Bundle) (sources : Sources) :
    (2 : ENNReal)^128 * (coins.prod law)
      {execution | ConstructedGoldAnyProfileSecurity.Failure Memory code publicData privateData dummy (registered bundle sources) execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData :=
  ClassicalGoldDescriptorSetup.work_bound coins Memory code publicData privateData dummy bundle.specification bundle.plans
    bundle.prepared bundle.accepted bundle.steps bundle.entries bundle.allocated (references sources) (oracles bundle sources) (collected bundle sources)
end
end FormalProof4FHE.HasteBoots.ClassicalGoldStageRegistry
