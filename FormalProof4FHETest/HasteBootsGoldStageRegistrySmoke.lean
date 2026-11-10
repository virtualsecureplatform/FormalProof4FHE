module
import all FormalProof4FHE.HasteBoots.ClassicalGoldStageRegistry
import all FormalProof4FHE.HasteBoots.ClassicalGoldRoleBundle
import all FormalProof4FHETest.HasteBootsGoldDescriptorSmoke
open FormalProof4FHE.HasteBoots MeasureTheory
open InputIndexedOracle (Input law)
open NativeRootMessage (Digest)
open PrivateCoinReplay (Tape)
open ClassicalGoldRoleBundle (Stage Bundle roleIndex parameters)
open HasteBootsConstructedTargetsSmoke (usize)
namespace HasteBootsGoldStageRegistrySmoke

def stages : List Stage :=
  [.coefficients,.evaluations,.key,.inputs,.borrows,.helper,
   .accumulator 0,.accumulator 1,.accumulator 2,.accumulator 3,.monomial,
   .finalCoefficients,.finalEvaluations,.finalKey,.finalInput,.finalBorrows,.finalHelper]

def quota (index : Fin 4) : ℕ := match index.val with
  | 0 => 544 | 1 => 600 | 2 => 700 | _ => 800

def specification : ClassicalGoldDescriptor.Specification :=
  let base := HasteBootsGoldDescriptorSmoke.specification 544
  {base with roles := fun index => {base.roles index with queries := usize (quota index)}}

def root (index : ℕ) : Digest := fun position => Fin.ofNat 256 (index+position.val)

def allSources : ClassicalGoldStageRegistry.Sources :=
  ⟨(List.finRange 17).map (fun index => (stages.get ⟨index.val, by change index.val < 17; exact index.isLt⟩, root index.val)),
    by simp only [List.length_map, List.length_finRange]; decide +kernel⟩

def repeated (count : NativeUsizeMessage.Usize) : ClassicalGoldStageRegistry.Sources :=
  ⟨(List.range count.val).map (fun index => (stages[index%17]?.getD .coefficients,root index)),
    by simp only [List.length_map, List.length_range]; exact count.isLt⟩

-- Every literal native parameter use is exercised. Distinct retained quotas
-- expose helper/final/main routing mistakes, including all four accumulators.
/-- info: true -/
#guard_msgs in
#eval ClassicalGoldDescriptor.admitted specification &&
  match ClassicalGoldDescriptor.prepare specification with
  | .error _ => false
  | .ok plans =>
    let runs := ClassicalGoldDescriptor.invocations plans (fun _ => 6)
    match ConstructedGoldObjectSetup.allocate [] (ConstructedGoldConstructorSetup.jobs runs) with
    | some (.ok entries) =>
      match NativeGoldParameterStore.registry entries (ClassicalGoldStageRegistry.references allSources) with
      | some registry =>
        registry.val.map (fun source : NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored => source.parameters.queries.val) ==
          [544,544,544,544,544,600,544,544,544,544,544,700,700,700,700,700,800] &&
        registry.val.map (fun source : NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored => source.parameters.numVariables.val) ==
          [19,19,19,19,19,21,19,19,19,19,19,9,9,9,9,9,11] &&
        registry.val.map (fun source : NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored => List.ofFn source.root) ==
          allSources.val.map (fun source : Stage × Digest => List.ofFn source.2)
      | none => false
    | _ => false

-- Empty and large original registries use the same four allocated objects.
-- No aliases or unused positions are removed before collection.
/-- info: true -/
#guard_msgs in
#eval match ClassicalGoldDescriptor.prepare specification with
  | .error _ => false
  | .ok plans =>
    match ConstructedGoldObjectSetup.allocate [] (ConstructedGoldConstructorSetup.jobs
        (ClassicalGoldDescriptor.invocations plans (fun _ => 6))) with
    | some (.ok entries) =>
      match NativeGoldParameterStore.registry entries (ClassicalGoldStageRegistry.references (repeated 1024)),
          NativeGoldParameterStore.registry entries (ClassicalGoldStageRegistry.references (repeated 0)) with
      | some large, some empty => entries.length == 4 && large.val.length == 1024 && empty.val.isEmpty &&
          large.val.map (fun source : NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored => List.ofFn source.root) ==
            (repeated 1024).val.map (fun source : Stage × Digest => List.ofFn source.2)
      | _, _ => false
    | _ => false

noncomputable section

-- Each stage's actual retained quota comes from its descriptor position.
example (bundle : Bundle) (stage : Stage) :
    (parameters bundle stage).queries = (bundle.specification.roles (roleIndex stage)).queries :=
  (ClassicalGoldRoleBundle.entry_descriptor bundle (roleIndex stage)).2.2

-- Source roots/positions do not require a separate collection-success premise.
example (Memory : Type) (code : List PrivateCoinByteMachine.Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (bundle : Bundle)
    (sources : ClassicalGoldStageRegistry.Sources) :
    MeasurableSet {execution | ConstructedGoldAnyProfileSecurity.Failure Memory code publicData privateData dummy
      (ClassicalGoldStageRegistry.registered bundle sources) execution} :=
  ClassicalGoldStageRegistry.failure_measurable Memory code publicData privateData dummy bundle sources

-- No stage-parameter association, target certificate, source-count cap or
-- collection/check certificate is supplied to the final registered-source bound.
example (coins : Measure Tape) (Memory : Type) (code : List PrivateCoinByteMachine.Instruction)
    (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (bundle : Bundle)
    (sources : ClassicalGoldStageRegistry.Sources) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | ConstructedGoldAnyProfileSecurity.Failure Memory code publicData privateData dummy
      (ClassicalGoldStageRegistry.registered bundle sources) execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData :=
  ClassicalGoldStageRegistry.work_bound coins Memory code publicData privateData dummy bundle sources
end
end HasteBootsGoldStageRegistrySmoke
