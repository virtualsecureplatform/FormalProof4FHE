module
public import FormalProof4FHE.HasteBoots.ClassicalGoldDescriptor
@[expose] public section

/-! A single trusted role descriptor supplies all constructor inputs. Its
checked projection, executed constructor/allocation runs and original registry
collection derive the existing all-profile executable-source work theorem.
Native field/profile validation, serialization, Rust and PBS coverage are open. -/
namespace FormalProof4FHE.HasteBoots.ClassicalGoldDescriptorSetup
open ClassicalGoldDescriptor (Specification Plans prepare admitted invocations prepared_admitted invocations_admitted)
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeSharedLookupParent (Oracle)
open InputIndexedOracle (Input law)
open NativeRootMessage (Digest)
open PrivateCoinReplay (Tape)
open MeasureTheory
noncomputable section

def registered (specification : Specification) (plans : Plans)
    (prepared : prepare specification = .ok plans) (accepted : admitted specification = true) (steps : Fin 4 → ℕ)
    (entries : List Entry) (allocated : ConstructedGoldObjectSetup.allocate []
      (ConstructedGoldConstructorSetup.jobs (invocations plans steps)) = some (.ok entries))
    (references : Vector Reference) (registry : Vector (Oracle NativeGoldBlockCode.Stored))
    (collected : NativeGoldParameterStore.registry entries references = some registry) : ConstructedGoldRegisteredSecurity.Registry :=
  ConstructedGoldConstructorSetup.registered (invocations plans steps)
    (invocations_admitted plans (prepared_admitted specification plans prepared accepted) steps)
    entries allocated references registry collected

theorem retained (specification : Specification) (plans : Plans)
    (prepared : prepare specification = .ok plans) (accepted : admitted specification = true) (steps : Fin 4 → ℕ)
    (entries : List Entry) (allocated : ConstructedGoldObjectSetup.allocate []
      (ConstructedGoldConstructorSetup.jobs (invocations plans steps)) = some (.ok entries))
    (references : Vector Reference) (registry : Vector (Oracle NativeGoldBlockCode.Stored))
    (collected : NativeGoldParameterStore.registry entries references = some registry) :
    (registered specification plans prepared accepted steps entries allocated references registry collected).references = references ∧
      (registered specification plans prepared accepted steps entries allocated references registry collected).registry = registry := ⟨rfl,rfl⟩

theorem work_bound (coins : Measure Tape) (Memory : Type) (code : List PrivateCoinByteMachine.Instruction)
    (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)
    (specification : Specification) (plans : Plans) (prepared : prepare specification = .ok plans)
    (accepted : admitted specification = true) (steps : Fin 4 → ℕ)
    (entries : List Entry) (allocated : ConstructedGoldObjectSetup.allocate []
      (ConstructedGoldConstructorSetup.jobs (invocations plans steps)) = some (.ok entries))
    (references : Vector Reference) (registry : Vector (Oracle NativeGoldBlockCode.Stored))
    (collected : NativeGoldParameterStore.registry entries references = some registry) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | ConstructedGoldAnyProfileSecurity.Failure Memory code publicData privateData dummy
      (registered specification plans prepared accepted steps entries allocated references registry collected) execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData :=
  ConstructedGoldConstructorSetup.work_bound coins Memory code publicData privateData dummy (invocations plans steps)
    (invocations_admitted plans (prepared_admitted specification plans prepared accepted) steps)
    entries allocated references registry collected (by change 4 ≤ 256; decide +kernel)
end
end FormalProof4FHE.HasteBoots.ClassicalGoldDescriptorSetup
