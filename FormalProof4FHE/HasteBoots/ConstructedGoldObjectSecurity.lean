module
public import FormalProof4FHE.HasteBoots.ConstructedGoldAnyProfileSecurity
@[expose] public section

/-! Count immutable admitted parameter objects, while covering the unchanged
failure event of every original registered source slot. No roots, aliases or
unused slots are removed from the registry. Unrelated unadmitted arena entries
are allowed. Native four-role setup/dispatch and physical work remain open. -/
namespace FormalProof4FHE.HasteBoots.ConstructedGoldObjectSecurity
open MeasureTheory
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction)
open PrivateCoinExecutableSoundness (Target)
open ConstructedGoldRegisteredSecurity (Registry family)
open ConstructedGoldRegistryTargets (classify classify_sound)
open NativeGoldParameterStore (Entry)
noncomputable section

def Admitted (registered : Registry) :=
  { index : Fin registered.entries.length // ∃ role, classify (registered.entries.get index).request (registered.entries.get index).header = some role }

instance (registered : Registry) : Fintype (Admitted registered) := by
  classical
  unfold Admitted
  infer_instance

def role (registered : Registry) (index : Admitted registered) : NativeBrakedownCalibration.Role :=
  Classical.choose index.property

theorem classified (registered : Registry) (index : Admitted registered) :
    classify (registered.entries.get index.val).request (registered.entries.get index.val).header = some (role registered index) :=
  Classical.choose_spec index.property

/-- Only parameters are used to anchor a target. Its actual accepted candidate
retains its own root, opening, transcript, backend and scheduling evidence. -/
def context (entry : Entry) : NativeGoldBatchPcsProgram.Context where
  tables := ⟨fun _ => false, fun _ => false, fun _ => none⟩
  parameters := entry.initialized.parameters
  parent := ⟨[], fun _ => 0⟩
  root := fun _ => 0
  queries := ⟨[], by decide⟩
  values := ⟨[], by decide⟩
  opening := ⟨⟨[], by decide⟩, ⟨[], by decide⟩, ⟨[], by decide⟩⟩
  fieldFuel := 0

def targets (registered : Registry) (index : Admitted registered) : Target :=
  ConstructedGoldTargets.target (registered.entries.get index.val)
    (NativeGoldParameterStore.reachable_good registered.entries registered.reachable _ (List.get_mem _ _))
    (role registered index) (classify_sound _ _ _ (classified registered index)) (context (registered.entries.get index.val)) rfl

theorem card_le_arena (registered : Registry) : Fintype.card (Admitted registered) ≤ registered.entries.length := by
  have bound := Fintype.card_le_of_injective (fun index : Admitted registered => index.val) Subtype.val_injective
  simpa only [Fintype.card_fin] using bound

/-- Every original slot maps through its actual handle, not through a filtered
list of used roots. The chosen object's constructor receipt fixes its role. -/
theorem slot_target (registered : Registry) (slot : Fin registered.registry.val.length) :
    ∃ index : Admitted registered,
      (ConstructedGoldRegistrySoundness.targets (family registered (fun _ => 0)) slot).ctx.parameters = (targets registered index).ctx.parameters ∧
      (ConstructedGoldRegistrySoundness.targets (family registered (fun _ => 0)) slot).role = (targets registered index).role := by
  let bound := ConstructedGoldRegistrySoundness.binding (family registered (fun _ => 0)) slot
  obtain ⟨before, selected⟩ := List.getElem?_eq_some_iff.mp bound.atEntry
  let position : Fin registered.entries.length := ⟨bound.reference.handle, before⟩
  have entry : registered.entries.get position = bound.entry := selected
  let index : Admitted registered := ⟨position, by rw [entry]; exact ⟨bound.role, bound.classified⟩⟩
  refine ⟨index, ?_, ?_⟩
  · change (ConstructedGoldRegisteredSecurity.representative registered (fun _ => 0) slot).parameters =
      (registered.entries.get position).initialized.parameters
    rw [entry]
    exact bound.parameters
  · have chosen := classified registered index
    change classify (registered.entries.get position).request (registered.entries.get position).header = some (role registered index) at chosen
    rw [entry] at chosen
    exact Option.some.inj (bound.classified.symm.trans chosen)


/-- Reanchor the same executable acceptance/falsity witness at its original
parameter object. Root and profile choices incur no extra index here. -/
theorem failure_covered (Memory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (registered : Registry)
    (execution : Tape × World)
    (failed : ConstructedGoldAnyProfileSecurity.Failure Memory code publicData privateData dummy registered execution) :
    PrivateCoinByteAnyProfile.FamilyFailure Memory code publicData privateData dummy (targets registered) execution := by
  obtain ⟨slot, profile, fuel, ⟨witness⟩⟩ :=
    (ConstructedGoldAnyProfileSecurity.failure_iff Memory code publicData privateData dummy registered execution).mp failed
  obtain ⟨index, parameters, sameRole⟩ := slot_target registered slot
  refine ⟨index, profile, fuel, ⟨?_⟩⟩
  change ClosedByteMachineExecutableSoundness.Witness Memory dummy
    (PrivateCoinByteAnyProfile.withProfile (targets registered index) profile).ctx
    (NativeBrakedownCalibration.radius .goldilocks (targets registered index).role) _ _
  change ClosedByteMachineExecutableSoundness.Witness Memory dummy
    (PrivateCoinByteAnyProfile.withProfile (ConstructedGoldRegistrySoundness.targets (family registered (fun _ => 0)) slot) profile).ctx
    (NativeBrakedownCalibration.radius .goldilocks
      (ConstructedGoldRegistrySoundness.targets (family registered (fun _ => 0)) slot).role) _ _ at witness
  rw [sameRole] at witness
  have updated :
      (PrivateCoinByteAnyProfile.withProfile (ConstructedGoldRegistrySoundness.targets (family registered (fun _ => 0)) slot) profile).ctx.parameters =
      (PrivateCoinByteAnyProfile.withProfile (targets registered index) profile).ctx.parameters := parameters
  exact ConstructedGoldRegisteredSecurity.rebase updated rfl witness

/-- The event remains the full original registered event; only its covering
family is indexed by immutable objects. -/
theorem scaled_bound (coins : Measure Tape) (Memory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (registered : Registry) :
    (2 : ENNReal)^128 * (coins.prod law)
      {execution | ConstructedGoldAnyProfileSecurity.Failure Memory code publicData privateData dummy registered execution} ≤
      ((Fintype.card (Admitted registered) : ENNReal)*(9/4096)) * PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  apply (mul_le_mul' le_rfl (measure_mono (fun execution failed =>
    failure_covered Memory code publicData privateData dummy registered execution failed))).trans
  exact PrivateCoinByteAnyProfile.scaled_family_bound coins Memory code publicData privateData dummy (targets registered)

theorem work_bound (coins : Measure Tape) (Memory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (registered : Registry)
    (bounded : Fintype.card (Admitted registered) ≤ 256) :
    (2 : ENNReal)^128 * (coins.prod law)
      {execution | ConstructedGoldAnyProfileSecurity.Failure Memory code publicData privateData dummy registered execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  apply (mul_le_mul' le_rfl (measure_mono (fun execution failed =>
    failure_covered Memory code publicData privateData dummy registered execution failed))).trans
  exact PrivateCoinByteAnyProfile.family_work_bound coins Memory code publicData privateData dummy (targets registered) bounded

/-- Arbitrarily many roots may borrow each retained object. This bound puts
no additional limit on the registry length or number of attempts. -/
theorem arena_work_bound (coins : Measure Tape) (Memory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (registered : Registry)
    (bounded : registered.entries.length ≤ 256) :
    (2 : ENNReal)^128 * (coins.prod law)
      {execution | ConstructedGoldAnyProfileSecurity.Failure Memory code publicData privateData dummy registered execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData :=
  work_bound coins Memory code publicData privateData dummy registered ((card_le_arena registered).trans bounded)

theorem selected_work_bound (coins : Measure Tape) (Memory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (registered : Registry)
    (select : Tape × World → Digest) (bounded : Fintype.card (Admitted registered) ≤ 256) :
    (2 : ENNReal)^128 * (coins.prod law)
      {execution | ConstructedGoldRegisteredSecurity.Failure Memory code publicData privateData dummy registered (select execution) execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  apply (mul_le_mul' le_rfl (measure_mono (fun execution failed =>
    (show ConstructedGoldAnyProfileSecurity.Failure Memory code publicData privateData dummy registered execution from
      ⟨select execution, failed⟩)))).trans
  exact work_bound coins Memory code publicData privateData dummy registered bounded

end
end FormalProof4FHE.HasteBoots.ConstructedGoldObjectSecurity
