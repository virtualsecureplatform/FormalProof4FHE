module
public import FormalProof4FHE.HasteBoots.ConstructedGoldRegisteredSecurity
public import FormalProof4FHE.HasteBoots.PrivateCoinByteAnyProfile
@[expose] public section

/-! Registered executable-source security for every profile identifier on one
execution. Geometry remains checked and fixed. Native profile/setup validation,
complete PBS semantics, and physical work refinement remain open. -/
namespace FormalProof4FHE.HasteBoots.ConstructedGoldAnyProfileSecurity
open MeasureTheory
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction)
open ConstructedGoldRegisteredSecurity (Registry family)
noncomputable section

def Failure (Memory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (registered : Registry)
    (execution : Tape × World) : Prop :=
  ∃ profile : Digest, ConstructedGoldRegisteredSecurity.Failure Memory code publicData privateData dummy registered profile execution

theorem failure_measurable (Memory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (registered : Registry) :
    MeasurableSet {execution | Failure Memory code publicData privateData dummy registered execution} := by
  have union : {execution | Failure Memory code publicData privateData dummy registered execution} =
      ⋃ profile : Digest, {execution | ConstructedGoldRegisteredSecurity.Failure Memory code publicData privateData dummy registered profile execution} := by
    ext execution
    simp only [Failure, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [union]
  exact MeasurableSet.iUnion fun profile =>
    ConstructedGoldRegisteredSecurity.failure_measurable Memory code publicData privateData dummy registered profile

theorem failure_iff (Memory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (registered : Registry) (execution : Tape × World) :
    Failure Memory code publicData privateData dummy registered execution ↔
      PrivateCoinByteAnyProfile.FamilyFailure Memory code publicData privateData dummy
        (ConstructedGoldRegistrySoundness.targets (family registered (fun _ => 0))) execution := by
  constructor
  · rintro ⟨profile, failed⟩
    obtain ⟨index, fuel, ⟨witness⟩⟩ :=
      (ConstructedGoldRegisteredSecurity.failure_iff Memory code publicData privateData dummy registered profile execution).mp failed
    refine ⟨index, profile, fuel, ⟨?_⟩⟩
    rw [ConstructedGoldRegisteredSecurity.target_role registered profile index] at witness
    change ClosedByteMachineExecutableSoundness.Witness Memory dummy
      (PrivateCoinByteAnyProfile.withProfile (ConstructedGoldRegistrySoundness.targets (family registered (fun _ => 0)) index) profile).ctx
      (NativeBrakedownCalibration.radius .goldilocks (ConstructedGoldRegistrySoundness.targets (family registered (fun _ => 0)) index).role) _ _
    rw [ConstructedGoldRegisteredSecurity.target_role registered (fun _ => 0) index]
    exact witness
  · rintro ⟨index, profile, fuel, ⟨witness⟩⟩
    refine ⟨profile, (ConstructedGoldRegisteredSecurity.failure_iff Memory code publicData privateData dummy registered profile execution).mpr ?_⟩
    refine ⟨index, fuel, ⟨?_⟩⟩
    change ClosedByteMachineExecutableSoundness.Witness Memory dummy
      (PrivateCoinByteAnyProfile.withProfile (ConstructedGoldRegistrySoundness.targets (family registered (fun _ => 0)) index) profile).ctx
      (NativeBrakedownCalibration.radius .goldilocks (ConstructedGoldRegistrySoundness.targets (family registered (fun _ => 0)) index).role) _ _ at witness
    rw [ConstructedGoldRegisteredSecurity.target_role registered (fun _ => 0) index] at witness
    rw [ConstructedGoldRegisteredSecurity.target_role registered profile index]
    exact witness

theorem work_bound (coins : Measure Tape) (Memory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (registered : Registry)
    (bounded : registered.registry.val.length ≤ 256) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | Failure Memory code publicData privateData dummy registered execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  simp only [failure_iff]
  exact PrivateCoinByteAnyProfile.family_work_bound coins Memory code publicData privateData dummy
    (ConstructedGoldRegistrySoundness.targets (family registered (fun _ => 0))) (by
      change Fintype.card (Fin registered.registry.val.length) ≤ 256
      simpa only [Fintype.card_fin] using bounded)

/-- A measurable adaptive identifier gives a genuine measurable selected
failure event, not merely an outer-measure upper bound. -/
theorem selected_failure_measurable (Memory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (registered : Registry)
    (select : Tape × World → Digest) (selected : Measurable select) :
    MeasurableSet {execution | ConstructedGoldRegisteredSecurity.Failure Memory code publicData privateData dummy registered (select execution) execution} := by
  have union : {execution | ConstructedGoldRegisteredSecurity.Failure Memory code publicData privateData dummy registered (select execution) execution} =
      ⋃ profile : Digest, {execution | select execution = profile} ∩
        {execution | ConstructedGoldRegisteredSecurity.Failure Memory code publicData privateData dummy registered profile execution} := by
    ext execution
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro failed; exact ⟨select execution, rfl, failed⟩
    · rintro ⟨profile, same, failed⟩; simpa only [same] using failed
  rw [union]
  exact MeasurableSet.iUnion fun profile =>
    (measurableSet_eq_fun selected measurable_const).inter
      (ConstructedGoldRegisteredSecurity.failure_measurable Memory code publicData privateData dummy registered profile)

theorem selected_work_bound (coins : Measure Tape) (Memory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (registered : Registry)
    (select : Tape × World → Digest) (bounded : registered.registry.val.length ≤ 256) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | ConstructedGoldRegisteredSecurity.Failure Memory code publicData privateData dummy registered (select execution) execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  apply (mul_le_mul' le_rfl (measure_mono (fun execution failed =>
    (show Failure Memory code publicData privateData dummy registered execution from ⟨select execution, failed⟩)))).trans
  exact work_bound coins Memory code publicData privateData dummy registered bounded

end
end FormalProof4FHE.HasteBoots.ConstructedGoldAnyProfileSecurity
