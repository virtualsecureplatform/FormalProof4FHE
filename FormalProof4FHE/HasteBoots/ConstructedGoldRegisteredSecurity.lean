module
public import FormalProof4FHE.HasteBoots.ConstructedGoldRegistrySoundness
@[expose] public section

/-! Registered executable-source security without a supplied family of verifier
contexts. Representatives carry only registered parameters and a fixed trusted
profile. They are analysis indices, not simulated native verifier executions.
Actual application registration and profile binding remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.ConstructedGoldRegisteredSecurity
open MeasureTheory
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open NativePrefixCodec (Vector)
open NativeGoldParameterStore (Entry Reference)
open NativeGoldBatchPcsProgram (Context)
open ConstructedGoldRegistryTargets (checkReferences)
open PrivateCoinReplay (Tape)
open ClosedByteMachineExecutableSoundness (Witness)
noncomputable section

structure Registry where
  entries : List Entry
  reachable : NativeGoldParameterStore.Reachable entries
  references : Vector Reference
  checked : checkReferences entries references.val = true
  registry : Vector (NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored)
  retained : NativeGoldParameterStore.registry entries references = some registry

/-- The remaining fields are irrelevant to the witness anchor. Acceptance is
always witnessed by an actual candidate, never by this empty representative. -/
def representative (registered : Registry) (profile : Digest) (index : Fin registered.registry.val.length) : Context where
  tables := ⟨fun _ => false, fun _ => false, fun _ => none⟩
  parameters := (registered.registry.val.get index).parameters
  parent := ⟨[], profile⟩
  root := fun _ => 0
  queries := ⟨[], by decide⟩
  values := ⟨[], by decide⟩
  opening := ⟨⟨[], by decide⟩, ⟨[], by decide⟩, ⟨[], by decide⟩⟩
  fieldFuel := 0

def family (registered : Registry) (profile : Digest) : ConstructedGoldRegistrySoundness.Family where
  entries := registered.entries
  reachable := registered.reachable
  references := registered.references
  checked := registered.checked
  registry := registered.registry
  retained := registered.retained
  contexts := representative registered profile
  associated := fun _ => rfl

def role (registered : Registry) (index : Fin registered.registry.val.length) : NativeBrakedownCalibration.Role :=
  (ConstructedGoldRegistrySoundness.targets (family registered (fun _ => 0)) index).role

/-- Reanchoring preserves the same accepted candidate, its executable public
false claim, scheduler and history. No verifier is rerun. -/
def rebase {Memory : Type} {dummy : Digest} {first second : Context} {radius : ℕ}
    {world : World} {history : List NativeTranscript.Observation}
    (same : first.parameters = second.parameters) (profile : first.parent.profile = second.parent.profile)
    (witness : Witness Memory dummy first radius world history) : Witness Memory dummy second radius world history :=
  { witness with
    sameParameters := witness.sameParameters.trans same
    sameProfile := witness.sameProfile.trans profile }

theorem target_role (registered : Registry) (profile : Digest) (index : Fin registered.registry.val.length) :
    (ConstructedGoldRegistrySoundness.targets (family registered profile) index).role = role registered index := by
  let first := ConstructedGoldRegistrySoundness.binding (family registered profile) index
  let second := ConstructedGoldRegistrySoundness.binding (family registered (fun _ => 0)) index
  have original : first.original = second.original := by
    exact (ConstructedGoldRegistrySoundness.binding_original (family registered profile) index).trans
      (ConstructedGoldRegistrySoundness.binding_original (family registered (fun _ => 0)) index).symm
  have reference : first.reference = second.reference := Option.some.inj (first.atReference.symm.trans (original ▸ second.atReference))
  have entry : first.entry = second.entry := by
    have selected := second.atEntry
    rw [← reference] at selected
    exact Option.some.inj (first.atEntry.symm.trans selected)
  have classified := second.classified
  rw [← entry] at classified
  exact Option.some.inj (first.classified.symm.trans classified)

/-- The original owner receipt determines the registered slot and its role;
no context-to-registry association is supplied separately. -/
theorem binding_registered (registered : Registry) (ctx : Context)
    (bound : ConstructedGoldRegistryTargets.Binding registered.entries registered.references ctx) :
    ∃ index : Fin registered.registry.val.length, bound.original = index.val ∧
      ctx.parameters = (registered.registry.val.get index).parameters ∧ bound.role = role registered index := by
  obtain ⟨before, _⟩ := List.getElem?_eq_some_iff.mp bound.atReference
  have lengths := (NativeGoldParameterStore.registry_values registered.entries registered.references
    registered.registry registered.retained).2
  let index : Fin registered.registry.val.length := ⟨bound.original, by rw [lengths]; exact before⟩
  let canonical := ConstructedGoldRegistrySoundness.binding (family registered (fun _ => 0)) index
  have original : canonical.original = bound.original :=
    ConstructedGoldRegistrySoundness.binding_original (family registered (fun _ => 0)) index
  have selected := canonical.atReference
  rw [original] at selected
  have reference : canonical.reference = bound.reference := Option.some.inj (selected.symm.trans bound.atReference)
  have stored := canonical.atEntry
  rw [reference] at stored
  have entry : canonical.entry = bound.entry := Option.some.inj (stored.symm.trans bound.atEntry)
  refine ⟨index, rfl, ?_, ?_⟩
  · have parameters := canonical.parameters
    rw [entry] at parameters
    exact bound.parameters.trans parameters.symm
  · have classified := canonical.classified
    rw [entry] at classified
    exact Option.some.inj (bound.classified.symm.trans classified)

/-- All candidate contexts with registered parameters and the fixed profile,
across every prefix of the same execution. Other candidate fields are free. -/
def Failure (Memory : Type) (code : List PrivateCoinByteMachine.Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (registered : Registry)
    (profile : Digest) (execution : Tape × World) : Prop :=
  ∃ fuel, ∃ index : Fin registered.registry.val.length, ∃ candidate : Context,
    candidate.parameters = (registered.registry.val.get index).parameters ∧ candidate.parent.profile = profile ∧
    Nonempty (Witness Memory dummy candidate (NativeBrakedownCalibration.radius .goldilocks (role registered index))
      execution.2 (PrivateCoinByteLineage.history code publicData privateData execution.1 fuel execution.2).run.2)

/-- Apply an original-owner binding (for example, from successful observed
public extraction) to the same prefix's accepted executable false claim. -/
theorem failure_of_binding (Memory : Type) (code : List PrivateCoinByteMachine.Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (registered : Registry)
    (profile : Digest) (execution : Tape × World) (fuel : ℕ) (ctx : Context)
    (bound : ConstructedGoldRegistryTargets.Binding registered.entries registered.references ctx)
    (sameProfile : ctx.parent.profile = profile)
    (witness : Witness Memory dummy ctx (NativeBrakedownCalibration.radius .goldilocks bound.role)
      execution.2 (PrivateCoinByteLineage.history code publicData privateData execution.1 fuel execution.2).run.2) :
    Failure Memory code publicData privateData dummy registered profile execution := by
  obtain ⟨index, _, parameters, sameRole⟩ := binding_registered registered ctx bound
  refine ⟨fuel, index, ctx, parameters, sameProfile, ⟨?_⟩⟩
  rw [← sameRole]
  exact witness

theorem failure_iff (Memory : Type) (code : List PrivateCoinByteMachine.Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (registered : Registry)
    (profile : Digest) (execution : Tape × World) :
    Failure Memory code publicData privateData dummy registered profile execution ↔
      ConstructedGoldRegistrySoundness.Failure Memory code publicData privateData dummy (family registered profile) execution := by
  constructor
  · rintro ⟨fuel, index, candidate, parameters, sameProfile, ⟨witness⟩⟩
    refine ⟨index, fuel, ⟨?_⟩⟩
    rw [target_role]
    exact rebase parameters sameProfile witness
  · rintro ⟨index, fuel, ⟨witness⟩⟩
    refine ⟨fuel, index, representative registered profile index, rfl, rfl, ⟨?_⟩⟩
    rw [← target_role registered profile index]
    exact witness

theorem failure_measurable (Memory : Type) (code : List PrivateCoinByteMachine.Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (registered : Registry) (profile : Digest) :
    MeasurableSet {execution | Failure Memory code publicData privateData dummy registered profile execution} := by
  simp only [failure_iff]
  exact ConstructedGoldRegistrySoundness.failure_measurable Memory code publicData privateData dummy (family registered profile)

theorem scaled_bound (coins : Measure Tape) (Memory : Type) (code : List PrivateCoinByteMachine.Instruction)
    (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)
    (registered : Registry) (profile : Digest) :
    (2 : ENNReal)^128 * (coins.prod law)
      {execution | Failure Memory code publicData privateData dummy registered profile execution} ≤
      ((registered.registry.val.length : ENNReal)*(9/4096)) * PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  simp only [failure_iff]
  exact ConstructedGoldRegistrySoundness.scaled_bound coins Memory code publicData privateData dummy (family registered profile)

theorem configured_bound (coins : Measure Tape) (Memory : Type) (code : List PrivateCoinByteMachine.Instruction)
    (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)
    (registered : Registry) (profile : Digest) (bounded : registered.registry.val.length ≤ 256) :
    (2 : ENNReal)^128 * (coins.prod law)
      {execution | Failure Memory code publicData privateData dummy registered profile execution} ≤
      (9/16 : ENNReal) * PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  simp only [failure_iff]
  exact ConstructedGoldRegistrySoundness.configured_bound coins Memory code publicData privateData dummy (family registered profile) bounded
/-- The configured family fits one unit of specified interpreter work. This
is not a conversion from the interpreter counter to physical attacker work. -/
theorem work_bound (coins : Measure Tape) (Memory : Type) (code : List PrivateCoinByteMachine.Instruction)
    (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)
    (registered : Registry) (profile : Digest) (bounded : registered.registry.val.length ≤ 256) :
    (2 : ENNReal)^128 * (coins.prod law)
      {execution | Failure Memory code publicData privateData dummy registered profile execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  have numeric : (9/16 : NNReal) ≤ 1 := by
    apply (NNReal.coe_le_coe).mp
    norm_num
  have allowance := ENNReal.coe_le_coe.mpr numeric
  simp only [ENNReal.coe_div (by norm_num : (16 : NNReal) ≠ 0), ENNReal.coe_ofNat, ENNReal.coe_one] at allowance
  exact (configured_bound coins Memory code publicData privateData dummy registered profile bounded).trans
    (by simpa only [one_mul] using mul_le_mul' allowance (le_refl (PrivateCoinByteWork.expectedWork coins code publicData privateData)))

end
end FormalProof4FHE.HasteBoots.ConstructedGoldRegisteredSecurity
