module
public import FormalProof4FHE.HasteBoots.ClassicalGoldDescriptorSetup
public import FormalProof4FHE.HasteBoots.ConstructedGoldAllocationOrder
@[expose] public section

/-! Original allocated role objects and the literal canonical/classical.rs
parameter-index routing. These are logical immutable handles and projections;
Rust pointer/heap/ABI and whole-PBS dispatcher refinement remain separate. -/
namespace FormalProof4FHE.HasteBoots.ClassicalGoldRoleBundle
open ClassicalGoldDescriptor (Specification Plans prepare admitted invocations calibrationRole)
open NativeGoldParameterStore (Entry GoodEntry)
open ConstructedGoldObjectSetup (Job allocate)
open ConstructedGoldConstructorSetup (jobs job)
open ConstructedGoldAllocationOrder (entryJob)
noncomputable section

structure Bundle where
  specification : Specification
  plans : Plans
  prepared : prepare specification = .ok plans
  accepted : admitted specification = true
  steps : Fin 4 → ℕ
  entries : List Entry
  allocated : allocate [] (jobs (invocations plans steps)) = some (.ok entries)

def jobAt (bundle : Bundle) (index : Fin 4) : Job :=
  job ⟨(bundle.plans.at index).request,(bundle.plans.at index).header,bundle.steps index⟩

theorem jobs_lookup (bundle : Bundle) (index : Fin 4) :
    (jobs (invocations bundle.plans bundle.steps))[index.val]? = some (jobAt bundle index) := by
  fin_cases index <;> rfl

theorem allocated_slot (bundle : Bundle) (index : Fin 4) :
    ∃ entry, bundle.entries[index.val]? = some entry ∧ entryJob entry = jobAt bundle index :=
  ConstructedGoldAllocationOrder.initial_lookup _ bundle.entries bundle.allocated index.val _ (jobs_lookup bundle index)


theorem entries_length (bundle : Bundle) : bundle.entries.length = 4 := by
  have size := ConstructedGoldObjectSetup.allocation_length [] _ bundle.entries bundle.allocated
  simpa only [List.length_nil, zero_add, jobs, invocations, List.length_map, List.length_cons] using size

def entry (bundle : Bundle) (index : Fin 4) : Entry :=
  bundle.entries.get ⟨index.val, by rw [entries_length]; exact index.isLt⟩

theorem entry_spec (bundle : Bundle) (index : Fin 4) :
    bundle.entries[index.val]? = some (entry bundle index) ∧ entryJob (entry bundle index) = jobAt bundle index := by
  have actual : bundle.entries[index.val]? = some (entry bundle index) :=
    List.getElem?_eq_getElem (by rw [entries_length]; exact index.isLt)
  obtain ⟨stored, found, source⟩ := allocated_slot bundle index
  have same : stored = entry bundle index := Option.some.inj (found.symm.trans actual)
  rw [same] at source
  exact ⟨actual,source⟩

theorem entry_request (bundle : Bundle) (index : Fin 4) :
    (entry bundle index).request = (bundle.plans.at index).request :=
  congrArg Job.request (entry_spec bundle index).2

theorem entry_header (bundle : Bundle) (index : Fin 4) :
    (entry bundle index).header = (bundle.plans.at index).header :=
  congrArg Job.header (entry_spec bundle index).2

theorem configured (bundle : Bundle) : ConstructedGoldRegistryTargets.Configured bundle.entries :=
  ConstructedGoldObjectSetup.configured [] .empty (jobs (invocations bundle.plans bundle.steps))
    (ConstructedGoldConstructorSetup.jobs_reachable _)
    (ConstructedGoldConstructorSetup.jobs_admitted _ (ClassicalGoldDescriptor.invocations_admitted bundle.plans
      (ClassicalGoldDescriptor.prepared_admitted bundle.specification bundle.plans bundle.prepared bundle.accepted) bundle.steps))
    bundle.entries bundle.allocated

theorem entry_good (bundle : Bundle) (index : Fin 4) : GoodEntry (entry bundle index) :=
  NativeGoldParameterStore.reachable_good bundle.entries
    (ConstructedGoldRegistryTargets.configured_reachable bundle.entries (configured bundle)) _
    (List.mem_of_getElem? (entry_spec bundle index).1)

def target (bundle : Bundle) (index : Fin 4) : PrivateCoinExecutableSoundness.Target :=
  ConstructedGoldTargets.target (entry bundle index) (entry_good bundle index) (calibrationRole index)
    (by
      rw [entry_request, entry_header]
      exact ClassicalGoldDescriptor.admitted_at bundle.plans
        (ClassicalGoldDescriptor.prepared_admitted bundle.specification bundle.plans bundle.prepared bundle.accepted) index)
    (ConstructedGoldObjectSecurity.context (entry bundle index)) rfl

theorem header_fields (bundle : Bundle) (index : Fin 4) :
    (entry bundle index).initialized.parameters.numVariables = (bundle.plans.at index).header.numVariables ∧
    (entry bundle index).initialized.parameters.width = (bundle.plans.at index).header.width ∧
    (entry bundle index).initialized.parameters.leftVariables = (bundle.plans.at index).header.leftVariables ∧
    (entry bundle index).initialized.parameters.queries = (bundle.plans.at index).header.queries := by
  obtain ⟨result, _, encoded⟩ := NativeGoldParameterInitialization.finish_origin _ _ _ (entry_good bundle index).2
  have retained := NativeGoldEncodedParameters.header_fields _ result.code _ encoded
  rwa [entry_header] at retained


theorem entry_descriptor (bundle : Bundle) (index : Fin 4) :
    (entry bundle index).initialized.parameters.numVariables = (bundle.specification.roles index).numVariables ∧
    (entry bundle index).initialized.parameters.width = (bundle.specification.roles index).width ∧
    (entry bundle index).initialized.parameters.queries = (bundle.specification.roles index).queries := by
  have retained := header_fields bundle index
  have projected := ClassicalGoldDescriptor.project_fields bundle.specification index (bundle.plans.at index)
    (ClassicalGoldDescriptor.prepare_at bundle.specification bundle.plans bundle.prepared index)
  exact ⟨retained.1.trans projected.1, retained.2.1.trans projected.2.1, retained.2.2.2.trans projected.2.2.1⟩

theorem entry_variables (bundle : Bundle) (index : Fin 4) :
    (entry bundle index).initialized.parameters.numVariables.val =
      NativeBrakedownCalibration.roleVariables .goldilocks (calibrationRole index) := by
  rw [(header_fields bundle index).1]
  exact ((ConstructedGoldTargets.admitted_iff _ _ _).mp
    (ClassicalGoldDescriptor.admitted_at bundle.plans
      (ClassicalGoldDescriptor.prepared_admitted bundle.specification bundle.plans bundle.prepared bundle.accepted) index)).arity

theorem entry_left (bundle : Bundle) (index : Fin 4) :
    (entry bundle index).initialized.parameters.leftVariables.val =
      NativeBrakedownCalibration.left .goldilocks (calibrationRole index) := by
  rw [(header_fields bundle index).2.2.1]
  exact ((ConstructedGoldTargets.admitted_iff _ _ _).mp
    (ClassicalGoldDescriptor.admitted_at bundle.plans
      (ClassicalGoldDescriptor.prepared_admitted bundle.specification bundle.plans bundle.prepared bundle.accepted) index)).partition

/-- Parameter uses in canonical/classical.rs::parameters, including all four
main accumulator borrows and every final key-switch source/helper borrow. -/
inductive Stage where
  | coefficients | evaluations | key | inputs | borrows | helper
  | accumulator (index : Fin 4)
  | monomial
  | finalCoefficients | finalEvaluations | finalKey | finalInput | finalBorrows | finalHelper
  deriving DecidableEq

def roleIndex : Stage → Fin 4
  | .helper => 1
  | .finalCoefficients | .finalEvaluations | .finalKey | .finalInput | .finalBorrows => 2
  | .finalHelper => 3
  | _ => 0

def parameters (bundle : Bundle) (stage : Stage) := (entry bundle (roleIndex stage)).initialized.parameters

theorem stage_geometry (bundle : Bundle) (stage : Stage) :
    (parameters bundle stage).numVariables.val = NativeBrakedownCalibration.roleVariables .goldilocks (calibrationRole (roleIndex stage)) ∧
    (parameters bundle stage).width.val = NativeBrakedownCalibration.testWidth .goldilocks (calibrationRole (roleIndex stage)) ∧
    (parameters bundle stage).leftVariables.val = NativeBrakedownCalibration.left .goldilocks (calibrationRole (roleIndex stage)) ∧
    544 ≤ (parameters bundle stage).queries.val :=
  ⟨entry_variables bundle _, (target bundle _).compatible.width, entry_left bundle _, (target bundle _).compatible.queries⟩
end
end FormalProof4FHE.HasteBoots.ClassicalGoldRoleBundle
