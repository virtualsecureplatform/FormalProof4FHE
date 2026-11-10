module
public import FormalProof4FHE.HasteBoots.ConstructedGoldConstructorSetup
@[expose] public section

/-! Logical projection of classical_profile.rs Specification/Role fields into
Brakedown constructor inputs, preserving canonical four-role order. The shift
and split gates combine the descriptor constructor's checks with the backend
projection. Field/basis, version, serialization, hash and Rust refinement are
separate; security admission below is not a new native constructor check. -/
namespace FormalProof4FHE.HasteBoots.ClassicalGoldDescriptor
open NativeUsizeMessage (Usize)
open NativeGoldBlockCodeProgram (Request)
open NativeGoldEncodedParameters (Header)
open ConstructedGoldConstructorSetup (Invocation)

inductive Backend where
  | brakedown | polyfrim | fragmentedPipfri | polyfrimDictionary | fragmentedPipfriVirtual
  deriving DecidableEq

structure RoleDescription where
  numVariables : Usize
  width : Usize
  queries : Usize
  leftVariables : Option Usize
  blockWidth : Option Usize
  deriving DecidableEq

structure Specification where
  backend : Backend
  roles : Fin 4 → RoleDescription
  blowup : Usize
  fragmentVariables : Option Usize

structure Plan where
  request : Request
  header : Header

structure Plans where
  source : Plan
  helper : Plan
  finalSource : Plan
  finalHelper : Plan

inductive Error where
  | backend | fragments | missingLeft | missingBlock | dimensions
  deriving DecidableEq

/-- Rust's checked descriptor establishes num_vars < 64 and left <= num_vars
before the backend computes 1usize << (num_vars-left). No truncation is used. -/
def projectRole (specification : Specification) (index : Fin 4) : Except Error Plan :=
  let role := specification.roles index
  match role.leftVariables with
  | none => .error .missingLeft
  | some left => match role.blockWidth with
    | none => .error .missingBlock
    | some block =>
      if valid : role.numVariables.val < 64 ∧ left.val ≤ role.numVariables.val then
        let message : Usize := ⟨2^(role.numVariables.val-left.val),
          (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mpr (by omega)⟩
        .ok ⟨⟨message,block,specification.blowup⟩,⟨role.numVariables,role.width,left,role.queries⟩⟩
      else .error .dimensions

def prepare (specification : Specification) : Except Error Plans :=
  if specification.backend ≠ .brakedown then .error .backend else
  if specification.fragmentVariables.isSome then .error .fragments else do
    let source ← projectRole specification 0
    let helper ← projectRole specification 1
    let finalSource ← projectRole specification 2
    let finalHelper ← projectRole specification 3
    pure ⟨source,helper,finalSource,finalHelper⟩

def Plans.admitted (plans : Plans) : Bool :=
  ConstructedGoldTargets.admitted .source plans.source.request plans.source.header &&
  ConstructedGoldTargets.admitted .helper plans.helper.request plans.helper.header &&
  ConstructedGoldTargets.admitted .finalSource plans.finalSource.request plans.finalSource.header &&
  ConstructedGoldTargets.admitted .finalHelper plans.finalHelper.request plans.finalHelper.header

def admitted (specification : Specification) : Bool :=
  match prepare specification with
  | .error _ => false
  | .ok plans => plans.admitted

def invocations (plans : Plans) (steps : Fin 4 → ℕ) : List Invocation :=
  [⟨plans.source.request,plans.source.header,steps 0⟩,
   ⟨plans.helper.request,plans.helper.header,steps 1⟩,
   ⟨plans.finalSource.request,plans.finalSource.header,steps 2⟩,
   ⟨plans.finalHelper.request,plans.finalHelper.header,steps 3⟩]

theorem project_fields (specification : Specification) (index : Fin 4) (plan : Plan)
    (prepared : projectRole specification index = .ok plan) :
    plan.header.numVariables = (specification.roles index).numVariables ∧
    plan.header.width = (specification.roles index).width ∧
    plan.header.queries = (specification.roles index).queries ∧
    (specification.roles index).leftVariables = some plan.header.leftVariables ∧
    (specification.roles index).blockWidth = some plan.request.block ∧
    plan.request.blowup = specification.blowup ∧
    plan.request.message.val = 2^(plan.header.numVariables.val-plan.header.leftVariables.val) ∧
    plan.header.numVariables.val < 64 ∧ plan.header.leftVariables.val ≤ plan.header.numVariables.val := by
  unfold projectRole at prepared
  cases left : (specification.roles index).leftVariables with
  | none => simp only [left] at prepared; cases prepared
  | some splitPoint =>
    simp only [left] at prepared
    cases block : (specification.roles index).blockWidth with
    | none => simp only [block] at prepared; cases prepared
    | some blockWidth =>
      simp only [block] at prepared
      split at prepared
      · rename_i valid
        cases prepared
        exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,valid⟩
      · cases prepared

theorem prepare_roles (specification : Specification) (plans : Plans) (prepared : prepare specification = .ok plans) :
    projectRole specification 0 = .ok plans.source ∧ projectRole specification 1 = .ok plans.helper ∧
      projectRole specification 2 = .ok plans.finalSource ∧ projectRole specification 3 = .ok plans.finalHelper := by
  unfold prepare at prepared
  split at prepared
  · cases prepared
  · split at prepared
    · cases prepared
    · cases first : projectRole specification 0 with
      | error error => simp only [first] at prepared; cases prepared
      | ok source =>
        cases second : projectRole specification 1 with
        | error error => simp only [first, second] at prepared; cases prepared
        | ok helper =>
          cases third : projectRole specification 2 with
          | error error => simp only [first, second, third] at prepared; cases prepared
          | ok finalSource =>
            cases fourth : projectRole specification 3 with
            | error error => simp only [first, second, third, fourth] at prepared; cases prepared
            | ok finalHelper =>
              simp only [first, second, third, fourth, pure, Except.pure] at prepared
              cases prepared
              exact ⟨rfl,rfl,rfl,rfl⟩



theorem prepare_backend (specification : Specification) (plans : Plans) (prepared : prepare specification = .ok plans) :
    specification.backend = .brakedown ∧ specification.fragmentVariables = none := by
  unfold prepare at prepared
  split at prepared
  · cases prepared
  · rename_i backend
    have same : specification.backend = .brakedown := by
      by_contra different
      exact backend different
    split at prepared
    · cases prepared
    · rename_i fragments
      refine ⟨same, ?_⟩
      cases found : specification.fragmentVariables with
      | none => rfl
      | some value => simp [found] at fragments

def Plans.at (plans : Plans) (index : Fin 4) : Plan :=
  match index.val with
  | 0 => plans.source
  | 1 => plans.helper
  | 2 => plans.finalSource
  | _ => plans.finalHelper

def calibrationRole (index : Fin 4) : NativeBrakedownCalibration.Role :=
  match index.val with
  | 0 => .source
  | 1 => .helper
  | 2 => .finalSource
  | _ => .finalHelper

theorem prepare_at (specification : Specification) (plans : Plans) (prepared : prepare specification = .ok plans) (index : Fin 4) :
    projectRole specification index = .ok (plans.at index) := by
  have all := prepare_roles specification plans prepared
  fin_cases index
  · exact all.1
  · exact all.2.1
  · exact all.2.2.1
  · exact all.2.2.2

theorem admitted_at (plans : Plans) (accepted : plans.admitted = true) (index : Fin 4) :
    ConstructedGoldTargets.admitted (calibrationRole index) (plans.at index).request (plans.at index).header = true := by
  simp only [Plans.admitted, Bool.and_eq_true] at accepted
  fin_cases index
  · exact accepted.1.1.1
  · exact accepted.1.1.2
  · exact accepted.1.2
  · exact accepted.2

theorem prepared_admitted (specification : Specification) (plans : Plans)
    (prepared : prepare specification = .ok plans) (accepted : admitted specification = true) : plans.admitted = true := by
  simpa only [admitted, prepared] using accepted


/-- Admission applies to the descriptor's own fields at the canonical role
index, rather than to independently supplied request/header certificates. -/
theorem descriptor_geometry (specification : Specification) (plans : Plans)
    (prepared : prepare specification = .ok plans) (accepted : admitted specification = true) (index : Fin 4) :
    (specification.roles index).numVariables.val = NativeBrakedownCalibration.roleVariables .goldilocks (calibrationRole index) ∧
    (specification.roles index).width.val = NativeBrakedownCalibration.testWidth .goldilocks (calibrationRole index) ∧
    544 ≤ (specification.roles index).queries.val ∧
    (∃ left, (specification.roles index).leftVariables = some left ∧ left.val = NativeBrakedownCalibration.left .goldilocks (calibrationRole index)) ∧
    (∃ block, (specification.roles index).blockWidth = some block ∧ block.val = 4) ∧ specification.blowup.val = 2 := by
  have checked := prepared_admitted specification plans prepared accepted
  have policy := (ConstructedGoldTargets.admitted_iff _ _ _).mp (admitted_at plans checked index)
  obtain ⟨arity, width, queries, left, block, blowup, _, _, _⟩ :=
    project_fields specification index (plans.at index) (prepare_at specification plans prepared index)
  refine ⟨(congrArg (fun value : Usize => value.val) arity).symm.trans policy.arity,
    (congrArg (fun value : Usize => value.val) width).symm.trans policy.width, ?_,
    ⟨_, left, policy.partition⟩, ⟨_, block, policy.block⟩, ?_⟩
  · have quota := policy.queries
    rwa [queries] at quota
  · have expansion := policy.blowup
    rwa [blowup] at expansion

theorem classify_present (role : NativeBrakedownCalibration.Role) (request : Request) (header : Header)
    (accepted : ConstructedGoldTargets.admitted role request header = true) :
    (ConstructedGoldRegistryTargets.classify request header).isSome = true := by
  cases role <;> unfold ConstructedGoldRegistryTargets.classify <;> split_ifs <;> simp_all

theorem invocations_admitted (plans : Plans) (accepted : plans.admitted = true) (steps : Fin 4 → ℕ) :
    ConstructedGoldConstructorSetup.admitted (invocations plans steps) = true := by
  simp only [Plans.admitted, Bool.and_eq_true] at accepted
  have first := classify_present .source _ _ accepted.1.1.1
  have second := classify_present .helper _ _ accepted.1.1.2
  have third := classify_present .finalSource _ _ accepted.1.2
  have fourth := classify_present .finalHelper _ _ accepted.2
  simp only [ConstructedGoldConstructorSetup.admitted, invocations, List.all_cons, List.all_nil,
    first, second, third, fourth, Bool.and_self]
end ClassicalGoldDescriptor
end FormalProof4FHE.HasteBoots
