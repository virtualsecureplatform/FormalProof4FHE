module
import all FormalProof4FHE.HasteBoots.LookupSourceParameterAssociation
import all FormalProof4FHETest.HasteBootsSingleSelectedSmoke

namespace FormalProof4FHE.HasteBoots.ContextAssociationSmoke
open HasteBootsBatchMeaningSmoke (usize root)
open NativeBrakedownContext (Parameters)
open NativeGoldBlockCode (Stored description)
open InputIndexedOracle (World)
open OracleProgram (Program run bind)
noncomputable section

def base := SingleSelectedSmoke.ctx.parameters
def other := {base with queries := usize 99}

theorem different : base ≠ other := by
  intro same
  have impossible : (3 : ℕ) = 99 := congrArg (fun parameters => parameters.queries.val) same
  cases impossible

/-- Full quota and split metadata are retained in the original hash input. -/
example : GoldContextInput.bytes base ≠ GoldContextInput.bytes other := fun same => different (GoldContextInput.bytes_injective same)
example : GoldContextInput.bytes base ≠ GoldContextInput.bytes {base with leftVariables := usize 0} := by
  intro same
  have impossible : (1 : ℕ) = 0 := congrArg (fun parameters => parameters.leftVariables.val) (GoldContextInput.bytes_injective same)
  cases impossible

/-- Equal field values do not erase distinct raw serialized row-code words. -/
def codeRoot := {base with code := {base.code with domainRoot := usize 1}}
def aliasRoot := {base with code := {base.code with domainRoot := usize (NativeFields.goldilocksModulus+1)}}
example : NativeFieldRepresentation.goldValue codeRoot.code.domainRoot = NativeFieldRepresentation.goldValue aliasRoot.code.domainRoot := by decide +kernel
example : GoldContextInput.bytes codeRoot ≠ GoldContextInput.bytes aliasRoot := by
  intro same
  have impossible : (1 : ℕ) = NativeFields.goldilocksModulus+1 :=
    congrArg (fun parameters => parameters.code.domainRoot.val) (GoldContextInput.bytes_injective same)
  have different : (1 : ℕ) ≠ NativeFields.goldilocksModulus+1 := by decide +kernel
  exact different impossible

def world : World := fun _ => 0

def program : Program (Option NativeRootMessage.Digest) := bind (NativeBrakedownContext.context description.row base)
  (fun _ => NativeBrakedownContext.context description.row other)
def history := (run program world).run.2

theorem base_context : (run (NativeBrakedownContext.context description.row base) world).run.1 = some root := by
  rw [GoldContextCollision.context_run]
  rfl

theorem other_context : (run (NativeBrakedownContext.context description.row other) world).run.1 = some root := by
  rw [GoldContextCollision.context_run]
  rfl

theorem base_observed : (run (NativeBrakedownContext.context description.row base) world).run.2.Sublist history := by
  change (run (NativeBrakedownContext.context description.row base) world).run.2.Sublist
    ((run (NativeBrakedownContext.context description.row base) world).run.2 ++
      (run (NativeBrakedownContext.context description.row other) world).run.2)
  exact List.sublist_append_left _ _

theorem other_observed : (run (NativeBrakedownContext.context description.row other) world).run.2.Sublist history := by
  change (run (NativeBrakedownContext.context description.row other) world).run.2.Sublist
    ((run (NativeBrakedownContext.context description.row base) world).run.2 ++
      (run (NativeBrakedownContext.context description.row other) world).run.2)
  exact List.sublist_append_right _ _

/-- The deliberately colliding oracle world enters the existing shared bad
branch, rather than proving equality of unequal parameter records. -/
example : NativeRootFamilyLifetime.Bad root history :=
  (GoldContextCollision.parameters_or_bad base other world root base_context other_context root history
    ((OracleProgram.run_replay program).truthful world) base_observed other_observed).resolve_left different

example : OracleComp.CacheHasCollision (JointHashCache.project history).cache := by
  by_contra noCollision
  exact different (GoldContextCollision.parameters_eq base other world root base_context other_context history
    ((OracleProgram.run_replay program).truthful world) base_observed other_observed noCollision)

/-- All literal context observations are retained, even when inputs differ. -/
example : history.length = 2 := by rw [history,program,OracleProgram.run_bind,ObservationReplay.run_bind,GoldContextCollision.context_run,GoldContextCollision.context_run]; rfl

def repeatProgram : Program (Option NativeRootMessage.Digest) := bind (NativeBrakedownContext.context description.row base)
  (fun _ => NativeBrakedownContext.context description.row base)
def repeatHistory := (run repeatProgram world).run.2

/-- A cached repeat of one input has one cache key and cannot create collision. -/
example : ¬OracleComp.CacheHasCollision (JointHashCache.project repeatHistory).cache := by
  have valid := (JointHashCache.project_valid world repeatHistory ((OracleProgram.run_replay repeatProgram).truthful world)).1
  have keys : (JointHashCache.project repeatHistory).keys = {GoldContextInput.bytes base} := by
    rw [JointHashCache.project_keys]
    simp only [repeatHistory,repeatProgram,OracleProgram.run_bind,ObservationReplay.run_bind,GoldContextCollision.context_run,
      List.singleton_append,JointHashCache.hashInputs,List.toFinset_cons,List.toFinset_nil,Finset.insert_empty]
    exact Finset.insert_eq_of_mem (Finset.mem_singleton_self _)
  rintro ⟨first,second,firstValue,secondValue,distinct,firstKnown,secondKnown,_⟩
  have firstKey := (valid.mem_keys_iff first).mpr ⟨firstValue,firstKnown⟩
  have secondKey := (valid.mem_keys_iff second).mpr ⟨secondValue,secondKnown⟩
  simp only [keys,Finset.mem_singleton] at firstKey secondKey
  exact distinct (firstKey.trans secondKey.symm)

end
end FormalProof4FHE.HasteBoots.ContextAssociationSmoke
