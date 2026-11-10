module
public import FormalProof4FHE.HasteBoots.NativeGoldConstructedRegistry
public import FormalProof4FHE.HasteBoots.PrivateCoinByteConfigurationUnion
@[expose] public section

/-! Calibrated targets derived from retained parameter constructors and an
explicit trusted-configuration policy. This policy is not an extra check in
the native generic constructor; native application admission remains separate.
No constructor, primitive-root or role-calibration certificate is supplied to
the target builder independently of those receipts and checked fields. -/
namespace FormalProof4FHE.HasteBoots.ConstructedGoldTargets
open NativeGoldBlockCodeProgram (Request)
open NativeGoldEncodedParameters (Header)
open NativeGoldParameterStore (Entry GoodEntry)
open NativeGoldBatchPcsProgram (Context)
open NativeBrakedownCalibration (Role roleVariables left codeWidth testWidth)
open PrivateCoinExecutableSoundness (Target)
noncomputable section

structure Policy (role : Role) (request : Request) (header : Header) : Prop where
  arity : header.numVariables.val = roleVariables .goldilocks role
  width : header.width.val = testWidth .goldilocks role
  partition : header.leftVariables.val = left .goldilocks role
  queries : 544 ≤ header.queries.val
  message : request.message.val = 2^(roleVariables .goldilocks role-left .goldilocks role)
  block : request.block.val = codeWidth .goldilocks
  blowup : request.blowup.val = 2

def admitted (role : Role) (request : Request) (header : Header) : Bool := decide
  (header.numVariables.val = roleVariables .goldilocks role ∧
   header.width.val = testWidth .goldilocks role ∧
   header.leftVariables.val = left .goldilocks role ∧ 544 ≤ header.queries.val ∧
   request.message.val = 2^(roleVariables .goldilocks role-left .goldilocks role) ∧
   request.block.val = codeWidth .goldilocks ∧ request.blowup.val = 2)

theorem admitted_iff (role : Role) (request : Request) (header : Header) :
    admitted role request header = true ↔ Policy role request header := by
  simp only [admitted, decide_eq_true_eq]
  constructor
  · rintro ⟨arity, width, partition, queries, message, block, blowup⟩
    exact ⟨arity, width, partition, queries, message, block, blowup⟩
  · intro policy
    exact ⟨policy.arity, policy.width, policy.partition, policy.queries, policy.message, policy.block, policy.blowup⟩

def tables (entry : Entry) (good : GoodEntry entry) : NativeGoldBlockCode.Tables :=
  NativeGoldBlockCodeBackend.observations entry.config.cache
    (NativeGoldBlockCodeProgram.reachable_good entry.request entry.config good.1).1

theorem entry_build (entry : Entry) (good : GoodEntry entry) :
    NativeGoldBlockCode.build (tables entry good) entry.request.message entry.request.block entry.request.blowup =
      .ok entry.initialized.parameters.code := by
  obtain ⟨result, finished, encoded⟩ := NativeGoldParameterInitialization.finish_origin entry.header entry.config entry.initialized good.2
  rw [NativeGoldEncodedParameters.retained_code entry.header result.code entry.initialized encoded]
  exact NativeGoldBlockCodeBackend.completed_build entry.request entry.config good.1 result finished

theorem entry_matches (entry : Entry) (good : GoodEntry entry) (role : Role)
    (accepted : admitted role entry.request entry.header = true) (ctx : Context)
    (same : ctx.parameters = entry.initialized.parameters) : NativeGoldBatchCalibration.Matches ctx role := by
  have policy := (admitted_iff role entry.request entry.header).mp accepted
  obtain ⟨result, _, encoded⟩ := NativeGoldParameterInitialization.finish_origin entry.header entry.config entry.initialized good.2
  have fields := NativeGoldEncodedParameters.header_fields entry.header result.code entry.initialized encoded
  have built := NativeGoldBlockCode.build_spec (tables entry good) entry.request.message entry.request.block entry.request.blowup
    entry.initialized.parameters.code (entry_build entry good)
  constructor
  · rw [same, fields.2.1]
    exact policy.width
  · rw [same]
    unfold NativeGoldBlockCode.logSize
    rw [built.count, policy.message, policy.block, policy.blowup]
    rfl
  · rw [same, built.padded, policy.message, policy.block]
    rfl
  · rw [same, fields.2.2.2]
    exact policy.queries

/-- The retained constructor/cache observations supply all code and root
certificates. The context is associated with the original stored parameters. -/
def target (entry : Entry) (good : GoodEntry entry) (role : Role)
    (accepted : admitted role entry.request entry.header = true) (ctx : Context)
    (same : ctx.parameters = entry.initialized.parameters) : Target where
  ctx := ctx
  role := role
  tables := tables entry good
  message := entry.request.message
  block := entry.request.block
  blowup := entry.request.blowup
  constructed := by rw [same]; exact entry_build entry good
  primitive := by
    rw [same]
    exact NativeGoldParameterInitialization.code_primitive entry.header entry.request entry.config good.1 entry.initialized good.2
  compatible := entry_matches entry good role accepted ctx same

end
end FormalProof4FHE.HasteBoots.ConstructedGoldTargets
