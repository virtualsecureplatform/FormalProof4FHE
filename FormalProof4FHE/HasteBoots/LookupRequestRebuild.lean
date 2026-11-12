module
public import FormalProof4FHE.HasteBoots.NativeLookupRequestWire
public import FormalProof4FHE.HasteBoots.NativeSharedLookupConfig
@[expose] public section

/-! Typed original wire requests are rebuilt by the existing native
configuration operation before allocation. Policies retain request/slot order;
only canonicalization can change raw public words. No validation flag is an
input to rebuilding. Physical constructor cost/refinement remains separate. -/
namespace FormalProof4FHE.HasteBoots.LookupRequestRebuild
open NativePrefixCodec (Vector)
open NativeLookupRequestWire (Request normalizeRequest)
open NativeSharedLookupValues (Policy)

def check (request : Request) : Bool :=
  NativeTupleLookupConfig.valid request.config.logicalLength request.config.repetitions.val request.config.table.values

def normalized (policy : Policy) (requests : Vector Request) : Vector Request :=
  ⟨requests.val.map (normalizeRequest policy),by rw [List.length_map]; exact requests.property⟩

def rebuild (policy : Policy) (requests : Vector Request) : Option (Vector Request) :=
  if requests.val.all check then some (normalized policy requests) else none

theorem list_model (policy : Policy) (requests : List Request) :
    NativeSharedLookupConfig.rebuild policy (requests.map Request.toModel) =
      if requests.all check then some ((requests.map (normalizeRequest policy)).map Request.toModel) else none := by
  induction requests with
  | nil => rfl
  | cons request rest ih =>
    rw [List.map_cons,NativeSharedLookupConfig.rebuild,NativeLookupRequestWire.rebuild_model]
    change ((if check request then some (normalizeRequest policy request).toModel else none).bind _) = _
    cases first : check request <;> cases tail : rest.all check <;>
      simp only [first,tail,Bool.false_eq_true,ite_false,ite_true,Option.bind_none,Option.bind_some,ih,
        List.all_cons,Bool.false_and,Bool.true_and,List.map_cons,Option.map_none,Option.map_some]

theorem model_rebuild (policy : Policy) (requests : Vector Request) :
    NativeSharedLookupConfig.rebuild policy (requests.val.map Request.toModel) =
      (rebuild policy requests).map (fun output => output.val.map Request.toModel) := by
  rw [list_model]
  cases accepted : requests.val.all check <;> simp only [rebuild,accepted,Bool.false_eq_true,ite_false,ite_true,
    Option.map_none,Option.map_some,normalized]

theorem successful {policy : Policy} {requests output : Vector Request} (built : rebuild policy requests = some output) :
    output = normalized policy requests ∧ requests.val.all check = true := by
  unfold rebuild at built
  split at built
  next accepted => exact ⟨(Option.some.inj built).symm,accepted⟩
  next => contradiction

theorem valid {policy : Policy} {requests output : Vector Request} (built : rebuild policy requests = some output) :
    NativeSharedLookupConfig.Valid (output.val.map Request.toModel) := by
  have native := model_rebuild policy requests
  rw [built,Option.map_some] at native
  exact NativeSharedLookupConfig.rebuild_valid policy _ _ native

theorem length {policy : Policy} {requests output : Vector Request} (built : rebuild policy requests = some output) :
    output.val.length = requests.val.length := by
  rw [(successful built).1]
  exact List.length_map _

theorem preserves {policy : Policy} {requests output : Vector Request} (built : rebuild policy requests = some output) :
    List.Forall₂ (fun original result => result.repetitions = original.repetitions ∧ result.terminal = original.terminal ∧
      result.table.map (List.map NativeFieldRepresentation.goldValue) = original.table.map (List.map NativeFieldRepresentation.goldValue))
      (requests.val.map Request.toModel) (output.val.map Request.toModel) := by
  have native := model_rebuild policy requests
  rw [built,Option.map_some] at native
  exact NativeSharedLookupConfig.rebuild_preserves policy _ _ native

end FormalProof4FHE.HasteBoots.LookupRequestRebuild
