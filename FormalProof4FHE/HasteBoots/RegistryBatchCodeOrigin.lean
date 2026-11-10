module
public import FormalProof4FHE.HasteBoots.AllocatedCodeOrigin
public import FormalProof4FHE.HasteBoots.NativeGoldLookupAvailability
@[expose] public section

/-! Actual deferred batch calls and lookup receipts select the original borrowed
registry object. Reachable allocation/collection derives completed backend
provenance for that call context, without an independent parameter/code match.
This is logical object association, not physical heap or PBS soundness. -/
namespace FormalProof4FHE.HasteBoots.RegistryBatchCodeOrigin
open CacheBackedCodeOrigin (Origin)
open NativeGoldParameterStore (Entry Reference)
open NativeGoldBlockCode (Stored Tables)
open NativePrefixCodec (Vector)
open NativeSharedLookupParent (Oracle)
open NativeDeferredBatchVerification (Call Receipt)
open NativeTranscript (Transcript)
open NativeGoldBatchOpening (Opening)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

/-- A successful native lookup supplies its own index bound. -/
def index (registry : Vector (Oracle Stored)) (slot : ℕ) (oracle : Oracle Stored)
    (found : registry.val[slot]? = some oracle) : Fin registry.val.length :=
  ⟨slot,by obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp found; exact bound⟩

theorem at_index (registry : Vector (Oracle Stored)) (slot : ℕ) (oracle : Oracle Stored)
    (found : registry.val[slot]? = some oracle) : registry.val.get (index registry slot oracle found) = oracle :=
  Option.some.inj ((List.getElem?_eq_getElem (index registry slot oracle found).isLt).symm.trans found)

def ofFound (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (references : Vector Reference) (registry : Vector (Oracle Stored))
    (collected : NativeGoldParameterStore.registry entries references = some registry)
    (call : Call) (found : registry.val[call.slot]? = some call.oracle)
    (tables : Tables) (fieldFuel : ℕ) (parent : Transcript) : Origin (call.context tables fieldFuel parent) :=
  AllocatedCodeOrigin.ofRegistry entries reachable references registry collected (index registry call.slot call.oracle found)
    (call.context tables fieldFuel parent) (congrArg (fun oracle => oracle.parameters) (at_index registry call.slot call.oracle found).symm)

/-- Both code provenance and the commitment remain the selected original
reference's fields. Aliases are not replaced by synthesized commitments. -/
theorem found_original (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (references : Vector Reference) (registry : Vector (Oracle Stored))
    (collected : NativeGoldParameterStore.registry entries references = some registry)
    (call : Call) (found : registry.val[call.slot]? = some call.oracle) :
    ∃ reference entry, references.val[call.slot]? = some reference ∧ entries[reference.handle]? = some entry ∧
      NativeGoldParameterStore.GoodEntry entry ∧ call.oracle.parameters = entry.initialized.parameters ∧
      call.oracle.root = reference.root := by
  obtain ⟨reference,referenceAt,entryAt,good,source⟩ := AllocatedCodeOrigin.registry_entry_spec entries reachable references registry collected
    (index registry call.slot call.oracle found)
  have original := (at_index registry call.slot call.oracle found).symm.trans source
  exact ⟨reference,_,referenceAt,entryAt,good,congrArg (fun oracle => oracle.parameters) original,
    congrArg (fun oracle => oracle.root) original⟩

/-- The native call factory derives registry association from its actual
first-representative selection, rather than a supplied context equality. -/
def ofCall (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (references : Vector Reference) (registry : Vector (Oracle Stored))
    (collected : NativeGoldParameterStore.registry entries references = some registry)
    (state : NativeDeferredOpeningBatch.State)
    (group : Fin (NativeSourceRegistry.groupCount state.sources)) (opening : Opening) (call : Call)
    (computed : NativeDeferredBatchVerification.call registry state group opening = some call)
    (tables : Tables) (fieldFuel : ℕ) (parent : Transcript) : Origin (call.context tables fieldFuel parent) :=
  ofFound entries reachable references registry collected call
    (NativeDeferredBatchVerification.call_spec registry state group opening call computed).2.2.1 tables fieldFuel parent

variable {Memory : Type}
    (ctx : NativeGoldHelperVerification.Context (Vector Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (prepared : NativeGoldLookupVerification.Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (result : NativeDeferredBatchVerification.Result Memory)
    (executed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase =
      .batches prepared progress (.verification result)) (receipt : Receipt Memory) (member : receipt ∈ result.progress.receipts)

include executed member

theorem receipt_found : ctx.registry.val[receipt.call.slot]? = some receipt.call.oracle := by
  obtain ⟨slot,same,found,_,_,_⟩ := NativeGoldLookupAvailability.receipt_owner_key ctx chooseHelper chooseBatch memory world
    prepared progress result executed receipt member
  simpa only [same] using found

/-- Every actual dispatcher receipt obtains provenance from the same allocated
original registry. No code identity, parameter identity or owner proof is input. -/
def ofReceipt (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries) (references : Vector Reference)
    (collected : NativeGoldParameterStore.registry entries references = some ctx.registry) :
    Origin (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) :=
  ofFound entries reachable references ctx.registry collected receipt.call
    (receipt_found ctx chooseHelper chooseBatch memory world prepared progress result executed receipt member)
    ctx.tables ctx.fieldFuel receipt.before

end
end FormalProof4FHE.HasteBoots.RegistryBatchCodeOrigin
