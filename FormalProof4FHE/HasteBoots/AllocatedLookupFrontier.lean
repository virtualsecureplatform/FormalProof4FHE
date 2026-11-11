module
public import FormalProof4FHE.HasteBoots.AllocatedLookupTables
@[expose] public section

/-! Stability of the complete original allocated table family at a positive
pending read. One shared seed-order exception covers all source columns and
the original helper; no future answer or opening selects replacement tables. -/
namespace FormalProof4FHE.HasteBoots.AllocatedLookupFrontier
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (Input World)
open AllocatedLookupTables (sources helpers sourceAt helperIndex Geometry)
noncomputable section

variable {ctx : Context (Vector Opening)} {world : World} {body : NativeSharedLookupBody.Bound}
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world body) (index : Fin origin.ready.jobs.length)
    (job : LookupExecutionJob.Job origin index)
    (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries) (helperHandle : ℕ)
    (references : Vector Reference) (template : Context (Vector Opening))
    (assembled : AllocatedLookupContext.assemble entries helperHandle references template = some ctx)
    (geometry : Geometry origin index job) (dummy : Digest) (radius : ℕ)

def sourceKey (slot : Fin ctx.registry.val.length) : NativeCanonicalLookupWire.Source :=
  (InputIndexedOracle.sha512 world (GoldContextInput.bytes (ctx.registry.val.get slot).parameters),(ctx.registry.val.get slot).root)

def helperKey : NativeCanonicalLookupWire.Source :=
  (InputIndexedOracle.sha512 world (GoldContextInput.bytes ctx.helper),ctx.proof.roots.val.get (helperIndex origin index))

def resolved (history : List Observation) (input : Input) (key : NativeCanonicalLookupWire.Source) : Prop :=
  key ∈ NativeParentLedger.resolve (NativeRootFamilyHistory.reconstruct NativeGoldColumnAuthentication.encoding dummy history).1.1
    (NativeRootFamilyHistory.reconstruct NativeGoldColumnAuthentication.encoding dummy history).1.2 input

structure Resolved (history : List Observation) (input : Input) : Prop where
  sources : ∀ column : Fin (origin.ready.jobs.get index).tag.request.columns,
    resolved dummy history input (sourceKey (ctx := ctx) (world := world) (job.slots.slot column))
  helper : resolved dummy history input (helperKey origin index)

theorem sourceAt_read (slot : Fin ctx.registry.val.length)
    (sizes : GoldHistorySourceTable.Geometry (RegistryPublicSource.context ctx slot).parameters)
    (before after : List Observation) (input : Input) (offset : ℕ) (values : Input) (positive : values ≠ [])
    (found : resolved dummy before input (sourceKey (ctx := ctx) (world := world) slot)) :
    sourceAt origin entries reachable helperHandle references template assembled dummy (before ++ .output input offset values :: after) radius slot sizes =
      sourceAt origin entries reachable helperHandle references template assembled dummy before radius slot sizes := by
  unfold sourceAt ScalarPublicSourceModel.publicPacked
  rw [SourceFrontierStability.cube_read _ dummy _ _ before after radius _ sizes input offset values positive found]

theorem helpers_read (before after : List Observation) (input : Input) (offset : ℕ) (values : Input) (positive : values ≠ [])
    (found : resolved dummy before input (helperKey origin index)) :
    helpers origin index job entries reachable helperHandle references template assembled geometry dummy (before ++ .output input offset values :: after) radius =
      helpers origin index job entries reachable helperHandle references template assembled geometry dummy before radius := by
  unfold helpers ScalarPublicSourceModel.publicPacked
  dsimp only
  rw [SourceFrontierStability.cube_read _ dummy _ _ before after radius _ _ input offset values positive found]

/-- All original source columns and the helper remain the same for any
nonempty answer, byte offset and continuation, including repeated slots. -/
theorem read (before after : List Observation) (input : Input) (offset : ℕ) (values : Input) (positive : values ≠ [])
    (found : Resolved origin index job dummy before input) :
    sources origin index job entries reachable helperHandle references template assembled geometry dummy (before ++ .output input offset values :: after) radius =
        sources origin index job entries reachable helperHandle references template assembled geometry dummy before radius ∧
      helpers origin index job entries reachable helperHandle references template assembled geometry dummy (before ++ .output input offset values :: after) radius =
        helpers origin index job entries reachable helperHandle references template assembled geometry dummy before radius := by
  constructor
  · funext column
    exact sourceAt_read origin entries reachable helperHandle references template assembled dummy radius (job.slots.slot column)
      (geometry.source column) before after input offset values positive (found.sources column)
  · exact helpers_read origin index job entries reachable helperHandle references template assembled geometry dummy radius
      before after input offset values positive found.helper

/-- The family at an actual positive observation equals its pre-read family;
no prior snapshot of these keys is required. -/
theorem read_at (history : List Observation) (position : ℕ) (input : Input) (offset : ℕ) (values : Input)
    (positive : values ≠ []) (positioned : history[position]? = some (.output input offset values))
    (found : Resolved origin index job dummy (history.take position) input) :
    sources origin index job entries reachable helperHandle references template assembled geometry dummy history radius =
        sources origin index job entries reachable helperHandle references template assembled geometry dummy (history.take position) radius ∧
      helpers origin index job entries reachable helperHandle references template assembled geometry dummy history radius =
        helpers origin index job entries reachable helperHandle references template assembled geometry dummy (history.take position) radius := by
  obtain ⟨bound,same⟩ := List.getElem?_eq_some_iff.mp positioned
  have parts := List.take_append_drop position history
  rw [List.drop_eq_getElem_cons bound,same] at parts
  have stable := read origin index job entries reachable helperHandle references template assembled geometry dummy radius
    (history.take position) (history.drop (position+1)) input offset values positive found
  rw [parts] at stable
  exact stable

end
end FormalProof4FHE.HasteBoots.AllocatedLookupFrontier
