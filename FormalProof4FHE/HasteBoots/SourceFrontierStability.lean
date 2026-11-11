module
public import FormalProof4FHE.HasteBoots.ScalarPublicSourceModel
public import FormalProof4FHE.HasteBoots.NativeSeedAncestry
@[expose] public section

/-! Public source selection at a pending positive read uses only the earlier
history. Once the pending input resolves the source key, every actual positive
answer and arbitrary continuation retain that very source, including keys
not previously frozen. No read values or future opening select a new table. -/
namespace FormalProof4FHE.HasteBoots.SourceFrontierStability
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open NativeRootFamilySourceSelection (Log)
open NativeGoldColumnAuthentication (encoding)
open NativeGoldBatchPcsProgram (Context)
noncomputable section

/-- The charged executable selector and native causal selector agree even
before the key has a snapshot, including their current-hash-log fallback. -/
theorem selected_eq_native (dummy : Digest) (history : List Observation) (context root : Digest) :
    SourceHistoryOwnerLog.selected history context root =
      NativeRootFamilySourceSelection.select (NativeRootFamilyHistory.reconstruct encoding dummy history) (context,root) := by
  unfold SourceHistoryOwnerLog.selected
  rw [StoredSourceSnapshotSelection.run_value,SourceHistoryOwnerLog.key_view,
    ExecutableSourceHistory.reconstruct_eq encoding dummy]
  exact ExecutableSourceSelection.select_eq _ _

/-- A resolved pending input freezes the pre-read public owner at all heights.
The supplied answer is arbitrary apart from being nonempty. -/
theorem read_snapshot (dummy : Digest) (before after : List Observation) (context root : Digest)
    (input : Input) (offset : ℕ) (values : Input) (positive : values ≠ [])
    (resolved : (context,root) ∈ NativeParentLedger.resolve
      (NativeRootFamilyHistory.reconstruct encoding dummy before).1.1
      (NativeRootFamilyHistory.reconstruct encoding dummy before).1.2 input) :
    ∀ height : NativeMerkleShapeFamily.Height,
      ⟨(context,height),⟨root,SourceHistoryOwnerLog.selected before context root⟩⟩ ∈
        (NativeGoldBatchFamilyAvailability.reconstructed dummy (before ++ .output input offset values :: after)).checkpoints.checkpoints := by
  rw [selected_eq_native dummy before context root]
  exact NativeRootFamilySourceSelection.selected_history encoding dummy before after (context,root) input offset values positive resolved

/-- Unlike plain append stability, this theorem also handles a key whose
first freeze is the current pending read. No existing snapshot is assumed. -/
theorem selected_read (dummy : Digest) (before after : List Observation) (context root : Digest)
    (input : Input) (offset : ℕ) (values : Input) (positive : values ≠ [])
    (resolved : (context,root) ∈ NativeParentLedger.resolve
      (NativeRootFamilyHistory.reconstruct encoding dummy before).1.1
      (NativeRootFamilyHistory.reconstruct encoding dummy before).1.2 input) :
    SourceHistoryOwnerLog.selected (before ++ .output input offset values :: after) context root =
      SourceHistoryOwnerLog.selected before context root :=
  SourceHistoryOwnerLog.of_snapshot dummy _ context root 0 _
    (read_snapshot dummy before after context root input offset values positive resolved 0)

/-- The executable public cube itself is fixed at the pending frontier.
Stability needs no decoding-radius or algebraic constructor assumption. -/
theorem cube_read (ctx : Context) (dummy context root : Digest) (before after : List Observation) (radius : ℕ)
    (capacity : GoldCommonSourceTable.Capacity ctx.parameters) (geometry : GoldHistorySourceTable.Geometry ctx.parameters)
    (input : Input) (offset : ℕ) (values : Input) (positive : values ≠ [])
    (resolved : (context,root) ∈ NativeParentLedger.resolve
      (NativeRootFamilyHistory.reconstruct encoding dummy before).1.1
      (NativeRootFamilyHistory.reconstruct encoding dummy before).1.2 input) :
    GoldHistoryPublicExtraction.cube ctx dummy context root (before ++ .output input offset values :: after) radius capacity geometry =
      GoldHistoryPublicExtraction.cube ctx dummy context root before radius capacity geometry := by
  unfold GoldHistoryPublicExtraction.cube GoldHistoryPublicExtraction.rectangular
  rw [selected_read dummy before after context root input offset values positive resolved]

/-- Every original packing lane, including unused lanes, is fixed before the
new read value enters the native point or any future helper/source opening. -/
theorem scalar_read (ctx : Context) (dummy context root : Digest) (before after : List Observation) (radius : ℕ)
    (capacity : GoldCommonSourceTable.Capacity ctx.parameters) (geometry : GoldHistorySourceTable.Geometry ctx.parameters)
    {padding c : ℕ} (width : ctx.parameters.width.val = 3+padding) (shape : 3+padding = 2^c)
    (input : Input) (offset : ℕ) (values : Input) (positive : values ≠ [])
    (resolved : (context,root) ∈ NativeParentLedger.resolve
      (NativeRootFamilyHistory.reconstruct encoding dummy before).1.1
      (NativeRootFamilyHistory.reconstruct encoding dummy before).1.2 input) :
    ScalarPublicSourceModel.publicScalar ctx dummy context root (before ++ .output input offset values :: after) radius capacity geometry width shape =
      ScalarPublicSourceModel.publicScalar ctx dummy context root before radius capacity geometry width shape := by
  unfold ScalarPublicSourceModel.publicScalar ScalarPublicSourceModel.publicPacked
  rw [cube_read ctx dummy context root before after radius capacity geometry input offset values positive resolved]

/-- Chronological native source lineage supplies resolution using only the
old byte cache. No assumption that the source is already frozen is needed. -/
theorem known_resolves (dummy : Digest) (world : World) (before : List Observation) (parent input : Input) (context root : Digest)
    (known : NativeSourceLineage.Known world before parent (context,root)) (truthful : ObservationReplay.Agrees world before)
    (quoted : NativeChildSeedView.quote input = some (InputIndexedOracle.block world parent 0 64)) :
    (context,root) ∈ NativeParentLedger.resolve
      (NativeRootFamilyHistory.reconstruct encoding dummy before).1.1
      (NativeRootFamilyHistory.reconstruct encoding dummy before).1.2 input := by
  have resolved := NativeSourceLineage.resolve_known_source known truthful input quoted
  simpa only [NativeRootFamilyHistory.reconstruct,NativeRootFamilyHistory.initial,NativeRootFamilyState.fold_parent] using resolved

/-- Position-indexed form for an actual positive observation in one history. -/
theorem scalar_read_at (ctx : Context) (dummy context root : Digest) (history : List Observation) (radius : ℕ)
    (capacity : GoldCommonSourceTable.Capacity ctx.parameters) (geometry : GoldHistorySourceTable.Geometry ctx.parameters)
    {padding c : ℕ} (width : ctx.parameters.width.val = 3+padding) (shape : 3+padding = 2^c)
    (position : ℕ) (input : Input) (offset : ℕ) (values : Input) (positive : values ≠ [])
    (positioned : history[position]? = some (.output input offset values))
    (resolved : (context,root) ∈ NativeParentLedger.resolve
      (NativeRootFamilyHistory.reconstruct encoding dummy (history.take position)).1.1
      (NativeRootFamilyHistory.reconstruct encoding dummy (history.take position)).1.2 input) :
    ScalarPublicSourceModel.publicScalar ctx dummy context root history radius capacity geometry width shape =
      ScalarPublicSourceModel.publicScalar ctx dummy context root (history.take position) radius capacity geometry width shape := by
  obtain ⟨bound,entryEq⟩ := List.getElem?_eq_some_iff.mp positioned
  have parts := List.take_append_drop position history
  rw [List.drop_eq_getElem_cons bound,entryEq] at parts
  have stable := scalar_read ctx dummy context root (history.take position) (history.drop (position+1)) radius capacity geometry width shape
    input offset values positive resolved
  rw [parts] at stable
  exact stable

/-- Actual source ancestry fixes the table at the pre-read history, except
for the existing seed-quote-order bad event. This covers off-path and partially
observed streams and does not assume a chronological ancestry certificate. -/
theorem ancestry_scalar_read {S A : Type} (step : S → OracleMachine.Command S A) (fuel : ℕ) (initial : S) (world : World)
    (ctx : Context) (dummy context root : Digest) (radius : ℕ)
    (capacity : GoldCommonSourceTable.Capacity ctx.parameters) (geometry : GoldHistorySourceTable.Geometry ctx.parameters)
    {padding c : ℕ} (width : ctx.parameters.width.val = 3+padding) (shape : 3+padding = 2^c)
    (parent : Input) (parentIndex : ℕ) (fact : NativeSeedAncestry.Fact)
    (realized : NativeSeedAncestry.Realized world (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2
      parent parentIndex fact)
    (position : ℕ) (input : Input) (offset : ℕ) (values : Input) (positive : values ≠ [])
    (positioned : (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2[position]? = some (.output input offset values))
    (quoted : NativeChildSeedView.quote input = some (InputIndexedOracle.block world parent 0 64))
    (member : (context,root) ∈ NativeSeedAncestry.Keys input fact) :
    ScalarPublicSourceModel.publicScalar ctx dummy context root
        (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2 radius capacity geometry width shape =
      ScalarPublicSourceModel.publicScalar ctx dummy context root
        ((OracleProgram.run (OracleMachine.take step fuel initial) world).run.2.take position) radius capacity geometry width shape ∨
      SeedQuoteOrder.Bad step initial world := by
  by_cases safe : ¬SeedQuoteOrder.Bad step initial world
  · apply Or.inl
    have resolved := realized.before_read_resolves step fuel initial world safe position input offset values positive positioned quoted
      (context,root) member
    have nativeResolved : (context,root) ∈ NativeParentLedger.resolve
        (NativeRootFamilyHistory.reconstruct encoding dummy
          ((OracleProgram.run (OracleMachine.take step fuel initial) world).run.2.take position)).1.1
        (NativeRootFamilyHistory.reconstruct encoding dummy
          ((OracleProgram.run (OracleMachine.take step fuel initial) world).run.2.take position)).1.2 input := by
      simpa only [NativeRootFamilyHistory.reconstruct,NativeRootFamilyHistory.initial,NativeRootFamilyState.fold_parent] using resolved
    exact scalar_read_at ctx dummy context root _ radius capacity geometry width shape position input offset values positive positioned nativeResolved
  · exact Or.inr (not_not.mp safe)

end
end FormalProof4FHE.HasteBoots.SourceFrontierStability
