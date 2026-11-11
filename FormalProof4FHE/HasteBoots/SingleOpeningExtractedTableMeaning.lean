module
public import FormalProof4FHE.HasteBoots.QueryRectangularNativeMeaning
public import FormalProof4FHE.HasteBoots.SingleOpeningCausalCoverage
public import FormalProof4FHE.HasteBoots.QueryReindex
@[expose] public section

/-! The same common rectangular extractor table, viewed at native cube
addresses, is consumed by an interpreted abstract opening query. This changes
neither source selection nor decoding, and assumes no honest table padding. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningExtractedTableMeaning
open NativeGoldPcsExecution (Context)
open NativeRootMessage (Digest)
open NativeFields (Goldilocks)
open SingleOpeningChallengeLink (View)
open SingleOpeningConcreteColumnFamily (Domain source)
open SingleOpeningFixedResponseData (left right claimed)
noncomputable section

abbrev Log := MerkleTreeExtractor.QueryLog InputIndexedOracle.Input Digest

def rectangular (dummy : Digest) (ctx : Context) (origin : CacheBackedSingleOpening.Origin ctx)
    (decoded : View) (sourceLog : Log) (radius : ℕ) :=
  RectangularMatrixOpeningKernel.extract (Domain ctx origin.primitive) origin.capacity radius (source dummy ctx decoded sourceLog)

/-- Fixed public dimensions reindex one common extracted table; opening query
matrices and claimed values are not inputs to the source layout. -/
def cube (dummy : Digest) (ctx : Context) (origin : CacheBackedSingleOpening.Origin ctx)
    (decoded : View) (sourceLog : Log) (radius back : ℕ) (length : ctx.parameters.code.messageLength.val = 2^back) :=
  QueryRectangularNativeMeaning.source ctx.parameters back length (rectangular dummy ctx origin decoded sourceLog radius)

theorem fold_cube (dummy : Digest) (ctx : Context) (origin : CacheBackedSingleOpening.Origin ctx)
    (decoded : View) (sourceLog : Log) (radius back : ℕ) (length : ctx.parameters.code.messageLength.val = 2^back)
    (query : ExtensionQuery.Broadcast Goldilocks ctx.parameters.width.val (ctx.parameters.leftVariables.val + back))
    (read : NativeGoldCoefficientsQuery.interpret ctx.parameters.width.val (ctx.parameters.leftVariables.val + back)
      ⟨decoded.field.data.query.models,none⟩ = some query) :
    query.query.fold (cube dummy ctx origin decoded sourceLog radius back length) =
      matrixEvaluation (left ctx.parameters decoded.field.data.query) (right ctx.parameters decoded.field.data.query)
        (rectangular dummy ctx origin decoded sourceLog radius) :=
  QueryRectangularNativeMeaning.fold_source ctx.parameters decoded.field.data.query back query read length _

/-- Only the complete context/root and exact selected log fix the word.
Changing opening queries, raw responses or claims cannot change this table. -/
theorem rectangular_same (dummy : Digest) (ctx : Context) (origin : CacheBackedSingleOpening.Origin ctx)
    (first second : View) (sourceLog : Log) (radius : ℕ)
    (context : first.field.data.context = second.field.data.context)
    (root : first.field.data.root = second.field.data.root) :
    rectangular dummy ctx origin first sourceLog radius = rectangular dummy ctx origin second sourceLog radius := by
  unfold rectangular source
  rw [context,root]

theorem cube_same (dummy : Digest) (ctx : Context) (origin : CacheBackedSingleOpening.Origin ctx)
    (first second : View) (sourceLog : Log) (radius back : ℕ) (length : ctx.parameters.code.messageLength.val = 2^back)
    (context : first.field.data.context = second.field.data.context)
    (root : first.field.data.root = second.field.data.root) :
    cube dummy ctx origin first sourceLog radius back length = cube dummy ctx origin second sourceLog radius back length := by
  unfold cube
  rw [rectangular_same dummy ctx origin first second sourceLog radius context root]

/-- Falsity used by the native causal lifetime theorem is exactly falsity of
this interpreted query on the same selected common-source cube. -/
theorem false_claim_iff (dummy : Digest) (ctx : Context) (origin : CacheBackedSingleOpening.Origin ctx)
    (decoded : View) (history : List NativeTranscript.Observation) (radius back : ℕ)
    (length : ctx.parameters.code.messageLength.val = 2^back)
    (query : ExtensionQuery.Broadcast Goldilocks ctx.parameters.width.val (ctx.parameters.leftVariables.val + back))
    (read : NativeGoldCoefficientsQuery.interpret ctx.parameters.width.val (ctx.parameters.leftVariables.val + back)
      ⟨decoded.field.data.query.models,none⟩ = some query) :
    SingleOpeningCausalCoverage.FalseClaim dummy ctx origin decoded history radius ↔
      ∀ sourceLog, SingleOpeningFirstFieldSource.recover dummy history decoded.field = some sourceLog →
        claimed ctx decoded.field.data.claimed ≠ query.query.fold (cube dummy ctx origin decoded sourceLog radius back length) := by
  simp only [SingleOpeningCausalCoverage.FalseClaim,fold_cube dummy ctx origin decoded _ radius back length query read,rectangular]

/-- Native total lane lookup agrees with an already established field vector,
including raw aliases of the same canonical coefficient. -/
theorem claimed_of_encoded (ctx : Context) (value : NativeLookupRequestWire.Row)
    (expected : Fin ctx.parameters.width.val → Goldilocks)
    (encoded : value.val.map NativeFieldRepresentation.goldValue = List.ofFn expected) :
    claimed ctx value = expected := by
  funext lane
  have atLane := congrArg (fun words : List Goldilocks => (words[lane.val]?).getD (NativeFieldRepresentation.goldValue 0)) encoded
  simpa [claimed,List.getElem?_map,Option.getD_map] using atLane

theorem false_claim_of_encoded (dummy : Digest) (ctx : Context) (origin : CacheBackedSingleOpening.Origin ctx)
    (decoded : View) (history : List NativeTranscript.Observation) (radius back : ℕ)
    (length : ctx.parameters.code.messageLength.val = 2^back)
    (query : ExtensionQuery.Broadcast Goldilocks ctx.parameters.width.val (ctx.parameters.leftVariables.val + back))
    (read : NativeGoldCoefficientsQuery.interpret ctx.parameters.width.val (ctx.parameters.leftVariables.val + back)
      ⟨decoded.field.data.query.models,none⟩ = some query)
    (expected : Fin ctx.parameters.width.val → Goldilocks)
    (encoded : decoded.field.data.claimed.val.map NativeFieldRepresentation.goldValue = List.ofFn expected)
    (wrong : ∀ sourceLog, SingleOpeningFirstFieldSource.recover dummy history decoded.field = some sourceLog →
      expected ≠ query.query.fold (cube dummy ctx origin decoded sourceLog radius back length)) :
    SingleOpeningCausalCoverage.FalseClaim dummy ctx origin decoded history radius := by
  apply (false_claim_iff dummy ctx origin decoded history radius back length query read).mpr
  rw [claimed_of_encoded ctx decoded.field.data.claimed expected encoded]
  exact wrong

/-- Arity transport changes neither the original query's fold nor the table.
This accommodates the native terminal point's own dimension index. -/
theorem fold_cube_arity {n : ℕ} (dummy : Digest) (ctx : Context) (origin : CacheBackedSingleOpening.Origin ctx)
    (decoded : View) (sourceLog : Log) (radius back : ℕ) (length : ctx.parameters.code.messageLength.val = 2^back)
    (query : ExtensionQuery.Broadcast Goldilocks ctx.parameters.width.val n)
    (read : NativeGoldCoefficientsQuery.interpret ctx.parameters.width.val n ⟨decoded.field.data.query.models,none⟩ = some query)
    (arity : n = ctx.parameters.leftVariables.val + back) :
    query.query.fold (QueryReindex.source arity (cube dummy ctx origin decoded sourceLog radius back length)) =
      matrixEvaluation (left ctx.parameters decoded.field.data.query) (right ctx.parameters decoded.field.data.query)
        (rectangular dummy ctx origin decoded sourceLog radius) := by
  subst n
  exact fold_cube dummy ctx origin decoded sourceLog radius back length query read

theorem false_claim_iff_arity {n : ℕ} (dummy : Digest) (ctx : Context) (origin : CacheBackedSingleOpening.Origin ctx)
    (decoded : View) (history : List NativeTranscript.Observation) (radius back : ℕ)
    (length : ctx.parameters.code.messageLength.val = 2^back)
    (query : ExtensionQuery.Broadcast Goldilocks ctx.parameters.width.val n)
    (read : NativeGoldCoefficientsQuery.interpret ctx.parameters.width.val n ⟨decoded.field.data.query.models,none⟩ = some query)
    (arity : n = ctx.parameters.leftVariables.val + back) :
    SingleOpeningCausalCoverage.FalseClaim dummy ctx origin decoded history radius ↔
      ∀ sourceLog, SingleOpeningFirstFieldSource.recover dummy history decoded.field = some sourceLog →
        claimed ctx decoded.field.data.claimed ≠ query.query.fold
          (QueryReindex.source arity (cube dummy ctx origin decoded sourceLog radius back length)) := by
  subst n
  exact false_claim_iff dummy ctx origin decoded history radius back length query read

/-- Actual native preparation supplies the split arity and original message
length; no independent geometry or code-capacity certificate is required. -/
theorem prepared_dimensions (ctx : Context) (world : InputIndexedOracle.World) (work : NativeGoldPcsWorkers.Prepared)
    (prepared : (OracleProgram.run ctx.prefix world).run.1 = .prepared work) :
    ctx.parameters.numVariables.val = ctx.parameters.leftVariables.val +
      (ctx.parameters.numVariables.val - ctx.parameters.leftVariables.val) ∧
    ctx.parameters.code.messageLength.val = 2^(ctx.parameters.numVariables.val - ctx.parameters.leftVariables.val) := by
  have geometry := NativeBrakedownParameters.build_spec NativeGoldBlockCode.description ctx.parameters work.geometry
    (SingleOpeningRectangularData.geometry ctx world work prepared)
  exact ⟨by have bound := geometry.basic.2.1; omega,geometry.code.1⟩

/-- The native prepared call discharges both public-dimension premises of the
abstract/common-extractor false-claim equivalence. -/
theorem prepared_false_claim_iff (dummy : Digest) (ctx : Context) (origin : CacheBackedSingleOpening.Origin ctx)
    (world : InputIndexedOracle.World) (work : NativeGoldPcsWorkers.Prepared)
    (prepared : (OracleProgram.run ctx.prefix world).run.1 = .prepared work)
    (decoded : View) (history : List NativeTranscript.Observation) (radius : ℕ)
    (query : ExtensionQuery.Broadcast Goldilocks ctx.parameters.width.val ctx.parameters.numVariables.val)
    (read : NativeGoldCoefficientsQuery.interpret ctx.parameters.width.val ctx.parameters.numVariables.val
      ⟨decoded.field.data.query.models,none⟩ = some query) :
    let dimensions := prepared_dimensions ctx world work prepared
    SingleOpeningCausalCoverage.FalseClaim dummy ctx origin decoded history radius ↔
      ∀ sourceLog, SingleOpeningFirstFieldSource.recover dummy history decoded.field = some sourceLog →
        claimed ctx decoded.field.data.claimed ≠ query.query.fold
          (QueryReindex.source dimensions.1 (cube dummy ctx origin decoded sourceLog radius
            (ctx.parameters.numVariables.val - ctx.parameters.leftVariables.val) dimensions.2)) := by
  exact false_claim_iff_arity dummy ctx origin decoded history radius _
    (prepared_dimensions ctx world work prepared).2 query read (prepared_dimensions ctx world work prepared).1

end
end FormalProof4FHE.HasteBoots.SingleOpeningExtractedTableMeaning
