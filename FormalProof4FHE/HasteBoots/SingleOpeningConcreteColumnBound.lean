module
public import FormalProof4FHE.HasteBoots.SingleOpeningConcreteColumnFamily
public import FormalProof4FHE.HasteBoots.SingleOpeningWitnessedColumnBound
@[expose] public section

/-! Concrete shared-column loss for the combined native response family.
The source is recovered from the selecting history. Winning states include
their own disagreement witness, so correct states need no false-response
premise. No physical-work or full application-soundness claim is made. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningConcreteColumnBound
open NativeGoldPcsExecution (Context)
open SingleOpeningChallengeLink (View)
open SingleOpeningConcreteColumnFamily (raw claim Position)
open NativeRootMessage (Digest)
open NativeGoldBlockCode (logSize)
open NativeTranscript (Observation Execution)
open InputIndexedOracle (Input World law)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section

def distance (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (radius : ℕ) : ℕ :=
  min (Code.minDist (BlockCode.code (SingleOpeningConcreteColumnFamily.Domain ctx primitive)
    ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val : Set (Position ctx → SingleOpeningConcreteColumnFamily.Symbol ctx)) - radius) (radius+1)

def event (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (profile : Digest) (decoded : View) (history : List Observation) (radius : ℕ) (world : World) : Prop :=
  match SingleOpeningFirstFieldSource.recover dummy history decoded.field with
  | none => False
  | some sourceLog => ∃ fuel, SingleOpeningFieldColumnLaw.event profile fuel decoded (logSize ctx.parameters.code)
      (SingleOpeningWitnessedColumnBound.checked (logSize ctx.parameters.code) decoded.column.index.count.val
        (raw dummy ctx decoded sourceLog) (claim ctx primitive decoded) (distance ctx primitive radius)) world

theorem conditional_bound {S A : Type} {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (profile : Digest) (decoded : View) (input : Input) (parsed : SingleOpeningChallengeLink.parse input = some decoded)
    (step : S → OracleMachine.Command S A) (world : World)
    (selected : CausalStreamExposure.firstRead step (past world).run = some input)
    (power : decoded.column.index.domain.val = 2^(logSize ctx.parameters.code)) (radius : ℕ) :
    (law[|{other | (past other).run = (past world).run}])
      {other | event dummy ctx primitive profile decoded (past world).run.2 radius other} ≤
      ColumnOpening.missBound (Position ctx) decoded.column.index.count.val (distance ctx primitive radius) := by
  cases found : SingleOpeningFirstFieldSource.recover dummy (past world).run.2 decoded.field with
  | none => simp only [event,found,Set.ofPred_false,measure_empty]; exact bot_le
  | some sourceLog =>
    simp only [event,found]
    exact SingleOpeningWitnessedColumnBound.eventual_bound replay profile decoded input parsed step world selected
      (logSize ctx.parameters.code) power (raw dummy ctx decoded sourceLog) (claim ctx primitive decoded) (distance ctx primitive radius)

theorem fixed_measurable {P : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (profile : Digest) (decoded : View) (history : List Observation) (radius : ℕ) :
    MeasurableSet {world | event dummy ctx primitive profile decoded history radius world} := by
  cases found : SingleOpeningFirstFieldSource.recover dummy history decoded.field with
  | none => simp only [event,found,Set.ofPred_false]; exact MeasurableSet.empty
  | some sourceLog =>
    simp only [event,found]
    exact SingleOpeningWitnessedColumnBound.eventual_measurable replay profile decoded (logSize ctx.parameters.code)
      (raw dummy ctx decoded sourceLog) (claim ctx primitive decoded) (distance ctx primitive radius)

theorem event_append (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (profile : Digest) (decoded : View) (history suffix : List Observation) (radius : ℕ) (world : World)
    (sourceLog : NativeRootFamilySourceSelection.Log)
    (found : SingleOpeningFirstFieldSource.recover dummy history decoded.field = some sourceLog) :
    event dummy ctx primitive profile decoded (history++suffix) radius world ↔ event dummy ctx primitive profile decoded history radius world := by
  simp only [event,found,SingleOpeningFirstFieldSource.recover_append dummy history suffix decoded.field sourceLog found]

/-- The minimum distance formulation is exactly the maximum of the two
shared miss terms; it adds no union factor for random versus structured tests. -/
theorem miss_min (ctx : Context) (count first second : ℕ) :
    ColumnOpening.missBound (Position ctx) count (min first second) =
      max (ColumnOpening.missBound (Position ctx) count first) (ColumnOpening.missBound (Position ctx) count second) := by
  have anti (a b : ℕ) (ordered : a ≤ b) : ColumnOpening.missBound (Position ctx) count b ≤ ColumnOpening.missBound (Position ctx) count a := by
    unfold ColumnOpening.missBound
    apply pow_le_pow_left₀ zero_le
    exact ENNReal.div_le_div_right (by exact_mod_cast Nat.sub_le_sub_left ordered (Fintype.card (Position ctx))) _
  by_cases ordered : first ≤ second
  · rw [Nat.min_eq_left ordered,max_eq_left (anti first second ordered)]
  · have reverse := Nat.le_of_not_ge ordered
    rw [Nat.min_eq_right reverse,max_eq_right (anti second first reverse)]
end
end FormalProof4FHE.HasteBoots.SingleOpeningConcreteColumnBound
