module
public import FormalProof4FHE.HasteBoots.SingleOpeningEventContext
public import FormalProof4FHE.HasteBoots.NativeRootFamilyLifetime
public import FormalProof4FHE.HasteBoots.OracleMachinePrelude
@[expose] public section

/-! Ideal-oracle lifetime soundness for actual accepted single openings
with fixed original parameters/profile and retained constructor provenance.
Roots, parents, responses and schedulers may vary. Inherited reads remain
explicit; a causal prelude can be rebased and charged in the same lifetime.
This is analysis-extractor soundness, not public PBS extraction or physical work. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningLifetimeSoundness
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open NativeGoldPcsProgram (Scheduler)
open NativeGoldColumnAuthentication (encoding)
open NativeRootMessage (Digest)
open NativeTranscript (Execution Observation)
open InputIndexedOracle (World law)
open CausalExposureLifetime (history)
open OracleProgram (Program run)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

structure Witness (Memory : Type) (dummy : Digest) (ctx : Context) (radius : ℕ) (world : World) (log : List Observation) where
  candidate : Context
  sameParameters : candidate.parameters = ctx.parameters
  sameProfile : candidate.transcript.profile = ctx.transcript.profile
  origin : CacheBackedSingleOpening.Origin candidate
  choose : Scheduler Memory
  verifierFuel : ℕ
  memory : Memory
  work : Prepared
  sample : NativeIndexRequest.Result
  receipt : SingleOpeningSamplingReceipt.Receipt candidate world work sample
  decoded : SingleOpeningChallengeLink.View
  parsed : SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input receipt world) = some decoded
  responseFits : (SingleOpeningColumnLaw.payload candidate.opening).length < TranscriptFrame.lengthLimit
  accepted : SingleOpeningAvailability.Accepted world log candidate choose verifierFuel memory work
  falseClaim : SingleOpeningCausalCoverage.FalseClaim dummy candidate origin decoded log radius

def Failure {P S A : Type} (Memory : Type) (dummy : Digest) (ctx : Context) (radius : ℕ)
    (past : World → Execution P) (initial : P → S) (step : S → OracleMachine.Command S A) (world : World) : Prop :=
  ∃ fuel, Nonempty (Witness Memory dummy ctx radius world (history past initial step fuel world).run.2)

def Inherited {P S A : Type} (Memory : Type) (dummy : Digest) (ctx : Context) (radius : ℕ)
    (past : World → Execution P) (initial : P → S) (step : S → OracleMachine.Command S A) (world : World) : Prop :=
  ∃ fuel, ∃ witness : Witness Memory dummy ctx radius world (history past initial step fuel world).run.2,
    CausalStreamExposure.seen (past world).run.2 (SingleOpeningColumnLaw.input witness.receipt world) = true ∨
      CausalStreamExposure.seen (past world).run.2 (SingleOpeningFirstFieldSource.input witness.decoded.field) = true

def SourceBad {P S A : Type} (dummy : Digest) (past : World → Execution P) (initial : P → S)
    (step : S → OracleMachine.Command S A) (world : World) : Prop :=
  ∃ fuel, NativeRootFamilyLifetime.Bad dummy (history past initial step fuel world).run.2

theorem failure_covered {P S A : Type} (Memory : Type) (dummy : Digest) (ctx : Context)
    (origin : CacheBackedSingleOpening.Origin ctx) (radius : ℕ) (width : 3 ≤ ctx.parameters.width.val)
    {past : World → Execution P} (replay : ObservationReplay.Replayable past) (initial : P → S)
    (step : S → OracleMachine.Command S A) (world : World)
    (failed : Failure Memory dummy ctx radius past initial step world) :
    Inherited Memory dummy ctx radius past initial step world ∨ SourceBad dummy past initial step world ∨
    (∃ index, SingleOpeningEarlyReceiptBound.event ctx.transcript.profile step (history past initial step index world).run world) ∨
    (∃ index, SingleOpeningFieldProximity.event dummy ctx origin.primitive radius ctx.transcript.profile step (history past initial step index world).run world) ∨
    (∃ index, SingleOpeningProfileColumnExposure.event dummy ctx origin.primitive ctx.transcript.profile step (history past initial step index world).run radius world) := by
  obtain ⟨fuel,⟨witness⟩⟩ := failed
  have candidateWidth : 3 ≤ witness.candidate.parameters.width.val := by rw [witness.sameParameters]; exact width
  have covered := SingleOpeningCausalCoverage.accepted_coverage past replay initial step fuel world dummy witness.receipt witness.origin
    witness.choose witness.verifierFuel witness.memory witness.decoded witness.parsed witness.responseFits witness.accepted radius candidateWidth witness.falseClaim
  rcases covered with columnOld | fieldOld | different | early | field | column
  · exact Or.inl ⟨fuel,witness,Or.inl columnOld⟩
  · exact Or.inl ⟨fuel,witness,Or.inr fieldOld⟩
  · right; left
    have audit := NativeRootFamilyAudit.disagreement_implies_bad dummy world _
      ((CausalExposureLifetime.history_replay replay initial step fuel).truthful world)
    have decisions : (fun first second : Digest => Fintype.decidablePiFintype first second) =
        (inferInstance : DecidableEq Digest) := Subsingleton.elim _ _
    rw [decisions] at audit
    exact ⟨fuel,audit different⟩
  · right; right; left
    obtain ⟨index,_,event⟩ := early
    rw [witness.sameProfile] at event
    exact ⟨index,event⟩
  · right; right; right; left
    obtain ⟨index,_,event⟩ := field
    have transferred := (SingleOpeningEventContext.field_event dummy witness.candidate ctx witness.sameParameters witness.origin.primitive origin.primitive
      radius witness.candidate.transcript.profile step _ world).mp event
    rw [witness.sameProfile] at transferred
    exact ⟨index,transferred⟩
  · right; right; right; right
    obtain ⟨index,_,event⟩ := column
    have transferred := (SingleOpeningEventContext.profile_column_event dummy witness.candidate ctx witness.sameParameters witness.origin.primitive origin.primitive
      radius witness.candidate.transcript.profile step _ world).mp event
    rw [witness.sameProfile] at transferred
    exact ⟨index,transferred⟩

theorem lifetime_bound {P S A : Type} (Memory : Type) (dummy : Digest) (ctx : Context)
    (origin : CacheBackedSingleOpening.Origin ctx) (radius : ℕ) (width : 3 ≤ ctx.parameters.width.val)
    {past : World → Execution P} (replay : ObservationReplay.Replayable past) (initial : P → S)
    (step : S → OracleMachine.Command S A)
    (large : radius < Fintype.card NativeFields.Goldilocks)
    (small : 3*radius < Code.minDist (BlockCode.code (SingleOpeningConcreteColumnFamily.Domain ctx origin.primitive)
      ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
        Set (SingleOpeningConcreteColumnFamily.Position ctx → SingleOpeningConcreteColumnFamily.Symbol ctx))) :
    law {world | Failure Memory dummy ctx radius past initial step world} ≤
      law {world | Inherited Memory dummy ctx radius past initial step world} +
      (law {world | SourceBad dummy past initial step world} +
        ((∫⁻ world, SingleOpeningEarlyReceiptBound.totalCharge past initial step world ∂law) +
        ((∫⁻ world, SingleOpeningFieldProximity.totalCharge past initial dummy ctx origin.primitive radius step world ∂law) +
          (∫⁻ world, SingleOpeningProfileColumnExposure.totalCharge past initial dummy ctx origin.primitive step radius world ∂law)))) := by
  have receipt := SingleOpeningEarlyReceiptBound.lifetime_le replay initial ctx.transcript.profile step ∅
  have field := SingleOpeningFieldProximity.lifetime_le replay initial dummy ctx origin.primitive radius ctx.transcript.profile step ∅ large small
  have column := SingleOpeningProfileColumnExposure.lifetime_le replay initial dummy ctx origin.primitive ctx.transcript.profile step radius ∅
  simp only [Set.empty_union,measure_empty,zero_add] at receipt field column
  have included : {world | Failure Memory dummy ctx radius past initial step world} ⊆
      {world | Inherited Memory dummy ctx radius past initial step world} ∪
      ({world | SourceBad dummy past initial step world} ∪
      ({world | ∃ index, SingleOpeningEarlyReceiptBound.event ctx.transcript.profile step (history past initial step index world).run world} ∪
      ({world | ∃ index, SingleOpeningFieldProximity.event dummy ctx origin.primitive radius ctx.transcript.profile step (history past initial step index world).run world} ∪
       {world | ∃ index, SingleOpeningProfileColumnExposure.event dummy ctx origin.primitive ctx.transcript.profile step (history past initial step index world).run radius world}))) := by
    intro world failed
    exact failure_covered Memory dummy ctx origin radius width replay initial step world failed
  apply (measure_mono included).trans
  apply (measure_union_le _ _).trans
  apply add_le_add le_rfl
  apply (measure_union_le _ _).trans
  apply add_le_add le_rfl
  apply (measure_union_le _ _).trans
  apply add_le_add receipt
  exact (measure_union_le _ _).trans (add_le_add field column)

def exposureCharge {P S A : Type} (past : World → Execution P) (initial : P → S)
    (dummy : Digest) (ctx : Context) (origin : CacheBackedSingleOpening.Origin ctx)
    (radius : ℕ) (step : S → OracleMachine.Command S A) : ENNReal :=
  (∫⁻ world, SingleOpeningEarlyReceiptBound.totalCharge past initial step world ∂law) +
    ((∫⁻ world, SingleOpeningFieldProximity.totalCharge past initial dummy ctx origin.primitive radius step world ∂law) +
      (∫⁻ world, SingleOpeningProfileColumnExposure.totalCharge past initial dummy ctx origin.primitive step radius world ∂law))

def clean {S : Type} (state : S) (_ : World) : Execution S := pure state

theorem inherited_clean {S A : Type} (Memory : Type) (dummy : Digest) (ctx : Context) (radius : ℕ)
    (state : S) (step : S → OracleMachine.Command S A) :
    {world | Inherited Memory dummy ctx radius (clean state) id step world} = ∅ := by
  ext world
  simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
  rintro ⟨fuel,witness,old | old⟩ <;> cases old

theorem initialised_bound {S A : Type} (Memory : Type) (dummy : Digest) (ctx : Context)
    (origin : CacheBackedSingleOpening.Origin ctx) (radius : ℕ) (width : 3 ≤ ctx.parameters.width.val)
    (state : S) (step : S → OracleMachine.Command S A)
    (large : radius < Fintype.card NativeFields.Goldilocks)
    (small : 3*radius < Code.minDist (BlockCode.code (SingleOpeningConcreteColumnFamily.Domain ctx origin.primitive)
      ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
        Set (SingleOpeningConcreteColumnFamily.Position ctx → SingleOpeningConcreteColumnFamily.Symbol ctx))) :
    law {world | Failure Memory dummy ctx radius (clean state) id step world} ≤
      (⨆ fuel : ℕ, NativeRootFamilyLifetime.prefixCharge dummy (.pure state) step fuel) +
        exposureCharge (clean state) id dummy ctx origin radius step := by
  have bounded := lifetime_bound Memory dummy ctx origin radius width (ObservationReplay.pure_replay state) id step large small
  have empty : {world | Inherited Memory dummy ctx radius (fun _ => pure state) id step world} = ∅ :=
    inherited_clean Memory dummy ctx radius state step
  rw [empty,measure_empty,zero_add] at bounded
  have source : law {world | SourceBad dummy (clean state) id step world} ≤
      ⨆ fuel : ℕ, NativeRootFamilyLifetime.prefixCharge dummy (.pure state) step fuel := by
    change law {world | ∃ fuel, NativeRootFamilyLifetime.Bad dummy
      (run (NativeRootFamilyLifetime.program (.pure state) step fuel) world).run.2} ≤ _
    exact NativeRootFamilyLifetime.lifetime_bad_le_charge dummy (.pure state) step
  exact bounded.trans (add_le_add source le_rfl)

/-- Keep every recorded prelude exposure in the rebased causal machine. -/
theorem failure_rebase {S A : Type} (Memory : Type) (dummy : Digest) (ctx : Context) (radius : ℕ)
    (prelude : Program S) (step : S → OracleMachine.Command S A) (world : World)
    (failed : Failure Memory dummy ctx radius (run prelude) id step world) :
    Failure Memory dummy ctx radius (clean prelude) id (OracleMachinePrelude.prepend step) world := by
  obtain ⟨fuel,⟨witness⟩⟩ := failed
  refine ⟨(run prelude world).run.2.length+fuel,⟨?_⟩⟩
  have logs : (history (clean prelude) id (OracleMachinePrelude.prepend step)
        ((run prelude world).run.2.length+fuel) world).run.2 =
      (history (run prelude) id step fuel world).run.2 := by
    change [] ++ (run (OracleMachine.take (OracleMachinePrelude.prepend step)
      ((run prelude world).run.2.length+fuel) prelude) world).run.2 =
        (run prelude world).run.2 ++ (run (OracleMachine.take step fuel (run prelude world).run.1) world).run.2
    exact OracleMachinePrelude.prelude_log step prelude fuel world
  rw [logs]
  exact witness

/-- A finite causal prelude is charged inside the same unbounded lifetime. -/
theorem prelude_bound {S A : Type} (Memory : Type) (dummy : Digest) (ctx : Context)
    (origin : CacheBackedSingleOpening.Origin ctx) (radius : ℕ) (width : 3 ≤ ctx.parameters.width.val)
    (prelude : Program S) (step : S → OracleMachine.Command S A)
    (large : radius < Fintype.card NativeFields.Goldilocks)
    (small : 3*radius < Code.minDist (BlockCode.code (SingleOpeningConcreteColumnFamily.Domain ctx origin.primitive)
      ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
        Set (SingleOpeningConcreteColumnFamily.Position ctx → SingleOpeningConcreteColumnFamily.Symbol ctx))) :
    law {world | Failure Memory dummy ctx radius (run prelude) id step world} ≤
      (⨆ fuel : ℕ, NativeRootFamilyLifetime.prefixCharge dummy (.pure prelude) (OracleMachinePrelude.prepend step) fuel) +
        exposureCharge (clean prelude) id dummy ctx origin radius (OracleMachinePrelude.prepend step) := by
  have included : {world | Failure Memory dummy ctx radius (run prelude) id step world} ⊆
      {world | Failure Memory dummy ctx radius (clean prelude) id (OracleMachinePrelude.prepend step) world} :=
    fun world failed => failure_rebase Memory dummy ctx radius prelude step world failed
  exact (measure_mono included).trans (initialised_bound Memory dummy ctx origin radius width
    prelude (OracleMachinePrelude.prepend step) large small)

end
end FormalProof4FHE.HasteBoots.SingleOpeningLifetimeSoundness
