module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchEventContext
public import FormalProof4FHE.HasteBoots.NativeRootFamilyLifetime
public import FormalProof4FHE.HasteBoots.OracleMachinePrelude
@[expose] public section

/-! One lifetime probability bound covers all accepted native batches with
fixed public parameters/profile. Roots, parents, responses and schedulers may
vary. Prelude exposures remain explicit. This is analysis-extractor soundness
in the ideal-oracle model, not public PBS extraction or physical work. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchLifetimeSoundness
open NativeGoldBatchPcsProgram (Context Prepared Scheduler)
open NativeGoldBlockCode (Tables logSize)
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
  sameProfile : candidate.parent.profile = ctx.parent.profile
  primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue candidate.parameters.code.domainRoot) (2^(logSize candidate.parameters.code+1))
  capacity : candidate.parameters.code.messageLength.val ≤ candidate.parameters.code.messageBlocks.val*candidate.parameters.code.blockWidth.val
  choose : Scheduler Memory
  verifierFuel : ℕ
  memory : Memory
  work : Prepared
  decoded : NativeGoldBatchChallengeLink.View
  parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input candidate work world) = some decoded
  responseFits : (NativeGoldBatchResponseBinding.payload candidate.opening).length < TranscriptFrame.lengthLimit
  accepted : NativeGoldBatchAnySourceRisk.Accepted world log candidate choose verifierFuel memory work
  falseClaim : NativeGoldBatchCausalCoverage.FalseClaim dummy candidate primitive work decoded log capacity radius

def Failure {P S A : Type} (Memory : Type) (dummy : Digest) (ctx : Context) (radius : ℕ)
    (past : World → Execution P) (initial : P → S) (step : S → OracleMachine.Command S A) (world : World) : Prop :=
  ∃ fuel, Nonempty (Witness Memory dummy ctx radius world (history past initial step fuel world).run.2)

def Inherited {P S A : Type} (Memory : Type) (dummy : Digest) (ctx : Context) (radius : ℕ)
    (past : World → Execution P) (initial : P → S) (step : S → OracleMachine.Command S A) (world : World) : Prop :=
  ∃ fuel, ∃ witness : Witness Memory dummy ctx radius world (history past initial step fuel world).run.2,
    CausalStreamExposure.seen (past world).run.2 (NativeGoldBatchColumnRequestLaw.input witness.candidate witness.work world) = true ∨
      CausalStreamExposure.seen (past world).run.2 (NativeGoldBatchFirstFieldSource.input witness.decoded.field) = true

def SourceBad {P S A : Type} (dummy : Digest) (past : World → Execution P) (initial : P → S)
    (step : S → OracleMachine.Command S A) (world : World) : Prop :=
  ∃ fuel, NativeRootFamilyLifetime.Bad dummy (history past initial step fuel world).run.2

theorem failure_covered {P S A : Type} (Memory : Type) (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (radius : ℕ) (width : 3 ≤ ctx.parameters.width.val)
    {past : World → Execution P} (replay : ObservationReplay.Replayable past) (initial : P → S)
    (step : S → OracleMachine.Command S A) (world : World)
    (failed : Failure Memory dummy ctx radius past initial step world) :
    Inherited Memory dummy ctx radius past initial step world ∨ SourceBad dummy past initial step world ∨
    (∃ index, NativeEarlyReceiptBound.event ctx.parent.profile step (history past initial step index world).run world) ∨
    (∃ index, NativeGoldBatchFieldProximity.event dummy ctx primitive radius ctx.parent.profile step (history past initial step index world).run world) ∨
    (∃ index, NativeGoldBatchProfileColumnExposure.event dummy ctx primitive ctx.parent.profile step (history past initial step index world).run radius world) := by
  obtain ⟨fuel,⟨witness⟩⟩ := failed
  have candidateConstructed : NativeGoldBlockCode.build tables message block blowup = .ok witness.candidate.parameters.code := by
    rw [witness.sameParameters]
    exact constructed
  have candidateWidth : 3 ≤ witness.candidate.parameters.width.val := by rw [witness.sameParameters]; exact width
  have covered := NativeGoldBatchCausalCoverage.accepted_coverage past replay initial step fuel world dummy witness.candidate witness.work
    tables message block blowup candidateConstructed witness.primitive witness.choose witness.verifierFuel witness.memory witness.decoded
    witness.parsed witness.responseFits witness.accepted witness.capacity radius candidateWidth witness.falseClaim
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
    have transferred := (NativeGoldBatchEventContext.field_event dummy witness.candidate ctx witness.sameParameters witness.primitive primitive
      radius witness.candidate.parent.profile step _ world).mp event
    rw [witness.sameProfile] at transferred
    exact ⟨index,transferred⟩
  · right; right; right; right
    obtain ⟨index,_,event⟩ := column
    have transferred := (NativeGoldBatchEventContext.profile_column_event dummy witness.candidate ctx witness.sameParameters witness.primitive primitive
      radius witness.candidate.parent.profile step _ world).mp event
    rw [witness.sameProfile] at transferred
    exact ⟨index,transferred⟩
theorem lifetime_bound {P S A : Type} (Memory : Type) (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (radius : ℕ) (width : 3 ≤ ctx.parameters.width.val)
    {past : World → Execution P} (replay : ObservationReplay.Replayable past) (initial : P → S)
    (step : S → OracleMachine.Command S A)
    (large : radius < Fintype.card NativeFields.Goldilocks)
    (small : 3*radius < Code.minDist (BlockCode.code (NativeGoldBatchResponseMeaning.Domain ctx primitive)
      ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
        Set (NativeGoldBatchConcreteColumnFamily.Position ctx → NativeGoldBatchConcreteColumnFamily.Symbol ctx))) :
    law {world | Failure Memory dummy ctx radius past initial step world} ≤
      law {world | Inherited Memory dummy ctx radius past initial step world} +
      (law {world | SourceBad dummy past initial step world} +
        ((∫⁻ world, NativeEarlyReceiptBound.totalCharge past initial step world ∂law) +
        ((∫⁻ world, NativeGoldBatchFieldProximity.totalCharge past initial dummy ctx primitive radius step world ∂law) +
          (∫⁻ world, NativeGoldBatchProfileColumnExposure.totalCharge past initial dummy ctx primitive step radius world ∂law)))) := by
  have receipt := NativeEarlyReceiptBound.lifetime_le replay initial ctx.parent.profile step ∅
  have field := NativeGoldBatchFieldProximity.lifetime_le replay initial dummy ctx primitive radius ctx.parent.profile step ∅ large small
  have column := NativeGoldBatchProfileColumnExposure.lifetime_le replay initial dummy ctx primitive ctx.parent.profile step radius ∅
  simp only [Set.empty_union,measure_empty,zero_add] at receipt field column
  have included : {world | Failure Memory dummy ctx radius past initial step world} ⊆
      {world | Inherited Memory dummy ctx radius past initial step world} ∪
      ({world | SourceBad dummy past initial step world} ∪
      ({world | ∃ index, NativeEarlyReceiptBound.event ctx.parent.profile step (history past initial step index world).run world} ∪
      ({world | ∃ index, NativeGoldBatchFieldProximity.event dummy ctx primitive radius ctx.parent.profile step (history past initial step index world).run world} ∪
       {world | ∃ index, NativeGoldBatchProfileColumnExposure.event dummy ctx primitive ctx.parent.profile step (history past initial step index world).run radius world}))) := by
    intro world failed
    exact failure_covered Memory dummy ctx primitive tables message block blowup constructed radius width replay initial step world failed
  apply (measure_mono included).trans
  apply (measure_union_le _ _).trans
  apply add_le_add le_rfl
  apply (measure_union_le _ _).trans
  apply add_le_add le_rfl
  apply (measure_union_le _ _).trans
  apply add_le_add receipt
  exact (measure_union_le _ _).trans (add_le_add field column)

def exposureCharge {P S A : Type} (past : World → Execution P) (initial : P → S)
    (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (radius : ℕ) (step : S → OracleMachine.Command S A) : ENNReal :=
  (∫⁻ world, NativeEarlyReceiptBound.totalCharge past initial step world ∂law) +
    ((∫⁻ world, NativeGoldBatchFieldProximity.totalCharge past initial dummy ctx primitive radius step world ∂law) +
      (∫⁻ world, NativeGoldBatchProfileColumnExposure.totalCharge past initial dummy ctx primitive step radius world ∂law))

def clean {S : Type} (state : S) (_ : World) : Execution S := pure state

theorem inherited_clean {S A : Type} (Memory : Type) (dummy : Digest) (ctx : Context) (radius : ℕ)
    (state : S) (step : S → OracleMachine.Command S A) :
    {world | Inherited Memory dummy ctx radius (clean state) id step world} = ∅ := by
  ext world
  simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
  rintro ⟨fuel,witness,old | old⟩ <;> cases old

theorem initialised_bound {S A : Type} (Memory : Type) (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (radius : ℕ) (width : 3 ≤ ctx.parameters.width.val)
    (state : S) (step : S → OracleMachine.Command S A)
    (large : radius < Fintype.card NativeFields.Goldilocks)
    (small : 3*radius < Code.minDist (BlockCode.code (NativeGoldBatchResponseMeaning.Domain ctx primitive)
      ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
        Set (NativeGoldBatchConcreteColumnFamily.Position ctx → NativeGoldBatchConcreteColumnFamily.Symbol ctx))) :
    law {world | Failure Memory dummy ctx radius (clean state) id step world} ≤
      (⨆ fuel : ℕ, NativeRootFamilyLifetime.prefixCharge dummy (.pure state) step fuel) +
        exposureCharge (clean state) id dummy ctx primitive radius step := by
  have bounded := lifetime_bound Memory dummy ctx primitive tables message block blowup constructed radius width
    (ObservationReplay.pure_replay state) id step large small
  have empty : {world | Inherited Memory dummy ctx radius (fun _ => pure state) id step world} = ∅ :=
    inherited_clean Memory dummy ctx radius state step
  rw [empty,measure_empty,zero_add] at bounded
  have source : law {world | SourceBad dummy (clean state) id step world} ≤
      ⨆ fuel : ℕ, NativeRootFamilyLifetime.prefixCharge dummy (.pure state) step fuel := by
    change law {world | ∃ fuel, NativeRootFamilyLifetime.Bad dummy
      (run (NativeRootFamilyLifetime.program (.pure state) step fuel) world).run.2} ≤ _
    exact NativeRootFamilyLifetime.lifetime_bad_le_charge dummy (.pure state) step
  exact bounded.trans (add_le_add source le_rfl)

/-- Rebase the entire recorded prelude and continuation onto one clean causal
machine. Earlier partial field/column reads remain in the same history. -/
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

/-- All finite causal prelude exposures are charged inside the same unbounded
machine, rather than left as an uncharged inherited probability. -/
theorem prelude_bound {S A : Type} (Memory : Type) (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (radius : ℕ) (width : 3 ≤ ctx.parameters.width.val)
    (prelude : Program S) (step : S → OracleMachine.Command S A)
    (large : radius < Fintype.card NativeFields.Goldilocks)
    (small : 3*radius < Code.minDist (BlockCode.code (NativeGoldBatchResponseMeaning.Domain ctx primitive)
      ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
        Set (NativeGoldBatchConcreteColumnFamily.Position ctx → NativeGoldBatchConcreteColumnFamily.Symbol ctx))) :
    law {world | Failure Memory dummy ctx radius (run prelude) id step world} ≤
      (⨆ fuel : ℕ, NativeRootFamilyLifetime.prefixCharge dummy (.pure prelude) (OracleMachinePrelude.prepend step) fuel) +
        exposureCharge (clean prelude) id dummy ctx primitive radius (OracleMachinePrelude.prepend step) := by
  have included : {world | Failure Memory dummy ctx radius (run prelude) id step world} ⊆
      {world | Failure Memory dummy ctx radius (clean prelude) id (OracleMachinePrelude.prepend step) world} :=
    fun world failed => failure_rebase Memory dummy ctx radius prelude step world failed
  exact (measure_mono included).trans (initialised_bound Memory dummy ctx primitive tables message block blowup constructed radius width
    prelude (OracleMachinePrelude.prepend step) large small)

end
end FormalProof4FHE.HasteBoots.NativeGoldBatchLifetimeSoundness
