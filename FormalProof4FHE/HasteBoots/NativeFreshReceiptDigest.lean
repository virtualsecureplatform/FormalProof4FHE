module
public import FormalProof4FHE.HasteBoots.NativeFieldObservationScope
public import FormalProof4FHE.HasteBoots.OracleProgramHistory
@[expose] public section

/-! A field collector cannot reveal its distinct receipt key. Retaining the
native collector result refines the actual past, so an unqueried receipt has
its full512-bit digest bound even though its key depends on collected bytes.
The receipt payload is compared whole; no consumed-length decoding, wrapping
assumption, retry cap or completion normalization is used. -/
namespace FormalProof4FHE.HasteBoots.NativeFreshReceiptDigest
open InputIndexedOracle (Input World law block)
open NativeRootMessage (Digest)
open NativeTranscript (Execution Observation)
open NativeIndexExposureRisk (Packet)
open NativeGoldBatchChallengeLink (View)
open NativeEarlyReceiptPrefixRisk (select fieldInput)
open OracleProgram (Program run bind)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
open scoped Classical
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

abbrev Result := Option (View × NativeFieldVector.State)

def digest (payload : Input) : Digest := fun index => (payload[16+index.val]?).getD 0

theorem digest_receipt (world : World) (consumed : Input) :
    digest (NativeTranscript.receipt world consumed).run.1 = block world (NativeReceiptPrefixView.key consumed) 0 64 := by
  funext index
  change ((TranscriptFrame.littleEndian 16 consumed.length ++ InputIndexedOracle.bytes world (NativeReceiptPrefixView.key consumed) 0 64)[16+index.val]?).getD 0 = _
  rw [List.getElem?_append_right (by rw [TranscriptFrame.littleEndian_length]; omega),TranscriptFrame.littleEndian_length]
  simp only [Nat.add_sub_cancel_left,InputIndexedOracle.bytes,List.getElem?_ofFn,dite_eq_left index.isLt,Option.getD_some]

def collected (profile : Digest) (fuel : ℕ) (view : View) (world : World) :=
  NativeFieldVector.execute NativeFields.goldilocksModulus fuel
    (NativeFieldVector.initial (view.field.phase profile) view.field.count.val) world

def program {S A : Type} (profile : Digest) (fuel : ℕ) (step : S → OracleMachine.Command S A) (packet : Packet S A) : Program Result :=
  match select step packet with
  | none => .pure none
  | some view => bind (NativeFieldVector.collect NativeFields.goldilocksModulus fuel
      (NativeFieldVector.initial (view.field.phase profile) view.field.count.val)) (fun state => .pure (some (view,state)))

theorem run_some {S A : Type} (profile : Digest) (fuel : ℕ) (step : S → OracleMachine.Command S A)
    (packet : Packet S A) (world : World) (view : View) (chosen : select step packet = some view) :
    (run (program profile fuel step packet) world).run = (some (view,(collected profile fuel view world).1),(collected profile fuel view world).2) := by
  simp only [program,chosen,OracleProgram.run_bind,ObservationReplay.run_bind,NativeFieldVector.run_collect,
    OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]
  rfl

theorem run_none {S A : Type} (profile : Digest) (fuel : ℕ) (step : S → OracleMachine.Command S A)
    (packet : Packet S A) (world : World) (chosen : select step packet = none) :
    (run (program profile fuel step packet) world).run = (none,[]) := by
  simp only [program,chosen,OracleProgram.run,CanonicalTranscriptSampler.run_pure]

def after {S A : Type} (packet : Packet S A) (result : Result) (world : World) : Prop :=
  match result with
  | none => False
  | some (view,state) => state.remaining = 0 ∧
      CausalStreamExposure.seen packet.2 (NativeReceiptPrefixView.key state.phase.consumed) = false ∧
      (NativeTranscript.receipt world state.phase.consumed).run.1 = view.receipt

def event {S A : Type} (profile : Digest) (fuel : ℕ) (step : S → OracleMachine.Command S A) (packet : Packet S A) (world : World) : Prop :=
  after packet (run (program profile fuel step packet) world).run.1 world

def extended {S A : Type} (past : World → Execution (S ⊕ A)) (profile : Digest) (fuel : ℕ)
    (step : S → OracleMachine.Command S A) := OracleProgramHistory.extend past (program profile fuel step)

theorem extended_replay {S A : Type} {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (profile : Digest) (fuel : ℕ) (step : S → OracleMachine.Command S A) : ObservationReplay.Replayable (extended past profile fuel step) :=
  OracleProgramHistory.replay replay _

theorem after_measurable {S A : Type} (packet : Packet S A) (result : Result) : MeasurableSet {world | after packet result world} := by
  cases result with
  | none => simp [after]
  | some result =>
    rcases result with ⟨view,state⟩
    by_cases eligible : state.remaining = 0 ∧ CausalStreamExposure.seen packet.2 (NativeReceiptPrefixView.key state.phase.consumed) = false
    · simp only [after,eligible,true_and]
      simpa only [NativeTranscriptProgram.run_receipt] using
        OracleExecutionLaw.event_measurable (OracleProgram.run_replay (NativeTranscriptProgram.receipt state.phase.consumed))
          (fun result => result.1 = view.receipt)
    · have empty : {world | after packet (some (view,state)) world} = ∅ := by
        ext world
        simp only [after,Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
        exact fun yes => eligible ⟨yes.1,yes.2.1⟩
      rw [empty]
      exact MeasurableSet.empty

theorem event_measurable {S A : Type} {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (profile : Digest) (fuel : ℕ) (step : S → OracleMachine.Command S A) :
    MeasurableSet {world | event profile fuel step (past world).run world} := by
  exact OracleProgramHistory.event_measurable (extended_replay replay profile fuel step)
    (fun packet world => after packet.1.1 packet.1.2 world) (fun packet => after_measurable packet.1.1 packet.1.2)

/-- The auxiliary collector adds only field reads. Its adaptively chosen
receipt key remains unseen when that key was unseen in the original history. -/
theorem unseen_extended {S A : Type} (profile : Digest) (fuel : ℕ) (step : S → OracleMachine.Command S A)
    (past : World → Execution (S ⊕ A)) (world : World) (view : View) (chosen : select step (past world).run = some view)
    (unseen : CausalStreamExposure.seen (past world).run.2
      (NativeReceiptPrefixView.key (collected profile fuel view world).1.phase.consumed) = false) :
    CausalStreamExposure.seen (extended past profile fuel step world).run.2
      (NativeReceiptPrefixView.key (collected profile fuel view world).1.phase.consumed) = false := by
  obtain ⟨input,_,parsed⟩ := NativeEarlyReceiptPrefixRisk.selected_link step (past world).run view chosen
  have linked := NativeGoldBatchChallengeLink.parse_sound input view parsed profile
  have inputEq := linked.2.2.1
  change (view.field.phase profile).pending.input = fieldInput view at inputEq
  have apart : (view.field.phase profile).pending.input ≠ NativeReceiptPrefixView.key (collected profile fuel view world).1.phase.consumed := by
    rw [inputEq]
    exact NativeEarlyReceiptPrefixRisk.selected_not_receipt step (past world).run view chosen _
  change CausalStreamExposure.seen ((past world).run.2 ++ (run (program profile fuel step (past world).run) world).run.2) _ = false
  rw [run_some profile fuel step (past world).run world view chosen]
  exact NativeFieldObservationScope.unseen_after_collect NativeFields.goldilocksModulus fuel
    (NativeFieldVector.initial (view.field.phase profile) view.field.count.val) world _ _ unseen apart

/-- Condition on the selecting history and the complete actual collector
result/log. A fresh receipt digest is still bounded by2^-512. -/
theorem retained_bound {S A : Type} {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (profile : Digest) (fuel : ℕ) (step : S → OracleMachine.Command S A) (world : World) :
    (law[|{other | (extended past profile fuel step other).run = (extended past profile fuel step world).run}])
      {other | event profile fuel step (past other).run other} ≤ 1/(2 : ENNReal)^512 := by
  have rp := extended_replay replay profile fuel step
  calc
    _ = (law[|{other | (extended past profile fuel step other).run = (extended past profile fuel step world).run}])
        {other | after (past world).run (run (program profile fuel step (past world).run) world).run.1 other} := by
      apply NativeShakeProjection.conditional_event_congr rp world
      intro other same
      have values := congrArg Prod.fst same
      change after (extended past profile fuel step other).run.1.1 (extended past profile fuel step other).run.1.2 other ↔
        after (extended past profile fuel step world).run.1.1 (extended past profile fuel step world).run.1.2 other
      rw [values]
    _ ≤ _ := by
      cases chosen : select step (past world).run with
      | none => simp only [run_none profile fuel step (past world).run world chosen,after,Set.ofPred_false,measure_empty]; exact bot_le
      | some view =>
        rw [run_some profile fuel step (past world).run world view chosen]
        by_cases complete : (collected profile fuel view world).1.remaining = 0
        · by_cases unseen : CausalStreamExposure.seen (past world).run.2
              (NativeReceiptPrefixView.key (collected profile fuel view world).1.phase.consumed) = false
          · simp only [after,complete,unseen,true_and]
            have fresh := unseen_extended profile fuel step past world view chosen unseen
            have probability := OracleSeedGuessing.fresh_seed_targets rp world
              (NativeReceiptPrefixView.key (collected profile fuel view world).1.phase.consumed) {digest view.receipt}
              (fun position => CausalStreamExposure.unseen_coordinates _ _ fresh position.val)
            simp only [Finset.card_singleton,Finset.mem_singleton,Nat.cast_one] at probability
            refine (measure_mono ?_).trans probability.le
            intro other matching
            have equal := congrArg digest matching
            simpa only [digest_receipt,Set.mem_ofPred_eq] using equal
          · simp [after,complete,unseen]
        · simp [after,complete]

/-- Average the refined result fibers inside the original selecting-history
posterior, retaining the mass of both complete and suspended collector states. -/
theorem conditional_bound {S A : Type} {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (profile : Digest) (fuel : ℕ) (step : S → OracleMachine.Command S A) (world : World) :
    (law[|{other | (past other).run = (past world).run}]) {other | event profile fuel step (past other).run other} ≤ 1/(2 : ENNReal)^512 := by
  have positive : law {other | (past other).run = (past world).run} ≠ 0 := by
    rw [ObservationReplay.fiber_eq_assignment replay world]
    exact OraclePosterior.assignment_ne_zero _ _
  let := cond_isProbabilityMeasure (μ := law) positive
  rw [OracleHistoryComposition.refinement_event replay (extended_replay replay profile fuel step)
    (fun packet => packet.1.1) (fun _ => rfl) world _ (event_measurable replay profile fuel step)]
  calc _ ≤ ∫⁻ _other, (1/(2 : ENNReal)^512) ∂law[|{other | (past other).run = (past world).run}] :=
          lintegral_mono (fun current => retained_bound replay profile fuel step current)
       _ = _ := by simp
end
end FormalProof4FHE.HasteBoots.NativeFreshReceiptDigest
