module
public import FormalProof4FHE.HasteBoots.NativeFreshReceiptLifetime
@[expose] public section

/-! Combine early receipt-key prefix guesses with fresh digest guesses.
The target Goldilocks profile has at least nine coefficients. Every native
collector budget is included, without decoding or assuming a nonwrapping
receipt-length header. This is an early-receipt probability bound, not the
full field/column application-soundness or physical-work theorem. -/
namespace FormalProof4FHE.HasteBoots.NativeEarlyReceiptBound
open InputIndexedOracle (Input World law)
open NativeTranscript (Execution Observation)
open NativeRootMessage (Digest)
open NativeIndexExposureRisk (Packet)
open NativeFreshReceiptDigest (Result program collected)
open NativeEarlyReceiptPrefixRisk (select)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section

def matching (result : Result) (world : World) : Prop :=
  match result with
  | none => False
  | some (view,state) => 9 ≤ view.field.count.val ∧ state.remaining = 0 ∧
      (NativeTranscript.receipt world state.phase.consumed).run.1 = view.receipt

def finiteEvent {S A : Type} (profile : Digest) (fuel : ℕ) (step : S → OracleMachine.Command S A) (packet : Packet S A) (world : World) : Prop :=
  matching (OracleProgram.run (program profile fuel step packet) world).run.1 world

def event {S A : Type} (profile : Digest) (step : S → OracleMachine.Command S A) (packet : Packet S A) (world : World) : Prop :=
  ∃ fuel, finiteEvent profile fuel step packet world

/-- A positive read leaves a known coordinate, including far-offset reads. -/
theorem seen_coordinate (log : List Observation) (input : Input) (seen : CausalStreamExposure.seen log input = true) :
    ∃ position, (.inl (input,position) : InputIndexedOracle.Coordinate) ∈ ObservationReplay.footprint log := by
  obtain ⟨entry,present,hit⟩ := List.any_eq_true.mp seen
  cases entry with
  | start other => simp [CausalStreamExposure.touches] at hit
  | hash other digest => simp [CausalStreamExposure.touches] at hit
  | output other offset values =>
    have info : other = input ∧ 0 < values.length := of_decide_eq_true hit
    rcases info with ⟨same,positive⟩
    subst other
    refine ⟨offset,Finset.mem_biUnion.mpr ⟨.output input offset values,List.mem_toFinset.mpr present,?_⟩⟩
    apply (NativeShakeProjection.output_coordinate _ _ _ _).mpr
    exact ⟨rfl,le_rfl,by omega⟩

/-- Every completed matching receipt lies in the already-queried-key branch
or the fresh-digest branch, including partial prior receipt reads. -/
theorem split_event {S A : Type} (profile : Digest) (fuel : ℕ) (step : S → OracleMachine.Command S A)
    (packet : Packet S A) (world : World) (accepted : finiteEvent profile fuel step packet world) :
    NativeEarlyReceiptPrefixRisk.event 72 step packet world ∨ NativeFreshReceiptDigest.event profile fuel step packet world := by
  cases chosen : select step packet with
  | none => simp only [finiteEvent,NativeFreshReceiptDigest.run_none profile fuel step packet world chosen,matching] at accepted
  | some view =>
    simp only [finiteEvent,NativeFreshReceiptDigest.run_some profile fuel step packet world view chosen,matching] at accepted
    obtain ⟨count,complete,receipt⟩ := accepted
    cases seen : CausalStreamExposure.seen packet.2 (NativeReceiptPrefixView.key (collected profile fuel view world).1.phase.consumed) with
    | false =>
      right
      simp only [NativeFreshReceiptDigest.event,NativeFreshReceiptDigest.run_some profile fuel step packet world view chosen,
        NativeFreshReceiptDigest.after,complete,seen,true_and]
      exact receipt
    | true =>
      left
      obtain ⟨position,known⟩ := seen_coordinate packet.2 _ seen
      apply NativeEarlyReceiptPrefixRisk.completed_receipt_event 72 step packet world view chosen profile fuel position complete _ known
      have width : CanonicalByteSampler.byteCount NativeFields.goldilocksModulus = 8 := by decide +kernel
      rw [width]
      omega

theorem matching_measurable (result : Result) : MeasurableSet {world | matching result world} := by
  cases result with
  | none => simp [matching]
  | some result =>
    rcases result with ⟨view,state⟩
    by_cases count : 9 ≤ view.field.count.val
    · by_cases complete : state.remaining = 0
      · simp only [matching,count,complete,true_and]
        simpa only [NativeTranscriptProgram.run_receipt] using
          OracleExecutionLaw.event_measurable (OracleProgram.run_replay (NativeTranscriptProgram.receipt state.phase.consumed))
            (fun result => result.1 = view.receipt)
      · simp [matching,complete]
    · simp [matching,count]

theorem finite_measurable {S A : Type} {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (profile : Digest) (fuel : ℕ) (step : S → OracleMachine.Command S A) :
    MeasurableSet {world | finiteEvent profile fuel step (past world).run world} :=
  OracleProgramHistory.event_measurable (NativeFreshReceiptDigest.extended_replay replay profile fuel step)
    (fun packet world => matching packet.1.2 world) (fun packet => matching_measurable packet.1.2)

theorem event_measurable {S A : Type} {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (profile : Digest) (step : S → OracleMachine.Command S A) : MeasurableSet {world | event profile step (past world).run world} := by
  have union : {world | event profile step (past world).run world} = ⋃ fuel : ℕ,
      {world | finiteEvent profile fuel step (past world).run world} := by ext world; simp [event]
  rw [union]
  exact MeasurableSet.iUnion (fun fuel => finite_measurable replay profile fuel step)

def risk {S A : Type} (step : S → OracleMachine.Command S A) (packet : Packet S A) : ENNReal :=
  NativeEarlyReceiptPrefixRisk.risk 72 step packet + NativeFreshReceiptLifetime.risk step packet

theorem risk_selected {S A : Type} (step : S → OracleMachine.Command S A) (packet : Packet S A)
    (view : NativeGoldBatchChallengeLink.View) (chosen : select step packet = some view) :
    risk step packet = ((NativeReceiptPrefixView.guesses 72 packet.2).card : ENNReal)/(2 : ENNReal)^576 + 1/(2 : ENNReal)^512 := by
  rw [risk,NativeEarlyReceiptPrefixRisk.gold_risk step packet view chosen]
  simp only [NativeFreshReceiptLifetime.risk,chosen]

/-- The full early-receipt event, over all collector budgets, has the sum
of the raw-prefix target charge and a single fresh512-bit digest charge. -/
theorem conditional_bound {S A : Type} {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (profile : Digest) (step : S → OracleMachine.Command S A) (world : World) :
    (law[|{other | (past other).run = (past world).run}]) {other | event profile step (past other).run other} ≤
      risk step (past world).run := by
  calc
    _ ≤ (law[|{other | (past other).run = (past world).run}])
      ({other | NativeEarlyReceiptPrefixRisk.event 72 step (past other).run other} ∪
       {other | NativeFreshReceiptLifetime.ever profile step (past other).run other}) := by
      apply measure_mono
      intro other yes
      obtain ⟨fuel,yes⟩ := yes
      rcases split_event profile fuel step (past other).run other yes with old | fresh
      · exact Or.inl old
      · exact Or.inr ⟨fuel,fresh⟩
    _ ≤ _ := (measure_union_le _ _).trans
      (add_le_add (NativeEarlyReceiptPrefixRisk.conditional_event 72 step replay world).le
        (NativeFreshReceiptLifetime.conditional_ever_bound replay profile step world))

theorem averaged_bound {S A : Type} {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (profile : Digest) (step : S → OracleMachine.Command S A) :
    law {world | event profile step (past world).run world} ≤ ∫⁻ world, risk step (past world).run ∂law := by
  rw [OracleHistoryComposition.average_event replay law _ (event_measurable replay profile step)]
  exact lintegral_mono (fun world => conditional_bound replay profile step world)

def totalCharge {P S A : Type} (past : World → Execution P) (initial : P → S)
    (step : S → OracleMachine.Command S A) (world : World) : ENNReal :=
  ∑' fuel : ℕ, risk step (CausalExposureLifetime.history past initial step fuel world).run

theorem lifetime_le {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (profile : Digest) (step : S → OracleMachine.Command S A) (inherited : Set World) :
    law (inherited ∪ {world | ∃ fuel, event profile step (CausalExposureLifetime.history past initial step fuel world).run world}) ≤
      law inherited + ∫⁻ world, totalCharge past initial step world ∂law := by
  have union : {world | ∃ fuel, event profile step (CausalExposureLifetime.history past initial step fuel world).run world} =
      ⋃ fuel : ℕ, {world | event profile step (CausalExposureLifetime.history past initial step fuel world).run world} := by ext world; simp
  rw [union]
  apply (measure_union_le _ _).trans
  apply add_le_add le_rfl
  calc _ ≤ ∑' fuel : ℕ, law {world | event profile step (CausalExposureLifetime.history past initial step fuel world).run world} := measure_iUnion_le _
       _ ≤ ∑' fuel : ℕ, ∫⁻ world, risk step (CausalExposureLifetime.history past initial step fuel world).run ∂law :=
          ENNReal.tsum_le_tsum (fun fuel => averaged_bound (CausalExposureLifetime.history_replay replay initial step fuel) profile step)
       _ = _ := (lintegral_tsum (fun fuel =>
          (OracleExecutionLaw.score_measurable (CausalExposureLifetime.history_replay replay initial step fuel) (risk step)).aemeasurable)).symm
end
end FormalProof4FHE.HasteBoots.NativeEarlyReceiptBound
