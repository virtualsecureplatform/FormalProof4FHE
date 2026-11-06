module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchChallengeLink
public import FormalProof4FHE.HasteBoots.NativeReceiptPrefixView
public import FormalProof4FHE.HasteBoots.NativeFieldConsumedPrefix
@[expose] public section

/-! Early column queries whose recovered field stream is wholly unseen.
Earlier receipt keys are guesses of that stream's raw consumed-byte prefix,
even when only one receipt coordinate was read. Requests and target sets are
selected from the actual causal history. Fresh receipt-digest guesses and
physical attacker-work coupling remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.NativeEarlyReceiptPrefixRisk
open InputIndexedOracle (Input Byte World law)
open NativeTranscript (Execution)
open NativeIndexExposureRisk (Packet)
open NativeGoldBatchChallengeLink (View)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
open scoped Classical
noncomputable section

def fieldInput (view : View) : Input := TranscriptFrame.encodeMany view.fieldFrames

def select {S A : Type} (step : S → OracleMachine.Command S A) (packet : Packet S A) : Option View := do
  let input ← CausalStreamExposure.firstRead step packet
  let view ← NativeGoldBatchChallengeLink.parse input
  if view.column.index.label = NativeGoldBatchColumns.label ∧ 0 < view.column.index.count.val ∧
      CausalStreamExposure.seen packet.2 (fieldInput view) = false then some view else none

theorem selected_link {S A : Type} (step : S → OracleMachine.Command S A) (packet : Packet S A)
    (view : View) (selected : select step packet = some view) :
    ∃ input, CausalStreamExposure.firstRead step packet = some input ∧
      NativeGoldBatchChallengeLink.parse input = some view := by
  unfold select at selected
  obtain ⟨input,first,chosen⟩ := Option.bind_eq_some_iff.mp selected
  obtain ⟨decoded,parsed,chosen⟩ := Option.bind_eq_some_iff.mp chosen
  split at chosen
  next valid =>
    have equal := Option.some.inj chosen
    subst view
    exact ⟨input,first,parsed⟩
  next => contradiction

/-- The recovered field input is a complete frame stream, whereas receipt
keys start outside the frame-kind range. This separation holds for every body. -/
theorem selected_not_receipt {S A : Type} (step : S → OracleMachine.Command S A) (packet : Packet S A)
    (view : View) (selected : select step packet = some view) (consumed : Input) :
    fieldInput view ≠ NativeReceiptPrefixView.key consumed := by
  obtain ⟨input,_,parsed⟩ := selected_link step packet view selected
  obtain ⟨column,_,read⟩ := Option.bind_eq_some_iff.mp parsed
  have field := (NativeGoldBatchChallengeLink.readColumn_sound column view read).2.2.1
  intro equal
  change NativeGoldBatchFieldInputView.parse (fieldInput view) = some view.field at field
  rw [equal] at field
  unfold NativeGoldBatchFieldInputView.parse at field
  rw [show NativeReceiptPrefixView.key consumed = NativeTranscript.utf8 "HasteBoots consumed field bytes v1" ++ consumed from rfl,
    NativeTranscript.receipt_decode_rejected] at field
  cases field

theorem selected_unseen {S A : Type} (step : S → OracleMachine.Command S A) (packet : Packet S A)
    (view : View) (selected : select step packet = some view) : CausalStreamExposure.seen packet.2 (fieldInput view) = false := by
  unfold select at selected
  obtain ⟨input,_,chosen⟩ := Option.bind_eq_some_iff.mp selected
  obtain ⟨decoded,_,chosen⟩ := Option.bind_eq_some_iff.mp chosen
  split at chosen
  next valid =>
    have equal := Option.some.inj chosen
    subst view
    exact valid.2.2
  next => contradiction

/-- Generic fresh-byte target law; no512-bit denominator is used for a
partially known block. Here freshness is supplied by the selector's unseen test. -/
theorem fresh_targets {P : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (world : World) (input : Input) (count : ℕ) (targets : Finset (Fin count → Byte))
    (unseen : CausalStreamExposure.seen (past world).run.2 input = false) :
    (law[|{other | (past other).run = (past world).run}]) {other | InputIndexedOracle.block other input 0 count ∈ targets} =
      (targets.card : ENNReal)/(256 : ENNReal)^count := by
  have response : (law[|{other | (past other).run = (past world).run}]).map
      (fun other => InputIndexedOracle.block other input 0 count) = uniformOn (Set.univ : Set (Fin count → Byte)) := by
    rw [ObservationReplay.fiber_eq_assignment replay world]
    exact CachedOracleResponse.fresh_response _ _ (CachedOracleResponse.shakeCoordinates input 0 count)
      (CachedOracleResponse.shake_distinct input 0 count)
      (by intro position; simpa only [CachedOracleResponse.shakeCoordinates,Nat.zero_add] using
        CausalStreamExposure.unseen_coordinates _ input unseen position.val)
  have same := congrArg (fun measure : Measure (Fin count → Byte) => measure (targets : Set (Fin count → Byte))) response
  rw [Measure.map_apply (InputIndexedOracle.block_measurable input 0 count) targets.measurableSet] at same
  rw [show (Set.univ : Set (Fin count → Byte)) = (↑(Finset.univ : Finset (Fin count → Byte)) : Set (Fin count → Byte)) by simp,
    uniformOn_apply_finset] at same
  simpa only [Finset.univ_inter,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,
    Set.preimage,Finset.mem_coe] using same

def event {S A : Type} (count : ℕ) (step : S → OracleMachine.Command S A) (packet : Packet S A) (world : World) : Prop :=
  match select step packet with
  | none => False
  | some view => InputIndexedOracle.block world (fieldInput view) 0 count ∈ NativeReceiptPrefixView.guesses count packet.2

def risk {S A : Type} (count : ℕ) (step : S → OracleMachine.Command S A) (packet : Packet S A) : ENNReal :=
  match select step packet with
  | none => 0
  | some _ => ((NativeReceiptPrefixView.guesses count packet.2).card : ENNReal)/(256 : ENNReal)^count

/-- A prior partial receipt observation enters the actual selected event
whenever its key names the raw field prefix. No full receipt read is needed. -/
theorem known_receipt_event {S A : Type} (count : ℕ) (step : S → OracleMachine.Command S A)
    (packet : Packet S A) (world : World) (view : View) (selected : select step packet = some view)
    (tail : Input) (position : ℕ)
    (known : (.inl (NativeReceiptPrefixView.key
      (List.ofFn (InputIndexedOracle.block world (fieldInput view) 0 count) ++ tail),position) : InputIndexedOracle.Coordinate) ∈
        ObservationReplay.footprint packet.2) : event count step packet world := by
  simp only [event,selected]
  exact NativeReceiptPrefixView.known_prefix count _ tail position packet.2 known

/-- Coverage for the actual completed native collector under the recovered
phase. The key's raw prefix is derived from completion, not supplied as a guess. -/
theorem completed_receipt_event {S A : Type} (count : ℕ) (step : S → OracleMachine.Command S A)
    (packet : Packet S A) (world : World) (view : View) (selected : select step packet = some view)
    (profile : NativeRootMessage.Digest) (fuel position : ℕ)
    (complete : (NativeFieldVector.execute NativeFields.goldilocksModulus fuel
      (NativeFieldVector.initial (view.field.phase profile) view.field.count.val) world).1.remaining = 0)
    (bounded : count ≤ CanonicalByteSampler.byteCount NativeFields.goldilocksModulus * view.field.count.val)
    (known : (.inl (NativeReceiptPrefixView.key (NativeFieldVector.execute NativeFields.goldilocksModulus fuel
      (NativeFieldVector.initial (view.field.phase profile) view.field.count.val) world).1.phase.consumed,position) : InputIndexedOracle.Coordinate) ∈
        ObservationReplay.footprint packet.2) : event count step packet world := by
  obtain ⟨input,_,parsed⟩ := selected_link step packet view selected
  have linked := NativeGoldBatchChallengeLink.parse_sound input view parsed profile
  have coherent : NativeTranscript.Coherent world (view.field.phase profile) := by
    unfold NativeGoldBatchFieldInputView.View.phase NativePrimeRequest.phase
    exact NativeTranscript.begin_coherent world _ _ _ _
  obtain ⟨tail,prefixBytes⟩ := NativeFieldConsumedPrefix.completed_prefix NativeFields.goldilocksModulus fuel view.field.count.val
    (view.field.phase profile) world coherent complete count bounded
  rw [linked.2.2.1] at prefixBytes
  rw [prefixBytes] at known
  exact known_receipt_event count step packet world view selected tail position known

theorem conditional_event {S A : Type} (count : ℕ) (step : S → OracleMachine.Command S A)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) (world : World) :
    (law[|{other | (past other).run = (past world).run}]) {other | event count step (past other).run other} =
      risk count step (past world).run := by
  calc
    _ = (law[|{other | (past other).run = (past world).run}]) {other | event count step (past world).run other} := by
      apply NativeShakeProjection.conditional_event_congr replay world
      intro other same
      rw [same]
    _ = _ := by
      cases chosen : select step (past world).run with
      | none => simp [event,risk,chosen]
      | some view =>
        simp only [event,risk,chosen]
        exact fresh_targets replay world _ count _ (selected_unseen step (past world).run view chosen)

theorem event_measurable {S A : Type} (count : ℕ) (step : S → OracleMachine.Command S A)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) :
    MeasurableSet {world | event count step (past world).run world} := by
  let := OracleHistoryCharge.histories_countable replay
  have fixed (packet : Packet S A) : MeasurableSet {world | event count step packet world} := by
    cases chosen : select step packet with
    | none => simp [event,chosen]
    | some view =>
      simpa only [event,chosen,Set.preimage,Finset.mem_coe] using
        (InputIndexedOracle.block_measurable (fieldInput view) 0 count) (NativeReceiptPrefixView.guesses count packet.2).measurableSet
  have union : {world | event count step (past world).run world} = ⋃ packet : OracleHistoryCharge.Histories past,
      OracleHistoryCharge.fiber past packet ∩ {world | event count step packet.val world} := by
    ext world
    constructor
    · intro yes
      exact Set.mem_iUnion.mpr ⟨⟨(past world).run,⟨world,rfl⟩⟩,rfl,yes⟩
    · intro yes
      obtain ⟨packet,same,yes⟩ := Set.mem_iUnion.mp yes
      change (past world).run = packet.val at same
      change event count step (past world).run world
      rw [same]
      exact yes
  rw [union]
  exact MeasurableSet.iUnion (fun packet => (OracleHistoryCharge.fiber_measurable replay packet).inter (fixed packet.val))

theorem averaged_event {S A : Type} (count : ℕ) (step : S → OracleMachine.Command S A)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) :
    law {world | event count step (past world).run world} = ∫⁻ world, risk count step (past world).run ∂law := by
  rw [OracleHistoryComposition.average_event replay law _ (event_measurable count step replay)]
  exact lintegral_congr (fun world => conditional_event count step replay world)

def totalCharge {P S A : Type} (count : ℕ) (past : World → Execution P) (initial : P → S)
    (step : S → OracleMachine.Command S A) (world : World) : ENNReal :=
  ∑' fuel : ℕ, risk count step (CausalExposureLifetime.history past initial step fuel world).run

theorem lifetime_le {P S A : Type} (count : ℕ) {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (step : S → OracleMachine.Command S A) (inherited : Set World) :
    law (inherited ∪ {world | ∃ fuel, event count step (CausalExposureLifetime.history past initial step fuel world).run world}) ≤
      law inherited + ∫⁻ world, totalCharge count past initial step world ∂law := by
  have union : {world | ∃ fuel, event count step (CausalExposureLifetime.history past initial step fuel world).run world} =
      ⋃ fuel : ℕ, {world | event count step (CausalExposureLifetime.history past initial step fuel world).run world} := by ext world; simp
  rw [union]
  apply (measure_union_le _ _).trans
  apply add_le_add le_rfl
  calc _ ≤ ∑' fuel : ℕ, law {world | event count step (CausalExposureLifetime.history past initial step fuel world).run world} := measure_iUnion_le _
       _ = ∑' fuel : ℕ, ∫⁻ world, risk count step (CausalExposureLifetime.history past initial step fuel world).run ∂law := by
         congr 1
         funext fuel
         exact averaged_event count step (CausalExposureLifetime.history_replay replay initial step fuel)
       _ = _ := (lintegral_tsum (fun fuel =>
          (OracleExecutionLaw.score_measurable (CausalExposureLifetime.history_replay replay initial step fuel) (risk count step)).aemeasurable)).symm

/-- The target profile's72 raw bytes give a576-bit prefix-guess denominator.
This is a probability charge, not a physical-work security conclusion. -/
theorem gold_risk {S A : Type} (step : S → OracleMachine.Command S A) (packet : Packet S A) (view : View)
    (selected : select step packet = some view) : risk 72 step packet =
      ((NativeReceiptPrefixView.guesses 72 packet.2).card : ENNReal)/(2 : ENNReal)^576 := by
  simp only [risk,selected]
  have denominator : (256 : ENNReal)^72 = (2 : ENNReal)^576 := by
    calc _ = ((2 : ENNReal)^8)^72 := congrArg (fun value : ENNReal => value^72) (by norm_num)
         _ = (2 : ENNReal)^(8*72) := (pow_mul _ _ _).symm
         _ = _ := congrArg (fun exponent : ℕ => (2 : ENNReal)^exponent) (by decide)
  rw [denominator]
end
end FormalProof4FHE.HasteBoots.NativeEarlyReceiptPrefixRisk
