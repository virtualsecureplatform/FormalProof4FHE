module

public import FormalProof4FHE.HasteBoots.NativeAtomicIndexLaw
public import FormalProof4FHE.HasteBoots.CachedOracleResponse

@[expose] public section

/-! Exact native atomic-index laws given the whole mixed-oracle past.
Known coordinates are reused even for newly selected transcript inputs.
Fresh-vector agreement is only a derived, explicitly disjoint corner case.
These laws do not establish the lazy interpreter distribution or early-root
Fiat–Shamir security; those remain separate obligations. -/

namespace FormalProof4FHE.HasteBoots.NativePrequeryIndexLaw
open MeasureTheory ProbabilityTheory OracleComp OracleSpec
open InputIndexedOracle (World Byte Input law)

noncomputable section

theorem conditional_draws {A : Type} {past : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable past) (world : World)
    (input : Input) (offset bits count : ℕ) :
    (law[|{other | (past other).run = (past world).run}]).map
      (fun other => NativeIndexRequest.typedDraws bits count
        (InputIndexedOracle.block other input offset (count*8))) =
      (uniformOn (Set.univ : Set (Fin (count*8) → Byte))).map
        (fun raw => NativeIndexRequest.typedDraws bits count
          (CachedOracleResponse.mask (ObservationReplay.footprint (past world).run.2) world
            (CachedOracleResponse.shakeCoordinates input offset (count*8)) raw)) := by
  have equation := congrArg (fun measure => measure.map (NativeIndexRequest.typedDraws bits count))
    (CachedOracleResponse.shake_response replay world input offset (count*8))
  rw [Measure.map_map (Measurable.of_discrete) (InputIndexedOracle.block_measurable _ _ _),
    Measure.map_map (Measurable.of_discrete) (CachedOracleResponse.mask_measurable _ _ _)] at equation
  exact equation

theorem conditional_event {A : Type} {past : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable past) (world : World)
    (input : Input) (offset bits count : ℕ)
    (event : (Fin count → Fin (2^bits)) → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | event (NativeIndexRequest.typedDraws bits count
        (InputIndexedOracle.block other input offset (count*8)))} =
      Pr{let raw ← $ᵗ (Fin (count*8) → Byte)}[event (NativeIndexRequest.typedDraws bits count
        (CachedOracleResponse.mask (ObservationReplay.footprint (past world).run.2) world
          (CachedOracleResponse.shakeCoordinates input offset (count*8)) raw))] := by
  rw [prEvent_eq_evalDist_of_discrete,SampleableType.evalDist_uniformSample]
  have equation := congrArg (fun measure => measure {draw | event draw})
    (conditional_draws replay world input offset bits count)
  have measurableDraw : Measurable (fun other : World => NativeIndexRequest.typedDraws bits count
      (InputIndexedOracle.block other input offset (count*8))) :=
    (Measurable.of_discrete : Measurable (NativeIndexRequest.typedDraws bits count)).comp
      (InputIndexedOracle.block_measurable input offset (count*8))
  rw [Measure.map_apply measurableDraw MeasurableSet.of_discrete,
    Measure.map_apply (Measurable.of_discrete) MeasurableSet.of_discrete] at equation
  exact equation


/-- The fresh-block bound is available only when every requested coordinate
is outside the entire preceding mixed history. -/
theorem fresh_agreement {A Symbol : Type} [DecidableEq Symbol]
    {past : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable past) (world : World)
    (input : Input) (offset bits count : ℕ) (fits : bits ≤ 64)
    (fresh : ∀ index, CachedOracleResponse.shakeCoordinates input offset (count*8) index ∉
      ObservationReplay.footprint (past world).run.2)
    (raw claimed : Fin (2^bits) → Symbol) :
    (law[|{other | (past other).run = (past world).run}])
      {other | ColumnOpening.Agrees raw claimed (NativeIndexRequest.typedDraws bits count
        (InputIndexedOracle.block other input offset (count*8)))} =
      (((2^bits - hammingDist raw claimed : ℕ) : ENNReal) / (2^bits)) ^ count := by
  rw [conditional_event replay world input offset bits count]
  have identity : CachedOracleResponse.mask (ObservationReplay.footprint (past world).run.2)
      world (CachedOracleResponse.shakeCoordinates input offset (count*8)) = id := by
    funext bytes index
    exact ite_eq_right (fresh index)
  simp only [identity,id_eq]
  exact NativeAtomicIndexLaw.agreement_probability bits count fits raw claimed

/-- Full overlap is deterministic, even when the verifier is visiting this
index phase for the first time. -/
theorem repeated_draws {A : Type} {past : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable past) (world : World)
    (input : Input) (offset bits count : ℕ)
    (known : ∀ index, CachedOracleResponse.shakeCoordinates input offset (count*8) index ∈
      ObservationReplay.footprint (past world).run.2) :
    (law[|{other | (past other).run = (past world).run}]).map
      (fun other => NativeIndexRequest.typedDraws bits count
        (InputIndexedOracle.block other input offset (count*8))) =
      Measure.dirac (NativeIndexRequest.typedDraws bits count
        (InputIndexedOracle.block world input offset (count*8))) := by
  rw [conditional_draws replay world input offset bits count]
  have constant : (fun raw => NativeIndexRequest.typedDraws bits count
      (CachedOracleResponse.mask (ObservationReplay.footprint (past world).run.2) world
        (CachedOracleResponse.shakeCoordinates input offset (count*8)) raw)) =
      fun _ : Fin (count*8) → Byte => NativeIndexRequest.typedDraws bits count
        (InputIndexedOracle.block world input offset (count*8)) := by
    funext bytes
    congr 1
    funext index
    exact ite_eq_left (known index)
  simp only [constant,Measure.map_const,measure_univ,one_smul]

/-- Preserve the native ordered list, including duplicate draws; sorting and
transport deduplication do not reduce the sampling quota. -/
theorem ordered_event {A : Type} {past : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable past) (world : World)
    (input : Input) (offset bits count : ℕ) (event : List ℕ → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | event (NativeIndexRequest.ordered (2^bits) count
        (InputIndexedOracle.bytes other input offset (count*8)))} =
      Pr{let raw ← $ᵗ (Fin (count*8) → Byte)}[event (NativeIndexRequest.ordered (2^bits) count
        (List.ofFn (CachedOracleResponse.mask (ObservationReplay.footprint (past world).run.2) world
          (CachedOracleResponse.shakeCoordinates input offset (count*8)) raw)))] := by
  simpa only [InputIndexedOracle.bytes,NativeIndexRequest.ordered_ofFn] using
    conditional_event replay world input offset bits count
      (fun draws => event ((List.ofFn draws).map Fin.val))

/-- Requests and predicates may be selected from the whole prior execution.
The history mass is retained without a success floor or query cutoff. -/
theorem adaptive_event {A : Type} {past : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable past) (world : World)
    (select : A × List NativeTranscript.Observation → Input × ℕ) (bits count : ℕ)
    (event : A × List NativeTranscript.Observation → (Fin count → Fin (2^bits)) → Prop) :
    law {other | (past other).run = (past world).run ∧
      event (past other).run (NativeIndexRequest.typedDraws bits count
        (InputIndexedOracle.block other (select (past other).run).1 (select (past other).run).2 (count*8)))} =
      law {other | (past other).run = (past world).run} *
      Pr{let raw ← $ᵗ (Fin (count*8) → Byte)}[event (past world).run
        (NativeIndexRequest.typedDraws bits count
          (CachedOracleResponse.mask (ObservationReplay.footprint (past world).run.2) world
            (CachedOracleResponse.shakeCoordinates (select (past world).run).1
              (select (past world).run).2 (count*8)) raw))] := by
  have same : {other | (past other).run = (past world).run ∧
      event (past other).run (NativeIndexRequest.typedDraws bits count
        (InputIndexedOracle.block other (select (past other).run).1 (select (past other).run).2 (count*8)))} =
      {other | (past other).run = (past world).run} ∩
      {other | event (past world).run (NativeIndexRequest.typedDraws bits count
        (InputIndexedOracle.block other (select (past world).run).1 (select (past world).run).2 (count*8)))} := by
    ext other
    constructor
    · rintro ⟨equal,yes⟩
      refine ⟨equal, ?_⟩
      change event (past world).run _
      simpa only [equal] using yes
    · rintro ⟨equal,yes⟩
      refine ⟨equal, ?_⟩
      rw [equal]
      exact yes
  rw [same,← cond_mul_eq_inter (ObservationReplay.fiber_measurable replay world) _ law,
    conditional_event replay world (select (past world).run).1 (select (past world).run).2 bits count,
    mul_comm]


/-- The literal framed input of the native atomic index request. -/
def requestInput (transcript : NativeTranscript.Transcript) (label : Input)
    (domain count : NativeUsizeMessage.Usize) : Input :=
  (NativeTranscript.absorb (NativeIndexRequest.prepare transcript domain) 2 label
    (TranscriptFrame.littleEndian 8 (count.val*8))).input

/-- Decode a complete byte block and retain the full native response and log. -/
def outcome (transcript : NativeTranscript.Transcript) (label : Input)
    (domain count : NativeUsizeMessage.Usize) (raw : Fin (count.val*8) → Byte) :
    Option NativeIndexRequest.Result × List NativeTranscript.Observation :=
  let pending := NativeTranscript.absorb (NativeIndexRequest.prepare transcript domain) 2 label
    (TranscriptFrame.littleEndian 8 (count.val*8))
  let bytes := List.ofFn raw
  let draws := NativeIndexRequest.ordered domain.val count.val bytes
  (some ⟨draws,NativeIndexRequest.distinct draws,NativeTranscript.absorb pending 3 label bytes⟩,
    [.start pending.input,.output pending.input 0 bytes])

/-- Exact checked native execution, including its new transcript, sorted
transport indices and both ordered observations. -/
theorem request_run (world : World) (transcript : NativeTranscript.Transcript) (label : Input)
    (domain count : NativeUsizeMessage.Usize) (valid : NativeIndexRequest.check domain count = true) :
    (OracleProgram.run (NativeIndexRequest.request transcript label domain count) world).run =
      outcome transcript label domain count
        (InputIndexedOracle.block world (requestInput transcript label domain count) 0 (count.val*8)) := by
  simp only [NativeIndexRequest.request,valid,↓reduceIte]
  rfl

/-- The actual native index request has the cache-masked finite-byte law.
This statement transports its complete result and observations, not just a
fresh surrogate vector. Partial, cloned and off-path prequeries are retained. -/
theorem request_event {A : Type} {past : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable past) (world : World)
    (transcript : NativeTranscript.Transcript) (label : Input)
    (domain count : NativeUsizeMessage.Usize) (valid : NativeIndexRequest.check domain count = true)
    (event : Option NativeIndexRequest.Result × List NativeTranscript.Observation → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | event (OracleProgram.run (NativeIndexRequest.request transcript label domain count) other).run} =
      Pr{let raw ← $ᵗ (Fin (count.val*8) → Byte)}[event (outcome transcript label domain count
        (CachedOracleResponse.mask (ObservationReplay.footprint (past world).run.2) world
          (CachedOracleResponse.shakeCoordinates (requestInput transcript label domain count) 0 (count.val*8)) raw))] := by
  rw [prEvent_eq_evalDist_of_discrete,SampleableType.evalDist_uniformSample]
  have equation := congrArg (fun measure => measure {raw | event (outcome transcript label domain count raw)})
    (CachedOracleResponse.shake_response replay world (requestInput transcript label domain count) 0 (count.val*8))
  rw [Measure.map_apply (InputIndexedOracle.block_measurable _ _ _) MeasurableSet.of_discrete,
    Measure.map_apply (CachedOracleResponse.mask_measurable _ _ _) MeasurableSet.of_discrete] at equation
  simpa only [request_run _ transcript label domain count valid,Set.preimage_ofPred_eq] using equation


/-- Parameters supplied to the actual native request after observing the past. -/
structure Request where
  transcript : NativeTranscript.Transcript
  label : Input
  domain : NativeUsizeMessage.Usize
  count : NativeUsizeMessage.Usize

def Request.program (request : Request) : OracleProgram.Program (Option NativeIndexRequest.Result) :=
  NativeIndexRequest.request request.transcript request.label request.domain request.count

/-- Whole native index phases may be chosen adaptively, including their quota,
without dropping the mass of the selecting history or assuming a fresh block. -/
theorem adaptive_request_event {A : Type} {past : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable past) (world : World)
    (select : A × List NativeTranscript.Observation → Request)
    (valid : NativeIndexRequest.check (select (past world).run).domain (select (past world).run).count = true)
    (event : A × List NativeTranscript.Observation →
      Option NativeIndexRequest.Result × List NativeTranscript.Observation → Prop) :
    law {other | (past other).run = (past world).run ∧
      event (past other).run (OracleProgram.run (select (past other).run).program other).run} =
      law {other | (past other).run = (past world).run} *
      Pr{let raw ← $ᵗ (Fin ((select (past world).run).count.val*8) → Byte)}[
        event (past world).run (outcome (select (past world).run).transcript (select (past world).run).label
          (select (past world).run).domain (select (past world).run).count
          (CachedOracleResponse.mask (ObservationReplay.footprint (past world).run.2) world
            (CachedOracleResponse.shakeCoordinates
              (requestInput (select (past world).run).transcript (select (past world).run).label
                (select (past world).run).domain (select (past world).run).count)
              0 ((select (past world).run).count.val*8)) raw))] := by
  have same : {other | (past other).run = (past world).run ∧
      event (past other).run (OracleProgram.run (select (past other).run).program other).run} =
      {other | (past other).run = (past world).run} ∩
      {other | event (past world).run (OracleProgram.run (select (past world).run).program other).run} := by
    ext other
    constructor
    · rintro ⟨equal,yes⟩
      refine ⟨equal, ?_⟩
      change event (past world).run _
      simpa only [equal] using yes
    · rintro ⟨equal,yes⟩
      refine ⟨equal, ?_⟩
      rw [equal]
      exact yes
  rw [same,← cond_mul_eq_inter (ObservationReplay.fiber_measurable replay world) _ law]
  rw [Request.program,request_event replay world _ _ _ _ valid,mul_comm]

end
end FormalProof4FHE.HasteBoots.NativePrequeryIndexLaw
