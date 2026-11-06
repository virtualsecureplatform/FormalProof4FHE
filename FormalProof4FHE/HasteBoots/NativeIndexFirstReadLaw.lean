module
public import FormalProof4FHE.HasteBoots.CausalStreamExposure
public import FormalProof4FHE.HasteBoots.NativePrequeryIndexLaw
public import FormalProof4FHE.HasteBoots.NativeGoldPcsDraws
@[expose] public section

/-! Actual checked atomic-index requests at causal first stream exposure.
Ordered vectors include repetitions; transport sorting/deduplication does not
change the quota. Any earlier partial read excludes first-read eligibility.
This is a local posterior law, not global lineage/coverage or physical work. -/
namespace FormalProof4FHE.HasteBoots.NativeIndexFirstReadLaw
open InputIndexedOracle (Input World law)
open NativeTranscript (Transcript)
open NativeUsizeMessage (Usize)
open OracleProgram (run)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section

theorem typed_ofFn (bits count : ℕ) (draw : Fin count → Fin (2^bits)) :
    NativeGoldPcsDraws.typed bits count ((List.ofFn draw).map Fin.val) = some draw := by
  have bounded : ((List.ofFn draw).map Fin.val).all (fun value => decide (value < 2^bits)) = true := by
    apply List.all_eq_true.mpr
    intro value member
    obtain ⟨entry,inList,rfl⟩ := List.mem_map.mp member
    exact decide_eq_true entry.isLt
  unfold NativeGoldPcsDraws.typed
  rw [dite_eq_left (by simp),dite_eq_left bounded]
  congr 1
  funext index
  apply Fin.ext
  simp only [List.getElem_map,List.getElem_ofFn]

def values (bits : ℕ) (transcript : Transcript) (label : Input) (domain count : Usize) (world : World) :=
  ((run (NativeIndexRequest.request transcript label domain count) world).run.1).bind
    (fun result => NativeGoldPcsDraws.typed bits count.val result.draws)

/-- Typed decoding is computed from the exact request result, retaining
all original ordered words, not inferred from the distinct worker list. -/
theorem values_run (bits : ℕ) (transcript : Transcript) (label : Input) (domain count : Usize)
    (valid : NativeIndexRequest.check domain count = true) (power : domain.val = 2^bits) (world : World) :
    values bits transcript label domain count world = some (NativeIndexRequest.typedDraws bits count.val
      (InputIndexedOracle.block world (NativePrequeryIndexLaw.requestInput transcript label domain count) 0 (count.val*8))) := by
  unfold values
  rw [NativePrequeryIndexLaw.request_run world transcript label domain count valid]
  simp only [NativePrequeryIndexLaw.outcome,Option.bind_some]
  rw [power,NativeIndexRequest.ordered_ofFn,typed_ofFn]

/-- Invalid request dimensions reject without a draw, including after any
prior cache history. The native rejection/log semantics are unchanged. -/
theorem invalid_values (bits : ℕ) (transcript : Transcript) (label : Input) (domain count : Usize)
    (invalid : NativeIndexRequest.check domain count ≠ true) (world : World) :
    values bits transcript label domain count world = none := by
  unfold values
  rw [NativeIndexRequest.invalid_request transcript label domain count world invalid]
  rfl

/-- Complete native result/log laws at first exposure reuse the original
framing and raw processing. No verifier-side certificate or draw is added. -/
theorem request_event {S A : Type} (step : S → OracleMachine.Command S A)
    {past : World → NativeTranscript.Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) (world : World)
    (transcript : Transcript) (label : Input) (domain count : Usize)
    (valid : NativeIndexRequest.check domain count = true)
    (selected : CausalStreamExposure.firstRead step (past world).run = some (NativePrequeryIndexLaw.requestInput transcript label domain count))
    (event : Option NativeIndexRequest.Result × List NativeTranscript.Observation → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | event (run (NativeIndexRequest.request transcript label domain count) other).run} =
      Pr{let raw ← $ᵗ (Fin (count.val*8) → InputIndexedOracle.Byte)}[event (NativePrequeryIndexLaw.outcome transcript label domain count raw)] := by
  rw [NativePrequeryIndexLaw.request_event replay world transcript label domain count valid event]
  have fresh := CausalStreamExposure.firstRead_fresh step (past world).run _ selected world 0
  have identity : CachedOracleResponse.mask (ObservationReplay.footprint (past world).run.2) world
      (CachedOracleResponse.shakeCoordinates (NativePrequeryIndexLaw.requestInput transcript label domain count) 0 (count.val*8)) = id := by
    funext raw index
    unfold CachedOracleResponse.mask
    apply ite_eq_right
    have absent := fresh index.val (by omega)
    unfold NativeShakeKernel.observed at absent
    split at absent
    · contradiction
    · simpa only [CachedOracleResponse.shakeCoordinates,Nat.zero_add] using (by assumption : Sum.inl (NativePrequeryIndexLaw.requestInput transcript label domain count,index.val) ∉ ObservationReplay.footprint (past world).run.2)
  simp only [identity,id_eq]

/-- The full ordered with-replacement draw vector is jointly uniform at
the actual next first positive read, at any byte offset. -/
theorem conditional_uniform {S A : Type} (step : S → OracleMachine.Command S A)
    {past : World → NativeTranscript.Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) (world : World)
    (bits : ℕ) (transcript : Transcript) (label : Input) (domain count : Usize)
    (valid : NativeIndexRequest.check domain count = true) (power : domain.val = 2^bits)
    (selected : CausalStreamExposure.firstRead step (past world).run = some (NativePrequeryIndexLaw.requestInput transcript label domain count))
    (event : (Fin count.val → Fin (2^bits)) → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | (values bits transcript label domain count other).elim False event} =
        Pr{let draw ← $ᵗ (Fin count.val → Fin (2^bits))}[event draw] := by
  have fits : bits ≤ 64 := by
    have bound : 2^bits < 2^64 := power ▸ domain.isLt
    have small := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp bound
    omega
  have actual := request_event step replay world transcript label domain count valid selected
    (fun result => (result.1.bind (fun sample => NativeGoldPcsDraws.typed bits count.val sample.draws)).elim False event)
  change _ = _ at actual
  have same : (fun raw => ((NativePrequeryIndexLaw.outcome transcript label domain count raw).1.bind
      (fun sample => NativeGoldPcsDraws.typed bits count.val sample.draws)).elim False event) =
      fun raw => event (NativeIndexRequest.typedDraws bits count.val raw) := by
    funext raw
    simp only [NativePrequeryIndexLaw.outcome,Option.bind_some,power,NativeIndexRequest.ordered_ofFn,typed_ofFn,Option.elim_some]
  rw [same] at actual
  exact actual.trans (NativeAtomicIndexLaw.uniform_draws bits count.val fits event)

/-- All checks share this one vector. A single disagreeing response gives
the loss; there is no factor for the number of groups or lanes. -/
theorem shared_bound {S A Test Symbol : Type} [DecidableEq Symbol] (step : S → OracleMachine.Command S A)
    {past : World → NativeTranscript.Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) (world : World)
    (bits : ℕ) (transcript : Transcript) (label : Input) (domain count : Usize)
    (valid : NativeIndexRequest.check domain count = true) (power : domain.val = 2^bits)
    (selected : CausalStreamExposure.firstRead step (past world).run = some (NativePrequeryIndexLaw.requestInput transcript label domain count))
    (raw claimed : Test → Fin (2^bits) → Symbol) (distance : ℕ)
    (witness : ∃ test, distance ≤ hammingDist (raw test) (claimed test)) :
    (law[|{other | (past other).run = (past world).run}])
      {other | (values bits transcript label domain count other).elim False (fun draw => ∀ test, ColumnOpening.Agrees (raw test) (claimed test) draw)} ≤
        ColumnOpening.missBound (Fin (2^bits)) count.val distance := by
  rw [conditional_uniform step replay world bits transcript label domain count valid power selected]
  exact ColumnOpening.shared_bound raw claimed count.val distance witness
end
end FormalProof4FHE.HasteBoots.NativeIndexFirstReadLaw
