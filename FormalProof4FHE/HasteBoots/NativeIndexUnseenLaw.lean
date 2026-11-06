module
public import FormalProof4FHE.HasteBoots.NativeIndexFirstReadLaw
@[expose] public section

/-! Native ordered-index laws on arbitrary retained replayable histories.
These lemmas consume absence of the complete input in the actual log; the
field/column composition derives that absence from the pending first read. -/
namespace FormalProof4FHE.HasteBoots.NativeIndexUnseenLaw
open InputIndexedOracle (Input World law)
open NativeTranscript (Transcript)
open NativeUsizeMessage (Usize)
open NativeIndexFirstReadLaw (values typed_ofFn)
open OracleProgram (run)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section

theorem request_event {A : Type}
    {past : World → NativeTranscript.Execution A} (replay : ObservationReplay.Replayable past) (world : World)
    (transcript : Transcript) (label : Input) (domain count : Usize)
    (valid : NativeIndexRequest.check domain count = true)
    (unseen : CausalStreamExposure.seen (past world).run.2 (NativePrequeryIndexLaw.requestInput transcript label domain count) = false)
    (event : Option NativeIndexRequest.Result × List NativeTranscript.Observation → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | event (run (NativeIndexRequest.request transcript label domain count) other).run} =
      Pr{let raw ← $ᵗ (Fin (count.val*8) → InputIndexedOracle.Byte)}[event (NativePrequeryIndexLaw.outcome transcript label domain count raw)] := by
  rw [NativePrequeryIndexLaw.request_event replay world transcript label domain count valid event]
  have fresh := CausalStreamExposure.unseen_coordinates _ _ unseen
  have identity : CachedOracleResponse.mask (ObservationReplay.footprint (past world).run.2) world
      (CachedOracleResponse.shakeCoordinates (NativePrequeryIndexLaw.requestInput transcript label domain count) 0 (count.val*8)) = id := by
    funext raw index
    unfold CachedOracleResponse.mask
    apply ite_eq_right
    simpa only [CachedOracleResponse.shakeCoordinates,Nat.zero_add] using fresh index.val
  simp only [identity,id_eq]

theorem conditional_uniform {A : Type}
    {past : World → NativeTranscript.Execution A} (replay : ObservationReplay.Replayable past) (world : World)
    (bits : ℕ) (transcript : Transcript) (label : Input) (domain count : Usize)
    (valid : NativeIndexRequest.check domain count = true) (power : domain.val = 2^bits)
    (unseen : CausalStreamExposure.seen (past world).run.2 (NativePrequeryIndexLaw.requestInput transcript label domain count) = false)
    (event : (Fin count.val → Fin (2^bits)) → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | (values bits transcript label domain count other).elim False event} =
        Pr{let draw ← $ᵗ (Fin count.val → Fin (2^bits))}[event draw] := by
  have fits : bits ≤ 64 := by
    have bound : 2^bits < 2^64 := power ▸ domain.isLt
    have small := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp bound
    omega
  have actual := request_event replay world transcript label domain count valid unseen
    (fun result => (result.1.bind (fun sample => NativeGoldPcsDraws.typed bits count.val sample.draws)).elim False event)
  change _ = _ at actual
  have same : (fun raw => ((NativePrequeryIndexLaw.outcome transcript label domain count raw).1.bind
      (fun sample => NativeGoldPcsDraws.typed bits count.val sample.draws)).elim False event) =
      fun raw => event (NativeIndexRequest.typedDraws bits count.val raw) := by
    funext raw
    simp only [NativePrequeryIndexLaw.outcome,Option.bind_some,power,NativeIndexRequest.ordered_ofFn,typed_ofFn,Option.elim_some]
  rw [same] at actual
  exact actual.trans (NativeAtomicIndexLaw.uniform_draws bits count.val fits event)

end
end FormalProof4FHE.HasteBoots.NativeIndexUnseenLaw
