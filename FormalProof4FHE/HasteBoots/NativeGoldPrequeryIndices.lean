module

public import FormalProof4FHE.HasteBoots.NativePrequeryIndexLaw
public import FormalProof4FHE.HasteBoots.NativeGoldPcsDraws

@[expose] public section

/-! The cache-aware native index law reaches the checked Goldilocks draw
adapter without changing the original quota or deduplicating samples. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldPrequeryIndices

open InputIndexedOracle (Byte Input World law)
open MeasureTheory ProbabilityTheory OracleSpec OracleComp

/-- The checked PCS adapter is a left inverse on literal typed draw vectors. -/
theorem typed_ofFn (height count : ℕ) (draws : Fin count → Fin (2^height)) :
    NativeGoldPcsDraws.typed height count ((List.ofFn draws).map Fin.val) = some draws := by
  obtain ⟨other,success⟩ := NativeGoldPcsDraws.typed_complete height count
    ((List.ofFn draws).map Fin.val) (by simp) (by
      intro value member
      obtain ⟨draw,_,rfl⟩ := List.mem_map.mp member
      exact draw.isLt)
  have values := NativeGoldPcsDraws.typed_values height count _ other success
  have same : other = draws := by
    funext index
    apply Fin.ext
    have atIndex := congrArg (fun values : List ℕ => values[index.val]?) values
    simpa using atIndex
  simpa only [same] using success

/-- Native byte decoding and checked PCS interpretation preserve every
with-replacement draw, including duplicate indices. -/
theorem typed_ordered (bits count : ℕ) (raw : Fin (count*8) → Byte) :
    NativeGoldPcsDraws.typed bits count
      (NativeIndexRequest.ordered (2^bits) count (List.ofFn raw)) =
      some (NativeIndexRequest.typedDraws bits count raw) := by
  rw [NativeIndexRequest.ordered_ofFn,typed_ofFn]

noncomputable section

/-- Full-history conditional law of the checked adapter's actual output.
Partial prequeries remain masked; successful typed parsing adds no freshness. -/
theorem checked_event {A : Type} {past : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable past) (world : World)
    (input : Input) (offset bits count : ℕ)
    (event : Option (Fin count → Fin (2^bits)) → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | event (NativeGoldPcsDraws.typed bits count
        (NativeIndexRequest.ordered (2^bits) count (InputIndexedOracle.bytes other input offset (count*8))))} =
      Pr{let raw ← $ᵗ (Fin (count*8) → Byte)}[event (some (NativeIndexRequest.typedDraws bits count
        (CachedOracleResponse.mask (ObservationReplay.footprint (past world).run.2) world
          (CachedOracleResponse.shakeCoordinates input offset (count*8)) raw)))] := by
  simpa only [InputIndexedOracle.bytes,typed_ordered] using
    NativePrequeryIndexLaw.conditional_event replay world input offset bits count (fun draws => event (some draws))

end
end FormalProof4FHE.HasteBoots.NativeGoldPrequeryIndices
