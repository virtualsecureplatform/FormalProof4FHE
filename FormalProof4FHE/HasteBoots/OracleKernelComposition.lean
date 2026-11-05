module

public import FormalProof4FHE.HasteBoots.OracleHistorySnapshot
public import FormalProof4FHE.HasteBoots.JointHashKernel

@[expose] public section

/-! Exact continuation transfer for physical SHAKE reads and SHA-512 queries.
The continuation hypothesis is conditional on the refined full history; no
freshness, disjointness, success floor or query bound is assumed. -/
namespace FormalProof4FHE.HasteBoots.OracleKernelComposition
open MeasureTheory ProbabilityTheory OracleSpec OracleComp
open InputIndexedOracle (World Input Byte law)
open NativeShakeCache (Cache)

noncomputable section

theorem read_score [MeasurableSpace (Input × Cache)] [DiscreteMeasurableSpace (Input × Cache)] {A : Type} {past : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable past) (world : World) (input : Input) (offset count : ℕ)
    (score : Input × Cache → ENNReal) :
    (∫⁻ other, score (NativeShakeReadLaw.outcome (NativeShakeKernel.observed (past world).run.2 world)
      input offset (InputIndexedOracle.block other input offset count))
      ∂law[|{other | (past other).run = (past world).run}]) =
      ∫⁻ result, score result ∂𝒟[NativeShakeReadLaw.sample input offset count
        (NativeShakeKernel.observed (past world).run.2 world)] := by
  rw [(NativeShakeReadLaw.sample_dist (NativeShakeKernel.observed (past world).run.2 world)
    input offset count).evalDist_eq,evalDist_map_of_discrete,SampleableType.evalDist_uniformSample,
    lintegral_map (Measurable.of_discrete) (Measurable.of_discrete)]
  simp only [NativeShakeReadLaw.eager_observed]
  have response := congrArg (fun measure => ∫⁻ raw, score
      (NativeShakeReadLaw.outcome (NativeShakeKernel.observed (past world).run.2 world) input offset raw) ∂measure)
    (CachedOracleResponse.shake_response replay world input offset count)
  rw [lintegral_map (Measurable.of_discrete) (InputIndexedOracle.block_measurable _ _ _),
    lintegral_map (Measurable.of_discrete) (CachedOracleResponse.mask_measurable _ _ _)] at response
  exact response

theorem read_transfer {A B : Type} {past : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable past) (world : World) (input : Input) (offset count : ℕ)
    (bad : Set World) (measurable : MeasurableSet bad)
    (next : Input × Cache → ProbComp B) (event : B → Prop)
    (tailLaw : ∀ current, (past current).run = (past world).run →
      (law[|{other | (OracleHistorySnapshot.read past input offset count other).run =
        (OracleHistorySnapshot.read past input offset count current).run}]) bad =
      Pr{let result ← next (NativeShakeReadLaw.outcome (NativeShakeKernel.observed (past world).run.2 world)
        input offset (InputIndexedOracle.block current input offset count))}[event result]) :
    (law[|{other | (past other).run = (past world).run}]) bad =
      Pr{let result ← (do
        let first ← NativeShakeReadLaw.sample input offset count (NativeShakeKernel.observed (past world).run.2 world)
        next first)}[event result] := by
  let : MeasurableSpace (Input × Cache) := ⊤
  rw [OracleHistorySnapshot.read_average replay world input offset count bad measurable]
  calc _ = ∫⁻ current, Pr{let result ← next (NativeShakeReadLaw.outcome (NativeShakeKernel.observed (past world).run.2 world)
            input offset (InputIndexedOracle.block current input offset count))}[event result]
          ∂law[|{other | (past other).run = (past world).run}] := by
        apply lintegral_congr_ae
        filter_upwards [ae_cond_mem (μ := law) (ObservationReplay.fiber_measurable replay world)] with current same
        exact tailLaw current same
       _ = _ := by
        rw [read_score replay world input offset count (fun result => Pr{let value ← next result}[event value])]
        exact (prEvent_bind_eq_lintegral_of_discrete _ next event).symm


theorem hash_score {A : Type} {past : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable past) (world : World) (input : Input)
    (score : NativeRootMessage.Digest → ENNReal) :
    (∫⁻ other, score (InputIndexedOracle.sha512 other input)
      ∂law[|{other | (past other).run = (past world).run}]) =
      ∫⁻ digest, score digest ∂𝒟[JointHashKernel.answer (JointHashCache.project (past world).run.2) input] := by
  have response := congrArg (fun measure => ∫⁻ digest, score digest ∂measure)
    (JointHashKernel.reply_law replay world input)
  rw [lintegral_map (Measurable.of_discrete) (InputIndexedOracle.hash_measurable input)] at response
  exact response

theorem hash_transfer {A B : Type} {past : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable past) (world : World) (input : Input)
    (bad : Set World) (measurable : MeasurableSet bad)
    (next : NativeRootMessage.Digest → ProbComp B) (event : B → Prop)
    (tailLaw : ∀ current, (past current).run = (past world).run →
      (law[|{other | (OracleHistorySnapshot.hash past input other).run =
        (OracleHistorySnapshot.hash past input current).run}]) bad =
      Pr{let result ← next (InputIndexedOracle.sha512 current input)}[event result]) :
    (law[|{other | (past other).run = (past world).run}]) bad =
      Pr{let result ← (do
        let digest ← JointHashKernel.answer (JointHashCache.project (past world).run.2) input
        next digest)}[event result] := by
  rw [OracleHistorySnapshot.hash_average replay world input bad measurable]
  calc _ = ∫⁻ current, Pr{let result ← next (InputIndexedOracle.sha512 current input)}[event result]
          ∂law[|{other | (past other).run = (past world).run}] := by
        apply lintegral_congr_ae
        filter_upwards [ae_cond_mem (μ := law) (ObservationReplay.fiber_measurable replay world)] with current same
        exact tailLaw current same
       _ = _ := by
        rw [hash_score replay world input (fun digest => Pr{let value ← next digest}[event value])]
        exact (prEvent_bind_eq_lintegral_of_discrete _ next event).symm

end
end FormalProof4FHE.HasteBoots.OracleKernelComposition
