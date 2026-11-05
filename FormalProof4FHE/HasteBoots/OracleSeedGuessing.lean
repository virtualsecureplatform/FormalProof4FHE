module

public import FormalProof4FHE.HasteBoots.OracleMaskCounting
public import FormalProof4FHE.HasteBoots.OracleHistorySnapshot
public import FormalProof4FHE.HasteBoots.JointHashKernel
@[expose] public section

/-! Exact target-guessing risk after complete native histories. Compatible
targets are counted against the remaining unseen SHAKE bytes. Conditional
averaging preserves this risk across partial reads and shared hash queries.
A fresh64-byte seed has its full2^512 denominator; no such denominator is
asserted for a partially known seed. Native descendant classification and
root-freeze placement remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.OracleSeedGuessing
open InputIndexedOracle (World Input Byte Coordinate law)
open NativeTranscript (Observation)
open NativeRootMessage (Digest)
open MeasureTheory ProbabilityTheory
open scoped Classical
noncomputable section

def known (log : List Observation) (input : Input) (offset count : ℕ) : Finset (Fin count) :=
  Finset.univ.filter (fun position => CachedOracleResponse.shakeCoordinates input offset count position ∈
    ObservationReplay.footprint log)

def risk (log : List Observation) (world : World) (input : Input) (offset count : ℕ)
    (targets : Finset (Fin count → Byte)) : ENNReal :=
  ((targets.filter (OracleMaskCounting.compatible (known log input offset count)
    (InputIndexedOracle.block world input offset count))).card : ENNReal) /
      (256 : ENNReal)^(count-(known log input offset count).card)

theorem mask_eq (log : List Observation) (world : World) (input : Input) (offset count : ℕ) :
    CachedOracleResponse.mask (ObservationReplay.footprint log) world
      (CachedOracleResponse.shakeCoordinates input offset count) =
      OracleMaskCounting.mask (known log input offset count) (InputIndexedOracle.block world input offset count) := by
  funext raw position
  simp [CachedOracleResponse.mask,OracleMaskCounting.mask,known]
  rfl

theorem target_law {A : Type} {past : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable past) (world : World) (input : Input) (offset count : ℕ)
    (targets : Finset (Fin count → Byte)) :
    (law[|{other | (past other).run = (past world).run}])
      {other | InputIndexedOracle.block other input offset count ∈ targets} =
      risk (past world).run.2 world input offset count targets := by
  have response := congrArg (fun measure : Measure (Fin count → Byte) => measure (targets : Set (Fin count → Byte)))
    (CachedOracleResponse.shake_response replay world input offset count)
  rw [Measure.map_apply (InputIndexedOracle.block_measurable input offset count) targets.measurableSet,
    mask_eq,OracleMaskCounting.targets_probability] at response
  simpa only [risk,Fintype.card_fin,Set.preimage,Finset.mem_coe] using response

theorem risk_read_average {A : Type} {past : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable past) (world : World) (input : Input) (offset count : ℕ)
    (targets : Finset (Fin count → Byte)) (readInput : Input) (readOffset readCount : ℕ) :
    (∫⁻ current, risk (OracleHistorySnapshot.read past readInput readOffset readCount current).run.2 current
      input offset count targets ∂law[|{other | (past other).run = (past world).run}]) =
      risk (past world).run.2 world input offset count targets := by
  have measurable : MeasurableSet {other | InputIndexedOracle.block other input offset count ∈ targets} := by
    simpa only [Set.preimage,Finset.mem_coe] using
      (InputIndexedOracle.block_measurable input offset count) targets.measurableSet
  simp_rw [← target_law (OracleHistorySnapshot.read_replay replay readInput readOffset readCount)]
  rw [← OracleHistorySnapshot.read_average replay world readInput readOffset readCount _ measurable]
  exact target_law replay world input offset count targets

theorem risk_hash_average {A : Type} {past : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable past) (world : World) (input : Input) (offset count : ℕ)
    (targets : Finset (Fin count → Byte)) (hashInput : Input) :
    (∫⁻ current, risk (OracleHistorySnapshot.hash past hashInput current).run.2 current
      input offset count targets ∂law[|{other | (past other).run = (past world).run}]) =
      risk (past world).run.2 world input offset count targets := by
  have measurable : MeasurableSet {other | InputIndexedOracle.block other input offset count ∈ targets} := by
    simpa only [Set.preimage,Finset.mem_coe] using
      (InputIndexedOracle.block_measurable input offset count) targets.measurableSet
  simp_rw [← target_law (OracleHistorySnapshot.hash_replay replay hashInput)]
  rw [← OracleHistorySnapshot.hash_average replay world hashInput _ measurable]
  exact target_law replay world input offset count targets

/-- Exact512-bit target probability only when every logical seed coordinate is unseen. -/
theorem fresh_seed_targets {A : Type} {past : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable past) (world : World) (input : Input)
    (targets : Finset Digest)
    (fresh : ∀ position : Fin 64, (.inl (input,position.val) : Coordinate) ∉ ObservationReplay.footprint (past world).run.2) :
    (law[|{other | (past other).run = (past world).run}])
      {other | InputIndexedOracle.block other input 0 64 ∈ targets} =
      (targets.card : ENNReal) / (2 : ENNReal)^512 := by
  classical
  have response : (law[|{other | (past other).run = (past world).run}]).map
      (fun other => InputIndexedOracle.block other input 0 64) = uniformOn (Set.univ : Set Digest) := by
    rw [ObservationReplay.fiber_eq_assignment replay world]
    exact CachedOracleResponse.fresh_response _ _ (CachedOracleResponse.shakeCoordinates input 0 64)
      (CachedOracleResponse.shake_distinct input 0 64) (by simpa [CachedOracleResponse.shakeCoordinates] using fresh)
  have event := congrArg (fun measure : Measure Digest => measure (targets : Set Digest)) response
  rw [Measure.map_apply (InputIndexedOracle.block_measurable input 0 64) targets.measurableSet] at event
  rw [show (Set.univ : Set Digest) = (↑(Finset.univ : Finset Digest) : Set Digest) by simp,
    uniformOn_apply_finset] at event
  simpa only [Finset.univ_inter,Finset.card_univ,JointHashKernel.digest_card,Nat.cast_pow,
    Nat.cast_ofNat,Set.preimage,Finset.mem_coe] using event

end
end FormalProof4FHE.HasteBoots.OracleSeedGuessing
