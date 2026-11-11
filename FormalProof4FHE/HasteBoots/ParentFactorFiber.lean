module
public import FormalProof4FHE.HasteBoots.ParentMetadataReplay
public import FormalProof4FHE.HasteBoots.ScalarParentSeparation
public import FormalProof4FHE.HasteBoots.FactorPosteriorMismatch
@[expose] public section

/-! One analysis fiber completes recognized parent seeds and earlier receipt
keys while retaining the original packet. Semantic ancestry and factor
fixation coexist there with the exact fresh scalar-stream law. Auxiliary
queries are not substituted for the original root-freezing history. -/
namespace FormalProof4FHE.HasteBoots.ParentFactorFiber
open InputIndexedOracle (Input World Byte law)
open NativeTranscript (Execution)
open OracleProgram (Program runPrefix)
open LookupFactorFixation (Sample Scalar Point)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section

def extend {A : Type} (past : World → Execution A) :=
  ReceiptCandidateCompletion.extend (ParentSeedCompletion.extend past)

theorem replay {A : Type} {past : World → Execution A} (old : ObservationReplay.Replayable past) :
    ObservationReplay.Replayable (extend past) := ReceiptCandidateCompletion.replay (ParentSeedCompletion.replay old)

theorem parent_packet {A : Type} (past : World → Execution A) (world other : World)
    (same : (extend past other).run = (extend past world).run) :
    (ParentSeedCompletion.extend past other).run = (ParentSeedCompletion.extend past world).run :=
  ReceiptCandidateCompletion.old_packet _ world other same

theorem old_packet {A : Type} (past : World → Execution A) (world other : World)
    (same : (extend past other).run = (extend past world).run) : (past other).run = (past world).run :=
  ParentSeedCompletion.old_packet past world other (parent_packet past world other same)

/-- Full equality of earlier receipt blocks and the old packet suffices to
reconstruct the earlier receipt-only completion packet. -/
theorem receipt_packet_of_blocks {A : Type} (past : World → Execution A) (world other : World)
    (old : (past other).run = (past world).run)
    (blocks : ∀ raw ∈ ReceiptPayloadView.payloads (past world).run.2,
      ReceiptCandidateCompletion.digest other raw = ReceiptCandidateCompletion.digest world raw) :
    (ReceiptCandidateCompletion.extend past other).run = (ReceiptCandidateCompletion.extend past world).run := by
  have observations : ReceiptCandidateCompletion.observations (ReceiptPayloadView.payloads (past world).run.2).toList other =
      ReceiptCandidateCompletion.observations (ReceiptPayloadView.payloads (past world).run.2).toList world := by
    unfold ReceiptCandidateCompletion.observations
    apply List.flatMap_congr
    intro raw named
    have equal := blocks raw (Finset.mem_toList.mp named)
    have bytes := congrArg List.ofFn equal
    exact congrArg (fun values => [NativeTranscript.Observation.start (NativeReceiptPrefixView.key raw),
      .output (NativeReceiptPrefixView.key raw) 0 values]) bytes
  simp only [ReceiptCandidateCompletion.extend,OracleProgramHistory.run_extend,ReceiptCandidateCompletion.run_program,old,observations]

theorem receipt_packet {A : Type} {past : World → Execution A} (old : ObservationReplay.Replayable past)
    (world other : World) (same : (extend past other).run = (extend past world).run) :
    (ReceiptCandidateCompletion.extend past other).run = (ReceiptCandidateCompletion.extend past world).run := by
  apply receipt_packet_of_blocks past world other (old_packet past world other same)
  intro raw named
  have included : (past world).run.2.Sublist (ParentSeedCompletion.extend past world).run.2 := List.sublist_append_left _ _
  exact ReceiptCandidateCompletion.digest_on_fiber (ParentSeedCompletion.replay old) world other raw
    (ReceiptCollisionOnset.payloads_mono _ _ included named) same

theorem ancestry_on_fiber {A : Type} {past : World → Execution A} (old : ObservationReplay.Replayable past)
    (world other : World) (input : Input) (fact : NativeSeedAncestry.Fact)
    (same : (extend past other).run = (extend past world).run) :
    NativeSeedAncestry.Known other (past other).run.2 input fact ↔ NativeSeedAncestry.Known world (past world).run.2 input fact :=
  ParentMetadataReplay.on_fiber old world other input fact (parent_packet past world other same)

theorem unseen {A : Type} (sample : Sample) (program : Program A)
    (first : ProgramFirstStreamRead.First program sample.view.reader.world sample.view.reader.entry.coefficients.phase.pending.input) :
    CausalStreamExposure.seen (extend (runPrefix first.position program) sample.view.reader.world).run.2
      sample.view.reader.entry.coefficients.phase.pending.input = false := by
  have parentFresh := ParentSeedCompletion.unseen (runPrefix first.position program) sample.view.reader.world _ first.fresh
    (ScalarParentSeparation.sample_rejected sample)
  obtain ⟨frames,encoded⟩ := FactorFiberUniform.input_framed sample
  apply ReceiptCandidateCompletion.unseen_extended (ParentSeedCompletion.extend (runPrefix first.position program)) sample.view.reader.world _ parentFresh
  intro raw _
  rw [encoded]
  exact NativeTranscript.receipt_not_frame_stream raw frames

theorem block_law {A : Type} (sample : Sample) (program : Program A)
    (first : ProgramFirstStreamRead.First program sample.view.reader.world sample.view.reader.entry.coefficients.phase.pending.input)
    (offset count : ℕ) :
    (law[|{other | (extend (runPrefix first.position program) other).run =
      (extend (runPrefix first.position program) sample.view.reader.world).run}]).map
        (fun other => InputIndexedOracle.block other sample.view.reader.entry.coefficients.phase.pending.input offset count) =
      uniformOn (Set.univ : Set (Fin count → Byte)) := by
  rw [ObservationReplay.fiber_eq_assignment (replay (OracleProgram.prefix_replay first.position program)) sample.view.reader.world]
  exact CachedOracleResponse.fresh_response _ _
    (CachedOracleResponse.shakeCoordinates sample.view.reader.entry.coefficients.phase.pending.input offset count)
    (CachedOracleResponse.shake_distinct _ offset count)
    (fun position => by simpa only [CachedOracleResponse.shakeCoordinates] using
      CausalStreamExposure.unseen_coordinates _ _ (unseen sample program first) (offset+position.val))

theorem scalar_on_fiber {A : Type} (program : Program A) (left right : Scalar)
    (sameInput : left.view.reader.entry.coefficients.phase.pending.input = right.view.reader.entry.coefficients.phase.pending.input)
    (samePosition : left.position = right.position)
    (first : ProgramFirstStreamRead.First program left.view.reader.world left.view.reader.entry.coefficients.phase.pending.input)
    (leftObserved : ProgramFactorFixation.Observed program left.toSample) (rightObserved : ProgramFactorFixation.Observed program right.toSample)
    (same : (extend (runPrefix first.position program) right.view.reader.world).run =
      (extend (runPrefix first.position program) left.view.reader.world).run) :
    right.word = left.word ∨ ProgramFactorFixation.Bad program left.toSample right.toSample :=
  ProgramFactorFixation.scalar_on_fiber program left right sameInput samePosition first leftObserved rightObserved
    (receipt_packet (OracleProgram.prefix_replay first.position program) _ _ same)

theorem point_on_fiber {A : Type} (program : Program A) (left right : Point)
    (sameInput : left.view.reader.entry.coefficients.phase.pending.input = right.view.reader.entry.coefficients.phase.pending.input)
    (samePosition : left.position = right.position)
    (first : ProgramFirstStreamRead.First program left.view.reader.world left.view.reader.entry.coefficients.phase.pending.input)
    (leftObserved : ProgramFactorFixation.Observed program left.toSample) (rightObserved : ProgramFactorFixation.Observed program right.toSample)
    (same : (extend (runPrefix first.position program) right.view.reader.world).run =
      (extend (runPrefix first.position program) left.view.reader.world).run) :
    right.point = left.point ∨ ProgramFactorFixation.Bad program left.toSample right.toSample :=
  ProgramFactorFixation.point_on_fiber program left right sameInput samePosition first leftObserved rightObserved
    (receipt_packet (OracleProgram.prefix_replay first.position program) _ _ same)

/-- Refining by parent seeds preserves the existing posterior mismatch
bound; the original reference-world exceptions stay explicit. -/
theorem scalar_mismatch_le {A : Type} (program : Program A) (left : Scalar)
    (first : ProgramFirstStreamRead.First program left.view.reader.world left.view.reader.entry.coefficients.phase.pending.input)
    (observed : ProgramFactorFixation.Observed program left.toSample)
    (freshSafe : ¬ ProgramReceiptCoverage.Bad program left.view.reader.world)
    (collisionSafe : ¬ ProgramReceiptCollision.Bad program left.view.reader.world) :
    (law[|{other | (extend (runPrefix first.position program) other).run =
      (extend (runPrefix first.position program) left.view.reader.world).run}])
      {other | FactorPosteriorMismatch.ScalarMismatch program left other} ≤
    (law[|{other | (extend (runPrefix first.position program) other).run =
      (extend (runPrefix first.position program) left.view.reader.world).run}])
      {other | ProgramReceiptCoverage.Bad program other} := by
  apply FactorPosteriorMismatch.conditional_mono (replay (OracleProgram.prefix_replay first.position program))
  intro other same mismatch
  exact FactorPosteriorMismatch.scalar_cover program left first observed freshSafe collisionSafe other
    (receipt_packet (OracleProgram.prefix_replay first.position program) _ _ same) mismatch

theorem point_mismatch_le {A : Type} (program : Program A) (left : Point)
    (first : ProgramFirstStreamRead.First program left.view.reader.world left.view.reader.entry.coefficients.phase.pending.input)
    (observed : ProgramFactorFixation.Observed program left.toSample)
    (freshSafe : ¬ ProgramReceiptCoverage.Bad program left.view.reader.world)
    (collisionSafe : ¬ ProgramReceiptCollision.Bad program left.view.reader.world) :
    (law[|{other | (extend (runPrefix first.position program) other).run =
      (extend (runPrefix first.position program) left.view.reader.world).run}])
      {other | FactorPosteriorMismatch.PointMismatch program left other} ≤
    (law[|{other | (extend (runPrefix first.position program) other).run =
      (extend (runPrefix first.position program) left.view.reader.world).run}])
      {other | ProgramReceiptCoverage.Bad program other} := by
  apply FactorPosteriorMismatch.conditional_mono (replay (OracleProgram.prefix_replay first.position program))
  intro other same mismatch
  exact FactorPosteriorMismatch.point_cover program left first observed freshSafe collisionSafe other
    (receipt_packet (OracleProgram.prefix_replay first.position program) _ _ same) mismatch

end
end FormalProof4FHE.HasteBoots.ParentFactorFiber
