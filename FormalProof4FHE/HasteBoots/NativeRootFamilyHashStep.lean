module
public import FormalProof4FHE.HasteBoots.ClosedByteMachineRootBudget
@[expose] public section

/-! Conditional first source/collision failure at a real SHA-512 request.
The posterior includes the full mixed history. Cached calls, partial SHAKE
reads and earlier source freezes use the same existing global world. -/
namespace FormalProof4FHE.HasteBoots.NativeRootFamilyHashStep
open InputIndexedOracle (Input World law sha512)
open NativeRootMessage (Digest)
open NativeTranscript (Observation Execution)
open NativeGoldColumnAuthentication (encoding)
open NativeGoldBatchFamilyAvailability (reconstructed)
open NativeMerkleShapeFamily (shape)
open NativeRootFamilyLifetime (Bad)
open MeasureTheory ProbabilityTheory OracleSpec OracleComp
noncomputable section
open scoped Classical

theorem reconstructed_append (dummy : Digest) (before later : List Observation) :
    reconstructed dummy (before++later) =
      (later.foldl (NativeRootFamilyState.record encoding dummy)
        (NativeRootFamilyHistory.reconstruct encoding dummy before)).2 := by
  simp only [reconstructed,NativeRootFamilyHistory.reconstruct,NativeRootFamilyHistory.initial,List.foldl_append]

theorem bad_start (dummy : Digest) (before : List Observation) (input : Input) :
    Bad dummy (before++[.start input]) ↔ Bad dummy before := by
  rw [Bad,reconstructed_append]
  rfl

theorem bad_read (dummy : Digest) (before : List Observation) (input : Input) (offset : ℕ) (values : Input) :
    Bad dummy (before++[.output input offset values]) ↔ Bad dummy before := by
  rw [Bad,reconstructed_append]
  simp only [List.foldl_cons,List.foldl_nil,NativeRootFamilyState.record]
  split
  · rfl
  · simp only [CheckpointCollision.Bad,RecordRoots.hash_eq,NativeRootFamilyAudit.roots_failed]
    rfl

theorem reconstructed_hash_step (dummy : Digest) (before : List Observation) (input : Input) (digest : Digest) :
    reconstructed dummy (before++[.hash input (List.ofFn digest)]) =
      CheckpointExecution.afterHash encoding dummy shape (reconstructed dummy before)
        (JointHashCache.record (JointHashCache.project before) (.hash input (List.ofFn digest))) := by
  rw [reconstructed_append]
  simp only [List.foldl_cons,List.foldl_nil,NativeRootFamilyState.record,NativeLazyStateExecution.record]
  change CheckpointExecution.afterHash encoding dummy shape (reconstructed dummy before)
    (JointHashCache.record (reconstructed dummy before).hash (.hash input (List.ofFn digest))) = _
  rw [NativeGoldBatchFamilyAvailability.reconstructed_hash]

def event (dummy : Digest) (input : Input) (before : List Observation) (world : World) : Prop :=
  ¬Bad dummy before ∧ Bad dummy (before++[.hash input (List.ofFn (sha512 world input))])

def risk (dummy : Digest) (input : Input) (before : List Observation) : ENNReal :=
  CheckpointCollision.loss unifSpec shape (.inr (.inl input)) (reconstructed dummy before)

theorem conditional_bound {A : Type} {past : World → Execution A} (replay : ObservationReplay.Replayable past)
    (dummy : Digest) (world : World) (input : Input) :
    (law[|{other | (past other).run = (past world).run}])
      {other | event dummy input (past world).run.2 other} ≤ risk dummy input (past world).run.2 := by
  by_cases oldBad : Bad dummy (past world).run.2
  · simp only [event,oldBad,not_true_eq_false,false_and,Set.ofPred_false,measure_empty]
    exact zero_le
  · have audited := NativeRootFamilyAudit.reconstructed_audited dummy world (past world).run.2 (replay.truthful world)
    have clear : (reconstructed dummy (past world).run.2).failed = false := by
      have notTrue : (reconstructed dummy (past world).run.2).failed ≠ true := fun yes => oldBad (Or.inl yes)
      cases h : (reconstructed dummy (past world).run.2).failed <;> simp_all
    have stable := audited.2 clear
    rw [NativeGoldBatchFamilyAvailability.reconstructed_hash] at stable
    have noCollision : ¬CacheHasCollision (JointHashCache.project (past world).run.2).cache := by
      rw [← NativeGoldBatchFamilyAvailability.reconstructed_hash dummy (past world).run.2]
      exact fun yes => oldBad (Or.inr yes)
    have cover : {other | event dummy input (past world).run.2 other} ⊆
        {other | ¬MerklePayloadCheckpoints.StableAt encoding dummy shape
          (reconstructed dummy (past world).run.2).checkpoints
          (JointHashCache.record (JointHashCache.project (past world).run.2)
            (.hash input (List.ofFn (sha512 other input)))).log} ∪
        {other | CacheHasCollision (JointHashCache.record (JointHashCache.project (past world).run.2)
          (.hash input (List.ofFn (sha512 other input)))).cache} := by
      intro other member
      have bad := member.2
      rw [Bad,reconstructed_hash_step] at bad
      rcases bad with failed | collision
      · have failure := (CheckpointExecution.afterHash_failed_iff encoding dummy shape _ _).mp failed
        rcases failure with earlier | unstable
        · rw [clear] at earlier
          contradiction
        · exact Or.inl unstable
      · exact Or.inr collision
    apply (measure_mono cover).trans
    apply (measure_union_le _ _).trans
    have source := JointHashKernel.checkpoint_step replay world input encoding dummy shape _ stable
    have collision := JointHashKernel.collision_step replay world input noCollision
    apply (add_le_add source collision).trans
    rw [risk,CheckpointCollision.hash_loss,NativeGoldBatchFamilyAvailability.reconstructed_hash]
    by_cases fresh : (JointHashCache.project (past world).run.2).cache input = none
    · simp only [fresh,ite_true,JointHashKernel.digest_card,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add]
      exact ENNReal.add_div.symm.le
    · simp only [fresh,ite_false,zero_add,le_refl]

theorem event_measurable (dummy : Digest) (input : Input) (before : List Observation) :
    MeasurableSet {world | event dummy input before world} := by
  exact OracleExecutionLaw.event_measurable (OracleProgram.run_replay (.hash input (fun _ => .pure ())))
    (fun result => ¬Bad dummy before ∧ Bad dummy (before++result.2))
end
end FormalProof4FHE.HasteBoots.NativeRootFamilyHashStep
