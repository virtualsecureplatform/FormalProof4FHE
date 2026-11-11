module
public import FormalProof4FHE.HasteBoots.ParentSeedCompletion
public import FormalProof4FHE.HasteBoots.FreshReceiptTargetRisk
@[expose] public section

/-! First naming of a recognized parent key carries a separate full-seed
collision charge. Starts and empty reads are included, matching parent
discovery. Earlier partial reads of other parents do not reduce the new
key's 512-bit law. This event is separate from receipt and hash collisions. -/
namespace FormalProof4FHE.HasteBoots.ParentSeedCollisionRisk
open InputIndexedOracle (Input World law)
open NativeTranscript (Execution)
open NativeIndexExposureRisk (Packet)

open OracleSpec OracleComp MeasureTheory ProbabilityTheory
open scoped Classical
noncomputable section

def seed (world : World) (input : Input) : NativeRootMessage.Digest := InputIndexedOracle.block world input 0 64

def Collision (history : List NativeTranscript.Observation) (world : World) : Prop :=
  ∃ left ∈ ParentSeedCandidates.inputs history, ∃ right ∈ ParentSeedCandidates.inputs history,
    left ≠ right ∧ seed world left = seed world right

def requestInput : OracleProgram.Request → Input
  | .start input | .read input _ _ | .hash input => input

def candidate (request : OracleProgram.Request) : Option Input :=
  ParentSeedCandidates.candidate (.start (requestInput request))

def select {S A : Type} (step : S → OracleMachine.Command S A) (packet : Packet S A) : Option Input :=
  (CausalSeedExposure.request step packet.1).bind fun request =>
    (candidate request).bind fun raw => if raw ∈ ParentSeedCandidates.inputs packet.2 then none else some raw

theorem selected_new {S A : Type} (step : S → OracleMachine.Command S A) (packet : Packet S A) (raw : Input)
    (chosen : select step packet = some raw) : raw ∉ ParentSeedCandidates.inputs packet.2 := by
  obtain ⟨request,_,chosen⟩ := Option.bind_eq_some_iff.mp chosen
  obtain ⟨value,_,chosen⟩ := Option.bind_eq_some_iff.mp chosen
  split at chosen
  · contradiction
  · obtain rfl := Option.some.inj chosen
    assumption

theorem selected_parsed {S A : Type} (step : S → OracleMachine.Command S A) (packet : Packet S A) (raw : Input)
    (chosen : select step packet = some raw) : ∃ frames, NativeParentInputView.parseParent raw = some frames := by
  obtain ⟨request,_,chosen⟩ := Option.bind_eq_some_iff.mp chosen
  obtain ⟨value,parsed,chosen⟩ := Option.bind_eq_some_iff.mp chosen
  split at chosen
  · contradiction
  · obtain rfl := Option.some.inj chosen
    apply ParentSeedCandidates.parsed [NativeTranscript.Observation.start (requestInput request)] value
    exact List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨_,List.mem_cons_self,parsed⟩)

theorem selected_unseen {S A : Type} (step : S → OracleMachine.Command S A) (packet : Packet S A) (raw : Input)
    (chosen : select step packet = some raw) : CausalStreamExposure.seen packet.2 raw = false := by
  obtain ⟨frames,parsed⟩ := selected_parsed step packet raw chosen
  have new := selected_new step packet raw chosen
  cases seen : CausalStreamExposure.seen packet.2 raw with
  | false => rfl
  | true =>
    obtain ⟨entry,member,touched⟩ := List.any_eq_true.mp seen
    cases entry with
    | start input => contradiction
    | hash input digest => contradiction
    | output input offset values =>
      obtain ⟨same,_⟩ := of_decide_eq_true touched
      subst input
      exact False.elim (new (ParentSeedCandidates.of_observation packet.2 _ member frames parsed))

def event {S A : Type} (step : S → OracleMachine.Command S A) (packet : Packet S A) (world : World) : Prop :=
  match select step packet with
  | none => False
  | some raw => ∃ old ∈ ParentSeedCandidates.inputs packet.2, seed world raw = seed world old

def risk {S A : Type} (step : S → OracleMachine.Command S A) (packet : Packet S A) : ENNReal :=
  match select step packet with
  | none => 0
  | some _ => ((ParentSeedCandidates.inputs packet.2).card : ENNReal)/(2 : ENNReal)^512

theorem fixed_measurable {S A : Type} (step : S → OracleMachine.Command S A) (packet : Packet S A) :
    MeasurableSet {world | event step packet world} := by
  cases chosen : select step packet with
  | none => simp only [event,chosen,Set.ofPred_false]; exact MeasurableSet.empty
  | some raw =>
    simp only [event,chosen,Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro old
    by_cases named : old ∈ ParentSeedCandidates.inputs packet.2
    · simp only [named,true_and]
      exact measurableSet_eq_fun (InputIndexedOracle.block_measurable raw 0 64)
        (InputIndexedOracle.block_measurable old 0 64)
    · simp only [named,false_and,Set.ofPred_false]
      exact MeasurableSet.empty

theorem event_measurable {S A : Type} (step : S → OracleMachine.Command S A)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) :
    MeasurableSet {world | event step (past world).run world} :=
  OracleProgramHistory.event_measurable replay (event step) (fixed_measurable step)

/-- Auxiliary completion reads earlier keys only; the new key is disjoint
from every completion query and has its full 512-bit conditional law. -/
theorem retained_bound {S A : Type} (step : S → OracleMachine.Command S A)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) (world : World) :
    (law[|{other | (ParentSeedCompletion.extend past other).run = (ParentSeedCompletion.extend past world).run}])
      {other | event step (past other).run other} ≤ risk step (past world).run := by
  let completed := ParentSeedCompletion.extend past
  have rp := ParentSeedCompletion.replay replay
  cases chosen : select step (past world).run with
  | none =>
    have equal : (law[|{other | (completed other).run = (completed world).run}]) {other | event step (past other).run other} = 0 := by
      calc _ = (law[|{other | (completed other).run = (completed world).run}]) {other | event step (past world).run other} := by
             apply NativeShakeProjection.conditional_event_congr rp world
             intro other same
             rw [ParentSeedCompletion.old_packet past world other same]
           _ = 0 := by simp only [event,chosen,Set.ofPred_false,measure_empty]
    simp only [risk,chosen]
    exact equal.le
  | some raw =>
    have new := selected_new step (past world).run raw chosen
    have unseen := selected_unseen step (past world).run raw chosen
    have fresh : CausalStreamExposure.seen (ParentSeedCompletion.extend past world).run.2 raw = false := by
      change CausalStreamExposure.seen ((past world).run.2 ++ (OracleProgram.run (ParentSeedCompletion.program _) world).run.2) raw = false
      rw [ParentSeedCompletion.run_program]
      simp only [CausalStreamExposure.seen,List.any_append]
      rw [show (past world).run.2.any (CausalStreamExposure.touches raw) = false from unseen]
      apply List.any_eq_false.mpr
      intro entry member
      obtain ⟨old,named,present⟩ := List.mem_flatMap.mp member
      have apart : old ≠ raw := by intro equal; exact new (equal ▸ Finset.mem_toList.mp named)
      simp only [List.mem_cons,List.not_mem_nil,or_false] at present
      rcases present with rfl | rfl
      · simp only [CausalStreamExposure.touches,Bool.false_eq_true,not_false_eq_true]
      · simp only [CausalStreamExposure.touches,apart,false_and,decide_false,Bool.false_eq_true,not_false_eq_true]
    let targets := (ParentSeedCandidates.inputs (past world).run.2).image (seed world)
    have probability := OracleSeedGuessing.fresh_seed_targets rp world raw targets
      (fun position => CausalStreamExposure.unseen_coordinates _ _ fresh position.val)
    have equal : (law[|{other | (completed other).run = (completed world).run}]) {other | event step (past other).run other} =
        (law[|{other | (completed other).run = (completed world).run}]) {other | InputIndexedOracle.block other raw 0 64 ∈ targets} := by
      apply NativeShakeProjection.conditional_event_congr rp world
      intro other same
      rw [ParentSeedCompletion.old_packet past world other same]
      simp only [event,chosen,targets,Finset.mem_image]
      constructor
      · rintro ⟨old,named,matching⟩
        exact ⟨old,named,(ParentSeedCompletion.seed_on_fiber replay world other old named same).symm.trans matching.symm⟩
      · rintro ⟨old,named,matching⟩
        exact ⟨old,named,matching.symm.trans (ParentSeedCompletion.seed_on_fiber replay world other old named same).symm⟩
    rw [equal,probability]
    simp only [risk,chosen,div_eq_mul_inv]
    exact mul_le_mul_left (by exact_mod_cast Finset.card_image_le) _

theorem averaged_bound {S A : Type} (step : S → OracleMachine.Command S A)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) :
    law {world | event step (past world).run world} ≤ ∫⁻ world, risk step (past world).run ∂law := by
  rw [OracleHistoryComposition.average_event (ParentSeedCompletion.replay replay) law _ (event_measurable step replay)]
  exact lintegral_mono (retained_bound step replay)

end
end FormalProof4FHE.HasteBoots.ParentSeedCollisionRisk
