module
public import FormalProof4FHE.HasteBoots.ContextDigestTargets
public import FormalProof4FHE.HasteBoots.OracleProgramHistory
public import FormalProof4FHE.HasteBoots.CausalSeedExposure
public import FormalProof4FHE.HasteBoots.JointHashKernel
@[expose] public section

/-! A fresh SHA-512 query hits earlier named context digests with exact
conditional probability targets/2^512. The selecting packet is the complete
mixed-oracle history; hash repeats receive no fresh charge. -/
namespace FormalProof4FHE.HasteBoots.ContextTargetRisk
open InputIndexedOracle (Input World law)
open NativeTranscript (Observation Execution)
open NativeRootMessage (Digest)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
open scoped Classical
noncomputable section

def touches (input : Input) : Observation → Bool
  | .hash key _ => decide (key = input)
  | _ => false

def seen (history : List Observation) (input : Input) : Bool := history.any (touches input)

theorem unseen_coordinates (history : List Observation) (input : Input) (fresh : seen history input = false) :
    ∀ index : Fin 64, (.inr (input,index) : InputIndexedOracle.Coordinate) ∉ ObservationReplay.footprint history := by
  intro index present
  obtain ⟨entry,member,coordinate⟩ := Finset.mem_biUnion.mp present
  cases entry with
  | start key => simp [ObservationReplay.coordinates] at coordinate
  | output key offset values =>
    obtain ⟨i,_,equal⟩ := Finset.mem_image.mp coordinate
    cases equal
  | hash key digest =>
    obtain ⟨i,_,equal⟩ := Finset.mem_image.mp coordinate
    have same : key = input := (Prod.mk.inj (Sum.inr.inj equal)).1
    have yes : seen history input = true := List.any_eq_true.mpr ⟨_,List.mem_toFinset.mp member,by simp [touches,same]⟩
    rw [fresh] at yes
    exact Bool.false_ne_true yes

def select {S A : Type} (step : S → OracleMachine.Command S A) (packet : (S ⊕ A) × List Observation) : Option Input :=
  match CausalSeedExposure.request step packet.1 with
  | some (.hash input) => if seen packet.2 input = false then some input else none
  | _ => none

def event {S A : Type} (step : S → OracleMachine.Command S A) (packet : (S ⊕ A) × List Observation) (world : World) : Prop :=
  match select step packet with
  | some input => InputIndexedOracle.sha512 world input ∈ ContextDigestTargets.targets packet.2
  | none => False

def risk {S A : Type} (step : S → OracleMachine.Command S A) (packet : (S ⊕ A) × List Observation) : ENNReal :=
  match select step packet with
  | some _ => (ContextDigestTargets.targets packet.2).card / (2 : ENNReal)^512
  | none => 0

theorem fresh_targets {A : Type} {past : World → Execution A} (replay : ObservationReplay.Replayable past)
    (world : World) (input : Input) (targets : Finset Digest) (fresh : seen (past world).run.2 input = false) :
    (law[|{other | (past other).run = (past world).run}]) {other | InputIndexedOracle.sha512 other input ∈ targets} =
      (targets.card : ENNReal)/(2 : ENNReal)^512 := by
  have response : (law[|{other | (past other).run = (past world).run}]).map
      (fun other => InputIndexedOracle.sha512 other input) = uniformOn (Set.univ : Set Digest) := by
    rw [ObservationReplay.fiber_eq_assignment replay world]
    exact CachedOracleResponse.fresh_response _ _ (CachedOracleResponse.hashCoordinates input)
      (CachedOracleResponse.hash_distinct input) (unseen_coordinates _ input fresh)
  have probability := congrArg (fun measure : Measure Digest => measure (targets : Set Digest)) response
  rw [Measure.map_apply (InputIndexedOracle.hash_measurable input) targets.measurableSet] at probability
  rw [show (Set.univ : Set Digest) = (↑(Finset.univ : Finset Digest) : Set Digest) by simp,uniformOn_apply_finset] at probability
  simpa only [Finset.univ_inter,Finset.card_univ,JointHashKernel.digest_card,Nat.cast_pow,Nat.cast_ofNat,Set.preimage,Finset.mem_coe] using probability

theorem selected_unseen {S A : Type} (step : S → OracleMachine.Command S A) (packet : (S ⊕ A) × List Observation)
    (input : Input) (selected : select step packet = some input) : seen packet.2 input = false := by
  unfold select at selected
  split at selected <;> simp at selected
  obtain ⟨fresh,rfl⟩ := selected
  exact fresh

theorem conditional_event {S A : Type} (step : S → OracleMachine.Command S A)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) (world : World) :
    (law[|{other | (past other).run = (past world).run}]) {other | event step (past other).run other} = risk step (past world).run := by
  calc
    _ = (law[|{other | (past other).run = (past world).run}]) {other | event step (past world).run other} := by
      apply NativeShakeProjection.conditional_event_congr replay world
      intro other same
      rw [same]
    _ = _ := by
      cases selected : select step (past world).run with
      | none => simp [event,risk,selected]
      | some input =>
        simp only [event,risk,selected]
        exact fresh_targets replay world input _ (selected_unseen step _ input selected)

theorem event_measurable {S A : Type} (step : S → OracleMachine.Command S A)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) : MeasurableSet {world | event step (past world).run world} := by
  apply OracleProgramHistory.event_measurable replay (fun packet world => event step packet world)
  intro packet
  cases selected : select step packet with
  | none => simp [event,selected]
  | some input =>
    simpa only [event,selected,Set.preimage,Finset.mem_coe] using
      (InputIndexedOracle.hash_measurable input) (ContextDigestTargets.targets packet.2).measurableSet

theorem averaged_event {S A : Type} (step : S → OracleMachine.Command S A)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) :
    law {world | event step (past world).run world} = ∫⁻ world, risk step (past world).run ∂law := by
  rw [OracleHistoryComposition.average_event replay law _ (event_measurable step replay)]
  exact lintegral_congr (fun world => conditional_event step replay world)


theorem risk_le_input_bytes {S A : Type} (step : S → OracleMachine.Command S A) (packet : (S ⊕ A) × List Observation) :
    risk step packet ≤ (2*ContextDigestTargets.inputBytes packet.2 : ℕ)/(2 : ENNReal)^512 := by
  cases selected : select step packet with
  | none => simp only [risk,selected]; exact zero_le
  | some input =>
    simp only [risk,selected,div_eq_mul_inv]
    exact mul_le_mul_left (by exact_mod_cast ContextDigestTargets.card packet.2) _

end
end FormalProof4FHE.HasteBoots.ContextTargetRisk
