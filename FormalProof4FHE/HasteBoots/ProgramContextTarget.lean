module
public import FormalProof4FHE.HasteBoots.ContextTargetRisk
public import FormalProof4FHE.HasteBoots.ReceiptProgramObservation
public import FormalProof4FHE.HasteBoots.GoldContextCollision
@[expose] public section

/-! A context named before its preimage is first hashed enters one causal
lifetime target ledger. Native hashes in the full execution yield prior
observation or this explicit exception at any selected raw prefix. -/
namespace FormalProof4FHE.HasteBoots.ProgramContextTarget
open InputIndexedOracle (Input World law)
open NativeTranscript (Observation)
open OracleProgram (Program run runPrefix)
open ContextTargetRisk (seen touches event risk)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
open scoped Classical
noncomputable section

def Bad {A : Type} (program : Program A) (world : World) : Prop :=
  ∃ position, event OracleProgramMachine.step (runPrefix position program world).run world

def totalCharge {A : Type} (program : Program A) (world : World) : ENNReal :=
  ∑' position : ℕ, risk OracleProgramMachine.step (runPrefix position program world).run

theorem bad_le {A : Type} (program : Program A) :
    law {world | Bad program world} ≤ ∫⁻ world, totalCharge program world ∂law := by
  have union : {world | Bad program world} =
      ⋃ position : ℕ, {world | event OracleProgramMachine.step (runPrefix position program world).run world} := by
    ext world
    simp only [Bad,Set.mem_ofPred_eq,Set.mem_iUnion]
  rw [union]
  calc _ ≤ ∑' position : ℕ, law {world | event OracleProgramMachine.step (runPrefix position program world).run world} := measure_iUnion_le _
       _ = ∑' position : ℕ, ∫⁻ world, risk OracleProgramMachine.step (runPrefix position program world).run ∂law := by
         congr 1
         funext position
         exact ContextTargetRisk.averaged_event OracleProgramMachine.step (OracleProgram.prefix_replay position program)
       _ = _ := (lintegral_tsum (fun position =>
         (OracleExecutionLaw.score_measurable (OracleProgram.prefix_replay position program) (risk OracleProgramMachine.step)).aemeasurable)).symm


theorem bad_measurable {A : Type} (program : Program A) : MeasurableSet {world | Bad program world} := by
  have union : {world | Bad program world} =
      ⋃ position : ℕ, {world | event OracleProgramMachine.step (runPrefix position program world).run world} := by
    ext world
    simp only [Bad,Set.mem_ofPred_eq,Set.mem_iUnion]
  rw [union]
  exact MeasurableSet.iUnion (fun position => ContextTargetRisk.event_measurable OracleProgramMachine.step (OracleProgram.prefix_replay position program))

/-- Averaging counterfactual late-target mass over any replayable selecting
prefix retains the same lifetime charge; no good-world assumption is made
about other members of a posterior fiber. -/
theorem posterior_average_le {A B : Type} (program : Program A) {past : World → NativeTranscript.Execution B}
    (replay : ObservationReplay.Replayable past) :
    (∫⁻ world, (law[|{other | (past other).run = (past world).run}]) {other | Bad program other} ∂law) ≤
      ∫⁻ world, totalCharge program world ∂law := by
  rw [← OracleHistoryComposition.average_event replay law _ (bad_measurable program)]
  exact bad_le program

theorem inherited_le {A : Type} (program : Program A) (inherited : Set World) :
    law (inherited ∪ {world | Bad program world}) ≤ law inherited + ∫⁻ world, totalCharge program world ∂law :=
  (measure_union_le _ _).trans (add_le_add le_rfl (bad_le program))

theorem hash_request {A : Type} (program : Program A) (world : World) (position : ℕ) (input bytes : Input)
    (found : (run program world).run.2[position]? = some (.hash input bytes)) :
    CausalSeedExposure.request OracleProgramMachine.step (runPrefix position program world).run.1 = some (.hash input) := by
  induction program generalizing position with
  | pure value => cases position <;> simp only [run,CanonicalTranscriptSampler.run_pure,List.getElem?_nil] at found <;> contradiction
  | start key next ih =>
    cases position with
    | zero => cases Option.some.inj found
    | succ position => exact ih position found
  | read key offset count next ih =>
    cases position with
    | zero => cases Option.some.inj found
    | succ position => exact ih _ position found
  | hash key next ih =>
    cases position with
    | zero =>
      have same := Observation.hash.inj (Option.some.inj found)
      rw [← same.1]
      rfl
    | succ position => exact ih _ position found

theorem first_hash (history : List Observation) (world : World) (input : Input)
    (truthful : ObservationReplay.Agrees world history) (occurred : seen history input = true) :
    ∃ before after, history = before ++ .hash input (List.ofFn (InputIndexedOracle.sha512 world input)) :: after ∧ seen before input = false := by
  induction history with
  | nil => contradiction
  | cons entry rest ih =>
    by_cases head : touches input entry = true
    · cases entry with
      | start key => contradiction
      | output key offset values => contradiction
      | hash key bytes =>
        have same : key = input := of_decide_eq_true head
        subst key
        have correct := truthful _ List.mem_cons_self
        exact ⟨[],rest,by rw [show bytes = List.ofFn (InputIndexedOracle.sha512 world input) from correct.symm]; rfl,rfl⟩
    · have untouched : touches input entry = false := Bool.eq_false_iff.mpr head
      have tail : seen rest input = true := by
        change (touches input entry || seen rest input) = true at occurred
        simpa only [untouched,Bool.false_or] using occurred
      obtain ⟨before,after,same,fresh⟩ := ih (fun e member => truthful e (List.mem_cons_of_mem _ member)) tail
      refine ⟨entry::before,after,by rw [same]; rfl,?_⟩
      change (touches input entry || seen before input) = false
      rw [untouched,fresh]
      rfl

/-- A later hash of an earlier named context is charged at its first actual
hash, even when the naming input was only started or read with count zero. -/
theorem named_hash_or_observed {A : Type} (program : Program A) (world : World) (position : ℕ) (input : Input)
    (named : InputIndexedOracle.sha512 world input ∈ ContextDigestTargets.targets (runPrefix position program world).run.2)
    (occurred : seen (run program world).run.2 input = true) :
    seen (runPrefix position program world).run.2 input = true ∨ Bad program world := by
  by_cases prior : seen (runPrefix position program world).run.2 input = true
  · exact Or.inl prior
  · apply Or.inr
    obtain ⟨before,after,split,fresh⟩ := first_hash (run program world).run.2 world input (OracleProgram.run_replay program |>.truthful world) occurred
    have found : (run program world).run.2[before.length]? = some (.hash input (List.ofFn (InputIndexedOracle.sha512 world input))) := by
      rw [split,List.getElem?_append_right (by omega),Nat.sub_self]
      rfl
    have old : (runPrefix before.length program world).run.2 = before := by
      rw [ReceiptProgramObservation.history,split,List.take_left]
    have order : position ≤ before.length := by
      by_contra earlier
      have inPrefix : .hash input (List.ofFn (InputIndexedOracle.sha512 world input)) ∈ (runPrefix position program world).run.2 := by
        apply List.mem_of_getElem? (i := before.length)
        rw [ReceiptProgramObservation.history,List.getElem?_take_of_lt (by omega)]
        exact found
      exact prior (List.any_eq_true.mpr ⟨_,inPrefix,by simp [touches]⟩)
    have included : (runPrefix position program world).run.2.Sublist before := by
      rw [ReceiptProgramObservation.history,← old,ReceiptProgramObservation.history]
      have included := (List.take_prefix position ((run program world).run.2.take before.length)).sublist
      simpa only [List.take_take,Nat.min_eq_left order] using included
    have selected : ContextTargetRisk.select OracleProgramMachine.step (runPrefix before.length program world).run = some input := by
      simp only [ContextTargetRisk.select,hash_request program world before.length input _ found,old,fresh,ite_true]
    refine ⟨before.length,?_⟩
    simp only [event,selected,old]
    exact ContextDigestTargets.mono _ _ included named

theorem observed_of_seen (parameters : NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored) (world : World)
    (history : List Observation) (truthful : ObservationReplay.Agrees world history)
    (observed : seen history (GoldContextInput.bytes parameters) = true) :
    (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row parameters) world).run.2.Sublist history := by
  obtain ⟨entry,member,touched⟩ := List.any_eq_true.mp observed
  cases entry with
  | start key => contradiction
  | output key offset values => contradiction
  | hash key bytes =>
    have same : key = GoldContextInput.bytes parameters := of_decide_eq_true touched
    subst key
    have correct := truthful _ member
    rw [GoldContextCollision.context_run,correct]
    exact List.singleton_sublist.mpr member

/-- Actual complete native context computation supplies the occurrence;
its presence in the selected prefix follows outside the target ledger. -/
theorem context_observed_or_bad {A : Type} (program : Program A) (world : World) (position : ℕ)
    (parameters : NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored) (digest : NativeRootMessage.Digest)
    (computed : (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row parameters) world).run.1 = some digest)
    (full : (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row parameters) world).run.2.Sublist (run program world).run.2)
    (named : digest ∈ ContextDigestTargets.targets (runPrefix position program world).run.2) :
    (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row parameters) world).run.2.Sublist
      (runPrefix position program world).run.2 ∨ Bad program world := by
  have present := GoldContextCollision.observed parameters world digest computed _ full
  have occurred : seen (run program world).run.2 (GoldContextInput.bytes parameters) = true :=
    List.any_eq_true.mpr ⟨_,present,by simp [touches]⟩
  have equal : InputIndexedOracle.sha512 world (GoldContextInput.bytes parameters) = digest := by
    rw [GoldContextCollision.context_run] at computed
    exact Option.some.inj computed
  rw [← equal] at named
  rcases named_hash_or_observed program world position _ named occurred with prior | bad
  · exact Or.inl (observed_of_seen parameters world _ (OracleProgram.prefix_replay position program |>.truthful world) prior)
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.ProgramContextTarget
