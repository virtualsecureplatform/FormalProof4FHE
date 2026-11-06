module
public import FormalProof4FHE.HasteBoots.CausalStreamExposure
public import FormalProof4FHE.HasteBoots.CausalExposureCoverage
@[expose] public section

/-! Complete-stream coverage at actual causal machine prefixes. Any positive
read, including far-offset and partial reads, has one earliest stream exposure.
The inherited mixed history is retained. This is chronological coverage, not
past-measurability of future native metadata or a physical-work bound. -/
namespace FormalProof4FHE.HasteBoots.CausalStreamCoverage
open InputIndexedOracle (Input World)
open NativeTranscript (Observation)
open CausalStreamExposure (touches seen firstRead)
noncomputable section

def locate (input : Input) : List Observation → Option ℕ
  | [] => none
  | entry :: rest => if touches input entry then some 0 else (locate input rest).map Nat.succ

theorem locate_none (input : Input) (log : List Observation) :
    locate input log = none ↔ seen log input = false := by
  induction log with
  | nil => simp [locate,seen]
  | cons entry rest ih =>
    simp only [locate,seen,List.any_cons] at *
    cases touches input entry <;> simp [ih]

theorem locate_some (input : Input) (log : List Observation) (index : ℕ) :
    locate input log = some index ↔ ∃ before entry after,
      log = before ++ entry :: after ∧ before.length = index ∧
      seen before input = false ∧ touches input entry = true := by
  induction log generalizing index with
  | nil => simp [locate]
  | cons entry rest ih =>
    cases hit : touches input entry with
    | true =>
      simp only [locate,hit,ite_true,Option.some.injEq]
      constructor
      · intro equal
        exact ⟨[],entry,rest,rfl,equal,rfl,hit⟩
      · rintro ⟨before,head,after,split,length,unseen,touched⟩
        cases before with
        | nil => simpa using length
        | cons first before =>
          have same := (List.cons.inj split).1
          subst first
          simp [seen,hit] at unseen
    | false =>
      simp only [locate,hit,Bool.false_eq_true,ite_false]
      constructor
      · intro found
        obtain ⟨position,found,equal⟩ := Option.map_eq_some_iff.mp found
        obtain ⟨before,head,after,split,length,unseen,touched⟩ := (ih position).mp found
        exact ⟨entry::before,head,after,by simp [split],by simp [length,← equal],by simpa [seen,hit] using unseen,touched⟩
      · rintro ⟨before,head,after,split,length,unseen,touched⟩
        cases before with
        | nil =>
          have same := (List.cons.inj split).1
          subst head
          rw [hit] at touched
          contradiction
        | cons first before =>
          obtain ⟨same,tail⟩ := List.cons.inj split
          subst first
          have earlier : seen before input = false := by simpa [seen,hit] using unseen
          rw [(ih before.length).mpr ⟨before,head,after,tail,rfl,earlier,touched⟩]
          simpa using congrArg some length

theorem locate_lt (input : Input) (log : List Observation) (index : ℕ)
    (found : locate input log = some index) : index < log.length := by
  obtain ⟨before,entry,after,rfl,rfl,_,_⟩ := (locate_some input log index).mp found
  simp

theorem seen_append (input : Input) (first later : List Observation) :
    seen (first++later) input = (seen first input || seen later input) := by
  simp only [seen,List.any_append]

theorem before_unseen (input : Input) (log : List Observation) (index : ℕ)
    (found : locate input log = some index) : seen (log.take index) input = false := by
  obtain ⟨before,entry,after,rfl,rfl,unseen,_⟩ := (locate_some input log index).mp found
  simpa only [List.take_left] using unseen

theorem locate_append (input : Input) (first later : List Observation) :
    locate input (first++later) = match locate input first with
      | some index => some index
      | none => (locate input later).map (fun index => first.length+index) := by
  induction first with
  | nil => simp [locate]
  | cons entry rest ih =>
    simp only [List.cons_append,locate]
    split
    · rfl
    · rw [ih]
      cases early : locate input rest <;> cases late : locate input later <;> simp [Nat.add_assoc,Nat.add_comm]

theorem locate_take_succ (input : Input) (log : List Observation) (index : ℕ)
    (found : locate input log = some index) : locate input (log.take (index+1)) = some index := by
  obtain ⟨before,entry,after,split,length,unseen,touched⟩ := (locate_some input log index).mp found
  apply (locate_some input _ index).mpr
  refine ⟨before,entry,[],?_,length,unseen,touched⟩
  rw [split,← length]
  simp [List.take_append]

theorem firstRead_of_next_touch {S A : Type} (step : S → OracleMachine.Command S A)
    (history : (S ⊕ A) × List Observation) (world : World) (input : Input)
    (unseen : seen history.2 input = false)
    (hit : locate input (OracleProgram.run (OracleMachine.resume step 1 history.1) world).run.2 = some 0) :
    firstRead step history = some input := by
  rcases history with ⟨current,log⟩
  cases current with
  | inr value => cases hit
  | inl state =>
    cases selected : step state with
    | done value =>
      rw [OracleMachine.resume,OracleMachine.take,selected] at hit
      cases hit
    | start key next =>
      rw [OracleMachine.resume,OracleMachine.take,selected] at hit
      change locate input (.start key :: (OracleProgram.run (OracleMachine.take step 0 next) world).run.2) = _ at hit
      simp [CausalExposureCoverage.take_zero_log,locate,touches] at hit
    | hash key next =>
      rw [OracleMachine.resume,OracleMachine.take,selected] at hit
      change locate input (.hash key (List.ofFn (InputIndexedOracle.sha512 world key)) ::
        (OracleProgram.run (OracleMachine.take step 0 (next (InputIndexedOracle.sha512 world key))) world).run.2) = _ at hit
      simp [CausalExposureCoverage.take_zero_log,locate,touches] at hit
    | read key offset count next =>
      rw [OracleMachine.resume,OracleMachine.take,selected] at hit
      change locate input (.output key offset (InputIndexedOracle.bytes world key offset count) ::
        (OracleProgram.run (OracleMachine.take step 0 (next (InputIndexedOracle.bytes world key offset count))) world).run.2) = _ at hit
      rw [CausalExposureCoverage.take_zero_log] at hit
      have touched : touches input (.output key offset (InputIndexedOracle.bytes world key offset count)) = true := by
        cases yes : touches input (.output key offset (InputIndexedOracle.bytes world key offset count)) <;> simp_all [locate]
      have info : key = input ∧ 0 < count := by
        simpa only [touches,InputIndexedOracle.bytes_length,decide_eq_true_eq] using touched
      rcases info with ⟨rfl,positive⟩
      simp [firstRead,CausalSeedExposure.request,selected,positive,unseen]

/-- Even a target selected retrospectively has an actual chronological first
stream read. No seed-window restriction is imposed on that read. -/
theorem selected_at_first_exposure {S A : Type} (step : S → OracleMachine.Command S A)
    (fuel index : ℕ) (initial : S) (world : World) (input : Input) (prior : List Observation)
    (inherited : seen prior input = false)
    (first : locate input (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2 = some index) :
    firstRead step ((OracleProgram.run (OracleMachine.take step index initial) world).run.1,
      prior ++ (OracleProgram.run (OracleMachine.take step index initial) world).run.2) = some input := by
  have indexLt := (locate_lt input _ index first).trans_le (OracleMachineExposure.log_length_le step fuel initial world)
  have fresh : seen (OracleProgram.run (OracleMachine.take step index initial) world).run.2 input = false := by
    rw [OracleMachineExposure.log_take step index fuel (by omega) initial world]
    exact before_unseen input _ index first
  have length : (OracleProgram.run (OracleMachine.take step index initial) world).run.2.length = index := by
    rw [OracleMachineExposure.log_take step index fuel (by omega) initial world,List.length_take]
    exact Nat.min_eq_left (Nat.le_of_lt (locate_lt input _ index first))
  have next := locate_take_succ input _ index first
  rw [← OracleMachineExposure.log_take step (index+1) fuel (by omega) initial world] at next
  rw [OracleMachine.take_resume step index 1 initial,OracleProgram.run_bind,ObservationReplay.run_bind] at next
  rw [locate_append,(locate_none input _).mpr fresh] at next
  obtain ⟨position,found,equal⟩ := Option.map_eq_some_iff.mp next
  have zero : position = 0 := by rw [length] at equal; omega
  rw [zero] at found
  exact firstRead_of_next_touch step _ world input (by rw [seen_append,inherited,fresh]; rfl) found

/-- Every stream touched by a finite prefix was either already touched in
the inherited history or is selected at a real earlier machine prefix. -/
theorem coverage {P S A : Type} (past : World → NativeTranscript.Execution P) (initial : P → S)
    (step : S → OracleMachine.Command S A) (fuel : ℕ) (world : World) (input : Input)
    (touched : seen (CausalExposureLifetime.history past initial step fuel world).run.2 input = true) :
    seen (past world).run.2 input = true ∨ ∃ index < fuel,
      firstRead step (CausalExposureLifetime.history past initial step index world).run = some input := by
  cases inherited : seen (past world).run.2 input with
  | true => exact Or.inl rfl
  | false =>
    have later : seen (OracleProgram.run (OracleMachine.take step fuel (initial (past world).run.1)) world).run.2 input = true := by
      rw [CausalExposureLifetime.history_run,seen_append,inherited] at touched
      exact touched
    cases found : locate input (OracleProgram.run (OracleMachine.take step fuel (initial (past world).run.1)) world).run.2 with
    | none => rw [(locate_none _ _).mp found] at later; contradiction
    | some index =>
      refine Or.inr ⟨index,(locate_lt input _ index found).trans_le (OracleMachineExposure.log_length_le step fuel _ world),?_⟩
      rw [CausalExposureLifetime.history_run]
      exact selected_at_first_exposure step fuel index _ world input _ inherited found
end
end FormalProof4FHE.HasteBoots.CausalStreamCoverage
