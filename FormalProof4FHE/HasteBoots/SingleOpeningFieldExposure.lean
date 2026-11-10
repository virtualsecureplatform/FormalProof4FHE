module
public import FormalProof4FHE.HasteBoots.SingleOpeningFieldInputView
public import FormalProof4FHE.HasteBoots.NativeIndexExposureRisk
public import FormalProof4FHE.HasteBoots.SingleOpeningRandomLaw
@[expose] public section

/-! The actual pending field input selects its complete native phase and original raw
single-opening binding. Uniform and all-budget laws use the real observed cache; no
future prepared work, freshness or checkpoint-state certificate is supplied.
Lifetime charges are probability bounds, not physical attacker costs. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningFieldExposure
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open NativeFields (Goldilocks goldilocksModulus)
open NativeIndexExposureRisk (Packet)
open SingleOpeningFieldInputView (View parse typedFrame primeFrame fieldFrame)
open NativeTranscript (Execution Observation)
open OracleComp OracleSpec MeasureTheory ProbabilityTheory
open scoped Classical
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

def select {S A : Type} (step : S → OracleMachine.Command S A) (packet : Packet S A) : Option View :=
  (CausalStreamExposure.firstRead step packet).bind parse

theorem selected_point {S A : Type} (profile : Digest) (step : S → OracleMachine.Command S A)
    (packet : Packet S A) (view : View) (selected : select step packet = some view) :
    CausalStreamExposure.firstRead step packet = some (view.phase profile).pending.input ∧ 0 < view.count.val ∧
      ∀ frame ∈ view.frames, TranscriptFrame.Valid frame := by
  obtain ⟨input,first,parsed⟩ := Option.bind_eq_some_iff.mp selected
  have sound := SingleOpeningFieldInputView.parse_sound input view parsed profile
  exact ⟨by rw [sound.1]; exact first,sound.2⟩

/-- A canonical auxiliary state for the sampler law. It uses precisely the
history's shared hash cache, with no caller-chosen monitor or hash-start premise. -/
def samplerState (log : List Observation) :
    CheckpointExecution.State (Input := Input) (Digest := Digest) NativeMerkleShapeFamily.shape :=
  { CheckpointExecution.empty NativeMerkleShapeFamily.shape with hash := JointHashCache.project log }

/-- The computed native ordered coefficient vector at the real first read. -/
theorem conditional_uniform {S A : Type} (profile : Digest) (step : S → OracleMachine.Command S A)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) (world : World)
    (view : View) (selected : select step (past world).run = some view) (fuel : ℕ)
    (event : (Fin view.count.val → Goldilocks) → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | (NativeFieldVectorLaw.values goldilocksModulus fuel view.count.val (view.phase profile) other).elim False event} =
      BudgetedUniformSequence.completion (CanonicalCoefficientVector.scalar goldilocksModulus 1) fuel view.count.val *
        Pr{let value ← $ᵗ (Fin view.count.val → Goldilocks)}[event value] := by
  have point := (selected_point profile step (past world).run view selected).1
  exact NativeFieldVectorLaw.conditional_uniform replay world NativeGoldColumnAuthentication.encoding (fun _ => 0)
    NativeMerkleShapeFamily.shape (samplerState (past world).run.2) rfl goldilocksModulus (by decide +kernel) fuel view.count.val
    (view.phase profile) (CausalStreamExposure.firstRead_fresh step (past world).run _ point world _) event

/-- Union over all retained native candidate budgets, not a rejection cap. -/
theorem eventual_le_uniform {S A : Type} (profile : Digest) (step : S → OracleMachine.Command S A)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) (world : World)
    (view : View) (selected : select step (past world).run = some view)
    (event : (Fin view.count.val → Goldilocks) → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | ∃ fuel, (NativeFieldVectorLaw.values goldilocksModulus fuel view.count.val (view.phase profile) other).elim False event} ≤
        Pr{let value ← $ᵗ (Fin view.count.val → Goldilocks)}[event value] := by
  have point := (selected_point profile step (past world).run view selected).1
  exact NativeFieldVectorLaw.eventual_le_uniform replay world NativeGoldColumnAuthentication.encoding (fun _ => 0)
    NativeMerkleShapeFamily.shape (samplerState (past world).run.2) rfl goldilocksModulus (by decide +kernel) view.count.val
    (view.phase profile) (CausalStreamExposure.firstRead_fresh step (past world).run _ point world _) event

def event {S A : Type} (profile : Digest) (step : S → OracleMachine.Command S A)
    (bad : (packet : Packet S A) → (view : View) → (Fin view.count.val → Goldilocks) → Prop)
    (packet : Packet S A) (world : World) : Prop :=
  match select step packet with
  | none => False
  | some view => ∃ fuel, (NativeFieldVectorLaw.values goldilocksModulus fuel view.count.val (view.phase profile) world).elim False (bad packet view)

def risk {S A : Type} (step : S → OracleMachine.Command S A)
    (bad : (packet : Packet S A) → (view : View) → (Fin view.count.val → Goldilocks) → Prop) (packet : Packet S A) : ENNReal :=
  match select step packet with
  | none => 0
  | some view => Pr{let value ← $ᵗ (Fin view.count.val → Goldilocks)}[bad packet view value]

theorem conditional_event_le {S A : Type} (profile : Digest) (step : S → OracleMachine.Command S A)
    (bad : (packet : Packet S A) → (view : View) → (Fin view.count.val → Goldilocks) → Prop)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) (world : World) :
    (law[|{other | (past other).run = (past world).run}]) {other | event profile step bad (past other).run other} ≤
      risk step bad (past world).run := by
  calc
    _ = (law[|{other | (past other).run = (past world).run}]) {other | event profile step bad (past world).run other} := by
      apply NativeShakeProjection.conditional_event_congr replay world
      intro other same
      rw [same]
    _ ≤ _ := by
      cases chosen : select step (past world).run with
      | none => simp [event,risk,chosen]
      | some view =>
        simp only [event,risk,chosen]
        exact eventual_le_uniform profile step replay world view chosen (bad (past world).run view)

theorem event_measurable {S A : Type} (profile : Digest) (step : S → OracleMachine.Command S A)
    (bad : (packet : Packet S A) → (view : View) → (Fin view.count.val → Goldilocks) → Prop)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) :
    MeasurableSet {world | event profile step bad (past world).run world} := by
  let := OracleHistoryCharge.histories_countable replay
  have fixed (packet : Packet S A) : MeasurableSet {world | event profile step bad packet world} := by
    cases chosen : select step packet with
    | none => simp [event,chosen]
    | some view =>
      have union : {world | event profile step bad packet world} = ⋃ fuel : ℕ,
          {world | (NativeFieldVectorLaw.values goldilocksModulus fuel view.count.val (view.phase profile) world).elim False (bad packet view)} := by
        ext world
        simp only [event,chosen,Set.mem_ofPred_eq,Set.mem_iUnion]
      rw [union]
      apply MeasurableSet.iUnion
      intro fuel
      simp only [NativeFieldVectorLaw.program_values]
      exact OracleExecutionLaw.event_measurable (OracleProgram.run_replay
        (NativeFieldVectorProgram.program goldilocksModulus fuel view.count.val (view.phase profile)))
        (fun result => result.1.elim False (bad packet view))
  have union : {world | event profile step bad (past world).run world} = ⋃ packet : OracleHistoryCharge.Histories past,
      OracleHistoryCharge.fiber past packet ∩ {world | event profile step bad packet.val world} := by
    ext world
    constructor
    · intro yes
      exact Set.mem_iUnion.mpr ⟨⟨(past world).run,⟨world,rfl⟩⟩,rfl,yes⟩
    · intro yes
      obtain ⟨packet,same,yes⟩ := Set.mem_iUnion.mp yes
      change (past world).run = packet.val at same
      change event profile step bad (past world).run world
      rw [same]
      exact yes
  rw [union]
  exact MeasurableSet.iUnion (fun packet => (OracleHistoryCharge.fiber_measurable replay packet).inter (fixed packet.val))

theorem averaged_event_le {S A : Type} (profile : Digest) (step : S → OracleMachine.Command S A)
    (bad : (packet : Packet S A) → (view : View) → (Fin view.count.val → Goldilocks) → Prop)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) :
    law {world | event profile step bad (past world).run world} ≤ ∫⁻ world, risk step bad (past world).run ∂law := by
  rw [OracleHistoryComposition.average_event replay law _ (event_measurable profile step bad replay)]
  exact lintegral_mono (fun world => conditional_event_le profile step bad replay world)

def totalCharge {P S A : Type} (past : World → Execution P) (initial : P → S)
    (step : S → OracleMachine.Command S A)
    (bad : (packet : Packet S A) → (view : View) → (Fin view.count.val → Goldilocks) → Prop) (world : World) : ENNReal :=
  ∑' fuel : ℕ, risk step bad (CausalExposureLifetime.history past initial step fuel world).run

theorem lifetime_le {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (profile : Digest) (step : S → OracleMachine.Command S A)
    (bad : (packet : Packet S A) → (view : View) → (Fin view.count.val → Goldilocks) → Prop) (inherited : Set World) :
    law (inherited ∪ {world | ∃ fuel, event profile step bad (CausalExposureLifetime.history past initial step fuel world).run world}) ≤
      law inherited + ∫⁻ world, totalCharge past initial step bad world ∂law := by
  have union : {world | ∃ fuel, event profile step bad (CausalExposureLifetime.history past initial step fuel world).run world} =
      ⋃ fuel : ℕ, {world | event profile step bad (CausalExposureLifetime.history past initial step fuel world).run world} := by ext world; simp
  rw [union]
  apply (measure_union_le _ _).trans
  apply add_le_add le_rfl
  calc _ ≤ ∑' fuel : ℕ, law {world | event profile step bad (CausalExposureLifetime.history past initial step fuel world).run world} := measure_iUnion_le _
       _ ≤ ∑' fuel : ℕ, ∫⁻ world, risk step bad (CausalExposureLifetime.history past initial step fuel world).run ∂law := by
         exact ENNReal.tsum_le_tsum (fun fuel => averaged_event_le profile step bad (CausalExposureLifetime.history_replay replay initial step fuel))
       _ = _ := (lintegral_tsum (fun fuel =>
          (OracleExecutionLaw.score_measurable (CausalExposureLifetime.history_replay replay initial step fuel) (risk step bad)).aemeasurable)).symm

end
end FormalProof4FHE.HasteBoots.SingleOpeningFieldExposure
