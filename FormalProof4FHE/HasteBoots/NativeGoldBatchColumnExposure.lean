module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchColumnInputView
public import FormalProof4FHE.HasteBoots.NativeIndexExposureRisk
public import FormalProof4FHE.HasteBoots.NativeGoldBatchColumnRequestLaw
@[expose] public section

/-! Causal selection of response-bound Goldilocks column requests from the
actual pending complete input. No future native work or known receipt is an
argument to selection. Exact local and lifetime charges retain all raw group
responses. Source/parameter ownership, receipt validity and the reduction of
all false native acceptance events remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchColumnExposure
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open NativeIndexExposureRisk (Packet Result)
open NativeGoldBatchColumnInputView (View parse responses responseFrame)
open NativeTranscript (Execution)
open OracleComp OracleSpec MeasureTheory ProbabilityTheory

/-- Only the current pending first read and its complete input are inspected. -/
def selectView {S A : Type} (step : S → OracleMachine.Command S A) (packet : Packet S A) : Option View := do
  let input ← CausalStreamExposure.firstRead step packet
  let view ← parse input
  if view.index.label = NativeGoldBatchColumns.label ∧ 0 < view.index.count.val then some view else none

def select {S A : Type} (profile : Digest) (step : S → OracleMachine.Command S A) (packet : Packet S A) :
    Option NativePrequeryIndexLaw.Request := (selectView step packet).map (fun view => view.index.request profile)

theorem selectView_sound {S A : Type} (step : S → OracleMachine.Command S A) (packet : Packet S A)
    (view : View) (selected : selectView step packet = some view) :
    ∃ input, CausalStreamExposure.firstRead step packet = some input ∧ parse input = some view ∧
      view.index.label = NativeGoldBatchColumns.label ∧ 0 < view.index.count.val := by
  unfold selectView at selected
  obtain ⟨input,first,selected⟩ := Option.bind_eq_some_iff.mp selected
  obtain ⟨decoded,parsed,selected⟩ := Option.bind_eq_some_iff.mp selected
  split at selected
  next label =>
    have equal := Option.some.inj selected
    subst view
    exact ⟨input,first,parsed,label⟩
  next => contradiction

/-- Every request produced by the selector is valid and matches the actual
pending first stream read. No external matching/freshness certificate is used. -/
theorem selected_eligible {S A : Type} (profile : Digest) (step : S → OracleMachine.Command S A)
    (packet : Packet S A) (request : NativePrequeryIndexLaw.Request) (selected : select profile step packet = some request) :
    NativeIndexExposureRisk.eligible step packet request := by
  change (selectView step packet).map (fun view => view.index.request profile) = some request at selected
  obtain ⟨view,decoded,equal⟩ := Option.map_eq_some_iff.mp selected
  subst request
  obtain ⟨input,first,parsed,_⟩ := selectView_sound step packet view decoded
  have sound := NativeGoldBatchColumnInputView.parse_sound input view parsed profile
  refine ⟨sound.2.1,?_⟩
  change CausalStreamExposure.firstRead step packet = some (NativePrequeryIndexLaw.requestInput
    (view.index.request profile).transcript view.index.label view.index.domain view.index.count)
  rw [sound.1]
  exact first

def predicate {S A : Type} (step : S → OracleMachine.Command S A)
    (bad : Packet S A → View → Result → Prop) (packet : Packet S A) (result : Result) : Prop :=
  match selectView step packet with
  | none => False
  | some view => bad packet view result

noncomputable section

def event {S A : Type} (profile : Digest) (step : S → OracleMachine.Command S A)
    (bad : Packet S A → View → Result → Prop) (packet : Packet S A) (world : World) : Prop :=
  NativeIndexExposureRisk.event step (select profile step) (predicate step bad) packet world

def risk {S A : Type} (profile : Digest) (step : S → OracleMachine.Command S A)
    (bad : Packet S A → View → Result → Prop) (packet : Packet S A) : ENNReal :=
  NativeIndexExposureRisk.risk step (select profile step) (predicate step bad) packet

/-- Selection supplies every raw response group to the predicate. -/
theorem event_selected {S A : Type} (profile : Digest) (step : S → OracleMachine.Command S A)
    (bad : Packet S A → View → Result → Prop) (packet : Packet S A) (world : World) (view : View)
    (selected : selectView step packet = some view) :
    event profile step bad packet world ↔ bad packet view (OracleProgram.run (view.index.request profile).program world).run := by
  have picked : select profile step packet = some (view.index.request profile) := by simp only [select,selected,Option.map_some]
  have valid := selected_eligible profile step packet _ picked
  simp only [event,NativeIndexExposureRisk.event,picked,valid,true_and,predicate,selected]

theorem risk_selected {S A : Type} (profile : Digest) (step : S → OracleMachine.Command S A)
    (bad : Packet S A → View → Result → Prop) (packet : Packet S A) (view : View)
    (selected : selectView step packet = some view) :
    risk profile step bad packet =
      Pr{let raw ← $ᵗ (Fin (view.index.count.val*8) → InputIndexedOracle.Byte)}[
        bad packet view (NativePrequeryIndexLaw.outcome (view.index.request profile).transcript
          view.index.label view.index.domain view.index.count raw)] := by
  have picked : select profile step packet = some (view.index.request profile) := by simp only [select,selected,Option.map_some]
  have valid := selected_eligible profile step packet _ picked
  simp only [risk,NativeIndexExposureRisk.risk,picked,valid,ite_true,predicate,selected]
  rfl

/-- All tests share the recovered native ordered vector. This bound does
not require knowing whether the receipt quoted in its parent is valid. -/
theorem shared_risk_bound {S A Test Symbol : Type} [DecidableEq Symbol]
    (profile : Digest) (step : S → OracleMachine.Command S A) (packet : Packet S A) (view : View)
    (selected : selectView step packet = some view) (bits : ℕ) (power : view.index.domain.val = 2^bits)
    (raw claimed : Packet S A → View → Test → Fin (2^bits) → Symbol) (distance : ℕ)
    (witness : ∃ test, distance ≤ hammingDist (raw packet view test) (claimed packet view test)) :
    risk profile step (fun current decoded result => (result.1.bind (fun sample =>
      NativeGoldPcsDraws.typed bits decoded.index.count.val sample.draws)).elim False
        (fun draw => ∀ test, ColumnOpening.Agrees (raw current decoded test) (claimed current decoded test) draw)) packet ≤
      ColumnOpening.missBound (Fin (2^bits)) view.index.count.val distance := by
  have fits : bits ≤ 64 := by
    have bound : 2^bits < 2^64 := power ▸ view.index.domain.isLt
    have small := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp bound
    omega
  rw [risk_selected profile step _ packet view selected]
  simp only [NativePrequeryIndexLaw.outcome,Option.bind_some,power,NativeIndexRequest.ordered_ofFn,
    NativeIndexFirstReadLaw.typed_ofFn,Option.elim_some]
  rw [NativeAtomicIndexLaw.uniform_draws bits view.index.count.val fits
    (fun draw => ∀ test, ColumnOpening.Agrees (raw packet view test) (claimed packet view test) draw)]
  exact ColumnOpening.shared_bound (raw packet view) (claimed packet view) view.index.count.val distance witness

theorem conditional_event {S A : Type} (profile : Digest) (step : S → OracleMachine.Command S A)
    (bad : Packet S A → View → Result → Prop)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) (world : World) :
    (law[|{other | (past other).run = (past world).run}]) {other | event profile step bad (past other).run other} =
      risk profile step bad (past world).run :=
  NativeIndexExposureRisk.conditional_event step (select profile step) (predicate step bad) replay world

theorem averaged_event {S A : Type} (profile : Digest) (step : S → OracleMachine.Command S A)
    (bad : Packet S A → View → Result → Prop)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) :
    law {world | event profile step bad (past world).run world} = ∫⁻ world, risk profile step bad (past world).run ∂law :=
  NativeIndexExposureRisk.averaged_event step (select profile step) (predicate step bad) replay

/-- Correctly framed native nonces are recovered from their pending input,
including all raw responses. Receipt knowledge is not a premise. -/
theorem selectView_native {S A : Type} (step : S → OracleMachine.Command S A) (packet : Packet S A)
    (before : List TranscriptFrame.Frame) (profile : Digest) (domain count : NativeUsizeMessage.Usize)
    (opening : NativeGoldBatchOpening.Opening)
    (valid : NativeIndexRequest.check domain count = true) (positive : 0 < count.val)
    (framed : ∀ frame ∈ NativeIndexInputView.View.frames
      ⟨before++[responseFrame opening],NativeGoldBatchColumns.label,domain,count⟩, TranscriptFrame.Valid frame)
    (first : CausalStreamExposure.firstRead step packet = some (NativeGoldBatchResponseBinding.input
      ⟨TranscriptFrame.encodeMany before,profile⟩ NativeGoldBatchColumns.label domain count opening)) :
    selectView step packet = some ⟨⟨before++[responseFrame opening],NativeGoldBatchColumns.label,domain,count⟩,responses opening⟩ := by
  simp only [selectView,first,Option.bind_eq_bind,Option.bind_some]
  rw [NativeGoldBatchColumnInputView.parse_native before profile NativeGoldBatchColumns.label domain count opening valid framed]
  simp only [Option.bind_some,positive,and_true,ite_true]

/-- The full lifetime statement now uses the actual input parser, rather
than a supplied history-to-request selector. The predicate still needs its
protocol soundness reduction and physical work coupling. -/
theorem lifetime_le {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (profile : Digest) (step : S → OracleMachine.Command S A)
    (bad : Packet S A → View → Result → Prop) (inherited : Set World) :
    law (inherited ∪ {world | ∃ fuel, event profile step bad
      (CausalExposureLifetime.history past initial step fuel world).run world}) ≤
      law inherited + ∫⁻ world, NativeIndexExposureRisk.totalCharge past initial step (select profile step) (predicate step bad) world ∂law :=
  NativeIndexExposureRisk.lifetime_le replay initial step (select profile step) (predicate step bad) inherited
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchColumnExposure
