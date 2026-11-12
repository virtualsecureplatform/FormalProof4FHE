module
public import FormalProof4FHE.HasteBoots.LookupCollectorTrace
@[expose] public section

/-! Original lookup draws witness scalar events on their exact stream input.
Canonical phases erase only irrelevant label/profile metadata. Both compression
and every rejected/accepted offset remain in one all-budget scalar kernel. -/
namespace FormalProof4FHE.HasteBoots.LookupScalarKernel
open InputIndexedOracle (Input World law)
open NativeTranscript (FieldPhase Transcript)
open NativeFields (goldilocksModulus)
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section
local instance : SampleableType Goldilocks3 := SampleableType.ofFintype _

def phase (input : Input) : FieldPhase := ⟨⟨input,fun _ => 0⟩,[],[]⟩

def Event (input : Input) (test : Goldilocks3 → Prop) (world : World) : Prop :=
  ∃ budget, (GoldScalarChallengeLaw.values budget (phase input) world).elim False test

theorem values_congr (fuel : ℕ) (left right : FieldPhase) (world : World)
    (input : left.pending.input = right.pending.input) (cursor : left.consumed.length = right.consumed.length) :
    GoldScalarChallengeLaw.values fuel left world = GoldScalarChallengeLaw.values fuel right world := by
  unfold GoldScalarChallengeLaw.values
  rw [EqualityCollectorInputCongruence.coefficients goldilocksModulus fuel 3 left right world input cursor]

theorem source_value (field : NativeFieldVector.State) (world : World) (history : List NativeTranscript.Observation)
    (source : LookupCollectorTrace.Source field world history) (complete : field.remaining = 0) :
    ∃ budget, GoldScalarChallengeLaw.values budget (phase field.phase.pending.input) world =
      some (TypedFieldRequest.scalarValue goldilocksBasis field.values) := by
  obtain ⟨budget,collected,_⟩ := source
  refine ⟨budget,?_⟩
  rw [← values_congr budget (LookupCollectorTrace.start field) (phase field.phase.pending.input) world rfl rfl]
  unfold GoldScalarChallengeLaw.values NativeFieldVectorLaw.values
  rw [collected]
  simp only [NativeFieldVectorValues.project,complete,ite_true,Option.map_some,Option.some.injEq,Nat.zero_add]
  rfl

theorem decoded_value (field : NativeFieldVector.State) (word : NativeGoldExtensionArithmetic.Word)
    (decoded : NativeGoldLookupProducer.decode field.values = some word) :
    NativeFieldWire.goldExtensionValue word = TypedFieldRequest.scalarValue goldilocksBasis field.values := by
  unfold NativeGoldLookupProducer.decode at decoded
  split at decoded
  next complete =>
    split at decoded
    next valid =>
      cases Option.some.inj decoded
      exact NativeGoldLookupCompleted.fromCoefficients_value field.values complete valid
    next => contradiction
  next => contradiction

theorem source_word (field : NativeFieldVector.State) (world : World) (history : List NativeTranscript.Observation)
    (source : LookupCollectorTrace.Source field world history) (complete : field.remaining = 0)
    (word : NativeGoldExtensionArithmetic.Word) (decoded : NativeGoldLookupProducer.decode field.values = some word) :
    ∃ budget, GoldScalarChallengeLaw.values budget (phase field.phase.pending.input) world = some (NativeFieldWire.goldExtensionValue word) := by
  obtain ⟨budget,collected⟩ := source_value field world history source complete
  exact ⟨budget,by rw [decoded_value field word decoded]; exact collected⟩

theorem draw_value (width fuel : ℕ) (rows : List (List NativeFields.Goldilocks)) (transcript : Transcript)
    (world : World) (draw : NativeLookupChallenge.Draw Goldilocks3)
    (member : draw ∈ (OracleProgram.run (NativeLookupChallenge.request goldilocksBasis 7 width fuel rows transcript) world).run.1.draws) :
    ∃ budget, GoldScalarChallengeLaw.values budget (phase draw.coefficients.phase.pending.input) world = some draw.value := by
  have traced := (LookupCollectorTrace.request width fuel rows transcript world).2 draw member
  obtain ⟨budget,collected⟩ := source_value draw.coefficients world _ traced.1 traced.2
  have valid := (NativeLookupChallenge.request_valid goldilocksBasis 7 width fuel rows transcript world).2 draw member
  exact ⟨budget,by rw [← valid.2.2] at collected; exact collected⟩

theorem of_draw (width fuel : ℕ) (rows : List (List NativeFields.Goldilocks)) (transcript : Transcript)
    (world : World) (draw : NativeLookupChallenge.Draw Goldilocks3)
    (member : draw ∈ (OracleProgram.run (NativeLookupChallenge.request goldilocksBasis 7 width fuel rows transcript) world).run.1.draws)
    (test : Goldilocks3 → Prop) (occurred : test draw.value) : Event draw.coefficients.phase.pending.input test world := by
  obtain ⟨budget,collected⟩ := draw_value width fuel rows transcript world draw member
  exact ⟨budget,by rw [collected]; exact occurred⟩

theorem conditional_bound {S A : Type} (step : S → OracleMachine.Command S A)
    {past : World → NativeTranscript.Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) (world : World)
    (dummy : NativeRootMessage.Digest) (input : Input)
    (selected : CausalStreamExposure.firstRead step (past world).run = some input) (test : Goldilocks3 → Prop) :
    (law[|{other | (past other).run = (past world).run}]) {other | Event input test other} ≤
      Pr{let value ← $ᵗ Goldilocks3}[test value] := by
  exact GoldScalarChallengeLaw.eventual_le_uniform step replay world dummy (phase input) selected test

end
end FormalProof4FHE.HasteBoots.LookupScalarKernel
