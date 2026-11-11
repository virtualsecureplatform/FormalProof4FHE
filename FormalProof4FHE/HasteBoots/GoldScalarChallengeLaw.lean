module
public import FormalProof4FHE.HasteBoots.CausalStreamExposure
public import FormalProof4FHE.HasteBoots.NativeGoldBatchFamilyAvailability
public import FormalProof4FHE.HasteBoots.NativeExtensionFields
public import FormalProof4FHE.HasteBoots.PackedSumcheckProbability
@[expose] public section

/-! The actual shared-budget native collector yields one uniform Goldilocks
extension challenge on first stream exposure. Suspension and rejection remain
in the experiment; no success conditioning or runtime retry cap is introduced. -/
namespace FormalProof4FHE.HasteBoots.GoldScalarChallengeLaw
open NativeFields (Goldilocks goldilocksModulus)
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
open InputIndexedOracle (World law)
open NativeTranscript (FieldPhase)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
open scoped Classical
noncomputable section
local instance : SampleableType Goldilocks3 := SampleableType.ofFintype _

def assemble (coefficients : Fin 3 → Goldilocks) : Goldilocks3 := goldilocksBasis.equivFun.symm coefficients

theorem uniform_assembly (event : Goldilocks3 → Prop) :
    Pr{let coefficients ← $ᵗ (Fin 3 → Goldilocks)}[event (assemble coefficients)] =
      Pr{let value ← $ᵗ Goldilocks3}[event value] :=
  SampleableType.prEvent_uniformSample_equiv goldilocksBasis.equivFun.symm.toEquiv event

def values (fuel : ℕ) (phase : FieldPhase) (world : World) : Option Goldilocks3 :=
  (NativeFieldVectorLaw.values goldilocksModulus fuel 3 phase world).map assemble

theorem conditional_uniform {S A : Type} (step : S → OracleMachine.Command S A)
    {past : World → NativeTranscript.Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) (world : World)
    (dummy : NativeRootMessage.Digest) (fuel : ℕ) (phase : FieldPhase)
    (selected : CausalStreamExposure.firstRead step (past world).run = some phase.pending.input)
    (event : Goldilocks3 → Prop) :
    (law[|{other | (past other).run = (past world).run}]) {other | (values fuel phase other).elim False event} =
      BudgetedUniformSequence.completion (CanonicalCoefficientVector.scalar goldilocksModulus 1) fuel 3 *
        Pr{let value ← $ᵗ Goldilocks3}[event value] := by
  have native := NativeFieldVectorLaw.conditional_uniform replay world NativeGoldColumnAuthentication.encoding dummy NativeMerkleShapeFamily.shape
    (NativeGoldBatchFamilyAvailability.reconstructed dummy (past world).run.2)
    (NativeGoldBatchFamilyAvailability.reconstructed_hash dummy (past world).run.2)
    goldilocksModulus (by decide +kernel) fuel 3 phase
    (CausalStreamExposure.firstRead_fresh step (past world).run phase.pending.input selected world phase.consumed.length)
    (fun coefficients => event (assemble coefficients))
  rw [uniform_assembly] at native
  simpa only [values,Option.elim_map,Function.comp_def] using native

theorem eventual_le_uniform {S A : Type} (step : S → OracleMachine.Command S A)
    {past : World → NativeTranscript.Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) (world : World)
    (dummy : NativeRootMessage.Digest) (phase : FieldPhase)
    (selected : CausalStreamExposure.firstRead step (past world).run = some phase.pending.input)
    (event : Goldilocks3 → Prop) :
    (law[|{other | (past other).run = (past world).run}]) {other | ∃ fuel, (values fuel phase other).elim False event} ≤
      Pr{let value ← $ᵗ Goldilocks3}[event value] := by
  have native := NativeFieldVectorLaw.eventual_le_uniform replay world NativeGoldColumnAuthentication.encoding dummy NativeMerkleShapeFamily.shape
    (NativeGoldBatchFamilyAvailability.reconstructed dummy (past world).run.2)
    (NativeGoldBatchFamilyAvailability.reconstructed_hash dummy (past world).run.2)
    goldilocksModulus (by decide +kernel) 3 phase
    (CausalStreamExposure.firstRead_fresh step (past world).run phase.pending.input selected world phase.consumed.length)
    (fun coefficients => event (assemble coefficients))
  rw [uniform_assembly] at native
  simpa only [values,Option.elim_map,Function.comp_def] using native

/-- The three canonical coordinates make one field element. The error is
D/card(Goldilocks3), not an independent three-lane agreement event. -/
theorem agreement_probability (sent honest : Polynomial Goldilocks3) (degree : ℕ)
    (different : sent ≠ honest) (sentDegree : sent.natDegree ≤ degree) (honestDegree : honest.natDegree ≤ degree) :
    Pr{let value ← $ᵗ Goldilocks3}[sent.eval value = honest.eval value] ≤
      (degree : ENNReal) / (goldilocksModulus^3 : ℕ) := by
  rw [SampleableType.prEvent_uniformSample,← NativeExtensionFields.goldilocks_card]
  apply ENNReal.div_le_div_right
  exact_mod_cast PackedSumcheckProbability.agreement_card sent honest degree different sentDegree honestDegree

theorem eventual_agreement_bound {S A : Type} (step : S → OracleMachine.Command S A)
    {past : World → NativeTranscript.Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) (world : World)
    (dummy : NativeRootMessage.Digest) (phase : FieldPhase)
    (selected : CausalStreamExposure.firstRead step (past world).run = some phase.pending.input)
    (sent honest : Polynomial Goldilocks3) (degree : ℕ) (different : sent ≠ honest)
    (sentDegree : sent.natDegree ≤ degree) (honestDegree : honest.natDegree ≤ degree) :
    (law[|{other | (past other).run = (past world).run}])
      {other | ∃ fuel, (values fuel phase other).elim False (fun value => sent.eval value = honest.eval value)} ≤
        (degree : ENNReal) / (goldilocksModulus^3 : ℕ) :=
  (eventual_le_uniform step replay world dummy phase selected _).trans
    (agreement_probability sent honest degree different sentDegree honestDegree)

end
end FormalProof4FHE.HasteBoots.GoldScalarChallengeLaw
