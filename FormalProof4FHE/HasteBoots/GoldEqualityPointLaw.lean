module
public import FormalProof4FHE.HasteBoots.GoldScalarChallengeLaw
public import FormalProof4FHE.HasteBoots.LookupInitialArithmetic
@[expose] public section

/-! Joint native equality-point law: consecutive canonical triples form
independent cubic extension elements. One candidate budget covers the whole
vector; the eventual bound retains every suspension and rejected candidate. -/
namespace FormalProof4FHE.HasteBoots.GoldEqualityPointLaw
open NativeFields (Goldilocks goldilocksModulus)
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
open InputIndexedOracle (World law)
open NativeTranscript (FieldPhase)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section
local instance : SampleableType Goldilocks3 := SampleableType.ofFintype _

def coordinates (n : ℕ) : (Fin (n*3) → Goldilocks) ≃ (Fin n → Fin 3 → Goldilocks) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Goldilocks)).trans (Equiv.curry _ _ _)

def assemble (n : ℕ) : (Fin (n*3) → Goldilocks) ≃ (Fin n → Goldilocks3) :=
  (coordinates n).trans (Equiv.piCongrRight (fun _ => goldilocksBasis.equivFun.symm.toEquiv))

theorem assemble_apply (n : ℕ) (values : Fin (n*3) → Goldilocks) (element : Fin n) :
    assemble n values element = goldilocksBasis.equivFun.symm
      (fun coordinate => values (finProdFinEquiv (element,coordinate))) := rfl

theorem uniform_assembly (n : ℕ) (event : (Fin n → Goldilocks3) → Prop) :
    Pr{let coefficients ← $ᵗ (Fin (n*3) → Goldilocks)}[event (assemble n coefficients)] =
      Pr{let point ← $ᵗ (Fin n → Goldilocks3)}[event point] :=
  SampleableType.prEvent_uniformSample_equiv (assemble n) event

def values (n fuel : ℕ) (phase : FieldPhase) (world : World) : Option (Fin n → Goldilocks3) :=
  (NativeFieldVectorLaw.values goldilocksModulus fuel (n*3) phase world).map (assemble n)

theorem conditional_uniform {S A : Type} (step : S → OracleMachine.Command S A)
    {past : World → NativeTranscript.Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) (world : World)
    (dummy : NativeRootMessage.Digest) (n fuel : ℕ) (phase : FieldPhase)
    (selected : CausalStreamExposure.firstRead step (past world).run = some phase.pending.input)
    (event : (Fin n → Goldilocks3) → Prop) :
    (law[|{other | (past other).run = (past world).run}]) {other | (values n fuel phase other).elim False event} =
      BudgetedUniformSequence.completion (CanonicalCoefficientVector.scalar goldilocksModulus 1) fuel (n*3) *
        Pr{let point ← $ᵗ (Fin n → Goldilocks3)}[event point] := by
  have native := NativeFieldVectorLaw.conditional_uniform replay world NativeGoldColumnAuthentication.encoding dummy NativeMerkleShapeFamily.shape
    (NativeGoldBatchFamilyAvailability.reconstructed dummy (past world).run.2)
    (NativeGoldBatchFamilyAvailability.reconstructed_hash dummy (past world).run.2)
    goldilocksModulus (by decide +kernel) fuel (n*3) phase
    (CausalStreamExposure.firstRead_fresh step (past world).run phase.pending.input selected world phase.consumed.length)
    (fun coefficients => event (assemble n coefficients))
  rw [uniform_assembly] at native
  simpa only [values,Option.elim_map,Function.comp_def] using native

theorem eventual_le_uniform {S A : Type} (step : S → OracleMachine.Command S A)
    {past : World → NativeTranscript.Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) (world : World)
    (dummy : NativeRootMessage.Digest) (n : ℕ) (phase : FieldPhase)
    (selected : CausalStreamExposure.firstRead step (past world).run = some phase.pending.input)
    (event : (Fin n → Goldilocks3) → Prop) :
    (law[|{other | (past other).run = (past world).run}]) {other | ∃ fuel, (values n fuel phase other).elim False event} ≤
      Pr{let point ← $ᵗ (Fin n → Goldilocks3)}[event point] := by
  have native := NativeFieldVectorLaw.eventual_le_uniform replay world NativeGoldColumnAuthentication.encoding dummy NativeMerkleShapeFamily.shape
    (NativeGoldBatchFamilyAvailability.reconstructed dummy (past world).run.2)
    (NativeGoldBatchFamilyAvailability.reconstructed_hash dummy (past world).run.2)
    goldilocksModulus (by decide +kernel) (n*3) phase
    (CausalStreamExposure.firstRead_fresh step (past world).run phase.pending.input selected world phase.consumed.length)
    (fun coefficients => event (assemble n coefficients))
  rw [uniform_assembly] at native
  simpa only [values,Option.elim_map,Function.comp_def] using native

/-- The entire fixed Boolean residual is chosen before the fresh native
vector. The extension dimension contributes no independent-lane power. -/
theorem eventual_residual_bound {S A : Type} (step : S → OracleMachine.Command S A)
    {past : World → NativeTranscript.Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) (world : World)
    (dummy : NativeRootMessage.Digest) (n : ℕ) (phase : FieldPhase)
    (selected : CausalStreamExposure.firstRead step (past world).run = some phase.pending.input)
    (residual : MatrixFold.Cube n → Goldilocks3) (bad : ∃ cell, residual cell ≠ 0) :
    (law[|{other | (past other).run = (past world).run}])
      {other | ∃ fuel, (values n fuel phase other).elim False
        (fun point => (∑ cell, PackedEqualityCube.weight point cell * residual cell) = 0)} ≤
      (n : ENNReal) / (goldilocksModulus^3 : ℕ) := by
  apply (eventual_le_uniform step replay world dummy n phase selected _).trans
  have nonzero : ∃ cell, residual ((PackedEqualityCube.bits n).symm cell) ≠ 0 := by
    obtain ⟨cell,bad⟩ := bad
    exact ⟨PackedEqualityCube.bits n cell,by simpa only [Equiv.symm_apply_apply] using bad⟩
  simpa only [PackedEqualityCube.weighted_sum,NativeExtensionFields.goldilocks_card] using
    (PackedZeroEquality.point_bound (fun cell => residual ((PackedEqualityCube.bits n).symm cell)) nonzero)

/-- A completed coefficient reader projects exactly the native consecutive
triple assembly, with no default coordinate changing a completed value. -/
theorem completed_values (n fuel : ℕ) (phase : FieldPhase) (world : World) (field : NativeFieldVector.State)
    (collected : (NativeFieldVector.execute goldilocksModulus fuel (NativeFieldVector.initial phase (n*3)) world).1 = field)
    (complete : field.remaining = 0) :
    values n fuel phase world = some (TypedFieldVector.value goldilocksBasis n field.values) := by
  unfold values NativeFieldVectorLaw.values
  rw [collected]
  simp only [NativeFieldVectorValues.project,complete,ite_true,Option.map_some,Option.some.injEq,Nat.zero_add]
  funext element
  rw [assemble_apply]
  rfl

end
end FormalProof4FHE.HasteBoots.GoldEqualityPointLaw
