module
public import FormalProof4FHE.HasteBoots.LookupPairChallengeBounds
@[expose] public section

/-! Fixed reciprocal statements on one original scalar stream. The missing
hashed-source guard is part of the event, so zero-event statements need no
chosen witness. This is a primitive kernel, not adaptive statement fixation. -/
namespace FormalProof4FHE.HasteBoots.LookupReciprocalKernel
open InputIndexedOracle (Input World law)
open NativeFields (goldilocksModulus)
open NativeExtensionFields (Goldilocks3)
open MeasureTheory ProbabilityTheory
noncomputable section

def test {count size : ℕ} (sources : Fin count → Goldilocks3)
    (table multiplicities : Fin size → Goldilocks3) (r : Goldilocks3) : Prop :=
  (∃ index, ∀ row, sources index ≠ table row) ∧
    (ReciprocalPolynomial.numerator sources table multiplicities).eval r = 0

def Event {count size : ℕ} (input : Input) (sources : Fin count → Goldilocks3)
    (table multiplicities : Fin size → Goldilocks3) : World → Prop :=
  LookupScalarKernel.Event input (test sources table multiplicities)

/-- All budgets on a fixed original trial are covered without conditioning
on acceptance or dividing by the accepted-domain probability. -/
theorem conditional_bound {S A : Type} (step : S → OracleMachine.Command S A)
    {past : World → NativeTranscript.Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (world : World) (dummy : NativeRootMessage.Digest) (input : Input)
    (selected : CausalStreamExposure.firstRead step (past world).run = some input)
    {count size : ℕ} (sources : Fin count → Goldilocks3) (table multiplicities : Fin size → Goldilocks3)
    (small : count < goldilocksModulus) :
    (law[|{other | (past other).run = (past world).run}])
      {other | Event input sources table multiplicities other} ≤
      ((count+size-1 : ℕ) : ENNReal)/(goldilocksModulus^3 : ℕ) := by
  classical
  by_cases missing : ∃ index, ∀ row, sources index ≠ table row
  · apply (measure_mono (show {other | Event input sources table multiplicities other} ⊆
        {other | LookupScalarKernel.Event input
          (fun r => (ReciprocalPolynomial.numerator sources table multiplicities).eval r = 0) other} from ?_)).trans
      (LookupPairChallengeBounds.reciprocal_root step replay world dummy input selected sources table multiplicities missing small)
    rintro other ⟨budget,occurred⟩
    refine ⟨budget,?_⟩
    cases found : GoldScalarChallengeLaw.values budget (LookupScalarKernel.phase input) other with
    | none => rw [found] at occurred; exact occurred.elim
    | some r => rw [found] at occurred; exact occurred.2
  · have empty : {other | Event input sources table multiplicities other} ⊆ ∅ := by
      rintro other ⟨budget,occurred⟩
      cases found : GoldScalarChallengeLaw.values budget (LookupScalarKernel.phase input) other with
      | none => rw [found] at occurred; exact occurred.elim
      | some r => rw [found] at occurred; exact (missing occurred.1).elim
    exact (measure_mono empty).trans (by simp)

end
end FormalProof4FHE.HasteBoots.LookupReciprocalKernel
