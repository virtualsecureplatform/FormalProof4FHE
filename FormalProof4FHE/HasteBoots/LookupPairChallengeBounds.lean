module
public import FormalProof4FHE.HasteBoots.LookupScalarKernel
public import FormalProof4FHE.HasteBoots.TupleLookupPair
@[expose] public section

/-! Causal native scalar kernels for tuple collisions and reciprocal roots.
Every original offset trial is priced before its accepted-domain guard;
neither successful completion nor reciprocal acceptance is normalized. -/
namespace FormalProof4FHE.HasteBoots.LookupPairChallengeBounds
open InputIndexedOracle (Input World law)
open NativeExtensionFields (Goldilocks3)
open NativeFields (Goldilocks goldilocksModulus)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
open scoped Classical
noncomputable section
local instance : SampleableType Goldilocks3 := SampleableType.ofFintype _
local instance : CharP Goldilocks3 goldilocksModulus :=
  charP_of_injective_algebraMap (algebraMap Goldilocks Goldilocks3).injective goldilocksModulus

def Domain {size : ℕ} (table : Fin size → Goldilocks3) (r : Goldilocks3) : Prop :=
  r ≠ 0 ∧ ∀ index, r+table index ≠ 0

variable {S A : Type} (step : S → OracleMachine.Command S A)
    {past : World → NativeTranscript.Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) (world : World)
    (dummy : NativeRootMessage.Digest) (input : Input)
    (selected : CausalStreamExposure.firstRead step (past world).run = some input)

include replay dummy selected

theorem tuple_family {Position : Type} {width size : ℕ}
    (sources : Position → Fin width → Goldilocks) (table : Fin size → Fin width → Goldilocks)
    (bad : ∃ position, ∀ row, sources position ≠ table row) :
    (law[|{other | (past other).run = (past world).run}])
      {other | LookupScalarKernel.Event input (fun y => ∀ position, ∃ row,
        TupleHash.hash y (sources position) = TupleHash.hash y (table row)) other} ≤
      (size : ENNReal)*(((width-1 : ℕ) : ENNReal)/(goldilocksModulus^3 : ℕ)) := by
  exact (LookupScalarKernel.conditional_bound step replay world dummy input selected _).trans
    (by simpa only [NativeExtensionFields.goldilocks_card] using
      TupleHash.family_miss_bound (K := Goldilocks3) sources table bad)

/-- A fixed bad hashed source forces a nonzero reciprocal polynomial. The
root bound applies to one original initialized trial, over all its budgets. -/
theorem reciprocal_root {count size : ℕ} (sources : Fin count → Goldilocks3)
    (table multiplicities : Fin size → Goldilocks3)
    (bad : ∃ index, ∀ row, sources index ≠ table row) (small : count < goldilocksModulus) :
    (law[|{other | (past other).run = (past world).run}])
      {other | LookupScalarKernel.Event input
        (fun r => (ReciprocalPolynomial.numerator sources table multiplicities).eval r = 0) other} ≤
      ((count+size-1 : ℕ) : ENNReal)/(goldilocksModulus^3 : ℕ) := by
  have nonzero := ReciprocalPolynomial.numerator_ne_zero (p := goldilocksModulus) sources table multiplicities bad small
  have positive : 0 < count := by obtain ⟨index,_⟩ := bad; exact Nat.zero_lt_of_lt index.isLt
  simpa only [LookupScalarKernel.Event,Polynomial.eval_zero] using
    GoldScalarChallengeLaw.eventual_agreement_bound step replay world dummy (LookupScalarKernel.phase input) selected
    (ReciprocalPolynomial.numerator sources table multiplicities) 0 (count+size-1) nonzero
    (ReciprocalPolynomial.numerator_degree sources table multiplicities positive) (by simp)

omit replay dummy selected

/-- Accepted-domain reciprocal passage implies the cleared numerator root.
This implication retains arbitrary multiplicities and repeated source rows. -/
theorem passes_root {count size : ℕ} (sources : Fin count → Goldilocks3)
    (table multiplicities : Fin size → Goldilocks3) (r : Goldilocks3)
    (allowed : Domain table r)
    (passed : ReciprocalDetection.Passes sources table multiplicities r) :
    (ReciprocalPolynomial.numerator sources table multiplicities).eval r = 0 := by
  obtain ⟨helpers,valid,total⟩ := passed
  exact ReciprocalPolynomial.helper_identity_implies_root sources table multiplicities helpers r valid allowed.2 total

include replay dummy selected

/-- The native accepted guard can only reduce the original trial event. In
particular this bound has no reciprocal-domain denominator or success floor. -/
theorem reciprocal_passes {count size : ℕ} (sources : Fin count → Goldilocks3)
    (table multiplicities : Fin size → Goldilocks3)
    (bad : ∃ index, ∀ row, sources index ≠ table row) (small : count < goldilocksModulus) :
    (law[|{other | (past other).run = (past world).run}])
      {other | LookupScalarKernel.Event input
        (fun r => Domain table r ∧ ReciprocalDetection.Passes sources table multiplicities r) other} ≤
      ((count+size-1 : ℕ) : ENNReal)/(goldilocksModulus^3 : ℕ) := by
  apply (measure_mono (show {other | LookupScalarKernel.Event input
      (fun r => Domain table r ∧ ReciprocalDetection.Passes sources table multiplicities r) other} ⊆
      {other | LookupScalarKernel.Event input
        (fun r => (ReciprocalPolynomial.numerator sources table multiplicities).eval r = 0) other} from ?_)).trans
    (reciprocal_root step replay world dummy input selected sources table multiplicities bad small)
  rintro other ⟨budget,occurred⟩
  refine ⟨budget,?_⟩
  cases found : GoldScalarChallengeLaw.values budget (LookupScalarKernel.phase input) other with
  | none => rw [found] at occurred; exact occurred.elim
  | some r => rw [found] at occurred; exact passes_root sources table multiplicities r occurred.1 occurred.2

end
end FormalProof4FHE.HasteBoots.LookupPairChallengeBounds
