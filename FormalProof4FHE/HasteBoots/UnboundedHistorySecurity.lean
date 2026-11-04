module

public import FormalProof4FHE.HasteBoots.SecurityExperiment
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Continuity

@[expose] public section

/-!
# Unrestricted stopping in the complete chronological security experiment

Bad prefixes persist after later rejection. Attacker work includes all work
slots, and its total is the supremum of prefix costs. Bounds at every finite
observation prefix imply the unbounded RiskBound and ExpectedWorkSecurity
contracts without runtime caps, finite-work premises or success floors.
The actual experiment law, per-prefix inequalities, and native work
refinement remain obligations; this module does not certify 128-bit security.
-/

namespace FormalProof4FHE.HasteBoots.UnboundedHistorySecurity

open MeasureTheory
open SecurityExperiment

noncomputable section

variable {Input Output : Type}

local instance : MeasurableSpace (Option (Event Input Output)) := ⊤
local instance : MeasurableSpace (History Input Output) := MeasurableSpace.pi

def badEvent (relation : Input → Output → Prop) : Set (Option (Event Input Output)) :=
  {entry | ∃ input output, entry = some (.submission input output true) ∧ ¬relation input output}

def prefixBad (relation : Input → Output → Prop) (depth : ℕ) : Set (History Input Output) :=
  {history | ∃ time, time < depth ∧ history time ∈ badEvent relation}

theorem prefixBad_measurable (relation : Input → Output → Prop) (depth : ℕ) :
    MeasurableSet (prefixBad relation depth) := by
  have equal : prefixBad relation depth =
      ⋃ time ∈ Finset.range depth, (fun history : History Input Output => history time) ⁻¹' badEvent relation := by
    ext history
    simp [prefixBad]
  rw [equal]
  apply MeasurableSet.biUnion (Finset.range depth).countable_toSet
  intro time _
  exact (measurable_pi_apply time) (show MeasurableSet (badEvent relation) from trivial)

theorem prefixBad_mono (relation : Input → Output → Prop) : Monotone (prefixBad relation) := by
  intro first last ordered history bad
  obtain ⟨time, before, failed⟩ := bad
  exact ⟨time, lt_of_lt_of_le before ordered, failed⟩

/-- Later rejection, idle slots and stopping cannot erase an earlier
accepted false submission. -/
theorem historyBad_union (relation : Input → Output → Prop) :
    {history | HistoryBad relation history} = ⋃ depth, prefixBad relation depth := by
  ext history
  constructor
  · rintro ⟨time, input, output, submitted, falseStatement⟩
    exact Set.mem_iUnion.mpr ⟨time + 1, time, Nat.lt_succ_self time, input, output, submitted, falseStatement⟩
  · intro member
    obtain ⟨depth, time, _, input, output, submitted, falseStatement⟩ := Set.mem_iUnion.mp member
    exact ⟨time, input, output, submitted, falseStatement⟩

theorem historyBad_measurable (relation : Input → Output → Prop) :
    MeasurableSet {history | HistoryBad relation history} := by
  rw [historyBad_union]
  exact MeasurableSet.iUnion (prefixBad_measurable relation)

theorem falseAcceptance_eq_iSup (relation : Input → Output → Prop) (μ : Measure (History Input Output)) :
    falseAcceptance relation μ = ⨆ depth, μ (prefixBad relation depth) := by
  unfold falseAcceptance
  rw [historyBad_union]
  exact (prefixBad_mono relation).measure_iUnion

theorem prefixSteps_mono (actor : Actor) (history : History Input Output) :
    Monotone (prefixSteps actor history) := by
  intro first last ordered
  exact Finset.sum_le_sum_of_subset (Finset.range_mono ordered)

theorem prefixWork_measurable (actor : Actor) (depth : ℕ) :
    Measurable (fun history : History Input Output => (prefixSteps actor history depth : ENNReal)) := by
  simp only [prefixSteps, Nat.cast_sum]
  apply Finset.measurable_sum
  intro time _
  exact (measurable_from_top : Measurable (fun entry : Option (Event Input Output) =>
    ((entry.elim 0 (eventSteps actor) : ℕ) : ENNReal))).comp (measurable_pi_apply time)

/-- Exact equality retains all cost tails, including infinite total work. -/
theorem totalWork_mean (actor : Actor) (μ : Measure (History Input Output)) :
    (∫⁻ history, totalSteps actor history ∂μ) =
      ⨆ depth, ∫⁻ history, (prefixSteps actor history depth : ENNReal) ∂μ := by
  unfold totalSteps
  apply lintegral_iSup (prefixWork_measurable actor)
  intro first last ordered history
  exact Nat.cast_le.mpr (prefixSteps_mono actor history ordered)

/-- Initial risk is preserved explicitly while passing to unrestricted
histories. Prefixes are proof approximations, not bounds on native retries. -/
theorem riskBound_of_prefix (relation : Input → Output → Prop) (μ : Measure (History Input Output))
    (initial rate : ENNReal)
    (bounded : ∀ depth, μ (prefixBad relation depth) ≤
      initial + rate * ∫⁻ history, (prefixSteps .attacker history depth : ENNReal) ∂μ) :
    RiskBound relation μ initial rate := by
  unfold RiskBound
  rw [falseAcceptance_eq_iSup]
  apply iSup_le
  intro depth
  apply (bounded depth).trans
  apply add_le_add_right
  apply mul_le_mul_right
  apply lintegral_mono
  intro history
  exact le_iSup (fun n => (prefixSteps .attacker history n : ENNReal)) depth

/-- Multiplicative expected-work form, allowing both zero success and
infinite mean work without dividing by an acceptance probability. -/
theorem expectedWork_of_prefix (relation : Input → Output → Prop) (μ : Measure (History Input Output))
    (factor : ENNReal)
    (bounded : ∀ depth, factor * μ (prefixBad relation depth) ≤
      ∫⁻ history, (prefixSteps .attacker history depth : ENNReal) ∂μ) :
    factor * falseAcceptance relation μ ≤ expectedAttackerWork μ := by
  rw [falseAcceptance_eq_iSup, ENNReal.mul_iSup]
  apply iSup_le
  intro depth
  exact (bounded depth).trans (lintegral_mono (fun history =>
    le_iSup (fun n => (prefixSteps .attacker history n : ENNReal)) depth))

/-- Exact target interface for any supplied actual experiment and adversary
class. The missing numerical/native prefix bounds remain explicit. -/
theorem expectedWorkSecurity_of_prefix (Adversary : Type)
    (experiment : Adversary → Measure (History Input Output)) (relation : Input → Output → Prop) (bits : ℕ)
    (bounded : ∀ adversary depth, (2 : ENNReal) ^ bits * experiment adversary (prefixBad relation depth) ≤
      ∫⁻ history, (prefixSteps .attacker history depth : ENNReal) ∂experiment adversary) :
    ExpectedWorkSecurity Adversary experiment relation bits := by
  intro adversary
  exact expectedWork_of_prefix relation (experiment adversary) _ (bounded adversary)

end

end FormalProof4FHE.HasteBoots.UnboundedHistorySecurity
