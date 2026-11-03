module

public import FormalProof4FHE.HasteBoots.CoefficientTraceWork

@[expose] public section

/-!
# Completed extension assembly retains the sequential byte-work mean

Pure basis assembly changes neither raw coefficient observations nor their
byte costs. Completion is exactly coefficient completion. Work-tail decay
and normalization are inherited from the actual sequential coefficient code.
Production field-constructor and SHA/XOF refinement remain separate.
-/

open OracleSpec OracleComp MeasureTheory
open scoped Classical

namespace FormalProof4FHE.HasteBoots.ExtensionTraceWork

noncomputable section

variable {p degree : ℕ} {K : Type} [AddCommGroup K] [Module (ZMod p) K]
local instance (count : ℕ) : MeasurableSpace
    (Option (Fin count → K) × CanonicalCoefficientVector.Result p (count * degree)) := ⊤

def complete {count : ℕ}
    (result : Option (Fin count → K) × CanonicalCoefficientVector.Result p (count * degree)) : Prop :=
  result.1 ≠ none

/-- Every raw chunk and partial coefficient remains in the completed law. -/
def measure (basis : Module.Basis (Fin degree) (ZMod p) K) (count : ℕ) :=
  CompletedObservationLimit.measure (fun fuel => CanonicalExtensionSampler.program basis fuel count)
    complete (fun _ _ h => CoefficientTraceOrder.extension basis count h)

/-- Incomplete assembly consumes exactly the incomplete coefficient bytes. -/
theorem partial_mean (basis : Module.Basis (Fin degree) (ZMod p) K) (fuel count : ℕ) :
    (∫⁻ value, value ∂𝒟[(fun result => if complete result then 0
      else (CanonicalCoefficientWork.consumedBytes p result.2 : ENNReal)) <$>
        CanonicalExtensionSampler.program basis fuel count]) =
      ∫⁻ value, value ∂𝒟[(fun result => if CoefficientTraceOrder.complete result then 0
        else (CanonicalCoefficientWork.consumedBytes p result : ENNReal)) <$>
          CanonicalCoefficientVector.program p fuel (count * degree)] := by
  rw [CanonicalExtensionSampler.program, Functor.map_map]
  apply congrArg (fun observation : CanonicalCoefficientVector.Result p (count * degree) → ENNReal =>
    ∫⁻ value, value ∂𝒟[observation <$> CanonicalCoefficientVector.program p fuel (count * degree)])
  funext result
  cases tag : result.values <;> simp [complete, CoefficientTraceOrder.complete, tag]

/-- The actual assembly work on unfinished prefixes tends to zero. -/
theorem partial_tends_zero (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K) (count : ℕ) :
    Filter.Tendsto (fun fuel => ∫⁻ value, value ∂𝒟[(fun result => if complete result then 0
      else (CanonicalCoefficientWork.consumedBytes p result.2 : ENNReal)) <$>
        CanonicalExtensionSampler.program basis fuel count]) Filter.atTop (nhds 0) := by
  simp_rw [partial_mean]
  exact CoefficientTraceWork.partial_tends_zero p valid (count * degree)

/-- The completed mean uses the requested element count and basis degree,
counting every raw rejected chunk before coefficient acceptance. -/
theorem expected (valid : 1 < p) [NeZero p] (basis : Module.Basis (Fin degree) (ZMod p) K) (count : ℕ) :
    (∫⁻ result, (CanonicalCoefficientWork.consumedBytes p result.2 : ENNReal) ∂measure basis count) =
      ((count * degree : ℕ) : ENNReal) * CanonicalByteSampler.totalExpectedBytes p := by
  apply CompletedCostTransfer.of_partial_tends_zero
  · simpa only [CanonicalExtensionSampler.expectedBytes] using
      CanonicalCoefficientWork.expectedBytes_tends_to p valid (count * degree)
  · exact partial_tends_zero valid basis count

/-- Pure extension assembly preserves almost-sure completion as well as cost. -/
theorem probability (valid : 1 < p) [NeZero p] (basis : Module.Basis (Fin degree) (ZMod p) K) (count : ℕ) :
    IsProbabilityMeasure (measure basis count) := by
  apply CompletedObservationLimit.probability
  have finite (fuel : ℕ) : Pr{let result ← CanonicalExtensionSampler.program basis fuel count}[complete result] =
      Pr{let result ← CanonicalCoefficientVector.program p fuel (count * degree)}[CoefficientTraceOrder.complete result] := by
    rw [CanonicalExtensionSampler.program, prEvent_map]
    apply prEvent_congr
    intro result
    cases tag : result.values <;> simp [complete, CoefficientTraceOrder.complete, tag]
  simp_rw [finite]
  let := CoefficientTraceWork.probability p valid (count * degree)
  have total := measure_univ (μ := CoefficientTraceWork.measure p (count * degree))
  rw [CoefficientTraceWork.measure, CompletedObservationLimit.measure_apply] at total
  simpa only [Set.mem_univ, and_true] using total

end

end FormalProof4FHE.HasteBoots.ExtensionTraceWork
