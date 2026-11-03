module

public import FormalProof4FHE.HasteBoots.ByteLookupPairLimit

@[expose] public section

/-!
# Work of the raw-byte joint pair sampler

Every first-challenge byte is charged, including on suspension. A completed
first challenge starts the reciprocal program for its actual hashed table.
The resulting expected work averages the distinct reciprocal domains; no
independence between the first challenge and its reciprocal work is used.
-/

open OracleSpec OracleComp MeasureTheory
open scoped Classical BigOperators
open FormalProof4FHE.HasteBoots.ByteLookupPairSampler

namespace FormalProof4FHE.HasteBoots.ByteLookupPairWork

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  {p degree width size : ℕ} [Module (ZMod p) K] [DecidableEq K] [Fintype K] [SampleableType K] [NeZero p]

def consumedBytes (result : Result p degree K) : ℕ :=
  ByteReciprocalSampler.cost result.hashTrial + result.offsetTrials.elim 0 ByteReciprocalSampler.consumedBytes

def expectedBytes (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (hashDepth inner outer : ℕ) : ENNReal :=
  ∫⁻ value, value ∂𝒟[(fun result => (consumedBytes result : ENNReal)) <$> program basis table hashDepth inner outer]

private theorem expected_const {B : Type} (program : ProbComp B) (cost : ENNReal) :
    (∫⁻ value, value ∂𝒟[(fun _ => cost) <$> program]) = cost := by
  let _ : MeasurableSpace B := ⊤
  rw [lintegral_id_evalDist_map]
  simp

/-- Exact finite work retains unfinished draws and the first-challenge
completion gate before taking the average of conditional reciprocal work. -/
theorem expectedBytes_formula (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (hashDepth inner outer : ℕ) :
    expectedBytes basis table hashDepth inner outer = CanonicalCoefficientWork.expectedBytes p hashDepth (1 * degree) +
      ByteReciprocalSampler.completion p degree hashDepth *
        ∑ y : K, Pr{let value ← $ᵗ K}[value = y] * ByteReciprocalSampler.expectedBytes basis (hashes table y) inner outer := by
  rw [expectedBytes, program, lintegral_id_evalDist_map_bind]
  let continuation := fun y : K => ByteReciprocalSampler.expectedBytes basis (hashes table y) inner outer
  have point : ∀ first : ByteReciprocalSampler.Trial p degree K,
      (∫⁻ value, value ∂𝒟[(fun result : Result p degree K => (consumedBytes result : ENNReal)) <$>
        (match ByteReciprocalSampler.candidate first with
         | none => pure (⟨none, first, none⟩ : Result p degree K)
         | some y => finish first y <$> ByteReciprocalSampler.program basis (hashes table y) inner outer)]) =
      (ByteReciprocalSampler.cost first : ENNReal) + (ByteReciprocalSampler.candidate first).elim 0 continuation := by
    intro first
    cases ByteReciprocalSampler.candidate first with
    | none => simp [consumedBytes, evalDist_pure]
    | some y =>
      simp only [Functor.map_map, consumedBytes, finish, Option.elim_some, Nat.cast_add]
      rw [lintegral_id_evalDist_map_add, expected_const]
      rfl
  have observed := congrArg (fun observation : ByteReciprocalSampler.Trial p degree K → ENNReal =>
    ∫⁻ value, value ∂𝒟[observation <$> ByteReciprocalSampler.step basis hashDepth]) (funext point)
  refine observed.trans ?_
  rw [lintegral_id_evalDist_map_add]
  change OptionalRejectionWork.headCost (ByteReciprocalSampler.step basis hashDepth) ByteReciprocalSampler.cost + _ = _
  rw [ByteReciprocalSampler.head_cost]
  congr 1
  have kernel : ∀ event : K → Prop,
      Pr{let candidate ← ByteReciprocalSampler.candidate <$> ByteReciprocalSampler.step basis hashDepth}[candidate.elim False event] =
      ByteReciprocalSampler.completion p degree hashDepth * Pr{let value ← $ᵗ K}[event value] := by
    intro event
    simpa only [prEvent_map] using ByteReciprocalSampler.candidate_law valid basis hashDepth event
  have weighted := OptionalUniformSequence.successful_expectation
    (ByteReciprocalSampler.candidate <$> ByteReciprocalSampler.step basis hashDepth)
    (ByteReciprocalSampler.completion p degree hashDepth) kernel continuation
  rw [Functor.map_map] at weighted
  refine weighted.trans ?_
  congr 1
  let _ : MeasurableSpace K := ⊤
  rw [lintegral_id_evalDist_map, lintegral_evalDist_eq_tsum, tsum_fintype]

/-- Completing the first draw retains unconditional work on all failed and
unfinished first trials, as well as the conditional continuation average. -/
theorem work_iSup_hash (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (inner outer : ℕ) :
    (⨆ hashDepth, expectedBytes basis table hashDepth inner outer) =
      ByteReciprocalLimit.fieldCost p degree +
        ∑ y : K, Pr{let value ← $ᵗ K}[value = y] * ByteReciprocalSampler.expectedBytes basis (hashes table y) inner outer := by
  have grows : Monotone (fun hashDepth => expectedBytes basis table hashDepth inner outer) := by
    intro i j ordered
    simp only [expectedBytes_formula valid basis]
    have costs := CanonicalCoefficientWork.expectedBytes_monotone p (1 * degree) ordered
    have complete := ByteReciprocalLimit.completion_monotone p degree ordered
    gcongr
  have continuation := ENNReal.Tendsto.mul (ByteReciprocalLimit.completion_tends p degree valid)
    (Or.inl (by simp))
    (tendsto_const_nhds (x := ∑ y : K, Pr{let value ← $ᵗ K}[value = y] *
      ByteReciprocalSampler.expectedBytes basis (hashes table y) inner outer)) (Or.inr (by simp))
  have total := (CanonicalCoefficientWork.expectedBytes_tends_to p valid (1 * degree)).add continuation
  apply tendsto_nhds_unique (tendsto_atTop_iSup grows)
  simpa only [expectedBytes_formula valid basis, one_mul, ByteReciprocalLimit.fieldCost] using total

/-- Raw-byte work includes both sampling stages and all nested approximations. -/
def totalExpectedBytes (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) : ENNReal :=
  ⨆ outer, ⨆ inner, ⨆ hashDepth, expectedBytes basis table hashDepth inner outer

/-- Exact work averages the actual reciprocal domain for each hash challenge.
Duplicate hashed poles affect this average through their true set cardinality. -/
theorem totalExpectedBytes_eq (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) :
    totalExpectedBytes basis table = ByteReciprocalLimit.fieldCost p degree +
      ∑ y : K, Pr{let value ← $ᵗ K}[value = y] * (ByteReciprocalLimit.fieldCost p degree *
        ((Fintype.card K : ENNReal) / (ReciprocalDetection.allowed (hashes table y)).card)) := by
  unfold totalExpectedBytes
  simp_rw [work_iSup_hash valid basis, ← ENNReal.add_iSup]
  congr 1
  have inner (outer : ℕ) :
      (⨆ inner, ∑ y : K, Pr{let value ← $ᵗ K}[value = y] * ByteReciprocalSampler.expectedBytes basis (hashes table y) inner outer) =
        ∑ y : K, Pr{let value ← $ᵗ K}[value = y] *
          (⨆ inner, ByteReciprocalSampler.expectedBytes basis (hashes table y) inner outer) := by
    rw [ByteLookupPairLimit.sum_iSup_nat]
    · simp_rw [ENNReal.mul_iSup]
    · intro y i j ordered
      exact mul_le_mul_right (ByteReciprocalLimit.work_monotone_inner valid basis (hashes table y) outer ordered) _
  simp_rw [inner]
  rw [ByteLookupPairLimit.sum_iSup_nat]
  · simp_rw [← ENNReal.mul_iSup]
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    exact ByteReciprocalLimit.totalExpectedBytes_eq valid basis (hashes table y)
  · intro y i j ordered
    apply mul_le_mul_right
    apply iSup_mono
    intro inner
    rw [ByteReciprocalSampler.expectedBytes_formula valid basis, ByteReciprocalSampler.expectedBytes_formula valid basis]
    exact mul_le_mul_right (Finset.sum_le_sum_of_subset (Finset.range_mono ordered)) _

/-- Public work bound uses the size bound for every challenge while the exact
law above retains collisions and duplicate poles. -/
theorem totalExpectedBytes_bound (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) :
    totalExpectedBytes basis table ≤ ByteReciprocalLimit.fieldCost p degree *
      (1 + (Fintype.card K : ENNReal) / ((Fintype.card K - size - 1 : ℕ) : ENNReal)) := by
  rw [totalExpectedBytes_eq valid basis, mul_add, mul_one]
  apply add_le_add_right
  calc _ ≤ ∑ y : K, Pr{let value ← $ᵗ K}[value = y] * (ByteReciprocalLimit.fieldCost p degree *
        ((Fintype.card K : ENNReal) / ((Fintype.card K - size - 1 : ℕ) : ENNReal))) := by
          apply Finset.sum_le_sum
          intro y _
          gcongr
          exact_mod_cast ReciprocalDetection.allowed_card_lower (hashes table y)
       _ = _ := by
          have weights : (∑ y : K, Pr{let value ← $ᵗ K}[value = y]) = 1 := by
            simpa only [tsum_fintype] using tsum_prEvent_eq_one ($ᵗ K)
          rw [← Finset.sum_mul, weights, one_mul]

end

end FormalProof4FHE.HasteBoots.ByteLookupPairWork
