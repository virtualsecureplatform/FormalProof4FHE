module

public import FormalProof4FHE.HasteBoots.ByteLookupPairSampler

@[expose] public section

/-!
# Joint pair law from all three raw-byte sampling approximations

The reciprocal completion probability may depend on the first challenge.
Finite sums and monotone suprema retain that dependence until all nested
prefixes have been completed. None of these prefixes is a protocol cap.
-/

open OracleSpec OracleComp
open scoped Classical BigOperators
open FormalProof4FHE.HasteBoots.ByteLookupPairSampler

namespace FormalProof4FHE.HasteBoots.ByteLookupPairLimit

noncomputable section

/-- Finite sums commute with increasing operational approximations. -/
theorem sum_iSup_nat {A : Type} [Fintype A] (f : A → ℕ → ENNReal)
    (grows : ∀ a, Monotone (f a)) :
    (⨆ n, ∑ a : A, f a n) = ∑ a : A, ⨆ n, f a n := by
  have total : Monotone (fun n => ∑ a : A, f a n) := by
    intro i j ordered
    exact Finset.sum_le_sum (fun a _ => grows a ordered)
  exact tendsto_nhds_unique (tendsto_atTop_iSup total)
    (tendsto_finsetSum Finset.univ (fun a _ => tendsto_atTop_iSup (grows a)))

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  {p degree width count size : ℕ} [Module (ZMod p) K] [DecidableEq K] [Fintype K] [SampleableType K] [NeZero p]

/-- Completing only the first field draw leaves the exact conditional
reciprocal prefixes, rather than normalizing their challenge-dependent mass. -/
theorem iSup_hash (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (inner outer : ℕ) (event : K × K → Prop) :
    (⨆ hashDepth, Pr{let result ← program basis table hashDepth inner outer}[result.value.elim False event]) =
      ∑ y : K, Pr{let value ← $ᵗ K}[value = y] * conditional basis table inner outer event y := by
  simp_rw [probability valid basis]
  rw [← ENNReal.iSup_mul]
  have complete : (⨆ hashDepth, ByteReciprocalSampler.completion p degree hashDepth) = 1 :=
    tendsto_nhds_unique (tendsto_atTop_iSup (ByteReciprocalLimit.completion_monotone p degree))
      (ByteReciprocalLimit.completion_tends p degree valid)
  rw [complete, one_mul]

/-- The joint event mass is obtained from every operational approximation;
no failed first draw or partially sampled reciprocal candidate is accepted. -/
def eventProbability (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (event : K × K → Prop) : ENNReal :=
  ⨆ outer, ⨆ inner, ⨆ hashDepth,
    Pr{let result ← program basis table hashDepth inner outer}[result.value.elim False event]

/-- The complete byte-backed pair law equals the existing joint lookup law,
including its challenge-dependent accepted reciprocal domain. -/
theorem law (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (event : K × K → Prop) :
    eventProbability basis table event = Pr{let pair ← TupleLookupPair.sample (K := K) table}[event pair] := by
  unfold eventProbability
  simp_rw [iSup_hash valid basis]
  have inner (outer : ℕ) :
      (⨆ inner, ∑ y : K, Pr{let value ← $ᵗ K}[value = y] * conditional basis table inner outer event y) =
        ∑ y : K, Pr{let value ← $ᵗ K}[value = y] *
          (⨆ inner, conditional basis table inner outer event y) := by
    rw [sum_iSup_nat]
    · simp_rw [ENNReal.mul_iSup]
    · intro y i j ordered
      exact mul_le_mul_right (ByteReciprocalLimit.probability_monotone_inner valid basis (hashes table y) outer _ ordered) _
  simp_rw [inner]
  rw [sum_iSup_nat]
  · simp_rw [← ENNReal.mul_iSup]
    rw [ideal_probability]
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    exact ByteReciprocalLimit.law valid basis (hashes table y) (fun r => event (y, r))
  · intro y i j ordered
    apply mul_le_mul_right
    apply iSup_mono
    intro inner
    exact ByteReciprocalLimit.probability_monotone_outer valid basis (hashes table y) inner _ ordered

/-- The unbounded byte pair inherits both lookup soundness losses. -/
theorem single_bound {char : ℕ} [CharP K char] (valid : 1 < p)
    (basis : Module.Basis (Fin degree) (ZMod p) K)
    (sources : Fin count → Fin width → F) (table : Fin size → Fin width → F)
    (multiplicities : Fin size → K) (bad : ∃ index, ∀ entry, sources index ≠ table entry) (small : count < char) :
    eventProbability basis table (TupleLookupPair.Passes sources table multiplicities) ≤
      TupleLookupPair.error (Fintype.card K) width count size := by
  rw [law valid basis]
  exact TupleLookupPair.single_bound sources table multiplicities bad small

/-- A sufficiently large reciprocal domain gives total eventual pair mass,
without placing a retry budget on either coordinate. -/
theorem completion_probability (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (enough : size + 1 < Fintype.card K) :
    eventProbability basis table (fun _ => True) = 1 := by
  rw [law valid basis]
  exact TupleLookupPair.sample_total table enough

end

end FormalProof4FHE.HasteBoots.ByteLookupPairLimit
