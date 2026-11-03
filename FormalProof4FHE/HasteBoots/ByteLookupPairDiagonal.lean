module

public import FormalProof4FHE.HasteBoots.ByteLookupPairWork

@[expose] public section

/-!
# Cofinal approximations of complete raw-byte pair execution

Increasing one common analysis depth covers every combination of the three
operational prefixes. This is cofinality, not a protocol retry budget.
-/

open OracleSpec OracleComp
open scoped Classical BigOperators
open FormalProof4FHE.HasteBoots.ByteLookupPairSampler

namespace FormalProof4FHE.HasteBoots.ByteLookupPairDiagonal

noncomputable section

/-- A common increasing depth covers every triple of finite prefixes. -/
theorem iSup_diagonal (f : ℕ → ℕ → ℕ → ENNReal)
    (grows : ∀ h i o h' i' o', h ≤ h' → i ≤ i' → o ≤ o' → f h i o ≤ f h' i' o') :
    (⨆ n, f n n n) = ⨆ o, ⨆ i, ⨆ h, f h i o := by
  apply le_antisymm
  · refine iSup_le fun n => ?_
    exact le_iSup_of_le n (le_iSup_of_le n (le_iSup_of_le n le_rfl))
  · refine iSup_le fun o => iSup_le fun i => iSup_le fun h => ?_
    let n := max h (max i o)
    have hh : h ≤ n := le_max_left _ _
    have hi : i ≤ n := (le_max_left _ _).trans (le_max_right _ _)
    have ho : o ≤ n := (le_max_right _ _).trans (le_max_right _ _)
    exact (grows h i o n n n hh hi ho).trans (le_iSup (fun n => f n n n) n)

/-- Powers commute with increasing operational approximations. -/
theorem iSup_power (f : ℕ → ENNReal) (grows : Monotone f) (count : ℕ) :
    (⨆ n, f n ^ count) = (⨆ n, f n) ^ count := by
  have powers : Monotone (fun n => f n ^ count) := by
    intro i j ordered
    exact pow_le_pow_left' (grows ordered) count
  exact tendsto_nhds_unique (tendsto_atTop_iSup powers)
    (ENNReal.Tendsto.pow (n := count) (tendsto_atTop_iSup grows))

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  {p degree width size : ℕ} [Module (ZMod p) K] [DecidableEq K] [Fintype K] [SampleableType K] [NeZero p]

theorem probability_mono (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (event : K × K → Prop)
    (h i o h' i' o' : ℕ) (hh : h ≤ h') (hi : i ≤ i') (ho : o ≤ o') :
    Pr{let result ← program basis table h i o}[result.value.elim False event] ≤
      Pr{let result ← program basis table h' i' o'}[result.value.elim False event] := by
  rw [probability valid basis, probability valid basis]
  apply mul_le_mul' (ByteReciprocalLimit.completion_monotone p degree hh)
  apply Finset.sum_le_sum
  intro y _
  apply mul_le_mul_right
  exact (ByteReciprocalLimit.probability_monotone_inner valid basis (hashes table y) o _ hi).trans
    (ByteReciprocalLimit.probability_monotone_outer valid basis (hashes table y) i' _ ho)

/-- Diagonal execution recovers exactly the complete joint pair law. -/
theorem law (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (event : K × K → Prop) :
    (⨆ n, Pr{let result ← program basis table n n n}[result.value.elim False event]) =
      Pr{let pair ← TupleLookupPair.sample (K := K) table}[event pair] := by
  rw [iSup_diagonal _ (probability_mono valid basis table event)]
  exact ByteLookupPairLimit.law valid basis table event

theorem probability_tends (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (event : K × K → Prop) :
    Filter.Tendsto (fun n => Pr{let result ← program basis table n n n}[result.value.elim False event])
      Filter.atTop (nhds (Pr{let pair ← TupleLookupPair.sample (K := K) table}[event pair])) := by
  rw [← law valid basis table event]
  exact tendsto_atTop_iSup (fun i j ordered => probability_mono valid basis table event i i i j j j ordered ordered ordered)

/-- Larger approximations retain the expected work of unfinished trials. -/
theorem work_mono (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F)
    (h i o h' i' o' : ℕ) (hh : h ≤ h') (hi : i ≤ i') (ho : o ≤ o') :
    ByteLookupPairWork.expectedBytes basis table h i o ≤ ByteLookupPairWork.expectedBytes basis table h' i' o' := by
  rw [ByteLookupPairWork.expectedBytes_formula valid basis, ByteLookupPairWork.expectedBytes_formula valid basis]
  apply add_le_add (CanonicalCoefficientWork.expectedBytes_monotone p (1 * degree) hh)
  apply mul_le_mul' (ByteReciprocalLimit.completion_monotone p degree hh)
  apply Finset.sum_le_sum
  intro y _
  apply mul_le_mul_right
  apply (ByteReciprocalLimit.work_monotone_inner valid basis (hashes table y) o hi).trans
  change ByteReciprocalSampler.expectedBytes basis (hashes table y) i' o ≤ _
  rw [ByteReciprocalSampler.expectedBytes_formula valid basis, ByteReciprocalSampler.expectedBytes_formula valid basis]
  exact mul_le_mul_right (Finset.sum_le_sum_of_subset (Finset.range_mono ho)) _

theorem work_law (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) :
    (⨆ n, ByteLookupPairWork.expectedBytes basis table n n n) = ByteLookupPairWork.totalExpectedBytes basis table :=
  iSup_diagonal _ (work_mono valid basis table)

theorem work_tends (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) :
    Filter.Tendsto (fun n => ByteLookupPairWork.expectedBytes basis table n n n) Filter.atTop
      (nhds (ByteLookupPairWork.totalExpectedBytes basis table)) := by
  rw [← work_law valid basis table]
  exact tendsto_atTop_iSup (fun i j ordered => work_mono valid basis table i i i j j j ordered ordered ordered)

end

end FormalProof4FHE.HasteBoots.ByteLookupPairDiagonal
