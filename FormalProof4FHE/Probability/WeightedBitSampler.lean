/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.BoundedUniform
import FormalProof4FHE.Probability.GaussianSamplerTV

/-!
# Compressed weights sampled with bounded fair bits

The retry budget changes the scalar law by at most `2⁻rounds`. All selected
tickets remain valid, including ticket zero on budget exhaustion, so every
stored-outcome invariant holds with probability one. This proves a random-bit
query bound; costs of integer arithmetic and the rest of key generation are
separate obligations.
-/

open OracleComp
open scoped ENNReal

namespace FormalProof4FHE

namespace WeightedSampler.Table

variable {Output : Type}

/-- A table's denominator is positive by construction. -/
instance ticketCountNeZero (table : Table Output) : NeZero table.ticketCount :=
  ⟨Nat.ne_of_gt table.total_pos⟩

/-- Bounded fair-bit implementation of the existing compressed scan. -/
def bitSampler (table : Table Output) (rounds : ℕ) : ProbComp Output :=
  (fun ticket : Fin table.ticketCount =>
    selectList table.entries table.fallback ticket.val) <$>
      BoundedUniform.sampleFin table.ticketCount rounds

theorem coinBound_bitSampler (table : Table Output) (rounds : ℕ) :
    BoundedUniform.CoinBound (table.bitSampler rounds)
      (rounds * BoundedUniform.ticketWidth table.ticketCount) :=
  BoundedUniform.coinBound_map _ (BoundedUniform.coinBound_sampleFin _ _)

/-- Canonical uniform tickets describe the original abstract sampler exactly. -/
theorem evalDist_sampler_eq_uniform (table : Table Output) :
    𝒟[table.sampler] =
      𝒟[(fun ticket : Fin table.ticketCount =>
        selectList table.entries table.fallback ticket.val) <$> ($ᵗ (Fin table.ticketCount))] := by
  have hsize : table.ticketCount - 1 + 1 = table.ticketCount := by
    have hpositive := table.total_pos
    change 0 < table.ticketCount at hpositive
    omega
  let cast : Fin (table.ticketCount - 1 + 1) ≃ Fin table.ticketCount := finCongr hsize
  have hraw : 𝒟[($[0..table.ticketCount - 1] : ProbComp _)] =
      𝒟[$ᵗ (Fin (table.ticketCount - 1 + 1))] := by
    apply evalDist_ext
    intro ticket
    simp only [ProbComp.probOutput_uniformFin, probOutput_uniformSample, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
  have hcast : 𝒟[cast <$> ($[0..table.ticketCount - 1] : ProbComp _)] =
      𝒟[$ᵗ (Fin table.ticketCount)] := by
    rw [evalDist_map, hraw, ← evalDist_map]
    exact evalDist_map_bijective_uniform_cross _ _ cast.bijective
  have hsampler : table.sampler =
      (fun ticket : Fin table.ticketCount =>
        selectList table.entries table.fallback ticket.val) <$>
          (cast <$> ($[0..table.ticketCount - 1] : ProbComp _)) := by
    simp only [sampler, Functor.map_map]
    rfl
  rw [hsampler, evalDist_map, hcast, ← evalDist_map]

theorem tvDist_bitSampler_le (table : Table Output) (rounds : ℕ) :
    tvDist (table.bitSampler rounds) table.sampler ≤ (1 / 2 : ℝ) ^ rounds := by
  calc
    tvDist (table.bitSampler rounds) table.sampler =
        tvDist (table.bitSampler rounds)
          ((fun ticket : Fin table.ticketCount =>
            selectList table.entries table.fallback ticket.val) <$> ($ᵗ (Fin table.ticketCount))) := by
      unfold tvDist
      rw [evalDist_sampler_eq_uniform]
    _ ≤ tvDist (BoundedUniform.sampleFin table.ticketCount rounds) ($ᵗ (Fin table.ticketCount)) :=
      tvDist_map_le _ _ _
    _ ≤ _ := BoundedUniform.tvDist_sampleFin_le _ _

/-- Budget exhaustion does not introduce outcomes outside the stored table. -/
theorem probEvent_bitSampler_eq_one_of_entries (table : Table Output) (rounds : ℕ)
    (event : Output → Prop) (hentries : ∀ entry ∈ table.entries, event entry.1) :
    Pr[event | table.bitSampler rounds] = 1 := by
  rw [bitSampler, probEvent_map]
  apply probEvent_eq_one_iff.2
  constructor
  · simp
  · intro ticket _
    exact selectList_property table.entries table.fallback ticket.val ticket.isLt event hentries

theorem probEvent_bitSampler_eq_zero_of_entries (table : Table Output) (rounds : ℕ)
    (event : Output → Prop) (hentries : ∀ entry ∈ table.entries, ¬ event entry.1) :
    Pr[event | table.bitSampler rounds] = 0 := by
  rw [bitSampler, probEvent_map]
  apply probEvent_eq_zero_iff.2
  intro ticket _
  exact selectList_property table.entries table.fallback ticket.val ticket.isLt
    (fun value => ¬ event value) hentries

end WeightedSampler.Table

namespace WeightedBitSampler

/-- The non-failing `ProbComp` observation preserves total PMF distance.
Mapping `none` to a fixed value is a left inverse on the `some` image. -/
theorem etvDist_liftM_eq_ofReal_tvDist {Output : Type} (fallback : Output)
    (left right : ProbComp Output) :
    (liftM left : PMF Output).etvDist (liftM right) = ENNReal.ofReal (tvDist left right) := by
  let p : PMF Output := liftM left
  let q : PMF Output := liftM right
  have hsome : (Option.some <$> p).etvDist (Option.some <$> q) = p.etvDist q := by
    apply le_antisymm (PMF.etvDist_map_le _ _ _)
    have h := PMF.etvDist_map_le (fun value : Option Output => value.getD fallback)
      (Option.some <$> p) (Option.some <$> q)
    simp only [Functor.map_map, Option.getD_some] at h
    change (id <$> p).etvDist (id <$> q) ≤ (Option.some <$> p).etvDist (Option.some <$> q) at h
    simpa only [id_map] using h
  have hleft : (liftM left : SPMF Output) = liftM p := rfl
  have hright : (liftM right : SPMF Output) = liftM q := rfl
  rw [tvDist, evalDist_def, evalDist_def, hleft, hright]
  simp only [SPMF.tvDist, PMF.tvDist, SPMF.toPMF_liftM]
  rw [ENNReal.ofReal_toReal (PMF.etvDist_ne_top _ _)]
  exact hsome.symm

theorem etvDist_bitSampler_le {Output : Type} (table : WeightedSampler.Table Output)
    (rounds : ℕ) :
    (liftM (table.bitSampler rounds) : PMF Output).etvDist table.outputPMF ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ rounds) := by
  rw [WeightedSampler.Table.outputPMF, etvDist_liftM_eq_ofReal_tvDist table.fallback]
  exact ENNReal.ofReal_le_ofReal (table.tvDist_bitSampler_le rounds)

/-- Fair-bit compilation adds only the bounded-rejection error to the proved
Gaussian approximation, with no modulus-size factor. -/
theorem modular_etvDist_le (modulus width precision rounds : ℕ) [NeZero modulus]
    (hwidth : 0 < width) :
    (liftM ((GaussianIntegerWeights.modularTable modulus width precision).bitSampler rounds) :
      PMF (ZMod modulus)).etvDist
        (ModularGaussian.distribution modulus width (Nat.cast_pos.mpr hwidth)) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ rounds) +
        ENNReal.ofReal (GaussianSamplerTV.approximationBound width precision) :=
  (PMF.etvDist_triangle _ _ _).trans
    (add_le_add (etvDist_bitSampler_le _ _) (GaussianSamplerTV.modular_etvDist_le _ _ _ hwidth))

/-- Squared retry budget for the existing Gaussian parameter family. -/
def familyRounds (dimension : ℕ) : ℕ := (dimension + 1) ^ 2

def familySampler (modulus dimension : ℕ) : ProbComp (ZMod modulus) :=
  (GaussianIntegerWeights.modularTable modulus (dimension + 1)
    (GaussianIntegerWeights.familyPrecision dimension)).bitSampler (familyRounds dimension)

theorem family_ticketWidth_le (modulus dimension : ℕ) :
    BoundedUniform.ticketWidth
        (GaussianIntegerWeights.modularTable modulus (dimension + 1)
          (GaussianIntegerWeights.familyPrecision dimension)).ticketCount ≤
      3 * (dimension + 1) ^ 2 + 1 :=
  BoundedUniform.ticketWidth_le
    (GaussianIntegerWeights.modularTable _ _ _).total_pos
    (GaussianIntegerWeights.family_ticketCount_lt modulus dimension)

/-- The actual scalar implementation uses a polynomial number of fair bits. -/
theorem coinBound_familySampler (modulus dimension : ℕ) :
    BoundedUniform.CoinBound (familySampler modulus dimension)
      ((dimension + 1) ^ 2 * (3 * (dimension + 1) ^ 2 + 1)) := by
  exact (WeightedSampler.Table.coinBound_bitSampler _ _).mono
    (Nat.mul_le_mul_left _ (family_ticketWidth_le modulus dimension))

theorem family_tvDist_le (modulus dimension : ℕ) :
    tvDist (familySampler modulus dimension)
      (GaussianIntegerWeights.modularTable modulus (dimension + 1)
        (GaussianIntegerWeights.familyPrecision dimension)).sampler ≤
      (1 / 2 : ℝ) ^ dimension := by
  apply (WeightedSampler.Table.tvDist_bitSampler_le _ _).trans
  apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
  unfold familyRounds
  nlinarith

theorem family_tvDist_negligible (moduli : ℕ → ℕ) :
    negligible (fun dimension => ENNReal.ofReal
      (tvDist (familySampler (moduli dimension) dimension)
        (GaussianIntegerWeights.modularTable (moduli dimension) (dimension + 1)
          (GaussianIntegerWeights.familyPrecision dimension)).sampler)) :=
  negligible_of_le (fun dimension => ENNReal.ofReal_le_ofReal (family_tvDist_le _ dimension))
    DiscreteGaussianTail.half_pow_negligible

end WeightedBitSampler

end FormalProof4FHE
