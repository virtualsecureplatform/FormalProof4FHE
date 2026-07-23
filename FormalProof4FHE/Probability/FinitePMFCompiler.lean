/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import VCVio.EvalDist.TVDist
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Certified Finite Compilation of Probability Mass Functions

An ideal discrete Gaussian is naturally specified as a mathematical `PMF`, while the native TFHE
games consume executable finite `ProbComp` samplers.  This file provides the small, auditable
bridge between those representations.

A `TicketTable` is a nonempty finite vector of outcomes.  Sampling a uniform ticket is executable,
and repeated outcomes encode arbitrary rational probabilities with the common denominator equal
to the table length.  The development proves:

* the exact probability of every output;
* the exact PMF total-variation distance to an arbitrary target PMF;
* a finite pointwise-error bound; and
* a triangle bound between two executable tables certified against the same ideal target.

The certificate is deliberately proof-carrying.  A table generated offline for concrete Gaussian
parameters can be imported as data, and Lean only has to check its finite per-residue errors.  No
irrational ideal probability is silently treated as executable.
-/

open BigOperators OracleComp
open scoped ENNReal

namespace FormalProof4FHE.FinitePMFCompiler

/-- A nonempty finite multiset of uniformly sampled tickets.  If an outcome occurs `k` times in a
table of length `N`, its exact output probability is `k / N`. -/
structure TicketTable (Output : Type) where
  sizePred : ℕ
  tickets : List.Vector Output (sizePred + 1)

namespace TicketTable

variable {Output : Type}

/-- The strictly positive common denominator of the encoded rational distribution. -/
def ticketCount (table : TicketTable Output) : ℕ := table.sizePred + 1

theorem ticketCount_pos (table : TicketTable Output) : 0 < table.ticketCount := by
  simp [ticketCount]

instance instNeZeroTicketCount (table : TicketTable Output) : NeZero table.ticketCount :=
  ⟨Nat.ne_of_gt table.ticketCount_pos⟩

/-- Executable uniform-ticket sampler. -/
def sampler (table : TicketTable Output) : ProbComp Output :=
  $! table.tickets

/-- The output stored at a uniformly sampled ticket index. -/
def ticketValue (table : TicketTable Output) (ticket : Fin table.ticketCount) : Output :=
  table.tickets[ticket]

/-- A ticket-table sampler is literally the deterministic image of its uniform finite index
space.  This presentation is useful for exact collision and fiber-cardinality calculations. -/
theorem sampler_eq_ticketValue_map_uniform (table : TicketTable Output) :
    table.sampler = ticketValue table <$> ($ᵗ (Fin table.ticketCount)) := by
  rfl

/-- Exact output law of the executable sampler. -/
theorem probOutput_sampler [DecidableEq Output]
    (table : TicketTable Output) (value : Output) :
    Pr[= value | table.sampler] =
      (table.tickets.toList.count value : ℝ≥0∞) /
        (table.ticketCount : ℝ≥0∞) := by
  unfold sampler ticketCount
  simpa only [Nat.cast_add, Nat.cast_one] using
    (ProbComp.probOutput_uniformSelectListVector table.tickets value)

/-- Mathematical PMF denoted by the executable ticket sampler. -/
noncomputable def outputPMF (table : TicketTable Output) : PMF Output :=
  liftM table.sampler

/-- The denoted PMF has exactly the rational ticket-count law. -/
theorem outputPMF_apply [DecidableEq Output]
    (table : TicketTable Output) (value : Output) :
    table.outputPMF value =
      (table.tickets.toList.count value : ℝ≥0∞) /
        (table.ticketCount : ℝ≥0∞) := by
  calc
    table.outputPMF value = Pr[= value | table.sampler] := by
      unfold outputPMF
      rw [probOutput_def, evalDist_def]
      exact (SPMF.liftM_apply (liftM table.sampler : PMF Output) value).symm
    _ = _ := table.probOutput_sampler value

/-- Finite extended-TV expression that a certificate checks against an ideal target PMF. -/
noncomputable def certificateError [Fintype Output] [DecidableEq Output]
    (table : TicketTable Output) (target : PMF Output) : ℝ≥0∞ :=
  (∑ value : Output,
      ENNReal.absDiff
        ((table.tickets.toList.count value : ℝ≥0∞) /
          (table.ticketCount : ℝ≥0∞))
        (target value)) / 2

/-- The finite certificate expression is exactly the extended total-variation distance between
the executable table's denotation and the ideal target. -/
theorem etvDist_outputPMF_eq_certificateError
    [Fintype Output] [DecidableEq Output]
    (table : TicketTable Output) (target : PMF Output) :
    (table.outputPMF).etvDist target = table.certificateError target := by
  simp only [PMF.etvDist, certificateError, outputPMF_apply]
  rw [tsum_fintype]

/-- Real-valued form of the exact certificate identity. -/
theorem tvDist_outputPMF_eq_certificateError_toReal
    [Fintype Output] [DecidableEq Output]
    (table : TicketTable Output) (target : PMF Output) :
    PMF.tvDist table.outputPMF target = (table.certificateError target).toReal := by
  simp only [PMF.tvDist, etvDist_outputPMF_eq_certificateError]

/-- A uniform per-outcome error bounds the complete certificate by
`card(Output) * pointwiseBound / 2`. -/
theorem certificateError_le_card_mul
    [Fintype Output] [DecidableEq Output]
    (table : TicketTable Output) (target : PMF Output) (pointwiseBound : ℝ≥0∞)
    (hpointwise : ∀ value : Output,
      ENNReal.absDiff
        ((table.tickets.toList.count value : ℝ≥0∞) /
          (table.ticketCount : ℝ≥0∞))
        (target value) ≤ pointwiseBound) :
    table.certificateError target ≤
      (Fintype.card Output : ℝ≥0∞) * pointwiseBound / 2 := by
  unfold certificateError
  apply ENNReal.div_le_div_right
  calc
    ∑ value : Output,
        ENNReal.absDiff
          ((table.tickets.toList.count value : ℝ≥0∞) /
            (table.ticketCount : ℝ≥0∞))
          (target value) ≤ ∑ _value : Output, pointwiseBound :=
      Finset.sum_le_sum fun value _ => hpointwise value
    _ = (Fintype.card Output : ℝ≥0∞) * pointwiseBound := by simp

/-- A proof-carrying finite rational approximation to an ideal PMF. -/
structure Certificate [Fintype Output] [DecidableEq Output]
    (target : PMF Output) where
  table : TicketTable Output
  bound : ℝ≥0∞
  bound_ne_top : bound ≠ ⊤
  valid : table.certificateError target ≤ bound

namespace Certificate

variable [Fintype Output] [DecidableEq Output]
  {target : PMF Output}

/-- The certified extended-TV bound. -/
theorem etvDist_le (certificate : Certificate target) :
    certificate.table.outputPMF.etvDist target ≤ certificate.bound := by
  rw [certificate.table.etvDist_outputPMF_eq_certificateError]
  exact certificate.valid

/-- The certified real-valued TV bound. -/
theorem tvDist_le (certificate : Certificate target) :
    PMF.tvDist certificate.table.outputPMF target ≤ certificate.bound.toReal := by
  rw [certificate.table.tvDist_outputPMF_eq_certificateError_toReal]
  exact ENNReal.toReal_mono certificate.bound_ne_top certificate.valid

/-- Build a complete certificate from a uniform per-output error proof. -/
noncomputable def ofPointwise
    (table : TicketTable Output) (pointwiseBound : ℝ≥0∞)
    (hpointwiseFinite : pointwiseBound ≠ ⊤)
    (hpointwise : ∀ value : Output,
      ENNReal.absDiff
        ((table.tickets.toList.count value : ℝ≥0∞) /
          (table.ticketCount : ℝ≥0∞))
        (target value) ≤ pointwiseBound) : Certificate target where
  table := table
  bound := (Fintype.card Output : ℝ≥0∞) * pointwiseBound / 2
  bound_ne_top := by
    exact ENNReal.div_ne_top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hpointwiseFinite)
      (by norm_num)
  valid := table.certificateError_le_card_mul target pointwiseBound hpointwise

end Certificate

/-- Monadic TV between the executable samplers is bounded by TV between their total PMF
denotations.  The former observes the latter through VCVio's `Option.some` embedding. -/
theorem tvDist_sampler_le_outputPMF
    [Fintype Output] [DecidableEq Output]
    (left right : TicketTable Output) :
    tvDist left.sampler right.sampler ≤
      PMF.tvDist left.outputPMF right.outputPMF := by
  rw [tvDist, evalDist_def, evalDist_def]
  have hleft : (liftM left.sampler : SPMF Output) = liftM left.outputPMF := by
    unfold outputPMF
    rfl
  have hright : (liftM right.sampler : SPMF Output) = liftM right.outputPMF := by
    unfold outputPMF
    rfl
  rw [hleft, hright]
  simpa only [SPMF.tvDist, SPMF.toPMF_liftM, map_eq_bind_pure_comp,
      Function.comp_def] using
    (PMF.tvDist_map_le Option.some left.outputPMF right.outputPMF)

/-- Mapping one executable ticket sampler and comparing it with the original sampler is bounded
by the corresponding total-variation distance between their mathematical PMF denotations.  This
is the one-table form used to certify translation/smudging costs. -/
theorem tvDist_map_sampler_le_outputPMF
    [Fintype Output] [DecidableEq Output]
    (table : TicketTable Output) (transform : Output → Output) :
    tvDist (transform <$> table.sampler) table.sampler ≤
      PMF.tvDist (transform <$> table.outputPMF) table.outputPMF := by
  rw [tvDist, evalDist_map, evalDist_def]
  have htable : (liftM table.sampler : SPMF Output) = liftM table.outputPMF := by
    unfold outputPMF
    rfl
  rw [htable]
  simp only [SPMF.tvDist, SPMF.toPMF_map, SPMF.toPMF_liftM,
    PMF.monad_map_eq_map, bind_pure_comp]
  rw [show PMF.map (Option.map transform) (PMF.map Option.some table.outputPMF) =
      PMF.map Option.some (PMF.map transform table.outputPMF) by
    rw [PMF.map_comp, PMF.map_comp]
    congr 1]
  exact PMF.tvDist_map_le Option.some
    (PMF.map transform table.outputPMF) table.outputPMF

/-- Two executable ticket tables certified against the same ideal target are close by the sum of
their certified errors.  This is the form consumed by finite sampler-replacement theorems. -/
theorem tvDist_samplers_le_of_common_target
    [Fintype Output] [DecidableEq Output]
    {target : PMF Output} (left right : Certificate target) :
    tvDist left.table.sampler right.table.sampler ≤
      left.bound.toReal + right.bound.toReal := by
  exact (tvDist_sampler_le_outputPMF left.table right.table).trans
    ((PMF.tvDist_triangle left.table.outputPMF target right.table.outputPMF).trans
      (add_le_add left.tvDist_le (by
        rw [PMF.tvDist_comm]
        exact right.tvDist_le)))

end TicketTable

end FormalProof4FHE.FinitePMFCompiler
