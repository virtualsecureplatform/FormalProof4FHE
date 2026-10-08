/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.FinitePMFCompiler

/-!
# Sampling compressed integer weights

A stored list contains one outcome/weight pair per entry. One uniform ticket
is interpreted by a linear scan and subtraction, without allocating a list of
repeated tickets. A proof-only expansion identifies the exact rational output
law with the existing finite PMF compiler. A weight denominator may be large
without increasing the number of stored entries or the number of scan steps.
Weight generation and a machine-bit cost model remain separate obligations.
-/

open OracleComp
open scoped BigOperators ENNReal

namespace FormalProof4FHE.WeightedSampler

variable {Output : Type}

/-- Total number of abstract tickets, represented by one natural number. -/
def totalWeight : List (Output × ℕ) → ℕ
  | [] => 0
  | entry :: rest => entry.2 + totalWeight rest

/-- Cumulative weighted selection. The fallback is used only for an invalid ticket. -/
def selectList (entries : List (Output × ℕ)) (fallback : Output) (ticket : ℕ) : Output :=
  match entries with
  | [] => fallback
  | (value, weight) :: rest =>
    if ticket < weight then value else selectList rest fallback (ticket - weight)

/-- Number of abstract tickets assigned to an outcome, allowing duplicate entries. -/
def outcomeWeight [DecidableEq Output] : List (Output × ℕ) → Output → ℕ
  | [], _ => 0
  | (value, weight) :: rest, output =>
    (if value = output then weight else 0) + outcomeWeight rest output

/-- Semantic expansion used only in proofs. Executable sampling never invokes it. -/
noncomputable def expandedTickets : List (Output × ℕ) → List Output
  | [] => []
  | (value, weight) :: rest => List.replicate weight value ++ expandedTickets rest

theorem length_expandedTickets (entries : List (Output × ℕ)) :
    (expandedTickets entries).length = totalWeight entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨value, weight⟩
    simp only [expandedTickets, List.length_append, List.length_replicate, totalWeight, ih]

theorem count_expandedTickets [DecidableEq Output] (entries : List (Output × ℕ)) (output : Output) :
    (expandedTickets entries).count output = outcomeWeight entries output := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨value, weight⟩
    simp [expandedTickets, outcomeWeight, ih, List.count_replicate]

/-- Every valid ticket selects exactly its entry in the semantic expansion. -/
theorem selectList_eq_get_expandedTickets (entries : List (Output × ℕ)) (fallback : Output)
    (ticket : ℕ) (hticket : ticket < totalWeight entries) :
    selectList entries fallback ticket =
      (expandedTickets entries)[ticket]'(by rw [length_expandedTickets]; exact hticket) := by
  induction entries generalizing ticket with
  | nil => simp [totalWeight] at hticket
  | cons entry rest ih =>
    rcases entry with ⟨value, weight⟩
    by_cases hhead : ticket < weight
    · simp [selectList, expandedTickets, hhead, List.length_replicate]
    · have hrest : ticket - weight < totalWeight rest := by
        simp only [totalWeight] at hticket
        omega
      simp only [selectList, expandedTickets, List.getElem_append,
        List.length_replicate, hhead, if_false]
      exact ih (ticket - weight) hrest

/-- Instrument the same selection branches with the number of entries inspected. -/
def selectCounted (entries : List (Output × ℕ)) (fallback : Output) (ticket : ℕ) : Output × ℕ :=
  match entries with
  | [] => (fallback, 0)
  | (value, weight) :: rest =>
    if ticket < weight then (value, 1) else
      let next := selectCounted rest fallback (ticket - weight)
      (next.1, next.2 + 1)

theorem selectCounted_value (entries : List (Output × ℕ)) (fallback : Output) (ticket : ℕ) :
    (selectCounted entries fallback ticket).1 = selectList entries fallback ticket := by
  induction entries generalizing ticket with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨value, weight⟩
    by_cases hhead : ticket < weight <;> simp [selectCounted, selectList, hhead, ih]

/-- Every draw inspects at most the stored number of entries, independently of the denominator. -/
theorem selectCounted_steps_le (entries : List (Output × ℕ)) (fallback : Output) (ticket : ℕ) :
    (selectCounted entries fallback ticket).2 ≤ entries.length := by
  induction entries generalizing ticket with
  | nil => exact le_rfl
  | cons entry rest ih =>
    rcases entry with ⟨value, weight⟩
    by_cases hhead : ticket < weight
    · simp [selectCounted, hhead]
    · simpa only [selectCounted, hhead, if_false, List.length_cons] using
        Nat.add_le_add_right (ih (ticket - weight)) 1

/-- A property of all stored outcomes holds for every valid ticket; the fallback is irrelevant. -/
theorem selectList_property (entries : List (Output × ℕ)) (fallback : Output) (ticket : ℕ)
    (hticket : ticket < totalWeight entries) (property : Output → Prop)
    (hentries : ∀ entry ∈ entries, property entry.1) :
    property (selectList entries fallback ticket) := by
  induction entries generalizing ticket with
  | nil => simp [totalWeight] at hticket
  | cons entry rest ih =>
    rcases entry with ⟨value, weight⟩
    by_cases hhead : ticket < weight
    · simpa only [selectList, hhead, if_true] using hentries (value, weight) (by simp)
    · have hrest : ticket - weight < totalWeight rest := by
        simp only [totalWeight] at hticket
        omega
      simp only [selectList, hhead, if_false]
      exact ih (ticket - weight) hrest (fun entry hentry ↦ hentries entry (by simp [hentry]))

/-- Bounded stored weights give a bound on the total denominator. -/
theorem totalWeight_le_length_mul (entries : List (Output × ℕ)) (bound : ℕ)
    (hentries : ∀ entry ∈ entries, entry.2 ≤ bound) :
    totalWeight entries ≤ entries.length * bound := by
  induction entries with
  | nil => simp [totalWeight]
  | cons entry rest ih =>
    have hhead := hentries entry (by simp)
    have hrest := ih (fun candidate hcandidate ↦ hentries candidate (by simp [hcandidate]))
    simp only [totalWeight, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- The uniform ticket needs at most `precision + entries.length` binary digits when each
stored weight is at most `2^precision`. This bounds integer sizes, not bit-operation cost. -/
theorem totalWeight_lt_two_pow (entries : List (Output × ℕ)) (precision : ℕ)
    (hentries : ∀ entry ∈ entries, entry.2 ≤ 2 ^ precision) :
    totalWeight entries < 2 ^ (precision + entries.length) := by
  calc
    _ ≤ entries.length * 2 ^ precision := totalWeight_le_length_mul entries _ hentries
    _ < 2 ^ entries.length * 2 ^ precision :=
      Nat.mul_lt_mul_of_pos_right (show entries.length < 2 ^ entries.length from Nat.lt_two_pow_self) (by positivity)
    _ = _ := by rw [← Nat.pow_add, Nat.add_comm]

/-- Stored compressed table. Its positive total ensures every sampled ticket is valid. -/
structure Table (Output : Type) where
  fallback : Output
  entries : List (Output × ℕ)
  total_pos : 0 < totalWeight entries

namespace Table

/-- The abstract ticket count; this does not allocate ticket data. -/
def ticketCount (table : Table Output) : ℕ := totalWeight table.entries

/-- Sampling uses one uniform query and a scan over the stored entries. -/
def sampler (table : Table Output) : ProbComp Output :=
  (fun ticket : Fin (table.ticketCount - 1 + 1) ↦
    selectList table.entries table.fallback ticket.val) <$> $[0..table.ticketCount - 1]

/-- Existing expanded representation, available only for semantic proofs. -/
noncomputable def expandedTable (table : Table Output) : FinitePMFCompiler.TicketTable Output where
  sizePred := table.ticketCount - 1
  tickets := ⟨expandedTickets table.entries, by
    rw [length_expandedTickets]
    have h := table.total_pos
    simp only [ticketCount]
    omega⟩

theorem ticketCount_expandedTable (table : Table Output) :
    table.expandedTable.ticketCount = table.ticketCount := by
  change totalWeight table.entries - 1 + 1 = totalWeight table.entries
  have h := table.total_pos
  omega

/-- The computations are equal extensionally; the operational definition keeps the compressed scan. -/
theorem sampler_eq_expandedTable (table : Table Output) :
    table.sampler = table.expandedTable.sampler := by
  unfold sampler FinitePMFCompiler.TicketTable.sampler
  rw [ProbComp.uniformSelectListVector_def]
  congr 1
  funext ticket
  apply selectList_eq_get_expandedTickets
  have h := table.total_pos
  have ht := ticket.isLt
  unfold ticketCount at ht
  omega

/-- Exact output probabilities from compressed counts, with no dependence on the fallback. -/
theorem probOutput_sampler [DecidableEq Output] (table : Table Output) (output : Output) :
    Pr[= output | table.sampler] =
      (outcomeWeight table.entries output : ℝ≥0∞) / (table.ticketCount : ℝ≥0∞) := by
  rw [sampler_eq_expandedTable, FinitePMFCompiler.TicketTable.probOutput_sampler,
    ticketCount_expandedTable]
  change ((expandedTickets table.entries).count output : ℝ≥0∞) / _ = _
  rw [count_expandedTickets]

/-- Events true of all stored outcomes occur with probability one. -/
theorem probEvent_eq_one_of_entries (table : Table Output) (event : Output → Prop)
    (hentries : ∀ entry ∈ table.entries, event entry.1) : Pr[event | table.sampler] = 1 := by
  rw [sampler, probEvent_map]
  apply probEvent_eq_one_iff.2
  constructor
  · simp
  · intro ticket _
    apply selectList_property table.entries table.fallback ticket.val _ event hentries
    have h := table.total_pos
    have ht := ticket.isLt
    unfold ticketCount at ht
    omega

/-- Events excluded by all stored outcomes have probability zero. -/
theorem probEvent_eq_zero_of_entries (table : Table Output) (event : Output → Prop)
    (hentries : ∀ entry ∈ table.entries, ¬ event entry.1) : Pr[event | table.sampler] = 0 := by
  rw [sampler, probEvent_map]
  apply probEvent_eq_zero_iff.2
  intro ticket _
  apply selectList_property table.entries table.fallback ticket.val _ (fun value ↦ ¬ event value) hentries
  have h := table.total_pos
  have ht := ticket.isLt
  unfold ticketCount at ht
  omega

/-- Exact mathematical denotation of the compressed executable sampler. -/
noncomputable def outputPMF (table : Table Output) : PMF Output := liftM table.sampler

theorem outputPMF_apply [DecidableEq Output] (table : Table Output) (output : Output) :
    table.outputPMF output =
      (outcomeWeight table.entries output : ℝ≥0∞) / (table.ticketCount : ℝ≥0∞) := by
  calc
    _ = Pr[= output | table.sampler] := by
      unfold outputPMF
      rw [probOutput_def, evalDist_def]
      exact (SPMF.liftM_apply (liftM table.sampler : PMF Output) output).symm
    _ = _ := table.probOutput_sampler output

/-- Direct certificate expression from compressed integer counts; it allocates no tickets. -/
noncomputable def certificateError [Fintype Output] [DecidableEq Output]
    (table : Table Output) (target : PMF Output) : ℝ≥0∞ :=
  (∑ output : Output,
    ENNReal.absDiff
      ((outcomeWeight table.entries output : ℝ≥0∞) / (table.ticketCount : ℝ≥0∞))
      (target output)) / 2

theorem etvDist_outputPMF_eq_certificateError [Fintype Output] [DecidableEq Output]
    (table : Table Output) (target : PMF Output) :
    table.outputPMF.etvDist target = table.certificateError target := by
  simp only [PMF.etvDist, certificateError, outputPMF_apply]
  rw [tsum_fintype]

/-- The same scalar approximation certificate is representation independent. -/
theorem certificateError_eq_expandedTable [Fintype Output] [DecidableEq Output]
    (table : Table Output) (target : PMF Output) :
    table.certificateError target = table.expandedTable.certificateError target := by
  simp only [certificateError, FinitePMFCompiler.TicketTable.certificateError,
    ticketCount_expandedTable]
  congr 2
  funext output
  congr 2
  change (outcomeWeight table.entries output : ℝ≥0∞) =
    ((expandedTickets table.entries).count output : ℝ≥0∞)
  rw [count_expandedTickets]

/-- Proof-carrying approximation whose operational data are compressed weights. -/
structure Certificate [Fintype Output] [DecidableEq Output] (target : PMF Output) where
  table : Table Output
  bound : ℝ≥0∞
  bound_ne_top : bound ≠ ⊤
  valid : table.certificateError target ≤ bound

namespace Certificate

variable [Fintype Output] [DecidableEq Output] {target : PMF Output}

theorem etvDist_le (certificate : Certificate target) :
    certificate.table.outputPMF.etvDist target ≤ certificate.bound := by
  rw [etvDist_outputPMF_eq_certificateError]
  exact certificate.valid

/-- Semantic adapter for reusing proved Gaussian bounds; this is excluded from executable code. -/
noncomputable def toExpanded (certificate : Certificate target) :
    FinitePMFCompiler.TicketTable.Certificate target where
  table := certificate.table.expandedTable
  bound := certificate.bound
  bound_ne_top := certificate.bound_ne_top
  valid := by
    rw [← certificateError_eq_expandedTable]
    exact certificate.valid

/-- Adapter correctness applies to the full error law, without any approximation loss. -/
theorem sampler_eq_toExpanded (certificate : Certificate target) :
    certificate.table.sampler = certificate.toExpanded.table.sampler :=
  sampler_eq_expandedTable certificate.table

end Certificate

end Table

end FormalProof4FHE.WeightedSampler
