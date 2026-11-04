module

public import FormalProof4FHE.HasteBoots.NativeSharedLookupBatchLink
public import Mathlib.Data.List.OfFn

@[expose] public section

/-!
# Independent shared lookup equation metadata and raw initial claims

Equation infos are built independently from original requests/repetitions.
The sampler's scheduled jobs are identified with the same request/repetition
order. Raw initial claims use each produced job's own inverse vector and its
original request's multiplicities, followed by zero. Checked vector packing
retains native usize domains. Canonical configuration validation, full child
framing and instruction refinement remain separate obligations.
-/

namespace FormalProof4FHE.HasteBoots.NativeSharedLookupStatement

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeGoldExtensionArithmetic (Word)
open NativeUsizeMessage (Usize)
open NativeScalarBatchWire (Info Statement)

structure Request where
  columns : ℕ
  table : List (List GoldWord)
  repetitions : ℕ
  terminal : NativeSharedLookupGuard.Request

structure Tagged where
  ordinal : Usize
  repetition : ℕ
  request : Request

structure Prepared where
  tag : Tagged
  output : NativeGoldLookupProducer.Output

noncomputable section

def Request.sampling (request : Request) : NativeLookupBatch.Request goldilocksModulus :=
  ⟨request.columns, request.table.map (List.map goldValue), request.repetitions⟩

def Tagged.job (tag : Tagged) : NativeLookupBatch.Job goldilocksModulus :=
  ⟨tag.ordinal, tag.repetition, tag.request.sampling⟩

def tags {count : ℕ} (fits : count ≤ 2 ^ 64) (requests : Fin count → Request) : List Tagged :=
  (List.ofFn (fun i : Fin count => List.ofFn (fun repetition : Fin (requests i).repetitions =>
    Tagged.mk ⟨i.val, i.isLt.trans_le fits⟩ repetition.val (requests i)))).flatten

def pair (n : Usize) (request : Request) : List Info :=
  [⟨⟨1, by decide⟩, n⟩,
   ⟨if request.terminal.logicalLength.val = 2 ^ n.val then ⟨3, by decide⟩ else ⟨4, by decide⟩, n⟩]

/-- Literal independent request/repetition metadata construction. -/
def infos (n : Usize) (requests : List Request) : List Info :=
  requests.flatMap (fun request => (List.range request.repetitions).flatMap (fun _ => pair n request))

def initialClaims (multiplicities : List (List GoldWord)) : List Prepared → Option (List Word)
  | [] => some []
  | job :: tail => multiplicities[job.tag.ordinal.val]?.bind (fun counts =>
      (initialClaims multiplicities tail).map (fun rest =>
        NativeGoldExtensionArithmetic.tableSum job.output.inverses counts :: NativeGoldLookup.zero :: rest))

def build (n : Usize) (requests : List Request) (jobs : List Prepared) (multiplicities : List (List GoldWord)) : Option Statement :=
  (initialClaims multiplicities jobs).bind (fun sums =>
    if infoFits : (infos n requests).length < 2 ^ 64 then
      if sumFits : sums.length < 2 ^ 64 then some ⟨⟨infos n requests, infoFits⟩, ⟨sums, sumFits⟩⟩ else none
    else none)

private theorem filter_samples {count : ℕ} (jobs : Fin count → NativeLookupBatch.Job goldilocksModulus) :
    NativeLookupBatch.jobs (List.ofFn (fun i => NativeLookupBatch.Action.sample (jobs i))) = List.ofFn jobs := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [List.ofFn_succ]
    change jobs 0 :: NativeLookupBatch.jobs (List.ofFn (fun i => .sample (jobs i.succ))) =
      jobs 0 :: List.ofFn (fun i => jobs i.succ)
    rw [ih]

/-- Erasing metadata tags gives exactly the existing sampler schedule jobs. -/
theorem schedule_jobs {count : ℕ} (fits : count ≤ 2 ^ 64) (requests : Fin count → Request) :
    NativeLookupBatch.jobs (NativeLookupBatch.schedule fits (fun i => (requests i).sampling)) =
      (tags fits requests).map Tagged.job := by
  simp only [NativeLookupBatch.jobs, NativeLookupBatch.schedule, List.filterMap_flatten, List.map_ofFn,
    Function.comp_def, List.filterMap_cons, List.map_flatten, tags, Request.sampling]
  congr 1
  apply congrArg List.ofFn
  funext i
  simpa only [NativeLookupBatch.jobs, Tagged.job, Request.sampling] using
    (filter_samples (fun repetition : Fin (requests i).repetitions =>
      Tagged.job ⟨⟨i.val, i.isLt.trans_le fits⟩, repetition.val, requests i⟩))

/-- Actual completed sampler execution supplies exact request/repetition
order; no separate job-order certificate is assumed. -/
theorem finished_jobs {count : ℕ} (fits : count ≤ 2 ^ 64) (requests : Fin count → Request)
    (w fuel : ℕ) (transcript : NativeTranscript.Transcript) (world : InputIndexedOracle.World) (final : NativeTranscript.Transcript)
    (finished : (NativeLookupBatch.execute goldilocksBasis w fuel
      (NativeLookupBatch.initial (NativeLookupBatch.schedule fits (fun i => (requests i).sampling)) transcript) world).1.control = .finished final) :
    (NativeLookupBatch.execute goldilocksBasis w fuel
      (NativeLookupBatch.initial (NativeLookupBatch.schedule fits (fun i => (requests i).sampling)) transcript) world).1.completed.map
        (fun completed => completed.job) = (tags fits requests).map Tagged.job := by
  rw [NativeLookupBatch.finished_jobs goldilocksBasis w fuel _ transcript world final finished, schedule_jobs]

/-- The independent infos function has exactly the ordered job-tag meaning. -/
theorem infos_tags {count : ℕ} (fits : count ≤ 2 ^ 64) (requests : Fin count → Request) (n : Usize) :
    infos n (List.ofFn requests) = (tags fits requests).flatMap (fun tag => pair n tag.request) := by
  unfold infos tags
  rw [List.flatten_eq_flatMap, List.flatMap_assoc]
  simp only [List.flatMap_def, id_eq, List.map_ofFn, Function.comp_def, List.map_const', List.length_range, List.ofFn_const]

/-- Each completed raw producer contributes exactly its own public sum and
one identity zero, even when multiple repetitions reuse a request index. -/
theorem initialClaims_length (multiplicities : List (List GoldWord)) (jobs : List Prepared) (sums : List Word)
    (success : initialClaims multiplicities jobs = some sums) : sums.length = 2 * jobs.length := by
  induction jobs generalizing sums with
  | nil => have same : [] = sums := Option.some.inj success; subst sums; rfl
  | cons job tail ih =>
    cases counts : multiplicities[job.tag.ordinal.val]? with
    | none => simp only [initialClaims, counts, Option.bind_none] at success; contradiction
    | some values =>
      cases rest : initialClaims multiplicities tail with
      | none => simp only [initialClaims, counts, Option.bind_some, rest, Option.map_none] at success; contradiction
      | some remaining =>
        have same : NativeGoldExtensionArithmetic.tableSum job.output.inverses values :: NativeGoldLookup.zero :: remaining = sums :=
          Option.some.inj (by simpa only [initialClaims, counts, Option.bind_some, rest, Option.map_some] using success)
        rw [← same, List.length_cons, List.length_cons, ih remaining rest, List.length_cons]
        omega

theorem pair_length (n : Usize) (request : Request) : (pair n request).length = 2 := rfl

theorem infos_numVariables (n : Usize) (requests : List Request) (info : Info) (member : info ∈ infos n requests) :
    info.numVariables = n := by
  obtain ⟨request, _, atRequest⟩ := List.mem_flatMap.mp member
  obtain ⟨_, _, atPair⟩ := List.mem_flatMap.mp atRequest
  simp only [pair, List.mem_cons, List.not_mem_nil, or_false] at atPair
  rcases atPair with same | same <;> subst info <;> rfl

theorem infos_length_tags {count : ℕ} (fits : count ≤ 2 ^ 64) (requests : Fin count → Request) (n : Usize) :
    (infos n (List.ofFn requests)).length = 2 * (tags fits requests).length := by
  rw [infos_tags fits requests n, List.length_flatMap]
  simp only [pair_length, List.map_const', List.sum_replicate, nsmul_eq_mul, Nat.cast_id]
  omega

/-- Every even entry is the native public table sum for that exact job and
request-indexed multiplicity vector; every following odd entry is raw zero. -/
theorem initialClaims_pair (multiplicities : List (List GoldWord)) (jobs : List Prepared) (sums : List Word)
    (success : initialClaims multiplicities jobs = some sums) (index : ℕ) (present : index < jobs.length) :
    ∃ counts, multiplicities[(jobs[index]).tag.ordinal.val]? = some counts ∧
      sums[2 * index]? = some (NativeGoldExtensionArithmetic.tableSum (jobs[index]).output.inverses counts) ∧
      sums[2 * index + 1]? = some NativeGoldLookup.zero := by
  induction jobs generalizing index sums with
  | nil => simp only [List.length_nil] at present; omega
  | cons job tail ih =>
    cases counts : multiplicities[job.tag.ordinal.val]? with
    | none => simp only [initialClaims, counts, Option.bind_none] at success; contradiction
    | some values =>
      cases rest : initialClaims multiplicities tail with
      | none => simp only [initialClaims, counts, Option.bind_some, rest, Option.map_none] at success; contradiction
      | some remaining =>
        have same : NativeGoldExtensionArithmetic.tableSum job.output.inverses values :: NativeGoldLookup.zero :: remaining = sums :=
          Option.some.inj (by simpa only [initialClaims, counts, Option.bind_some, rest, Option.map_some] using success)
        cases index with
        | zero =>
          refine ⟨values, ?_, ?_, ?_⟩
          · exact counts
          · rw [← same]; rfl
          · rw [← same]; rfl
        | succ index =>
          have inside : index < tail.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using present
          obtain ⟨selected, selectedGet, even, odd⟩ := ih remaining rest index inside
          refine ⟨selected, selectedGet, ?_, ?_⟩
          · rw [← same]
            simpa only [Nat.mul_succ, List.getElem?_cons_succ, List.getElem_cons_succ] using even
          · rw [← same]
            simpa only [Nat.mul_succ, Nat.add_assoc, List.getElem?_cons_succ] using odd

theorem build_spec (n : Usize) (requests : List Request) (jobs : List Prepared) (multiplicities : List (List GoldWord))
    (statement : Statement) (success : build n requests jobs multiplicities = some statement) :
    statement.infos.val = infos n requests ∧ initialClaims multiplicities jobs = some statement.claims.val := by
  rcases Option.bind_eq_some_iff.mp success with ⟨sums, sumsGet, rest⟩
  by_cases infoFits : (infos n requests).length < 2 ^ 64
  · rw [dite_eq_left infoFits] at rest
    by_cases sumFits : sums.length < 2 ^ 64
    · rw [dite_eq_left sumFits] at rest
      have same := Option.some.inj rest
      subst statement
      exact ⟨rfl, sumsGet⟩
    · rw [dite_eq_right sumFits] at rest; contradiction
  · rw [dite_eq_right infoFits] at rest; contradiction

end

end FormalProof4FHE.HasteBoots.NativeSharedLookupStatement
