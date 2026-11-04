module

public import FormalProof4FHE.HasteBoots.NativeGoldTerminalConstructed
public import FormalProof4FHE.HasteBoots.NativeScalarBatchVerifier

@[expose] public section

/-!
# Native strict shared-lookup post-sumcheck guard window

The common point is read from claims[0], and its actual pulled query is
constructed once. Each job checks claims[2*i] against helper_values[i],
clones the requested original source slots, and checks claims[2*i+1] using
that same point and query. Checked getters expose native index-domain
failures; caller preflight and the completed batch will discharge bounds.
Returned records are a retained execution trace, not supplied certificates.
Full caller framing, preflight, PCS and instruction refinement remain open.
-/

namespace FormalProof4FHE.HasteBoots.NativeSharedLookupGuard

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeGoldExtensionArithmetic (Word)
open NativeScalarBatchVerifier (SubClaim)
open NativeGoldCoefficientsQuery (Query)
open NativeUsizeMessage (Usize)

structure Request where
  sourceSlots : List ℕ
  logicalLength : Usize

/-- The fields of the actual completed challenge used in the terminal window. -/
structure Job where
  request : ℕ
  r : Word
  powers : List Word

def Job.fromProduced (request : ℕ) (output : NativeGoldLookupProducer.Output) : Job :=
  ⟨request, output.r, output.powers⟩

structure Inputs where
  requests : List Request
  jobs : List Job
  equalityPoints : List (List Word)
  sourceValues : List (List GoldWord)
  helperValues : List Word

structure Checked where
  ordinal : ℕ
  job : Job
  request : Request
  sumClaim : SubClaim
  identityClaim : SubClaim
  helper : Word
  equalityPoint : List Word
  values : List (List GoldWord)

structure Result where
  point : List Word
  pulled : Query
  checked : List Checked

/-- Literal ordered slot lookup/clone, preserving aliases and repetitions. -/
def gather (values : List (List GoldWord)) : List ℕ → Option (List (List GoldWord))
  | [] => some []
  | slot :: tail => values[slot]?.bind (fun value => (gather values tail).map (fun rest => value :: rest))

def runJob (data : Inputs) (claims : List SubClaim) (point : List Word) (pulled : Query) (width ordinal : ℕ)
    (job : Job) : Option Checked :=
  claims[2 * ordinal]?.bind (fun sum => data.helperValues[ordinal]?.bind (fun helper =>
    if NativeGoldInterpolation.equal sum.expected helper then
      data.requests[job.request]?.bind (fun request => (gather data.sourceValues request.sourceSlots).bind (fun values =>
        data.equalityPoints[ordinal]?.bind (fun equalityPoint => claims[2 * ordinal + 1]?.bind (fun identity =>
          if NativeGoldTerminalQuery.check width pulled equalityPoint point request.logicalLength job.r values job.powers helper identity.expected = some true then
            some ⟨ordinal, job, request, sum, identity, helper, equalityPoint, values⟩ else none))))
    else none))

def runJobs (data : Inputs) (claims : List SubClaim) (point : List Word) (pulled : Query) (width : ℕ) :
    ℕ → List Job → Option (List Checked)
  | _, [] => some []
  | ordinal, job :: tail => (runJob data claims point pulled width ordinal job).bind (fun checked =>
      (runJobs data claims point pulled width (ordinal + 1) tail).map (fun rest => checked :: rest))

def guard (data : Inputs) (claims : List SubClaim) (sourceVars width : ℕ) : Option Result :=
  claims.head?.bind (fun first => (NativeGoldScalarQuery.scalarQuery sourceVars width first.point).bind (fun pulled =>
    (runJobs data claims first.point pulled width 0 data.jobs).map (fun checked => ⟨first.point, pulled, checked⟩)))

structure Evidence (data : Inputs) (claims : List SubClaim) (point : List Word) (pulled : Query) (width : ℕ)
    (checked : Checked) : Prop where
  request : data.requests[checked.job.request]? = some checked.request
  sum : claims[2 * checked.ordinal]? = some checked.sumClaim
  identity : claims[2 * checked.ordinal + 1]? = some checked.identityClaim
  helper : data.helperValues[checked.ordinal]? = some checked.helper
  equalityPoint : data.equalityPoints[checked.ordinal]? = some checked.equalityPoint
  values : gather data.sourceValues checked.request.sourceSlots = some checked.values
  matched : NativeGoldInterpolation.equal checked.sumClaim.expected checked.helper = true
  terminal : NativeGoldTerminalQuery.check width pulled checked.equalityPoint point checked.request.logicalLength
    checked.job.r checked.values checked.job.powers checked.helper checked.identityClaim.expected = some true

structure Accepted (data : Inputs) (claims : List SubClaim) (sourceVars width : ℕ) (result : Result) : Prop where
  head : ∃ first, claims.head? = some first ∧ result.point = first.point
  query : NativeGoldScalarQuery.scalarQuery sourceVars width result.point = some result.pulled
  count : result.checked.length = data.jobs.length
  ordinals : result.checked.map Checked.ordinal = List.range' 0 data.jobs.length
  jobs : result.checked.map Checked.job = data.jobs
  checked : ∀ entry ∈ result.checked, Evidence data claims result.point result.pulled width entry

/-- Successful gathering identifies every copied vector with its original
registry slot, in the original order, including repeated slots. -/
theorem gather_related (values : List (List GoldWord)) (slots : List ℕ) (output : List (List GoldWord))
    (success : gather values slots = some output) : List.Forall₂ (fun slot value => values[slot]? = some value) slots output := by
  induction slots generalizing output with
  | nil => have same : [] = output := Option.some.inj success; subst output; exact .nil
  | cons slot tail ih =>
    cases found : values[slot]? with
    | none => simp only [gather, found, Option.bind_none] at success; contradiction
    | some value =>
      cases rest : gather values tail with
      | none => simp only [gather, found, Option.bind_some, rest, Option.map_none] at success; contradiction
      | some remaining =>
        have same : value :: remaining = output := Option.some.inj (by simpa only [gather, found, Option.bind_some, rest, Option.map_some] using success)
        rw [← same]
        exact .cons found (ih remaining rest)

theorem gather_complete (values : List (List GoldWord)) (slots : List ℕ) (output : List (List GoldWord))
    (related : List.Forall₂ (fun slot value => values[slot]? = some value) slots output) : gather values slots = some output := by
  induction related with
  | nil => rfl
  | cons found related ih => rw [gather, found, Option.bind_some, ih, Option.map_some]

theorem runJob_spec (data : Inputs) (claims : List SubClaim) (point : List Word) (pulled : Query) (width ordinal : ℕ)
    (job : Job) (entry : Checked) (success : runJob data claims point pulled width ordinal job = some entry) :
    entry.ordinal = ordinal ∧ entry.job = job ∧ Evidence data claims point pulled width entry := by
  simp only [runJob, Option.bind_eq_some_iff] at success
  rcases success with ⟨sum, sumGet, helper, helperGet, rest⟩
  by_cases matched : NativeGoldInterpolation.equal sum.expected helper = true
  · simp only [ite_eq_left matched, Option.bind_eq_some_iff] at rest
    rcases rest with ⟨request, requestGet, values, valuesGet, eqPoint, eqGet, identity, identityGet, checked⟩
    by_cases passed : NativeGoldTerminalQuery.check width pulled eqPoint point request.logicalLength job.r values job.powers helper identity.expected = some true
    · rw [ite_eq_left passed] at checked
      have same := Option.some.inj checked
      subst entry
      exact ⟨rfl, rfl, ⟨requestGet, sumGet, identityGet, helperGet, eqGet, valuesGet, matched, passed⟩⟩
    · rw [ite_eq_right passed] at checked; contradiction
  · rw [ite_eq_right matched] at rest; contradiction

theorem runJobs_spec (data : Inputs) (claims : List SubClaim) (point : List Word) (pulled : Query) (width start : ℕ)
    (jobs : List Job) (entries : List Checked) (success : runJobs data claims point pulled width start jobs = some entries) :
    entries.length = jobs.length ∧ entries.map Checked.ordinal = List.range' start jobs.length ∧ entries.map Checked.job = jobs ∧
      ∀ entry ∈ entries, Evidence data claims point pulled width entry := by
  induction jobs generalizing start entries with
  | nil =>
    have same : [] = entries := Option.some.inj success
    subst entries
    simp only [List.length_nil, List.map_nil, List.range'_zero, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_self]
  | cons job tail ih =>
    cases headRun : runJob data claims point pulled width start job with
    | none => simp only [runJobs, headRun, Option.bind_none] at success; contradiction
    | some checked =>
      cases tailRun : runJobs data claims point pulled width (start + 1) tail with
      | none => simp only [runJobs, headRun, Option.bind_some, tailRun, Option.map_none] at success; contradiction
      | some rest =>
        have same : checked :: rest = entries := Option.some.inj (by simpa only [runJobs, headRun, Option.bind_some, tailRun, Option.map_some] using success)
        rw [← same]
        have first := runJob_spec data claims point pulled width start job checked headRun
        have remaining := ih (start + 1) rest tailRun
        refine ⟨by simp only [List.length_cons, remaining.1], ?_, ?_, ?_⟩
        · simp only [List.map_cons, first.1, remaining.2.1, List.length_cons, List.range'_succ]
        · simp only [List.map_cons, first.2.1, remaining.2.2.1]
        · intro entry member
          rcases List.mem_cons.mp member with equal | member
          · subst entry; exact first.2.2
          · exact remaining.2.2.2 entry member

/-- A successful guard returns its retained operational evidence; the caller
supplies neither checked jobs nor an independent common point. -/
theorem guard_spec (data : Inputs) (claims : List SubClaim) (sourceVars width : ℕ) (result : Result)
    (success : guard data claims sourceVars width = some result) : Accepted data claims sourceVars width result := by
  simp only [guard, Option.bind_eq_some_iff, Option.map_eq_some_iff] at success
  rcases success with ⟨first, headGet, pulled, pulledGet, entries, entriesGet, same⟩
  subst result
  have done := runJobs_spec data claims first.point pulled width 0 data.jobs entries entriesGet
  exact ⟨⟨first, headGet, rfl⟩, pulledGet, done.1, done.2.1, done.2.2.1, done.2.2.2⟩

end FormalProof4FHE.HasteBoots.NativeSharedLookupGuard
