module
import FormalProof4FHE.HasteBoots.StagedPrivateSharedLookup
import Mathlib.Algebra.Field.ZMod
open OracleSpec OracleComp
open FormalProof4FHE.HasteBoots
open scoped Classical BigOperators Matrix
namespace HasteBootsPrivateSharedLookupSmoke
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩
abbrev F := ZMod 17
local instance : SampleableType F := SampleableType.ofFintype _
def widths : Fin 2 → ℕ := ![1,2]
def sizes : Fin 2 → ℕ := ![1,2]
def repetitions : Fin 2 → ℕ := ![1,3]
def active (_ : Fin 2) : ℕ := 1
def tables (request : Fin 2) : Fin (sizes request) → Fin (widths request) → F :=
  fun row _ => if request = 0 then 4 else row.val
theorem enough : ∀ request, sizes request + 1 < Fintype.card F := by
  intro request
  fin_cases request <;> norm_num [sizes,F,ZMod.card]
def sources (_ : Fin 1) : Fin 2 → F := ![2,2]
def multiplicities : Fin 2 → F := ![1,0]

theorem outside : ∃ i, ∀ j, sources i ≠ tables 1 j := by
  refine ⟨0,?_⟩
  intro row equal
  have first := congrFun equal (0 : Fin 2)
  fin_cases row
  · exact (by decide +kernel : (2 : F) ≠ 0) first
  · exact (by decide +kernel : (2 : F) ≠ 1) first

-- False tuples can pass on an actual allowed hash collision. The pair error
-- must retain tuple hashing as well as reciprocal-domain detection.
example : (1 : F) ∈ ReciprocalDetection.allowed (fun row => TupleHash.hash (-1 : F) (tables 1 row)) := by
  rw [ReciprocalDetection.mem_allowed]
  decide +kernel
example : TupleLookupPair.Passes (F := F) (K := F) sources (tables 1) multiplicities ((-1 : F),1) := by
  change TupleLookupPair.Passes (F := F) (K := F) (fun _ : Fin 1 => (![2,2] : Fin 2 → F))
    (fun row : Fin 2 => fun _ : Fin 2 => (row.val : F)) (![1,0] : Fin 2 → F) ((-1 : F),1)
  unfold TupleLookupPair.Passes
  rw [ReciprocalDetection.passes_iff]
  decide +kernel

-- Request zero has one pair, request one has three, hence four jobs total.
-- The last job is request one's third pair, not a fourth repetition.
example : (finSigmaFinEquiv (n := repetitions) ⟨(1 : Fin 2),(2 : Fin 3)⟩).val = 3 := by
  rw [finSigmaFinEquiv_apply]
  decide +kernel
example : RequestSharedLookup.request repetitions (finSigmaFinEquiv ⟨(1 : Fin 2),(2 : Fin 3)⟩) = 1 :=
  RequestSharedLookup.request_job _ _ _
example (pairs : RequestLookupPairs.Vector F repetitions) :
    RequestLookupPairs.flatten pairs (finSigmaFinEquiv ⟨(1 : Fin 2),(2 : Fin 3)⟩) = pairs 1 (2 : Fin 3) :=
  RequestLookupPairs.flatten_job _ _ _
example : (finSigmaFinEquiv (n := fun _ : Fin 3 => 2) ⟨(2 : Fin 3),(1 : Fin 2)⟩).val = 5 :=
  RequestLookupPairs.uniform_index _ _ _

-- The selected false request receives the full error cubed. Neither its
-- tuple width nor the total job count replaces its configured repetition count.
example : Pr{let pairs ← RequestLookupPairs.sample (K := F) 2 widths sizes repetitions tables enough}[
    LookupPairVector.AllPass sources (tables 1) multiplicities (pairs 1)] ≤
    TupleLookupPair.error 17 2 1 2 ^ 3 := by
  have bound := RequestLookupPairs.selected_bound (p := 17) 2 widths sizes repetitions tables enough (1 : Fin 2)
    sources multiplicities outside (by decide +kernel)
  convert bound using 1 <;> norm_num [F,ZMod.card]
  all_goals rfl

-- Request-specific errors are combined by maximum, not by addition.
example : RequestLookupPairMiddle.errorBudget 17 widths sizes active repetitions =
    max (TupleLookupPair.error 17 1 1 1 ^ 1) (TupleLookupPair.error 17 2 1 2 ^ 3) := by
  unfold RequestLookupPairMiddle.errorBudget
  apply le_antisymm
  · apply Finset.sup_le
    intro request _
    fin_cases request
    · exact le_max_left _ _
    · exact le_max_right _ _
  · have left := Finset.le_sup (s := Finset.univ)
      (f := fun request => TupleLookupPair.error 17 (widths request) (active request) (sizes request) ^ repetitions request)
      (Finset.mem_univ (0 : Fin 2))
    have right := Finset.le_sup (s := Finset.univ)
      (f := fun request => TupleLookupPair.error 17 (widths request) (active request) (sizes request) ^ repetitions request)
      (Finset.mem_univ (1 : Fin 2))
    exact max_le left right
end
end HasteBootsPrivateSharedLookupSmoke
