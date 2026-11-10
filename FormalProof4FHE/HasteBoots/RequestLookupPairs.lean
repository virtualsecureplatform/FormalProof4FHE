module
public import FormalProof4FHE.HasteBoots.LookupPairVector
public import FormalProof4FHE.HasteBoots.StagedSharedLookup
public import Mathlib.Algebra.BigOperators.Fin
@[expose] public section

/-! Request-major private pair sampling. Each request retains its own literal
table, tuple width, row count and configured repetition count. The selected
request's vector has the original repeated hash/reciprocal bound; there is no
union factor over other requests. This remains the ideal accepted-domain law,
not native rejection-loop/transcript/work refinement. -/
open OracleSpec OracleComp
open scoped Classical BigOperators
namespace FormalProof4FHE.HasteBoots.RequestLookupPairs
noncomputable section
variable {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq K] [Fintype K] [SampleableType K]

abbrev Vector (K : Type) [Zero K] {requests : ℕ} (repetitions : Fin requests → ℕ) :=
  (request : Fin requests) → Fin (repetitions request) → StagedSharedLookup.Pair K

def sample : (requests : ℕ) → (widths sizes repetitions : Fin requests → ℕ) →
    ((request : Fin requests) → Fin (sizes request) → Fin (widths request) → F) →
    (∀ request, sizes request + 1 < Fintype.card K) → ProbComp (Vector K repetitions)
  | 0, _, _, _, _, _ => pure (fun request => Fin.elim0 request)
  | requests+1, widths, sizes, repetitions, tables, enough => do
    let first ← LookupPairVector.vector (K := K) (tables 0) (enough 0) (repetitions 0)
    let rest ← sample requests (fun i => widths i.succ) (fun i => sizes i.succ) (fun i => repetitions i.succ)
      (fun i => tables i.succ) (fun i => enough i.succ)
    pure (Fin.cons first rest)

/-- Earlier and later request draws do not amplify an event of a fixed
selected request vector. Selection precedes the entire sampling program. -/
theorem selected_event_le (requests : ℕ) (widths sizes repetitions : Fin requests → ℕ)
    (tables : (request : Fin requests) → Fin (sizes request) → Fin (widths request) → F)
    (enough : ∀ request, sizes request + 1 < Fintype.card K)
    (selected : Fin requests) (event : (Fin (repetitions selected) → StagedSharedLookup.Pair K) → Prop) :
    Pr{let pairs ← sample (K := K) requests widths sizes repetitions tables enough}[event (pairs selected)] ≤
    Pr{let pairs ← LookupPairVector.vector (K := K) (tables selected) (enough selected) (repetitions selected)}[event pairs] := by
  induction requests with
  | zero => exact Fin.elim0 selected
  | succ requests ih =>
    revert event
    refine Fin.cases ?_ (fun index => ?_) selected
    · intro event
      rw [sample]
      apply prEvent_bind_le_prEvent_of_forall_eq_zero
        (LookupPairVector.vector (K := K) (tables 0) (enough 0) (repetitions 0)) _ event
      intro first outside
      simpa only [prEvent_norm,Fin.cons_zero,outside] using
        prEvent_false (sample (K := K) requests (fun i => widths i.succ) (fun i => sizes i.succ)
          (fun i => repetitions i.succ) (fun i => tables i.succ) (fun i => enough i.succ))
    · intro event
      rw [sample]
      apply prEvent_bind_le_of_forall_le
      intro first
      simpa only [prEvent_norm,Fin.cons_succ] using ih (fun i => widths i.succ) (fun i => sizes i.succ)
        (fun i => repetitions i.succ) (fun i => tables i.succ) (fun i => enough i.succ) index event

/-- Both tuple-hash and reciprocal-domain losses are amplified by the selected
request's actual repetition count, even when other requests have different
widths, table sizes, and repetition counts. -/
theorem selected_bound {p active : ℕ} [CharP K p]
    (requests : ℕ) (widths sizes repetitions : Fin requests → ℕ)
    (tables : (request : Fin requests) → Fin (sizes request) → Fin (widths request) → F)
    (enough : ∀ request, sizes request + 1 < Fintype.card K) (selected : Fin requests)
    (sources : Fin active → Fin (widths selected) → F) (multiplicities : Fin (sizes selected) → K)
    (bad : ∃ i, ∀ j, sources i ≠ tables selected j) (small : active < p) :
    Pr{let pairs ← sample (K := K) requests widths sizes repetitions tables enough}[
      LookupPairVector.AllPass sources (tables selected) multiplicities (pairs selected)] ≤
    TupleLookupPair.error (Fintype.card K) (widths selected) active (sizes selected) ^ repetitions selected :=
  (selected_event_le requests widths sizes repetitions tables enough selected
    (LookupPairVector.AllPass sources (tables selected) multiplicities)).trans
      (LookupPairVector.vector_bound sources (tables selected) multiplicities (enough selected) bad small (repetitions selected))

/-- Flattening preserves request-major/repetition-minor job order without
changing the configured repetition count or making fresh draws. -/
def flatten {requests : ℕ} {repetitions : Fin requests → ℕ} (pairs : Vector K repetitions) :
    Fin (∑ request, repetitions request) → StagedSharedLookup.Pair K :=
  fun job => pairs (finSigmaFinEquiv.symm job).1 (finSigmaFinEquiv.symm job).2

omit [Field F] [Algebra F K] [DecidableEq K] [Fintype K] [SampleableType K] in
theorem flatten_job {requests : ℕ} {repetitions : Fin requests → ℕ}
    (pairs : Vector K repetitions) (request : Fin requests) (repetition : Fin (repetitions request)) :
    flatten pairs (finSigmaFinEquiv ⟨request,repetition⟩) = pairs request repetition := by
  exact congrArg (fun index : (request : Fin requests) × Fin (repetitions request) => pairs index.1 index.2)
    ((finSigmaFinEquiv (n := repetitions)).symm_apply_apply ⟨request,repetition⟩)
/-- The dependent job numbering agrees with the native fixed-repetition
radix schedule: request * repetitions + repetition. -/
theorem uniform_index {requests : ℕ} (repetitions : ℕ) (request : Fin requests) (repetition : Fin repetitions) :
    (finSigmaFinEquiv (n := fun _ : Fin requests => repetitions) ⟨request,repetition⟩).val =
      request.val * repetitions + repetition.val := by
  rw [finSigmaFinEquiv_apply]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rfl

end
end FormalProof4FHE.HasteBoots.RequestLookupPairs
