module
public import FormalProof4FHE.HasteBoots.PaddedNTTSequence
@[expose] public section

/-! Derived safe error sums on the actual dependent padded NTT loop. Each
reached child inherits the preceding audit, memory and complete history. -/
namespace FormalProof4FHE.HasteBoots.PaddedNTTSequenceSoundness
open OracleSpec OracleComp BinaryTree
open PaddedNTTSequence
noncomputable section
variable {F Index Input Digest Cfg Response Memory CommitMemory : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {heights : Cfg → ℕ} {b c r k : ℕ}
variable (factory : Index → Memory → PaddedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory heights b c r k)
variable [SampleableType (Fin k → Fin r → F)] [SampleableType (Fin b → F)] [SampleableType Digest]
  [∀ index memory side, SampleableType (InteractiveAuthenticatedOpening.TestMatrix F (2^((factory index memory).code side).front) b)]
  [∀ index memory side, SampleableType (Fin ((factory index memory).code side).queries → Fin (2^heights ((factory index memory).tag side)))]

variable (enc : MerkleOracle.Encoding Input Digest (List F))

/-- An original-owner risk at a retained child end. -/
def LocalRisk (dummy : Digest)
    (capacity : ∀ index memory side, 2^((factory index memory).code side).suffix ≤ ((factory index memory).code side).m*b)
    (radius : Index → Memory → Bool → ℕ) (entry : Index × Child factory) : Prop :=
  PaddedNTT.OriginalRisk (shared factory enc entry.2.1.1 entry.2.1.2) dummy
    (capacity entry.2.1.1 entry.2.1.2) (radius entry.2.1.1 entry.2.1.2) entry.2.2

def LocalSafeRisk (dummy : Digest)
    (capacity : ∀ index memory side, 2^((factory index memory).code side).suffix ≤ ((factory index memory).code side).m*b)
    (radius : Index → Memory → Bool → ℕ) (entry : Index × Child factory) : Prop :=
  LocalRisk factory enc dummy capacity radius entry ∧
    ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) entry.2.2.2.2

def AnySafeRisk (dummy : Digest)
    (capacity : ∀ index memory side, 2^((factory index memory).code side).suffix ≤ ((factory index memory).code side).m*b)
    (radius : Index → Memory → Bool → ℕ) (trace : Trace factory) : Prop :=
  ∃ entry ∈ trace.results, LocalSafeRisk factory enc dummy capacity radius entry

def AnyOriginalRisk (dummy : Digest)
    (capacity : ∀ index memory side, 2^((factory index memory).code side).suffix ≤ ((factory index memory).code side).m*b)
    (radius : Index → Memory → Bool → ℕ) (trace : Trace factory) : Prop :=
  ∃ entry ∈ trace.results, LocalRisk factory enc dummy capacity radius entry

/-- Sum conditional local-safe risks over the trusted possible child list.
Later children are charged only through their reached actual incoming states. -/
theorem safe_union_bound
    (dummy : Digest) (indices : List Index)
    (capacity : ∀ index memory side, 2^((factory index memory).code side).suffix ≤ ((factory index memory).code side).m*b)
    (radius : Index → Memory → Bool → ℕ) (epsilon : Index → ENNReal)
    (conditional : ∀ index ∈ indices, ∀ memory initial,
      CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial →
      Pr{let child ← (PaddedNTT.witness (shared factory enc index memory) dummy initial)}[
        LocalSafeRisk factory enc dummy capacity radius (index,⟨(index,memory),child⟩)] ≤ epsilon index)
    (memory : Memory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (witness factory enc dummy indices memory initial)}[
      AnySafeRisk factory enc dummy capacity radius outcome.1] ≤ (indices.map epsilon).sum := by
  classical
  induction indices generalizing memory initial with
  | nil => simp [witness,AnySafeRisk,prEvent_norm]
  | cons index rest ih =>
    rw [witness]
    refine (prEvent_bind_le_prEvent_add_of_support (ε := (rest.map epsilon).sum) _ _
      (fun child => LocalSafeRisk factory enc dummy capacity radius (index,⟨(index,memory),child⟩)) _ ?_).trans ?_
    · intro child supported notHead
      have incoming := PaddedNTT.audited_witness (shared factory enc index memory) dummy initial audited child supported
      by_cases passes : PaddedNTT.accepted (factory index memory) child.2.1 = true
      · simp only [passes,ite_true,prEvent_norm]
        have tail := ih (fun other member => conditional other (List.mem_cons_of_mem index member))
          child.2.1.2.memory child.2.2 incoming
        apply le_trans (prEvent_mono _ _ (fun outcome => AnySafeRisk factory enc dummy capacity radius outcome.1) ?_) tail
        intro outcome event
        obtain ⟨entry,member,risk⟩ := event
        rcases List.mem_cons.mp member with equal | later
        · subst entry
          exact False.elim (notHead risk)
        · exact ⟨entry,later,risk⟩
      · simp only [ite_eq_right passes,pure_bind,prEvent_pure]
        split_ifs with event
        · obtain ⟨entry,member,risk⟩ := event
          have equal := List.mem_singleton.mp member
          subst entry
          exact False.elim (notHead risk)
        · exact zero_le
    · simpa only [List.map_cons,List.sum_cons] using
        add_le_add (conditional index (List.mem_cons_self) memory initial audited) le_rfl


/-- The final clear history excludes a failure at every retained child end. -/
theorem original_safe_le_local (dummy : Digest) (indices : List Index)
    (capacity : ∀ index memory side, 2^((factory index memory).code side).suffix ≤ ((factory index memory).code side).m*b)
    (radius : Index → Memory → Bool → ℕ) (memory : Memory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :
    Pr{let outcome ← (witness factory enc dummy indices memory initial)}[
      AnyOriginalRisk factory enc dummy capacity radius outcome.1 ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2] ≤
    Pr{let outcome ← (witness factory enc dummy indices memory initial)}[
      AnySafeRisk factory enc dummy capacity radius outcome.1] := by
  apply prEvent_mono_of_support
  intro actual actualSupported event
  obtain ⟨⟨entry,member,risk⟩,clear⟩ := event
  refine ⟨entry,member,risk,?_⟩
  intro bad
  exact clear (child_bad_persistent factory enc dummy indices memory initial actual actualSupported entry member bad)

/-- A false relation on a retained call's actual logical source views. -/
def AnyFalseRelation (dummy : Digest)
    (capacity : ∀ index memory side, 2^((factory index memory).code side).suffix ≤ ((factory index memory).code side).m*b)
    (radius : Index → Memory → Bool → ℕ) (trace : Trace factory) : Prop :=
  ∃ entry ∈ trace.results,
    PaddedNTT.FalseRelation (shared factory enc entry.2.1.1 entry.2.1.2) dummy
      (capacity entry.2.1.1 entry.2.1.2) (radius entry.2.1.1 entry.2.1.2) entry.2.2.1

/-- Accepted false logical relations give original-owner risks using owners
recorded by the actual execution, without a supplied authenticity certificate. -/
theorem accepted_false_implies_original (dummy : Digest) (indices : List Index)
    (capacity : ∀ index memory side, 2^((factory index memory).code side).suffix ≤ ((factory index memory).code side).m*b)
    (radius : Index → Memory → Bool → ℕ) (memory : Memory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : Trace factory × CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (supported : outcome ∈ support (witness factory enc dummy indices memory initial))
    (passes : outcome.1.accepted = true)
    (wrong : AnyFalseRelation factory enc dummy capacity radius outcome.1) :
    AnyOriginalRisk factory enc dummy capacity radius outcome.1 := by
  obtain ⟨entry,member,falseRelation⟩ := wrong
  obtain ⟨before,present⟩ := retained_child_support factory enc dummy indices memory initial outcome supported entry member
  exact ⟨entry,member,PaddedNTT.fresh_risk_implies_original (shared factory enc entry.2.1.1 entry.2.1.2)
    dummy (capacity entry.2.1.1 entry.2.1.2) (radius entry.2.1.1 entry.2.1.2) before entry.2.2 present falseRelation
      (accepted_children factory enc dummy indices memory initial outcome supported passes entry member)⟩

/-- The conversion preserves the single final-history exception. -/
theorem accepted_false_le_original (dummy : Digest) (indices : List Index)
    (capacity : ∀ index memory side, 2^((factory index memory).code side).suffix ≤ ((factory index memory).code side).m*b)
    (radius : Index → Memory → Bool → ℕ) (memory : Memory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :
    Pr{let outcome ← (witness factory enc dummy indices memory initial)}[
      outcome.1.accepted = true ∧ AnyFalseRelation factory enc dummy capacity radius outcome.1 ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2] ≤
    Pr{let outcome ← (witness factory enc dummy indices memory initial)}[
      AnyOriginalRisk factory enc dummy capacity radius outcome.1 ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2] := by
  apply prEvent_mono_of_support
  intro outcome supported event
  exact ⟨accepted_false_implies_original factory enc dummy indices capacity radius memory initial outcome supported event.1 event.2.1,event.2.2⟩

variable {K : Type} [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq K]
  [SampleableType F] [SampleableType (Fin r → F)]
  [∀ index memory side, SampleableType ((Fin (2^((factory index memory).code side).front) × Fin b) → K)]

/-- Every reached call pays its derived row/compression and two independent
physical PCS errors, bounded uniformly in its actual incoming private memory.
No conditional child security hypothesis or local collision charge is assumed. -/
theorem derived_original_safe_union_bound [NeZero b]
    [∀ index memory side, NeZero ((factory index memory).code side).m]
    (dummy : Digest) (basis : Module.Basis (Fin b) F K) (indices : List Index)
    (enough : ∀ index memory side, ((factory index memory).code side).m ≤
      Fintype.card (Fin (2^heights ((factory index memory).tag side))))
    (capacity : ∀ index memory side, 2^((factory index memory).code side).suffix ≤ ((factory index memory).code side).m*b)
    (radius : Index → Memory → Bool → ℕ) (epsilon : Index → ENNReal)
    (small : ∀ index memory side, (radius index memory side : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) ((factory index memory).domain side))
        ((factory index memory).code side).m : Set (Fin (2^heights ((factory index memory).tag side)) → K)) : ℚ≥0)/3)
    (calibrated : ∀ index memory,
      ((((r : ENNReal)/Fintype.card F)^k) + (c : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card F)^b))) +
      (JointMatrixOpening.error (K := K) (m := ((factory index memory).code false).m) (b := b)
          (queries := ((factory index memory).code false).queries) ((factory index memory).domain false) (radius index memory false) +
        JointMatrixOpening.error (K := K) (m := ((factory index memory).code true).m) (b := b)
          (queries := ((factory index memory).code true).queries) ((factory index memory).domain true) (radius index memory true)) ≤ epsilon index)
    (memory : Memory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (witness factory enc dummy indices memory initial)}[
      AnyOriginalRisk factory enc dummy capacity radius outcome.1 ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2] ≤ (indices.map epsilon).sum := by
  refine (original_safe_le_local factory enc dummy indices capacity radius memory initial).trans
    (safe_union_bound factory enc dummy indices capacity radius epsilon ?_ memory initial audited)
  intro index _ before initial incoming
  have bound := (PaddedNTT.original_safe_bound (shared factory enc index before) basis dummy
    (enough index before) (capacity index before) (radius index before) (small index before) initial incoming).trans
      (calibrated index before)
  exact bound

end
end FormalProof4FHE.HasteBoots.PaddedNTTSequenceSoundness
