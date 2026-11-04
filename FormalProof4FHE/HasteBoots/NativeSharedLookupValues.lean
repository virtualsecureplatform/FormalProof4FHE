module

public import FormalProof4FHE.HasteBoots.NativeSharedLookupProofShape

@[expose] public section

/-!
# Native backend value validation and unused-source zeros

The legacy Brakedown backend retains lazy base-field representatives;
PolyFRIM response backends require canonical ones. The trusted backend,
not proof metadata, selects that policy. Helper extension scalars are
always canonical. Unused source values use native field equality with
zero, so lazy zero is allowed by the retain policy. Slot safety and source
vector dimensions are supplied by the earlier preflight/shape checks.
-/

namespace FormalProof4FHE.HasteBoots.NativeSharedLookupValues

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeGoldExtensionArithmetic (Word)
open NativeSharedLookupStatement (Request)
open NativeSharedLookupProofShape (Values)

inductive Policy where
  | retain
  | canonical
  deriving DecidableEq

def canonical (values : List GoldWord) : Bool := values.all (fun value => decide (value.val < goldilocksModulus))

def validateVector : Policy → List GoldWord → Bool
  | .retain, _ => true
  | .canonical, values => canonical values

def helperCanonical (value : Word) : Bool := canonical (List.ofFn value)

def zeros (values : List GoldWord) : Bool := values.all (fun value => decide (goldCanonical value = 0))

def mark : List Bool → List ℕ → List Bool
  | flags, [] => flags
  | flags, slot :: tail => mark (flags.set slot true) tail

def usedSlots (count : ℕ) (requests : List Request) : List Bool :=
  mark (List.replicate count false) (requests.flatMap (fun request => request.terminal.sourceSlots))

def Requested (requests : List Request) (index : ℕ) : Prop :=
  ∃ request ∈ requests, index ∈ request.terminal.sourceSlots

def checkSources (policy : Policy) (used : List Bool) : ℕ → List (List GoldWord) → Bool
  | _, [] => true
  | index, values :: tail => validateVector policy values &&
      match used[index]? with
      | none => false
      | some flag => (flag || zeros values) && checkSources policy used (index + 1) tail

def check (policy : Policy) (count : ℕ) (requests : List Request) (values : Values) : Bool :=
  values.multiplicities.all (validateVector policy) &&
    checkSources policy (usedSlots count requests) 0 values.sources && values.helpers.all helperCanonical

theorem canonical_iff (values : List GoldWord) :
    canonical values = true ↔ ∀ value ∈ values, value.val < goldilocksModulus := by
  simp only [canonical,List.all_eq_true,decide_eq_true_eq]

theorem helperCanonical_iff (value : Word) :
    helperCanonical value = true ↔ ∀ coordinate, (value coordinate).val < goldilocksModulus := by
  simp only [helperCanonical,canonical_iff,List.mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff]

theorem zeros_iff (values : List GoldWord) : zeros values = true ↔ ∀ value ∈ values, goldValue value = 0 := by
  simp only [zeros,List.all_eq_true,decide_eq_true_eq]
  constructor
  · intro all value member
    rw [← goldCanonical_cast,all value member,Nat.cast_zero]
  · intro all value member
    have equal := congrArg (fun value : Goldilocks => value.val) (all value member)
    simpa only [goldValue_val,ZMod.val_zero] using equal

theorem canonical_zero (value : GoldWord) (valid : value.val < goldilocksModulus) (zero : goldValue value = 0) : value.val = 0 := by
  have normalized := congrArg (fun value : Goldilocks => value.val) zero
  rw [goldValue_val] at normalized
  simpa only [goldCanonical,Nat.not_le.mpr valid,ite_false,ZMod.val_zero] using normalized

theorem mark_length (flags : List Bool) (slots : List ℕ) : (mark flags slots).length = flags.length := by
  induction slots generalizing flags with
  | nil => rfl
  | cons slot tail ih => rw [mark,ih,List.length_set]

theorem mark_get (flags : List Bool) (slots : List ℕ) (index : ℕ) (inside : index < flags.length) :
    (mark flags slots)[index]?.getD false = true ↔ flags[index]?.getD false = true ∨ index ∈ slots := by
  induction slots generalizing flags with
  | nil => simp only [mark,List.not_mem_nil,or_false]
  | cons slot tail ih =>
    rw [mark,ih (flags.set slot true) (by simpa only [List.length_set] using inside)]
    by_cases same : slot = index
    · subst slot
      simp only [List.getElem?_set_self inside,Option.getD_some,List.mem_cons_self,or_true,true_or]
    · simp only [List.getElem?_set_ne same,List.mem_cons,Ne.symm same, false_or]

theorem usedSlots_length (count : ℕ) (requests : List Request) : (usedSlots count requests).length = count := by
  rw [usedSlots,mark_length,List.length_replicate]

theorem usedSlots_get (count : ℕ) (requests : List Request) (index : ℕ) (inside : index < count) :
    (usedSlots count requests)[index]?.getD false = true ↔ Requested requests index := by
  rw [usedSlots,mark_get _ _ index (by simpa only [List.length_replicate] using inside)]
  simp only [List.getElem?_replicate,inside,ite_true,Option.getD_some,Bool.false_eq_true,false_or,
    Requested,List.mem_flatMap]

theorem checkSources_spec (policy : Policy) (used : List Bool) (start : ℕ) (values : List (List GoldWord))
    (success : checkSources policy used start values = true) (index : ℕ) (inside : index < values.length) :
    ∃ flag, used[start + index]? = some flag ∧ validateVector policy values[index] = true ∧
      (flag = true ∨ zeros values[index] = true) := by
  induction values generalizing start index with
  | nil => simp only [List.length_nil] at inside; omega
  | cons value tail ih =>
    cases found : used[start]? with
    | none => simp only [checkSources,found,Bool.and_false,Bool.false_eq_true] at success
    | some flag =>
      simp only [checkSources,found,Bool.and_eq_true,Bool.or_eq_true] at success
      cases index with
      | zero => exact ⟨flag,found,success.1,success.2.1⟩
      | succ index =>
        have bound : index < tail.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using inside
        obtain ⟨next,read,valid,zero⟩ := ih (start + 1) success.2.2 index bound
        refine ⟨next,?_,valid,zero⟩
        simpa only [Nat.add_assoc,Nat.add_comm 1 index] using read

structure Accepted (policy : Policy) (count : ℕ) (requests : List Request) (values : Values) : Prop where
  multiplicities : ∀ vector ∈ values.multiplicities, validateVector policy vector = true
  sources : ∀ (index : ℕ) (inside : index < values.sources.length),
    validateVector policy values.sources[index] = true ∧
      (Requested requests index ∨ ∀ value ∈ values.sources[index], goldValue value = 0)
  helpers : ∀ helper ∈ values.helpers, ∀ coordinate, (helper coordinate).val < goldilocksModulus

theorem check_spec (policy : Policy) (count : ℕ) (requests : List Request) (values : Values)
    (success : check policy count requests values = true) : Accepted policy count requests values := by
  simp only [check,Bool.and_eq_true,List.all_eq_true,and_assoc] at success
  refine ⟨success.1,?_,?_⟩
  · intro index inside
    obtain ⟨flag,found,valid,zero⟩ := checkSources_spec policy (usedSlots count requests) 0 values.sources success.2.1 index inside
    have bound : index < count := by
      obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp found
      simpa only [Nat.zero_add,usedSlots_length] using bound
    refine ⟨valid,?_⟩
    rcases zero with used | zero
    · left
      apply (usedSlots_get count requests index bound).mp
      have read : (usedSlots count requests)[index]? = some flag := by simpa only [Nat.zero_add] using found
      rw [read,used]
      rfl
    · exact Or.inr ((zeros_iff _).mp zero)
  · intro helper member
    exact (helperCanonical_iff helper).mp (success.2.2 helper member)

/-- Canonical backends strengthen semantic unused zeros to literal raw zeros;
legacy retain backends preserve their original lazy-zero wire spelling. -/
theorem canonical_unused (count : ℕ) (requests : List Request) (values : Values)
    (success : check .canonical count requests values = true) (index : ℕ) (inside : index < values.sources.length)
    (unused : ¬ Requested requests index) : ∀ value ∈ values.sources[index], value.val = 0 := by
  have accepted := check_spec .canonical count requests values success
  have source := accepted.sources index inside
  have valid := (canonical_iff _).mp source.1
  have zero : ∀ value ∈ values.sources[index], goldValue value = 0 := source.2.resolve_left unused
  intro value member
  exact canonical_zero value (valid value member) (zero value member)

end FormalProof4FHE.HasteBoots.NativeSharedLookupValues
