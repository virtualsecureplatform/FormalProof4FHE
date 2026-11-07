module
public import FormalProof4FHE.HasteBoots.BytePrefixCost
@[expose] public section

/-! Prefix matching and complete equality over stored bytes, with explicit
byte/list/control charges. These functions invoke no parser or callback. -/
namespace FormalProof4FHE.HasteBoots.BytePrefixMatchCost
open InputIndexedOracle (Input)
open SolverOperationCost (Run)

def matchPrefix : Input → Input → Run (Option Input)
  | [],bytes => ⟨some bytes,1⟩
  | _::_,[] => ⟨none,1⟩
  | head::tail,first::rest =>
    if head = first then
      let next := matchPrefix tail rest
      ⟨next.value,next.cost+6⟩
    else ⟨none,6⟩

theorem matchPrefix_some (expected bytes rest : Input) :
    (matchPrefix expected bytes).value = some rest ↔ bytes = expected++rest := by
  induction expected generalizing bytes with
  | nil => simp [matchPrefix]
  | cons head tail ih =>
    cases bytes with
    | nil => simp [matchPrefix]
    | cons first remaining =>
      by_cases same : head = first
      · subst first; simp [matchPrefix,ih]
      · simp [matchPrefix,same,Ne.symm same]

theorem matchPrefix_append (expected rest : Input) :
    (matchPrefix expected (expected++rest)).value = some rest :=
  (matchPrefix_some expected _ rest).mpr rfl

theorem matchPrefix_value (expected bytes : Input) :
    (matchPrefix expected bytes).value =
      if bytes.take expected.length = expected then some (bytes.drop expected.length) else none := by
  by_cases prefixOK : bytes.take expected.length = expected
  · rw [ite_eq_left prefixOK]
    apply (matchPrefix_some expected bytes _).mpr
    calc
      bytes = bytes.take expected.length ++ bytes.drop expected.length :=
        (List.take_append_drop expected.length bytes).symm
      _ = expected ++ bytes.drop expected.length := by rw [prefixOK]
  · rw [ite_eq_right prefixOK]
    cases found : (matchPrefix expected bytes).value with
    | none => rfl
    | some rest =>
      have split := (matchPrefix_some expected bytes rest).mp found
      have prefixMatch : bytes.take expected.length = expected := by rw [split,List.take_left]
      contradiction

theorem matchPrefix_cost (expected bytes : Input) :
    (matchPrefix expected bytes).cost ≤ 6*(min expected.length bytes.length+1) := by
  induction expected generalizing bytes with
  | nil => simp [matchPrefix]
  | cons head tail ih =>
    cases bytes with
    | nil => simp only [matchPrefix,List.length_nil,Nat.min_zero]; omega
    | cons first remaining =>
      have bound := ih remaining
      by_cases same : head = first <;>
        simp only [matchPrefix,same,ite_true,ite_false,List.length_cons] <;> omega

theorem matchPrefix_append_cost (expected rest : Input) :
    (matchPrefix expected (expected++rest)).cost = 6*expected.length+1 := by
  induction expected with
  | nil => rfl
  | cons head tail ih =>
    simp only [matchPrefix,List.cons_append,ite_true,List.length_cons,ih]
    omega

def equal (expected bytes : Input) : Run Bool :=
  let matched := matchPrefix expected bytes
  ⟨match matched.value with | some [] => true | _ => false,matched.cost+3⟩

theorem equal_value (expected bytes : Input) :
    (equal expected bytes).value = decide (expected = bytes) := by
  by_cases same : expected = bytes
  · subst bytes
    have found := matchPrefix_append expected []
    simp only [List.append_nil] at found
    simp only [equal,found,decide_true]
  · have missing : (matchPrefix expected bytes).value ≠ some [] := by
      intro found
      have full := (matchPrefix_some expected bytes []).mp found
      simp only [List.append_nil] at full
      exact same full.symm
    cases found : (matchPrefix expected bytes).value with
    | none => simp only [equal,found,same,decide_false]
    | some rest =>
      cases rest with
      | nil => contradiction
      | cons head tail => simp only [equal,found,same,decide_false]

theorem equal_cost (expected bytes : Input) :
    (equal expected bytes).cost ≤ 6*(min expected.length bytes.length+1)+3 := by
  have bound := matchPrefix_cost expected bytes
  simp only [equal]
  omega
end FormalProof4FHE.HasteBoots.BytePrefixMatchCost
