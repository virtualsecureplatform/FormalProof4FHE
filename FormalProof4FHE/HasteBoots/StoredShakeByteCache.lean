module
public import FormalProof4FHE.HasteBoots.BytePrefixMatchCost
public import FormalProof4FHE.HasteBoots.ExecutableSourceHistory
@[expose] public section

/-! Stored observed SHAKE coordinates. New writes shadow older coordinates;
all entries remain stored. Inputs are shared immutable byte lists already
supplied by the caller. Lookup measures complete input comparison and offset
comparison. No cache callback executes. These abstract list/access charges do
not establish physical/compiler refinement or complete source replay cost. -/
namespace FormalProof4FHE.HasteBoots.StoredShakeByteCache
open InputIndexedOracle (Input Byte)
open SolverOperationCost (Run)
structure Entry where
  input : Input
  offset : ℕ
  value : Byte
  deriving DecidableEq, Repr
abbrev Cache := List Entry

def view : Cache → NativeShakeCache.Cache
  | [] => fun _ => none
  | head::tail => fun key =>
    if head.input = key.1 ∧ head.offset = key.2 then some head.value else view tail key

def lookup : Cache → Input → ℕ → Run (Option Byte)
  | [],_,_ => ⟨none,1⟩
  | head::tail,input,offset =>
    let same := BytePrefixMatchCost.equal input head.input
    if same.value && decide (head.offset = offset) then ⟨some head.value,same.cost+4⟩
    else let rest := lookup tail input offset; ⟨rest.value,same.cost+rest.cost+5⟩

theorem lookup_value (cache : Cache) (input : Input) (offset : ℕ) :
    (lookup cache input offset).value = view cache (input,offset) := by
  induction cache with
  | nil => rfl
  | cons head tail ih =>
    simp only [lookup,BytePrefixMatchCost.equal_value,ih,view]
    by_cases bytes : input = head.input <;> by_cases position : head.offset = offset <;>
      simp [bytes,position,eq_comm]

def lookupBound (inputLength entries : ℕ) := (6*inputLength+14)*entries+1

theorem lookup_cost (cache : Cache) (input : Input) (offset : ℕ) :
    (lookup cache input offset).cost ≤ lookupBound input.length cache.length := by
  induction cache with
  | nil => simp [lookup,lookupBound]
  | cons head tail ih =>
    have compared := BytePrefixMatchCost.equal_cost input head.input
    have size := Nat.min_le_left input.length head.input.length
    simp only [lookup,lookupBound,List.length_cons] at *
    split <;> dsimp only <;> nlinarith

def put (cache : Cache) (input : Input) (offset : ℕ) (value : Byte) : Run Cache :=
  ⟨⟨input,offset,value⟩::cache,5⟩

theorem put_view (cache : Cache) (input : Input) (offset : ℕ) (value : Byte) :
    view (put cache input offset value).value = Function.update (view cache) (input,offset) (some value) := by
  funext key
  rcases key with ⟨other,position⟩
  by_cases same : (other,position) = (input,offset)
  · cases same; simp only [put,view,and_self,ite_true,Function.update_self]
  · have different : ¬(input = other ∧ offset = position) := by
      rintro ⟨rfl,rfl⟩; exact same rfl
    simp only [put,view,different,ite_false,Function.update_of_ne same]

def write (cache : Cache) (input : Input) (offset : ℕ) : Input → Run Cache
  | [] => ⟨cache,1⟩
  | value::rest =>
    let first := put cache input offset value
    let tail := write first.value input (offset+1) rest
    ⟨tail.value,first.cost+tail.cost+3⟩

theorem write_view (cache : Cache) (input : Input) (offset : ℕ) (values : Input) :
    view (write cache input offset values).value =
      ExecutableSourceHistory.writeBytes (view cache) input offset values := by
  induction values generalizing cache offset with
  | nil => rfl
  | cons value rest ih =>
    simp only [write,ExecutableSourceHistory.writeBytes,ih,put_view]

theorem write_cost (cache : Cache) (input : Input) (offset : ℕ) (values : Input) :
    (write cache input offset values).cost = 8*values.length+1 := by
  induction values generalizing cache offset with
  | nil => rfl
  | cons value rest ih => simp only [write,put,ih,List.length_cons]; omega

theorem write_size (cache : Cache) (input : Input) (offset : ℕ) (values : Input) :
    (write cache input offset values).value.length = cache.length+values.length := by
  induction values generalizing cache offset with
  | nil => simp [write]
  | cons value rest ih => simp only [write,put,ih,List.length_cons]; omega
end FormalProof4FHE.HasteBoots.StoredShakeByteCache
