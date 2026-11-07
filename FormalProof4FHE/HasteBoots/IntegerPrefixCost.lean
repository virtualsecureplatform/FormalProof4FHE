module
public import FormalProof4FHE.HasteBoots.BytePrefixCost
public import FormalProof4FHE.HasteBoots.NativeIntegerPrefix
@[expose] public section

/-! Measured structural bincode integer-prefix reader, including truncation and
invalid tags. This retains the existing structural reader's permissiveness;
canonical role decoding still needs its own checks and cost composition.
Charges use abstract byte/access/arithmetic/control operations, not native time. -/
namespace FormalProof4FHE.HasteBoots.IntegerPrefixCost
open InputIndexedOracle (Input)
open SolverOperationCost (Run)

def read : Input → Run (Option (ℕ × Input))
  | [] => ⟨none,1⟩
  | tag::tail =>
    if tag.val < 251 then ⟨some (tag.val,tail),6⟩
    else if tag = 251 then
      let rest := BytePrefixCost.readWide 2 tail
      ⟨rest.value,rest.cost+8⟩
    else if tag = 252 then
      let rest := BytePrefixCost.readWide 4 tail
      ⟨rest.value,rest.cost+10⟩
    else if tag = 253 then
      let rest := BytePrefixCost.readWide 8 tail
      ⟨rest.value,rest.cost+12⟩
    else ⟨none,10⟩

theorem read_value (bytes : Input) : (read bytes).value = NativeIntegerPrefix.read bytes := by
  cases bytes with
  | nil => rfl
  | cons tag tail =>
    by_cases small : tag.val < 251
    · simp [read,small,NativeIntegerPrefix.read,NativeIntegerPrefix.headerSize,NativeUsizeMessage.read]
    · by_cases two : tag = 251
      · subst tag
        simp [read,NativeIntegerPrefix.read,NativeIntegerPrefix.headerSize,NativeUsizeMessage.read,
          BytePrefixCost.readWide_value]
      · by_cases four : tag = 252
        · subst tag
          simp [read,NativeIntegerPrefix.read,NativeIntegerPrefix.headerSize,NativeUsizeMessage.read,
            BytePrefixCost.readWide_value]
        · by_cases eight : tag = 253
          · subst tag
            simp [read,NativeIntegerPrefix.read,NativeIntegerPrefix.headerSize,NativeUsizeMessage.read,
              BytePrefixCost.readWide_value]
          · simp [read,small,two,four,eight,NativeIntegerPrefix.read,NativeIntegerPrefix.headerSize,
              NativeUsizeMessage.read]

theorem read_cost (bytes : Input) : (read bytes).cost ≤ 97 := by
  cases bytes with
  | nil => simp [read]
  | cons tag tail =>
    have two := BytePrefixCost.readWide_cost 2 tail
    have four := BytePrefixCost.readWide_cost 4 tail
    have eight := BytePrefixCost.readWide_cost 8 tail
    simp only [read]
    split
    · norm_num
    · split
      · dsimp only; omega
      · split
        · dsimp only; omega
        · split <;> dsimp only <;> omega
def readUsize (bytes : Input) : Run (Option (NativeUsizeMessage.Usize × Input)) :=
  let parsed := read bytes
  match parsed.value with
  | none => ⟨none,parsed.cost+2⟩
  | some (value,rest) =>
    if fits : value < 2^64 then ⟨some (⟨value,fits⟩,rest),parsed.cost+4⟩
    else ⟨none,parsed.cost+3⟩

theorem readUsize_value (bytes : Input) :
    (readUsize bytes).value = (NativeIntegerPrefix.read bytes).bind (fun pair =>
      if fits : pair.1 < 2^64 then some (⟨pair.1,fits⟩,pair.2) else none) := by
  cases parsed : NativeIntegerPrefix.read bytes with
  | none => simp only [readUsize,read_value,parsed,Option.bind_none]
  | some pair =>
    rcases pair with ⟨value,rest⟩
    simp only [readUsize,read_value,parsed,Option.bind_some]
    split <;> rfl

theorem readUsize_cost (bytes : Input) : (readUsize bytes).cost ≤ 101 := by
  have bound := read_cost bytes
  simp only [readUsize]
  split
  · dsimp only; omega
  · split <;> dsimp only <;> omega
end FormalProof4FHE.HasteBoots.IntegerPrefixCost
