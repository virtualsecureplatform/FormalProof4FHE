module
public import FormalProof4FHE.HasteBoots.NativePrefixCodec
public import FormalProof4FHE.HasteBoots.IntegerPrefixProgress
@[expose] public section

/-! Measured repeated usize-prefix parsing. Rejection stops at the first failed
integer, and every successful step consumes supplied bytes. Bounds therefore
need no cap on the attacker-declared count. Charges are abstract byte/access,
arithmetic and control operations; canonical role guards and native refinement
remain separate. -/
namespace FormalProof4FHE.HasteBoots.UsizeVectorCost
open InputIndexedOracle (Input)
open NativeUsizeMessage (Usize)
open SolverOperationCost (Run)

def readCount : ℕ → Input → Run (Option (List Usize × Input))
  | 0,bytes => ⟨some ([],bytes),1⟩
  | count+1,bytes =>
    let first := IntegerPrefixCost.readUsize bytes
    match first.value with
    | none => ⟨none,first.cost+3⟩
    | some (value,rest) =>
      let tail := readCount count rest
      ⟨tail.value.map (fun pair => (value::pair.1,pair.2)),first.cost+tail.cost+5⟩

theorem readCount_value (count : ℕ) (bytes : Input) :
    (readCount count bytes).value = NativePrefixCodec.readCount NativePrefixCodec.usize count bytes := by
  induction count generalizing bytes with
  | zero => rfl
  | succ count ih =>
    simp only [readCount,NativePrefixCodec.readCount,NativePrefixCodec.usize]
    cases parsed : (IntegerPrefixCost.readUsize bytes).value with
    | none => rfl
    | some pair =>
      rcases pair with ⟨value,rest⟩
      simp only [Option.bind_some,ih]
      rfl

theorem readCount_cost (count : ℕ) (bytes : Input) :
    (readCount count bytes).cost ≤ 107*(min count bytes.length+1) := by
  induction count generalizing bytes with
  | zero => simp [readCount]
  | succ count ih =>
    have first := IntegerPrefixCost.readUsize_cost bytes
    cases parsed : (IntegerPrefixCost.readUsize bytes).value with
    | none => simp only [readCount,parsed]; omega
    | some pair =>
      rcases pair with ⟨value,rest⟩
      have progress := IntegerPrefixCost.readUsize_remaining bytes value rest parsed
      have tail := ih rest
      simp only [readCount,parsed]
      omega

/-- Pure structural length invariant, kept separate from arithmetic resource
bounds so codec encodings do not inherit their additional proof dependencies. -/
theorem readCount_length (count : ℕ) (bytes : Input) (values : List Usize) (rest : Input)
    (found : (readCount count bytes).value = some (values,rest)) :
    values.length = count := by
  induction count generalizing bytes values rest with
  | zero =>
    have pair := Option.some.inj found
    cases pair
    rfl
  | succ count ih =>
    cases parsed : (IntegerPrefixCost.readUsize bytes).value with
    | none => simp only [readCount,parsed] at found; contradiction
    | some pair =>
      rcases pair with ⟨value,tail⟩
      simp only [readCount,parsed] at found
      obtain ⟨⟨remaining,last⟩,continued,same⟩ := Option.map_eq_some_iff.mp found
      have length := ih tail remaining last continued
      cases same
      simp only [List.length_cons,length]

theorem readCount_success (count : ℕ) (bytes : Input) (values : List Usize) (rest : Input)
    (found : (readCount count bytes).value = some (values,rest)) :
    values.length = count ∧ rest.length+count ≤ bytes.length := by
  induction count generalizing bytes values rest with
  | zero =>
    have pair := Option.some.inj found
    cases pair
    simp
  | succ count ih =>
    cases parsed : (IntegerPrefixCost.readUsize bytes).value with
    | none => simp only [readCount,parsed] at found; contradiction
    | some pair =>
      rcases pair with ⟨value,tail⟩
      simp only [readCount,parsed] at found
      obtain ⟨⟨remaining,last⟩,continued,same⟩ := Option.map_eq_some_iff.mp found
      have tailResult := ih tail remaining last continued
      have progress := IntegerPrefixCost.readUsize_remaining bytes value tail parsed
      cases same
      simp only [List.length_cons]
      omega
/-- The successful count parser already proves the length bound. Constructing
its bounded row uses that proof, rather than traversing the output list again. -/
def read (bytes : Input) : Run (Option (NativePrefixCodec.Vector Usize × Input)) :=
  let header := IntegerPrefixCost.readUsize bytes
  match header.value with
  | none => ⟨none,header.cost+3⟩
  | some (count,tail) =>
    let body := readCount count.val tail
    match decoded : body.value with
    | none => ⟨none,header.cost+body.cost+5⟩
    | some (values,rest) =>
      have fits : values.length < 2^64 := by
        have length := readCount_length count.val tail values rest decoded
        rw [length]
        exact count.isLt
      ⟨some (⟨values,fits⟩,rest),header.cost+body.cost+6⟩

theorem read_value (bytes : Input) :
    (read bytes).value = (NativePrefixCodec.vector NativePrefixCodec.usize).read bytes := by
  change (read bytes).value = (IntegerPrefixCost.readUsize bytes).value.bind (fun count =>
    (NativePrefixCodec.readCount NativePrefixCodec.usize count.1.val count.2).bind (fun result =>
      if fits : result.1.length < 2^64 then some (⟨result.1,fits⟩,result.2) else none))
  simp only [read,← readCount_value]
  split
  · rename_i parsed
    simp only [parsed,Option.bind_none]
  · rename_i count tail parsed
    simp only [parsed,Option.bind_some]
    split
    · rename_i decoded
      simp only [decoded,Option.bind_none]
    · rename_i values rest decoded
      have fits : values.length < 2^64 := by
        rw [readCount_length count.val tail values rest decoded]
        exact count.isLt
      simp only [decoded,Option.bind_some,dite_eq_left fits]

theorem read_cost (bytes : Input) :
    (read bytes).cost ≤ 107*(bytes.length+1)+3 := by
  have header := IntegerPrefixCost.readUsize_cost bytes
  cases parsed : (IntegerPrefixCost.readUsize bytes).value with
  | none => simp only [read,parsed]; omega
  | some pair =>
    rcases pair with ⟨count,tail⟩
    have progress := IntegerPrefixCost.readUsize_remaining bytes count tail parsed
    have body := readCount_cost count.val tail
    simp only [read,parsed]
    split <;> dsimp only <;> omega
theorem read_remaining (bytes : Input) (values : NativePrefixCodec.Vector Usize) (rest : Input)
    (found : (read bytes).value = some (values,rest)) :
    values.val.length+rest.length < bytes.length := by
  simp only [read] at found
  split at found
  · contradiction
  · rename_i count tail parsed
    split at found
    · contradiction
    · rename_i entries last decoded
      have body := readCount_success count.val tail entries last decoded
      have header := IntegerPrefixCost.readUsize_remaining bytes count tail parsed
      have pair := Option.some.inj found
      have sameValues := congrArg (fun pair => pair.1.val) pair
      have sameRest := congrArg Prod.snd pair
      change entries = values.val at sameValues
      change last = rest at sameRest
      have bounded : entries.length+last.length < bytes.length := by omega
      simpa only [sameValues,sameRest] using bounded
end FormalProof4FHE.HasteBoots.UsizeVectorCost
