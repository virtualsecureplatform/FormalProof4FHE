module
public import FormalProof4FHE.HasteBoots.NativePrefixCodec
public import FormalProof4FHE.HasteBoots.IntegerPrefixProgress
@[expose] public section

/-! Measured repeated-vector reading. Every element reader's declared operation
charge is included. Cost contracts below concern this abstract model, not arbitrary
Lean callback runtime; public byte endpoints instantiate concrete readers. Pure
length witnesses are separate from resource contracts. Native refinement remains open. -/
namespace FormalProof4FHE.HasteBoots.VectorWireReadCost
open InputIndexedOracle (Input)
open SolverOperationCost (Run)
variable {A : Type}

def weight (entry : A → ℕ) : List A → ℕ
  | [] => 0
  | head::tail => entry head+1+weight entry tail

theorem length_le_weight (entry : A → ℕ) (values : List A) : values.length ≤ weight entry values := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp only [weight,List.length_cons]; omega

def readCount (reader : Input → Run (Option (A × Input))) : ℕ → Input → Run (Option (List A × Input))
  | 0,bytes => ⟨some ([],bytes),1⟩
  | count+1,bytes =>
    let first := reader bytes
    match first.value with
    | none => ⟨none,first.cost+3⟩
    | some (value,rest) =>
      let tail := readCount reader count rest
      ⟨tail.value.map (fun pair => (value::pair.1,pair.2)),first.cost+tail.cost+5⟩

theorem readCount_value (reader : Input → Run (Option (A × Input))) (codec : NativePrefixCodec.Codec A)
    (correct : ∀ bytes, (reader bytes).value = codec.read bytes) (count : ℕ) (bytes : Input) :
    (readCount reader count bytes).value = NativePrefixCodec.readCount codec count bytes := by
  induction count generalizing bytes with
  | zero => rfl
  | succ count ih =>
    simp only [readCount,NativePrefixCodec.readCount,← correct]
    cases parsed : (reader bytes).value with
    | none => rfl
    | some pair => rcases pair with ⟨value,rest⟩; simp only [Option.bind_some,ih]

theorem readCount_length (reader : Input → Run (Option (A × Input))) (count : ℕ)
    (bytes : Input) (values : List A) (rest : Input)
    (found : (readCount reader count bytes).value = some (values,rest)) : values.length = count := by
  induction count generalizing bytes values rest with
  | zero => have same := Option.some.inj found; cases same; rfl
  | succ count ih =>
    cases parsed : (reader bytes).value with
    | none => simp only [readCount,parsed] at found; contradiction
    | some pair =>
      rcases pair with ⟨value,tail⟩
      simp only [readCount,parsed] at found
      obtain ⟨⟨remaining,last⟩,continued,same⟩ := Option.map_eq_some_iff.mp found
      have length := ih tail remaining last continued
      cases same
      simp only [List.length_cons,length]

theorem readCount_remaining (reader : Input → Run (Option (A × Input)))
    (progress : ∀ bytes value rest, (reader bytes).value = some (value,rest) → rest.length < bytes.length)
    (count : ℕ) (bytes : Input) (values : List A) (rest : Input)
    (found : (readCount reader count bytes).value = some (values,rest)) : rest.length ≤ bytes.length := by
  induction count generalizing bytes values rest with
  | zero => have same := Option.some.inj found; cases same; rfl
  | succ count ih =>
    cases parsed : (reader bytes).value with
    | none => simp only [readCount,parsed] at found; contradiction
    | some pair =>
      rcases pair with ⟨value,tail⟩
      simp only [readCount,parsed] at found
      obtain ⟨⟨remaining,last⟩,continued,same⟩ := Option.map_eq_some_iff.mp found
      have body := ih tail remaining last continued
      have first := progress bytes value tail parsed
      cases same
      dsimp only
      omega

theorem readCount_size (reader : Input → Run (Option (A × Input))) (entry : A → ℕ)
    (sized : ∀ bytes value rest, (reader bytes).value = some (value,rest) → entry value+rest.length+1 ≤ bytes.length)
    (count : ℕ) (bytes : Input) (values : List A) (rest : Input)
    (found : (readCount reader count bytes).value = some (values,rest)) :
    weight entry values+rest.length ≤ bytes.length := by
  induction count generalizing bytes values rest with
  | zero => have same := Option.some.inj found; cases same; simp [weight]
  | succ count ih =>
    cases parsed : (reader bytes).value with
    | none => simp only [readCount,parsed] at found; contradiction
    | some pair =>
      rcases pair with ⟨value,tail⟩
      simp only [readCount,parsed] at found
      obtain ⟨⟨remaining,last⟩,continued,same⟩ := Option.map_eq_some_iff.mp found
      have body := ih tail remaining last continued
      have first := sized bytes value tail parsed
      cases same
      simp only [weight]
      omega

theorem readCount_cost (reader : Input → Run (Option (A × Input))) (C : ℕ)
    (bounded : ∀ bytes, (reader bytes).cost ≤ C*(bytes.length+1))
    (success : ∀ bytes value rest, (reader bytes).value = some (value,rest) →
      (reader bytes).cost ≤ C*(bytes.length-rest.length)+1)
    (progress : ∀ bytes value rest, (reader bytes).value = some (value,rest) → rest.length < bytes.length)
    (count : ℕ) (bytes : Input) : (readCount reader count bytes).cost ≤ (C+6)*(bytes.length+1) := by
  induction count generalizing bytes with
  | zero => simp only [readCount]; nlinarith
  | succ count ih =>
    cases parsed : (reader bytes).value with
    | none =>
      have first := bounded bytes
      simp only [readCount,parsed]
      nlinarith
    | some pair =>
      rcases pair with ⟨value,rest⟩
      have first := success bytes value rest parsed
      have consumed := progress bytes value rest parsed
      have tail := ih rest
      have splitSize : bytes.length-rest.length+rest.length = bytes.length := by omega
      simp only [readCount,parsed]
      nlinarith

theorem readCount_success_cost (reader : Input → Run (Option (A × Input))) (C : ℕ)
    (success : ∀ bytes value rest, (reader bytes).value = some (value,rest) →
      (reader bytes).cost ≤ C*(bytes.length-rest.length)+1)
    (progress : ∀ bytes value rest, (reader bytes).value = some (value,rest) → rest.length < bytes.length)
    (count : ℕ) (bytes : Input) (values : List A) (rest : Input)
    (found : (readCount reader count bytes).value = some (values,rest)) :
    (readCount reader count bytes).cost ≤ (C+6)*(bytes.length-rest.length)+1 := by
  induction count generalizing bytes values rest with
  | zero => have same := Option.some.inj found; cases same; simp [readCount]
  | succ count ih =>
    cases parsed : (reader bytes).value with
    | none => simp only [readCount,parsed] at found; contradiction
    | some pair =>
      rcases pair with ⟨value,tail⟩
      simp only [readCount,parsed] at found ⊢
      obtain ⟨⟨remaining,last⟩,continued,same⟩ := Option.map_eq_some_iff.mp found
      have body := ih tail remaining last continued
      have first := success bytes value tail parsed
      have consumed := progress bytes value tail parsed
      have restSize := readCount_remaining reader progress count tail remaining last continued
      have left : bytes.length-tail.length+tail.length = bytes.length := by omega
      have right : tail.length-last.length+last.length = tail.length := by omega
      have total : bytes.length-last.length+last.length = bytes.length := by omega
      cases same
      dsimp only
      nlinarith

def read (reader : Input → Run (Option (A × Input))) (bytes : Input) : Run (Option (NativePrefixCodec.Vector A × Input)) :=
  let header := IntegerPrefixCost.readUsize bytes
  match header.value with
  | none => ⟨none,header.cost+3⟩
  | some (count,tail) =>
    let body := readCount reader count.val tail
    match decoded : body.value with
    | none => ⟨none,header.cost+body.cost+5⟩
    | some (values,rest) =>
      have fits : values.length < 2^64 := by rw [readCount_length reader count.val tail values rest decoded]; exact count.isLt
      ⟨some (⟨values,fits⟩,rest),header.cost+body.cost+6⟩

theorem read_value (reader : Input → Run (Option (A × Input))) (codec : NativePrefixCodec.Codec A)
    (correct : ∀ bytes, (reader bytes).value = codec.read bytes) (bytes : Input) :
    (read reader bytes).value = (NativePrefixCodec.vector codec).read bytes := by
  change _ = (IntegerPrefixCost.readUsize bytes).value.bind (fun count =>
    (NativePrefixCodec.readCount codec count.1.val count.2).bind (fun result =>
      if fits : result.1.length < 2^64 then some ((⟨result.1,fits⟩ : NativePrefixCodec.Vector A),result.2) else none))
  simp only [read,← readCount_value reader codec correct]
  split
  · rename_i parsed; simp only [parsed,Option.bind_none]
  · rename_i count tail parsed
    simp only [parsed,Option.bind_some]
    split
    · rename_i decoded; simp only [decoded,Option.bind_none]
    · rename_i values rest decoded
      have fits : values.length < 2^64 := by rw [readCount_length reader count.val tail values rest decoded]; exact count.isLt
      simp only [decoded,Option.bind_some,dite_eq_left fits]

theorem read_size (reader : Input → Run (Option (A × Input))) (entry : A → ℕ)
    (sized : ∀ bytes value rest, (reader bytes).value = some (value,rest) → entry value+rest.length+1 ≤ bytes.length)
    (bytes : Input) (values : NativePrefixCodec.Vector A) (rest : Input)
    (found : (read reader bytes).value = some (values,rest)) :
    weight entry values.val+rest.length+1 ≤ bytes.length := by
  simp only [read] at found
  split at found
  · contradiction
  · rename_i count tail parsed
    split at found
    · contradiction
    · rename_i rows last decoded
      have body := readCount_size reader entry sized count.val tail rows last decoded
      have header := IntegerPrefixCost.readUsize_remaining bytes count tail parsed
      have same := Option.some.inj found
      cases same
      dsimp only
      omega

theorem read_cost (reader : Input → Run (Option (A × Input))) (C : ℕ) (large : 101 ≤ C)
    (bounded : ∀ bytes, (reader bytes).cost ≤ C*(bytes.length+1))
    (success : ∀ bytes value rest, (reader bytes).value = some (value,rest) →
      (reader bytes).cost ≤ C*(bytes.length-rest.length)+1)
    (progress : ∀ bytes value rest, (reader bytes).value = some (value,rest) → rest.length < bytes.length)
    (bytes : Input) : (read reader bytes).cost ≤ (C+6)*(bytes.length+1)+3 := by
  have header := IntegerPrefixCost.readUsize_cost bytes
  cases parsed : (IntegerPrefixCost.readUsize bytes).value with
  | none => simp only [read,parsed]; nlinarith
  | some pair =>
    rcases pair with ⟨count,tail⟩
    have consumed := IntegerPrefixCost.readUsize_remaining bytes count tail parsed
    have body := readCount_cost reader C bounded success progress count.val tail
    have product := Nat.mul_le_mul_left (C+6) (show tail.length+1 ≤ bytes.length by omega)
    simp only [read,parsed]
    split <;> dsimp only <;> nlinarith

theorem read_success_cost (reader : Input → Run (Option (A × Input))) (C : ℕ) (large : 101 ≤ C)
    (success : ∀ bytes value rest, (reader bytes).value = some (value,rest) →
      (reader bytes).cost ≤ C*(bytes.length-rest.length)+1)
    (progress : ∀ bytes value rest, (reader bytes).value = some (value,rest) → rest.length < bytes.length)
    (bytes : Input) (values : NativePrefixCodec.Vector A) (rest : Input)
    (found : (read reader bytes).value = some (values,rest)) :
    (read reader bytes).cost ≤ (C+6)*(bytes.length-rest.length)+1 := by
  have header := IntegerPrefixCost.readUsize_cost bytes
  simp only [read] at found ⊢
  split at found
  · contradiction
  · rename_i count tail parsed
    split at found
    · contradiction
    · rename_i rows last decoded
      have body := readCount_success_cost reader C success progress count.val tail rows last decoded
      have first := IntegerPrefixCost.readUsize_remaining bytes count tail parsed
      have length := readCount_remaining reader progress count.val tail rows last decoded
      have product := Nat.mul_le_mul_left (C+6) (show tail.length+1 ≤ bytes.length by omega)
      have left : tail.length-last.length+last.length = tail.length := by omega
      have right : bytes.length-last.length+last.length = bytes.length := by omega
      have same := Option.some.inj found
      cases same
      dsimp only
      nlinarith
end FormalProof4FHE.HasteBoots.VectorWireReadCost
