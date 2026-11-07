module
public import FormalProof4FHE.HasteBoots.UsizeVectorSuccessCost
public import FormalProof4FHE.HasteBoots.RowEncodingCost
@[expose] public section

/-! Measured nested native public-table wire operations. Row and table counts
are untrusted; failures stop on supplied bytes. Consumed-byte bounds give linear
prefix decoding without a count cap. Raw u64 entries, empty/ragged rows and
original row order are retained. Physical/native refinement is separate. -/
namespace FormalProof4FHE.HasteBoots.TableWireCost
open InputIndexedOracle (Input)
open NativeLookupRequestWire (Row Table rowCodec tableCodec)
open SolverOperationCost (Run)

def cells : List Row → ℕ
  | [] => 0
  | head::tail => head.val.length+1+cells tail

theorem length_le_cells (rows : List Row) : rows.length ≤ cells rows := by
  induction rows with
  | nil => rfl
  | cons head tail ih => simp only [cells,List.length_cons]; omega

def readCount : ℕ → Input → Run (Option (List Row × Input))
  | 0,bytes => ⟨some ([],bytes),1⟩
  | count+1,bytes =>
    let first := UsizeVectorCost.read bytes
    match first.value with
    | none => ⟨none,first.cost+3⟩
    | some (row,rest) =>
      let tail := readCount count rest
      ⟨tail.value.map (fun pair => (row::pair.1,pair.2)),first.cost+tail.cost+5⟩

theorem readCount_value (count : ℕ) (bytes : Input) :
    (readCount count bytes).value = NativePrefixCodec.readCount rowCodec count bytes := by
  induction count generalizing bytes with
  | zero => rfl
  | succ count ih =>
    simp only [readCount,NativePrefixCodec.readCount,rowCodec]
    cases parsed : (UsizeVectorCost.read bytes).value with
    | none => rfl
    | some pair => rcases pair with ⟨row,rest⟩; simp only [Option.bind_some,ih]; rfl

/-- Pure list-length proof used for bounded table construction. -/
theorem readCount_length (count : ℕ) (bytes : Input) (rows : List Row) (rest : Input)
    (found : (readCount count bytes).value = some (rows,rest)) : rows.length = count := by
  induction count generalizing bytes rows rest with
  | zero => have same := Option.some.inj found; cases same; rfl
  | succ count ih =>
    cases parsed : (UsizeVectorCost.read bytes).value with
    | none => simp only [readCount,parsed] at found; contradiction
    | some pair =>
      rcases pair with ⟨row,tail⟩
      simp only [readCount,parsed] at found
      obtain ⟨⟨remaining,last⟩,continued,same⟩ := Option.map_eq_some_iff.mp found
      have length := ih tail remaining last continued
      cases same
      simp only [List.length_cons,length]

theorem readCount_remaining (count : ℕ) (bytes : Input) (rows : List Row) (rest : Input)
    (found : (readCount count bytes).value = some (rows,rest)) : cells rows+rest.length ≤ bytes.length := by
  induction count generalizing bytes rows rest with
  | zero => have same := Option.some.inj found; cases same; simp [cells]
  | succ count ih =>
    cases parsed : (UsizeVectorCost.read bytes).value with
    | none => simp only [readCount,parsed] at found; contradiction
    | some pair =>
      rcases pair with ⟨row,tail⟩
      simp only [readCount,parsed] at found
      obtain ⟨⟨remaining,last⟩,continued,same⟩ := Option.map_eq_some_iff.mp found
      have body := ih tail remaining last continued
      have first := UsizeVectorCost.read_remaining bytes row tail parsed
      cases same
      simp only [cells]
      omega

theorem readCount_cost (count : ℕ) (bytes : Input) :
    (readCount count bytes).cost ≤ 113*(bytes.length+1) := by
  induction count generalizing bytes with
  | zero => simp only [readCount]; omega
  | succ count ih =>
    cases parsed : (UsizeVectorCost.read bytes).value with
    | none =>
      have first := UsizeVectorCost.read_cost bytes
      simp only [readCount,parsed]
      omega
    | some pair =>
      rcases pair with ⟨row,rest⟩
      have first := UsizeVectorSuccessCost.read_cost bytes row rest parsed
      have progress := UsizeVectorCost.read_remaining bytes row rest parsed
      have tail := ih rest
      simp only [readCount,parsed]
      omega

theorem readCount_success_cost (count : ℕ) (bytes : Input) (rows : List Row) (rest : Input)
    (found : (readCount count bytes).value = some (rows,rest)) :
    (readCount count bytes).cost ≤ 113*(bytes.length-rest.length)+1 := by
  induction count generalizing bytes rows rest with
  | zero => have same := Option.some.inj found; cases same; simp [readCount]
  | succ count ih =>
    cases parsed : (UsizeVectorCost.read bytes).value with
    | none => simp only [readCount,parsed] at found; contradiction
    | some pair =>
      rcases pair with ⟨row,tail⟩
      simp only [readCount,parsed] at found ⊢
      obtain ⟨⟨remaining,last⟩,continued,same⟩ := Option.map_eq_some_iff.mp found
      have body := ih tail remaining last continued
      have first := UsizeVectorSuccessCost.read_cost bytes row tail parsed
      have progress := UsizeVectorCost.read_remaining bytes row tail parsed
      have remainingSize := readCount_remaining count tail remaining last continued
      cases same
      dsimp only
      omega

def read (bytes : Input) : Run (Option (Table × Input)) :=
  let header := IntegerPrefixCost.readUsize bytes
  match header.value with
  | none => ⟨none,header.cost+3⟩
  | some (count,tail) =>
    let body := readCount count.val tail
    match decoded : body.value with
    | none => ⟨none,header.cost+body.cost+5⟩
    | some (rows,rest) =>
      have fits : rows.length < 2^64 := by
        rw [readCount_length count.val tail rows rest decoded]
        exact count.isLt
      ⟨some (⟨rows,fits⟩,rest),header.cost+body.cost+6⟩

theorem read_value (bytes : Input) : (read bytes).value = tableCodec.read bytes := by
  change _ = (IntegerPrefixCost.readUsize bytes).value.bind (fun count =>
    (NativePrefixCodec.readCount rowCodec count.1.val count.2).bind (fun result =>
      if fits : result.1.length < 2^64 then some ((⟨result.1,fits⟩ : Table),result.2) else none))
  simp only [read,← readCount_value]
  split
  · rename_i parsed; simp only [parsed,Option.bind_none]
  · rename_i count tail parsed
    simp only [parsed,Option.bind_some]
    split
    · rename_i decoded; simp only [decoded,Option.bind_none]
    · rename_i rows rest decoded
      have fits : rows.length < 2^64 := by rw [readCount_length count.val tail rows rest decoded]; exact count.isLt
      simp only [decoded,Option.bind_some,dite_eq_left fits]

theorem read_cost (bytes : Input) : (read bytes).cost ≤ 113*(bytes.length+1)+3 := by
  have header := IntegerPrefixCost.readUsize_cost bytes
  cases parsed : (IntegerPrefixCost.readUsize bytes).value with
  | none => simp only [read,parsed]; omega
  | some pair =>
    rcases pair with ⟨count,tail⟩
    have first := IntegerPrefixCost.readUsize_remaining bytes count tail parsed
    have body := readCount_cost count.val tail
    simp only [read,parsed]
    split <;> dsimp only <;> omega

theorem read_remaining (bytes : Input) (table : Table) (rest : Input)
    (found : (read bytes).value = some (table,rest)) : cells table.val+rest.length < bytes.length := by
  simp only [read] at found
  split at found
  · contradiction
  · rename_i count tail parsed
    split at found
    · contradiction
    · rename_i rows last decoded
      have body := readCount_remaining count.val tail rows last decoded
      have header := IntegerPrefixCost.readUsize_remaining bytes count tail parsed
      have same := Option.some.inj found
      cases same
      dsimp only
      omega

theorem read_success_cost (bytes : Input) (table : Table) (rest : Input)
    (found : (read bytes).value = some (table,rest)) :
    (read bytes).cost ≤ 113*(bytes.length-rest.length)+1 := by
  have header := IntegerPrefixCost.readUsize_cost bytes
  simp only [read] at found ⊢
  split at found
  · contradiction
  · rename_i count tail parsed
    split at found
    · contradiction
    · rename_i rows last decoded
      have body := readCount_success_cost count.val tail rows last decoded
      have remainingSize := readCount_remaining count.val tail rows last decoded
      have first := IntegerPrefixCost.readUsize_remaining bytes count tail parsed
      have same := Option.some.inj found
      cases same
      dsimp only
      omega

def body : List Row → Run Input
  | [] => ⟨[],1⟩
  | head::tail =>
    let first := RowEncodingCost.encode head
    let rest := body tail
    let joined := RowEncodingCost.append first.value rest.value
    ⟨joined.value,first.cost+rest.cost+joined.cost+5⟩

theorem body_value (rows : List Row) : (body rows).value = rows.flatMap rowCodec.encode := by
  induction rows with
  | nil => rfl
  | cons head tail ih => simp only [body,RowEncodingCost.append_value,RowEncodingCost.encode_value,List.flatMap_cons,ih]

theorem body_cost (rows : List Row) : (body rows).cost ≤ 126*cells rows+1 := by
  induction rows with
  | nil => simp [body,cells]
  | cons head tail ih =>
    have first := RowEncodingCost.encode_cost head
    have size := RowEncodingCost.encode_length head
    simp only [body,RowEncodingCost.append_cost,cells]
    omega

theorem body_size (rows : List Row) : (body rows).value.length ≤ 9*cells rows := by
  induction rows with
  | nil => simp [body,cells]
  | cons head tail ih =>
    have first := RowEncodingCost.encode_length head
    simp only [body,RowEncodingCost.append_value,List.length_append,cells]
    omega

def encode (table : Table) : Run Input :=
  let count := RowEncodingCost.length table.val
  let header := IntegerEncodingCost.encode ⟨count.value,by rw [RowEncodingCost.length_value]; exact table.property⟩
  let bytes := body table.val
  let joined := RowEncodingCost.append header.value bytes.value
  ⟨joined.value,count.cost+header.cost+bytes.cost+joined.cost+4⟩

theorem encode_value (table : Table) : (encode table).value = tableCodec.encode table := by
  simp only [encode,RowEncodingCost.append_value,RowEncodingCost.length_value,IntegerEncodingCost.encode_value,
    body_value,tableCodec,NativePrefixCodec.vector,NativePrefixCodec.usize]

theorem encode_cost (table : Table) : (encode table).cost ≤ 129*cells table.val+93 := by
  have body := body_cost table.val
  have count := length_le_cells table.val
  have header := IntegerEncodingCost.encode_cost
    (⟨(RowEncodingCost.length table.val).value,by rw [RowEncodingCost.length_value]; exact table.property⟩ : NativeUsizeMessage.Usize)
  have size := IntegerEncodingCost.encode_length
    (⟨(RowEncodingCost.length table.val).value,by rw [RowEncodingCost.length_value]; exact table.property⟩ : NativeUsizeMessage.Usize)
  simp only [encode,RowEncodingCost.length_cost,RowEncodingCost.append_cost]
  omega

theorem encode_size (table : Table) : (encode table).value.length ≤ 9*(cells table.val+1) := by
  have body := body_size table.val
  have header := IntegerEncodingCost.encode_length
    (⟨(RowEncodingCost.length table.val).value,by rw [RowEncodingCost.length_value]; exact table.property⟩ : NativeUsizeMessage.Usize)
  simp only [encode,RowEncodingCost.append_value,List.length_append]
  omega
end FormalProof4FHE.HasteBoots.TableWireCost
