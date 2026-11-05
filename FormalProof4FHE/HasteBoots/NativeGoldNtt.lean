module

public import FormalProof4FHE.HasteBoots.NativeGoldSolinas

@[expose] public section

/-! Functional buffers for concrete-ntt's canonical Goldilocks scalar forward
kernel. Twiddle initialization, breadth-first stages, and the depth-first
1024-element cutoff follow the locked source. SIMD, root discovery/cache,
Div64 instruction refinement, in-place writes and work costs remain separate.
No transform result or correctness certificate is a protocol input. The
universal scalar-NTT evaluation/code correspondence is still open. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldNtt

open NativeFieldRepresentation NativeFields
open NativeGoldSolinas (Word)

def reverse : ℕ → ℕ → ℕ
  | 0,_ => 0
  | n+1,index => (index%2)*2^n+reverse n (index/2)

theorem reverse_bound (n index : ℕ) : reverse n index < 2^n := by
  induction n generalizing index with
  | zero => simp only [reverse,pow_zero]; omega
  | succ n ih =>
    have previous := ih (index/2)
    have bit := Nat.mod_lt index (by decide : 0 < 2)
    have positive : 0 < 2^n := by positivity
    rw [reverse,pow_succ]
    nlinarith

def init (log : ℕ) (root : Word) : ℕ → List Word × Word
  | 0 => (List.replicate (2^log) 0,1)
  | count+1 =>
    let earlier := init log root count
    (earlier.1.set (reverse log count) earlier.2,NativeGoldSolinas.mul earlier.2 root)

def twiddles (log : ℕ) (root : Word) : List Word := (init log root (2^log)).1

/-- One entire native butterfly stage reads each old pair before writing it.
`remaining` gives log2(t); `start` is the current source twiddle offset. -/
def stage (log remaining start : ℕ) (twid data : List Word) : List Word :=
  (List.range (2^log)).map (fun index =>
    let t := 2^remaining
    let group := index/(2*t)
    let first := group*(2*t)+index%t
    let low := data[first]?.getD 0
    let high := data[first+t]?.getD 0
    let weighted := NativeGoldSolinas.mul high (twid[start+group]?.getD 0)
    if index/t%2 = 0 then NativeGoldSolinas.add low weighted else NativeGoldSolinas.sub low weighted)

/-- Native m doubles, t halves and w_idx doubles after every stage. -/
def breadth (log depth half : ℕ) (twid : List Word) : ℕ → List Word → List Word
  | 0,data => data
  | remaining+1,data =>
    let m := 2^(log-(remaining+1))
    breadth log depth half twid remaining (stage log remaining (m*2^depth+half*m) twid data)

/-- Above 1024, execute one stage and recurse on the two contiguous halves. -/
def depthFirst : (log depth half : ℕ) → List Word → List Word → List Word
  | 0,depth,half,twid,data => breadth 0 depth half twid 0 data
  | log+1,depth,half,twid,data =>
    if log+1 ≤ 10 then breadth (log+1) depth half twid (log+1) data
    else
      let next := stage (log+1) log (2^depth+half) twid data
      depthFirst log (depth+1) (half*2) twid (next.take (2^log)) ++
        depthFirst log (depth+1) (half*2+1) twid (next.drop (2^log))

def forwardData (log : ℕ) (root : Word) (data : List GoldWord) : List GoldWord :=
  (depthFirst log 0 0 (twiddles log root) (data.map NativeGoldSolinas.canonical)).map NativeGoldSolinas.raw

/-- The Goldilocks wrapper canonicalizes the complete coefficient buffer
immediately before calling the plan's integer forward transform. -/
def forward (log : ℕ) (root : Word) (data : List GoldWord) : Option (List GoldWord) :=
  if 4 ≤ log ∧ log ≤ 31 then
    if data.length = 2^log then
      some (forwardData log root data)
    else none
  else none

theorem init_length (log : ℕ) (root : Word) (count : ℕ) : (init log root count).1.length = 2^log := by
  induction count with
  | zero => exact List.length_replicate
  | succ count ih => simp only [init,List.length_set,ih]

theorem init_power (log : ℕ) (root : Word) (count : ℕ) : (init log root count).2 = NativeGoldSolinas.pow root count := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [init,NativeGoldSolinas.pow,ih]

theorem twiddles_length (log : ℕ) (root : Word) : (twiddles log root).length = 2^log := init_length _ _ _

/-- Every source pair read by a valid stage is wholly inside the old buffer. -/
theorem pair_addresses (log remaining : ℕ) (before : remaining < log) (index : Fin (2^log)) :
    let t := 2^remaining
    let first := (index.val/(2*t))*(2*t)+index.val%t
    first < 2^log ∧ first+t < 2^log := by
  have power : 2^log = 2^(log-(remaining+1))*(2*2^remaining) := by
    conv_lhs => rw [← Nat.sub_add_cancel (by omega : remaining+1 ≤ log),pow_add,pow_succ]
    ac_rfl
  have groups : index.val/(2*2^remaining) < 2^(log-(remaining+1)) := by
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2*2^remaining)).mpr
    rw [← power]
    exact index.isLt
  have cap := Nat.mul_le_mul_right (2*2^remaining) (Nat.succ_le_of_lt groups)
  rw [Nat.succ_mul,← power] at cap
  have inside := Nat.mod_lt index.val (by positivity : 0 < 2^remaining)
  dsimp only
  constructor <;> omega

/-- The twiddle slice is also in bounds, including recursive subtransforms. -/
theorem twiddle_address (log remaining depth half : ℕ) (before : remaining < log)
    (halfBound : half < 2^depth) (index : Fin (2^log)) :
    let m := 2^(log-(remaining+1))
    m*2^depth+half*m+index.val/(2*2^remaining) < 2^(log+depth) := by
  have power : 2^log = 2^(log-(remaining+1))*(2*2^remaining) := by
    conv_lhs => rw [← Nat.sub_add_cancel (by omega : remaining+1 ≤ log),pow_add,pow_succ]
    ac_rfl
  have groups : index.val/(2*2^remaining) < 2^(log-(remaining+1)) := by
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2*2^remaining)).mpr
    rw [← power]
    exact index.isLt
  have capped := Nat.mul_le_mul_right (2^(log-(remaining+1))) (Nat.succ_le_of_lt halfBound)
  have stageBound : 2^(log-(remaining+1))*2^depth+half*2^(log-(remaining+1))+index.val/(2*2^remaining) <
      2^(log-(remaining+1))*2^depth*2 := by nlinarith
  have combine : 2^(log-(remaining+1))*2^depth*2 = 2^((log-(remaining+1))+depth+1) := by
    rw [pow_succ,pow_add]
  have total : 2^((log-(remaining+1))+depth+1) ≤ 2^(log+depth) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  exact lt_of_lt_of_le (stageBound.trans_eq combine) total

theorem stage_length (log remaining start : ℕ) (twid data : List Word) :
    (stage log remaining start twid data).length = 2^log := by simp only [stage,List.length_map,List.length_range]

theorem breadth_length (log depth half : ℕ) (twid : List Word) (rounds : ℕ) (data : List Word)
    (size : data.length = 2^log) : (breadth log depth half twid rounds data).length = 2^log := by
  induction rounds generalizing data with
  | zero => exact size
  | succ rounds ih => exact ih _ (stage_length _ _ _ _ _)

theorem depthFirst_length (log depth half : ℕ) (twid data : List Word) (size : data.length = 2^log) :
    (depthFirst log depth half twid data).length = 2^log := by
  induction log generalizing depth half data with
  | zero => exact size
  | succ log ih =>
    simp only [depthFirst]
    split
    · exact breadth_length _ _ _ _ _ _ size
    · rw [List.length_append,ih _ _ _ (by rw [List.length_take,stage_length,pow_succ]; omega),
        ih _ _ _ (by rw [List.length_drop,stage_length,pow_succ]; omega),pow_succ]
      omega

theorem forwardData_length (log : ℕ) (root : Word) (data : List GoldWord) (size : data.length = 2^log) :
    (forwardData log root data).length = 2^log := by
  rw [forwardData,List.length_map,depthFirst_length _ _ _ _ _ (by rw [List.length_map,size])]

theorem forwardData_canonical (log : ℕ) (root : Word) (data : List GoldWord) :
    ∀ word ∈ forwardData log root data, word.val < goldilocksModulus := by
  intro word member
  obtain ⟨canonical,_,same⟩ := List.mem_map.mp member
  subst word
  exact canonical.isLt

theorem forward_shape (log : ℕ) (root : Word) (data result : List GoldWord)
    (success : forward log root data = some result) :
    4 ≤ log ∧ log ≤ 31 ∧ data.length = 2^log ∧ result.length = 2^log ∧
      ∀ word ∈ result, word.val < goldilocksModulus := by
  unfold forward at success
  split at success
  · rename_i valid
    split at success
    · rename_i size
      have same := Option.some.inj success
      subst result
      dsimp only [forwardData]
      refine ⟨valid.1,valid.2,size,?_,?_⟩
      · rw [List.length_map,depthFirst_length _ _ _ _ _ (by rw [List.length_map,size])]
      · intro word member
        obtain ⟨canonical,_,same⟩ := List.mem_map.mp member
        subst word
        exact canonical.isLt
    · contradiction
  · contradiction

end FormalProof4FHE.HasteBoots.NativeGoldNtt
