module
public import FormalProof4FHE.HasteBoots.BytePrefixCost
public import FormalProof4FHE.HasteBoots.NativeUsizeMessage
@[expose] public section

/-! Measured bincode integer serialization. Charges cover abstract word
arithmetic, byte/list construction and control. Native integer arithmetic and
compiler refinement remain separate. -/
namespace FormalProof4FHE.HasteBoots.IntegerEncodingCost
open InputIndexedOracle (Input)
open NativeUsizeMessage (Usize)
open SolverOperationCost (Run)

def littleEndian : ℕ → ℕ → Run Input
  | 0,_ => ⟨[],1⟩
  | width+1,value =>
    let tail := littleEndian width (value/256)
    ⟨⟨value%256,Nat.mod_lt _ (by decide)⟩::tail.value,tail.cost+6⟩

theorem littleEndian_value (width value : ℕ) :
    (littleEndian width value).value = TranscriptFrame.littleEndian width value := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp only [littleEndian,TranscriptFrame.littleEndian,ih]

theorem littleEndian_cost (width value : ℕ) :
    (littleEndian width value).cost = 6*width+1 := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp only [littleEndian,ih]; omega

def encode (value : Usize) : Run Input :=
  if small : value.val < 251 then
    ⟨[⟨value.val,Nat.lt_trans small (by decide : 251 < 256)⟩],5⟩
  else if value.val < 2^16 then
    let bytes := littleEndian 2 value.val
    ⟨251::bytes.value,bytes.cost+6⟩
  else if value.val < 2^32 then
    let bytes := littleEndian 4 value.val
    ⟨252::bytes.value,bytes.cost+8⟩
  else
    let bytes := littleEndian 8 value.val
    ⟨253::bytes.value,bytes.cost+10⟩

theorem encode_value (value : Usize) :
    (encode value).value = NativeUsizeMessage.encode value := by
  simp only [encode,NativeUsizeMessage.encode]
  split_ifs <;> simp only [littleEndian_value]

theorem encode_cost (value : Usize) : (encode value).cost ≤ 59 := by
  simp only [encode]
  split
  · norm_num
  · split
    · simp only [littleEndian_cost]; norm_num
    · split <;> simp only [littleEndian_cost] <;> norm_num

theorem encode_length (value : Usize) : (encode value).value.length ≤ 9 := by
  rw [encode_value]
  exact NativeUsizeMessage.encode_length value
end FormalProof4FHE.HasteBoots.IntegerEncodingCost
