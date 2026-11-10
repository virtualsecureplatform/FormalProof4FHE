module
public import FormalProof4FHE.HasteBoots.CanonicalKeySwitch
public import FormalProof4FHE.HasteBoots.PackedAccumulatorTrace
public import FormalProof4FHE.HasteBoots.QueryReindex
@[expose] public section

/-! The native extraction shape has the three original roles increment,
public mask, public target, and relation increment*mask-target=0. Only the
increment requires an authenticated opening. The coefficient semantics below
retain this exact role order; authentication and Fiat--Shamir are separate. -/
namespace FormalProof4FHE.HasteBoots.KeySwitchExtraction
open NativeBlindRotation (Cipher)
noncomputable section
variable {q n dimension : ℕ} [NeZero n]

/-- Native mask: a0, a(N-i) for 1<=i<dimension, and b0. -/
def mask (q n dimension : ℕ) : Cipher q n := fun half index =>
  if half then (if index.val = 0 then 1 else 0)
  else if index.val = 0 then 1 else if n-index.val < dimension then 1 else 0

/-- The input accumulator already includes the public q/8 body bias. -/
def target (positive : 0 < dimension) (acc : Cipher q n) (output : NativePublic.Ciphertext q dimension) : Cipher q n :=
  fun half index => if half then (if index.val = 0 then output.body-acc true NativeKeySwitch.zeroIndex else 0)
    else if _zero : index.val = 0 then output.mask ⟨0,positive⟩
    else if small : n-index.val < dimension then -output.mask ⟨n-index.val,small⟩ else 0

def Masked (positive : 0 < dimension) (acc increment : Cipher q n) (output : NativePublic.Ciphertext q dimension) : Prop :=
  ∀ half index, increment half index * mask q n dimension half index = target positive acc output half index

theorem extraction_of_masked (shape : dimension ≤ n) (positive : 0 < dimension)
    (acc increment : Cipher q n) (output : NativePublic.Ciphertext q dimension) (checked : Masked positive acc increment output) :
    CanonicalKeySwitch.Extraction shape acc increment output := by
  constructor
  · intro i
    by_cases zero : i.val = 0
    · have selected := checked false NativeKeySwitch.zeroIndex
      have same : i = ⟨0,positive⟩ := Fin.ext zero
      simp only [zero,dite_true]
      simpa [mask,target,NativeKeySwitch.zeroIndex,same] using selected
    · let reverse : Fin n := ⟨n-i.val,by have := i.isLt; omega⟩
      have nonzero : reverse.val ≠ 0 := by dsimp [reverse]; have := i.isLt; omega
      have reversed : n-reverse.val = i.val := by dsimp [reverse]; have := i.isLt; omega
      have small : n-reverse.val < dimension := by rw [reversed]; exact i.isLt
      have same : (⟨n-reverse.val,small⟩ : Fin dimension) = i := Fin.ext reversed
      have selected := checked false reverse
      simp only [mask,target,Bool.false_eq_true,ite_false,nonzero,dite_false,small,ite_true,dite_true,mul_one,same] at selected
      simpa only [zero,dite_false,reverse] using selected
  · have selected := checked true NativeKeySwitch.zeroIndex
    simpa only [mask,target,NativeKeySwitch.zeroIndex,Fin.val_zero,Bool.true_eq,ite_true,mul_one] using selected

variable {c lanes : ℕ} [Fact q.Prime]

omit [Fact q.Prime] in
theorem transport_injective {a b : ℕ} (equal : a = b) :
    Function.Injective (QueryReindex.source (F := ZMod q) (k := 2^lanes) equal) := by
  cases equal
  intro first last same
  exact same

/-- Native coefficient/lane/half packing, transported only across addition
of dimensions. No source entries or lane coordinates are selected away. -/
def pack (value : Cipher q (2^(c+lanes))) : MatrixFold.Cube (c+1) → Fin (2^lanes) → ZMod q :=
  QueryReindex.source (Nat.add_comm c 1)
    (AccumulatorEndpointSoundness.publicTable (PackedAccumulatorTrace.endpoint (RingHom.id _) value))

theorem pack_injective : Function.Injective (pack (q := q) (c := c) (lanes := lanes)) := by
  intro first last same
  exact PackedAccumulatorTrace.public_injective (c := c) (lanes := lanes) (RingHom.id (ZMod q))
    ((transport_injective (lanes := lanes) (Nat.add_comm c 1)) same)

theorem pack_mul (first last : Cipher q (2^(c+lanes))) : pack (c := c) (lanes := lanes) (first*last) = pack first*pack last := rfl

/-- The first factor is the only private extraction source. The public mask
and target occupy native factor slots 1 and 2, respectively. -/
def tables (positive : 0 < dimension) (acc increment : Cipher q (2^(c+lanes))) (output : NativePublic.Ciphertext q dimension) :
    PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor 1) (c+1) (2^lanes) :=
  fun factor => match factor with
    | .inl (_,false) => pack increment
    | .inl (_,true) => pack (mask q (2^(c+lanes)) dimension)
    | .inr _ => pack (target positive acc output)

theorem masked_of_relation (positive : 0 < dimension) (acc increment : Cipher q (2^(c+lanes)))
    (output : NativePublic.Ciphertext q dimension) (relation : PBSHadamard.Relation (tables (c := c) (lanes := lanes) positive acc increment output)) :
    Masked positive acc increment output := by
  have packed : pack (c := c) (lanes := lanes) (target positive acc output) = pack (increment*mask q (2^(c+lanes)) dimension) := by
    rw [pack_mul]
    funext cell lane
    simpa only [tables,Fin.sum_univ_one,Pi.mul_apply] using relation cell lane
  have equal := pack_injective packed
  exact fun half index => (congrFun (congrFun equal half) index).symm

theorem extraction_of_relation (shape : dimension ≤ 2^(c+lanes)) (positive : 0 < dimension)
    (acc increment : Cipher q (2^(c+lanes))) (output : NativePublic.Ciphertext q dimension)
    (relation : PBSHadamard.Relation (tables (c := c) (lanes := lanes) positive acc increment output)) :
    CanonicalKeySwitch.Extraction shape acc increment output :=
  extraction_of_masked shape positive acc increment output (masked_of_relation positive acc increment output relation)

theorem false_zero_relation (shape : dimension ≤ 2^(c+lanes)) (positive : 0 < dimension)
    (acc increment : Cipher q (2^(c+lanes))) (output : NativePublic.Ciphertext q dimension)
    (wrong : ¬CanonicalKeySwitch.Extraction shape acc increment output) :
    ¬PackedZeroCube.Vanishes PBSHadamard.arity PBSHadamard.coefficient PBSHadamard.indices
      (tables (c := c) (lanes := lanes) positive acc increment output) := by
  intro vanishes
  exact wrong (extraction_of_relation shape positive acc increment output ((PBSHadamard.vanishes_iff _).mp vanishes))

/-- Literal terminal roles: the prover supplies only the increment value;
mask and target values are computed from the same full ordered query. -/
def values (query : PackedSumcheckSubclaim.Query (ZMod q) (2^lanes) (c+1))
    (positive : 0 < dimension) (acc : Cipher q (2^(c+lanes))) (output : NativePublic.Ciphertext q dimension)
    (claimed : Fin (2^lanes) → ZMod q) : PBSHadamard.Factor 1 → Fin (2^lanes) → ZMod q :=
  fun factor => match factor with
    | .inl (_,false) => claimed
    | .inl (_,true) => query.fold (pack (mask q (2^(c+lanes)) dimension))
    | .inr _ => query.fold (pack (target positive acc output))

theorem checked_truthful_or_wrong_increment (nodes : PackedSumcheckRound.Node (2^lanes) ↪ ZMod q)
    (positive : 0 < dimension) (acc increment : Cipher q (2^(c+lanes))) (output : NativePublic.Ciphertext q dimension)
    (claim : PackedZeroOracle.Subclaim (ZMod q) (2^lanes) c) (claimed : Fin (2^lanes) → ZMod q)
    (checked : PackedZeroOracle.Subclaim.check PBSHadamard.arity PBSHadamard.coefficient PBSHadamard.indices
      (values (claim.query nodes) positive acc output claimed) claim = true) :
    PackedZeroOracle.Subclaim.Truthful nodes PBSHadamard.arity PBSHadamard.coefficient PBSHadamard.indices
      (tables (c := c) (lanes := lanes) positive acc increment output) claim ∨
      claimed ≠ (claim.query nodes).fold (pack increment) := by
  rcases PackedZeroOracle.Subclaim.checked_truthful_or_wrong nodes PBSHadamard.arity PBSHadamard.coefficient PBSHadamard.indices
    (tables (c := c) (lanes := lanes) positive acc increment output)
    (values (claim.query nodes) positive acc output claimed) claim checked with truthful | ⟨factor,wrong⟩
  · exact Or.inl truthful
  · right
    rcases factor with ⟨index,bit⟩ | ⟨⟩
    · cases bit
      · exact wrong
      · exact False.elim (wrong rfl)
    · exact False.elim (wrong rfl)

end
end FormalProof4FHE.HasteBoots.KeySwitchExtraction
