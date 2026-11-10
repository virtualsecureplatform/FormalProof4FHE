module
public import FormalProof4FHE.HasteBoots.NativeKeySwitch
public import FormalProof4FHE.HasteBoots.PBSHadamardBlindRotation
@[expose] public section

/-! The native equal-dimension key switch decomposes the canonical residue of
-a, then ADDS the original key products. This is generally different from
subtracting digit(a)*key. The frozen NativeKeySwitch reference models the
latter and must not be used as a refinement of this native operation. We reuse
only its constant-body initialization and partial extraction functions. -/
namespace FormalProof4FHE.HasteBoots.CanonicalKeySwitch
open scoped BigOperators
open NativeBlindRotation (Poly Cipher digit mul)
noncomputable section
variable {q n levels dimension : ℕ} [NeZero n]

def increment (bits : ℕ) (key : NativeKeySwitch.Key q n levels) (mask : Poly q n) : Cipher q n :=
  fun half index => ∑ level : Fin levels, mul (digit bits level (-mask)) (key level half) index

def switch (bits : ℕ) (key : NativeKeySwitch.Key q n levels) (acc : Cipher q n) : Cipher q n :=
  NativeKeySwitch.initial acc + increment bits key (acc false)

structure Trace (q n : ℕ) where
  increment : Cipher q n
  switched : Cipher q n

def Valid (bits : ℕ) (key : NativeKeySwitch.Key q n levels) (shape : dimension ≤ n)
    (acc : Cipher q n) (trace : Trace q n) (output : NativePublic.Ciphertext q dimension) : Prop :=
  trace.increment = increment bits key (acc false) ∧
  trace.switched = NativeKeySwitch.initial acc + trace.increment ∧ output = NativeKeySwitch.extract shape trace.switched

def makeTrace (bits : ℕ) (key : NativeKeySwitch.Key q n levels) (acc : Cipher q n) : Trace q n :=
  ⟨increment bits key (acc false),switch bits key acc⟩

theorem makeTrace_valid (bits : ℕ) (key : NativeKeySwitch.Key q n levels) (shape : dimension ≤ n) (acc : Cipher q n) :
    Valid bits key shape acc (makeTrace bits key acc) (NativeKeySwitch.extract shape (switch bits key acc)) := ⟨rfl,rfl,rfl⟩

theorem valid_output (bits : ℕ) (key : NativeKeySwitch.Key q n levels) (shape : dimension ≤ n)
    (acc : Cipher q n) (trace : Trace q n) (output : NativePublic.Ciphertext q dimension) (valid : Valid bits key shape acc trace output) :
    output = NativeKeySwitch.extract shape (switch bits key acc) := by
  rcases valid with ⟨product,combined,extracted⟩
  rw [extracted,combined,product]
  rfl

/-- The coefficient positions selected by the native public extraction mask.
All unused mask coordinates remain unconstrained, as in partial extraction. -/
def Extraction (shape : dimension ≤ n) (acc increment : Cipher q n)
    (output : NativePublic.Ciphertext q dimension) : Prop :=
  (∀ i : Fin dimension, if zero : i.val = 0 then
    increment false NativeKeySwitch.zeroIndex = output.mask i else
    increment false ⟨n-i.val,by have := i.isLt; omega⟩ = -output.mask i) ∧
  increment true NativeKeySwitch.zeroIndex = output.body-acc true NativeKeySwitch.zeroIndex

theorem ciphertext_ext (first last : NativePublic.Ciphertext q dimension)
    (masks : first.mask = last.mask) (bodies : first.body = last.body) : first = last := by
  cases first
  cases last
  cases masks
  cases bodies
  rfl

theorem extract_of_constraints (shape : dimension ≤ n) (acc increment : Cipher q n)
    (output : NativePublic.Ciphertext q dimension) (checked : Extraction shape acc increment output) :
    output = NativeKeySwitch.extract shape (NativeKeySwitch.initial acc+increment) := by
  apply ciphertext_ext
  · funext i
    have selected := checked.1 i
    by_cases zero : i.val = 0
    · simp only [zero, dite_true] at selected
      simpa only [NativeKeySwitch.extract,zero,dite_true,Pi.add_apply,NativeKeySwitch.initial,
        Bool.false_and,Bool.false_eq_true,ite_false,zero_add] using selected.symm
    · simp only [zero,dite_false] at selected
      simp only [NativeKeySwitch.extract,zero,dite_false,Pi.add_apply,NativeKeySwitch.initial,
        Bool.false_and,Bool.false_eq_true,ite_false,zero_add,selected,neg_neg]
  · change output.body = (NativeKeySwitch.initial acc+increment) true NativeKeySwitch.zeroIndex
    change output.body = acc true NativeKeySwitch.zeroIndex + increment true NativeKeySwitch.zeroIndex
    exact eq_add_of_sub_eq' checked.2.symm

theorem valid_of_extraction (bits : ℕ) (key : NativeKeySwitch.Key q n levels) (shape : dimension ≤ n)
    (acc : Cipher q n) (trace : Trace q n) (output : NativePublic.Ciphertext q dimension)
    (product : trace.increment = increment bits key (acc false))
    (combined : trace.switched = NativeKeySwitch.initial acc+trace.increment)
    (extraction : Extraction shape acc trace.increment output) : Valid bits key shape acc trace output :=
  ⟨product,combined,(extract_of_constraints shape acc trace.increment output extraction).trans
    (congrArg (NativeKeySwitch.extract shape) combined.symm)⟩

theorem wrong_output_coverage (bits : ℕ) (key : NativeKeySwitch.Key q n levels) (shape : dimension ≤ n)
    (acc : Cipher q n) (trace : Trace q n) (output : NativePublic.Ciphertext q dimension)
    (wrong : output ≠ NativeKeySwitch.extract shape (switch bits key acc)) :
    trace.increment ≠ increment bits key (acc false) ∨
      trace.switched ≠ NativeKeySwitch.initial acc+trace.increment ∨ ¬Extraction shape acc trace.increment output := by
  classical
  by_contra absent
  push Not at absent
  exact wrong (valid_output bits key shape acc trace output
    (valid_of_extraction bits key shape acc trace output absent.1 absent.2.1 absent.2.2))

variable {log cells width : ℕ} [Fact q.Prime]

def project (tables : PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor levels) cells width)
    (address : Fin (2^log) → MatrixFold.Cube cells × Fin width) (factor : PBSHadamard.Factor levels) : Poly q (2^log) :=
  fun index => tables factor (address index).1 (address index).2

theorem projected_identity
    (tables : PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor levels) cells width)
    (address : Fin (2^log) → MatrixFold.Cube cells × Fin width) (relation : PBSHadamard.Relation tables) :
    project tables address (.inr ()) = ∑ level : Fin levels,
      project tables address (.inl (level,false)) * project tables address (.inl (level,true)) := by
  funext index
  simpa only [project, Finset.sum_apply, Pi.mul_apply] using relation (address index).1 (address index).2

omit [NeZero n] in
theorem increment_transform (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1))) (bits : ℕ)
    (key : NativeKeySwitch.Key q (2^log) levels) (mask : Poly q (2^log)) (half : Bool) :
    BlindRotationNTT.transform log psi (increment bits key mask half) = ∑ level : Fin levels,
      BlindRotationNTT.transform log psi (digit bits level (-mask)) * BlindRotationNTT.transform log psi (key level half) := by
  have represented : increment bits key mask half = ∑ level : Fin levels, mul (digit bits level (-mask)) (key level half) := by
    funext index
    simp only [increment,Finset.sum_apply]
  rw [represented,map_sum]
  simp only [BlindRotationNTT.transform_mul log psi primitive]

/-- The native result source is the signed increment (final minus initial),
not a positive-mask product followed by a sign change. -/
theorem increment_of_relations (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1))) (bits : ℕ)
    (key : NativeKeySwitch.Key q (2^log) levels) (mask : Poly q (2^log)) (result : Cipher q (2^log))
    (tables : PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor levels) cells width)
    (address : Bool → Fin (2^log) → MatrixFold.Cube cells × Fin width) (relation : PBSHadamard.Relation tables)
    (digits : ∀ half level, BlindRotationNTT.transform log psi (digit bits level (-mask)) =
      project tables (address half) (.inl (level,false)))
    (keys : ∀ half level, BlindRotationNTT.transform log psi (key level half) = project tables (address half) (.inl (level,true)))
    (output : ∀ half, BlindRotationNTT.transform log psi (result half) = project tables (address half) (.inr ())) :
    result = increment bits key mask := by
  funext half
  apply BlindRotationNTT.transform_injective log psi primitive
  rw [output,projected_identity tables (address half) relation,increment_transform psi primitive]
  apply Finset.sum_congr rfl
  intro level _
  rw [digits,keys]

theorem valid_of_relations (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1))) (bits : ℕ)
    (key : NativeKeySwitch.Key q (2^log) levels) (shape : dimension ≤ 2^log)
    (acc : Cipher q (2^log)) (trace : Trace q (2^log)) (output : NativePublic.Ciphertext q dimension)
    (tables : PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor levels) cells width)
    (address : Bool → Fin (2^log) → MatrixFold.Cube cells × Fin width) (relation : PBSHadamard.Relation tables)
    (digits : ∀ half level, BlindRotationNTT.transform log psi (digit bits level (-(acc false))) = project tables (address half) (.inl (level,false)))
    (keys : ∀ half level, BlindRotationNTT.transform log psi (key level half) = project tables (address half) (.inl (level,true)))
    (result : ∀ half, BlindRotationNTT.transform log psi (trace.increment half) = project tables (address half) (.inr ()))
    (combined : trace.switched = NativeKeySwitch.initial acc + trace.increment)
    (extracted : output = NativeKeySwitch.extract shape trace.switched) :
    Valid bits key shape acc trace output :=
  ⟨increment_of_relations psi primitive bits key (acc false) trace.increment tables address relation digits keys result,combined,extracted⟩

end
end FormalProof4FHE.HasteBoots.CanonicalKeySwitch
