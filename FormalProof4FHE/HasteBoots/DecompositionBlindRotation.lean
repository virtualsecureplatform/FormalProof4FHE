module
public import FormalProof4FHE.HasteBoots.RadixCanonicity
public import FormalProof4FHE.HasteBoots.PackedBlindRotationTrace
@[expose] public section

/-! Canonical decomposition constraints supply the original digit polynomials
used by the external-product NTT stage. Linear reconstruction alone is not
sufficient: membership in every public comparison table is retained. Native
accepted lookup/linear enforcement and source authentication remain separate. -/
namespace FormalProof4FHE.HasteBoots.DecompositionBlindRotation
open NativeBlindRotation (Poly Cipher Control digit)
noncomputable section
variable {q log d levels cells width : ℕ} [Fact q.Prime]

abbrev Registry (q d cells width : ℕ) :=
  Fin (2*d+2) → MatrixFold.Cube cells → Fin width → ZMod q

def project (registry : Registry q d cells width)
    (address : Fin (2^log) → MatrixFold.Cube cells × Fin width) (factor : Fin (2*d+2)) : Poly q (2^log) :=
  fun index => registry factor (address index).1 (address index).2

/-- Full canonical decomposition may contain more limbs than the particular
external product uses. The used limbs retain their original low-to-high indices. -/
theorem digit_of_constraints (bits : ℕ) (radixLarge : 1 < 2^bits) (radixSmall : 2^bits < q)
    (enough : q-1 < (2^bits)^d) (covered : levels ≤ d)
    (registry : Registry q d cells width) (address : Fin (2^log) → MatrixFold.Cube cells × Fin width)
    (input : Poly q (2^log)) (source : project registry address DecompositionLinear.input = input)
    (linear : DecompositionLinear.Relation ((2^bits : ℕ) : ZMod q) registry)
    (lookup : ∀ index, RadixCanonicity.LookupAt q (2^bits) registry (address index).1 (address index).2)
    (level : Fin levels) :
    project registry address (DecompositionLinear.digit (Fin.castLE covered level)) = digit bits level input := by
  funext index
  have canonical := RadixCanonicity.digits_of_constraints radixLarge radixSmall enough registry linear
    (address index).1 (address index).2 (lookup index) (Fin.castLE covered level)
  have field := congrArg (fun value : ℕ => (value : ZMod q)) canonical
  rw [ZMod.natCast_zmod_val] at field
  have bound := congrFun source index
  change registry DecompositionLinear.input (address index).1 (address index).2 = input index at bound
  rw [bound] at field
  exact field

variable {ec ew : ℕ}

/-- NTT bindings for the original digit columns now imply the digit premise
of the external-product relation. No canonical-digit equality is assumed. -/
theorem digits_transform_of_constraints (psi : ZMod q) (bits : ℕ)
    (radixLarge : 1 < 2^bits) (radixSmall : 2^bits < q) (enough : q-1 < (2^bits)^d) (covered : levels ≤ d)
    (registries : Bool → Registry q d cells width)
    (addresses : Bool → Fin (2^log) → MatrixFold.Cube cells × Fin width) (input : Cipher q (2^log))
    (source : ∀ source, project (registries source) (addresses source) DecompositionLinear.input = input source)
    (linear : ∀ source, DecompositionLinear.Relation ((2^bits : ℕ) : ZMod q) (registries source))
    (lookup : ∀ source index, RadixCanonicity.LookupAt q (2^bits) (registries source) (addresses source index).1 (addresses source index).2)
    (tables : PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor (2*levels)) ec ew)
    (address : Bool → Fin (2^log) → MatrixFold.Cube ec × Fin ew)
    (binding : ∀ half source level, BlindRotationNTT.transform log psi
      (project (registries source) (addresses source) (DecompositionLinear.digit (Fin.castLE covered level))) =
      PBSHadamardBlindRotation.project tables (address half) (.inl (PBSHadamardBlindRotation.digitIndex (source,level),false))) :
    ∀ half source level, BlindRotationNTT.transform log psi (digit bits level (input source)) =
      PBSHadamardBlindRotation.project tables (address half) (.inl (PBSHadamardBlindRotation.digitIndex (source,level),false)) := by
  intro half sourceHalf level
  have canonical := digit_of_constraints bits radixLarge radixSmall enough covered (registries sourceHalf)
    (addresses sourceHalf) (input sourceHalf) (source sourceHalf) (linear sourceHalf) (lookup sourceHalf) level
  exact (congrArg (BlindRotationNTT.transform log psi) canonical).symm.trans (binding half sourceHalf level)

theorem external_of_constraints (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1))) (bits : ℕ)
    (radixLarge : 1 < 2^bits) (radixSmall : 2^bits < q) (enough : q-1 < (2^bits)^d) (covered : levels ≤ d)
    (registries : Bool → Registry q d cells width)
    (addresses : Bool → Fin (2^log) → MatrixFold.Cube cells × Fin width)
    (control : Control q (2^log) levels) (input output : Cipher q (2^log))
    (source : ∀ source, project (registries source) (addresses source) DecompositionLinear.input = input source)
    (linear : ∀ source, DecompositionLinear.Relation ((2^bits : ℕ) : ZMod q) (registries source))
    (lookup : ∀ source index, RadixCanonicity.LookupAt q (2^bits) (registries source) (addresses source index).1 (addresses source index).2)
    (tables : PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor (2*levels)) ec ew)
    (address : Bool → Fin (2^log) → MatrixFold.Cube ec × Fin ew) (relation : PBSHadamard.Relation tables)
    (binding : ∀ half source level, BlindRotationNTT.transform log psi
      (project (registries source) (addresses source) (DecompositionLinear.digit (Fin.castLE covered level))) =
      PBSHadamardBlindRotation.project tables (address half) (.inl (PBSHadamardBlindRotation.digitIndex (source,level),false)))
    (keys : ∀ half source level, BlindRotationNTT.transform log psi (control source level half) =
      PBSHadamardBlindRotation.project tables (address half) (.inl (PBSHadamardBlindRotation.digitIndex (source,level),true)))
    (result : ∀ half, BlindRotationNTT.transform log psi (output half) = PBSHadamardBlindRotation.project tables (address half) (.inr ())) :
    output = NativeBlindRotation.externalProduct bits control input :=
  PBSHadamardBlindRotation.externalProduct_of_relations psi primitive bits control input output tables address relation
    (digits_transform_of_constraints psi bits radixLarge radixSmall enough covered registries addresses input source linear lookup tables address binding)
    keys result

/-- A wrong digit polynomial violates a concrete reconstruction/lookup source
constraint, even when its field reconstruction alone happens to pass. -/
theorem wrong_digit_coverage (bits : ℕ) (radixLarge : 1 < 2^bits) (radixSmall : 2^bits < q)
    (enough : q-1 < (2^bits)^d) (covered : levels ≤ d)
    (registry : Registry q d cells width) (address : Fin (2^log) → MatrixFold.Cube cells × Fin width)
    (input : Poly q (2^log)) (level : Fin levels)
    (wrong : project registry address (DecompositionLinear.digit (Fin.castLE covered level)) ≠ digit bits level input) :
    project registry address DecompositionLinear.input ≠ input ∨
      ¬DecompositionLinear.Relation ((2^bits : ℕ) : ZMod q) registry ∨
      ∃ index, ¬RadixCanonicity.LookupAt q (2^bits) registry (address index).1 (address index).2 := by
  classical
  by_contra absent
  push Not at absent
  exact wrong (digit_of_constraints bits radixLarge radixSmall enough covered registry address input absent.1 absent.2.1 absent.2.2 level)

end
end FormalProof4FHE.HasteBoots.DecompositionBlindRotation
