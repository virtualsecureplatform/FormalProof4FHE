module
public import FormalProof4FHE.HasteBoots.PackedPBSExternalProductCoverage
public import FormalProof4FHE.HasteBoots.DecompositionBlindRotation
@[expose] public section

/-! Canonical digit provenance for the actual retained NTT coefficient rows.
Reconstruction, lookup, input and registry-source failures remain explicit. -/
namespace FormalProof4FHE.HasteBoots.PackedCoefficientDecomposition
open NativeBlindRotation (Cipher Control Poly digit externalProduct)
open OracleSpec OracleComp
open NativeRootMessage (Digest)
open PackedPBSHadamardNTT (HadamardOutcome LoopOutcome)
noncomputable section
variable {q log d levels dc dw : ℕ} [Fact q.Prime]

/-- Concrete canonical-decomposition constraints at the selected original addresses. -/
def Failure (bits : ℕ) (registries : Bool → DecompositionBlindRotation.Registry q d dc dw)
    (addresses : Bool → Fin (2^log) → MatrixFold.Cube dc × Fin dw) (difference : Cipher q (2^log)) : Prop :=
  ∃ source, DecompositionBlindRotation.project (registries source) (addresses source) DecompositionLinear.input ≠ difference source ∨
    ¬DecompositionLinear.Relation ((2^bits : ℕ) : ZMod q) (registries source) ∨
    ∃ index, ¬RadixCanonicity.LookupAt q (2^bits) (registries source) (addresses source index).1 (addresses source index).2

/-- No canonical-digit equality is supplied: it follows from the actual
reconstruction and lookup constraints, or one of those failures is exposed. -/
theorem digit_coverage (bits : ℕ) (radixLarge : 1 < 2^bits) (radixSmall : 2^bits < q)
    (enough : q-1 < (2^bits)^d) (covered : levels ≤ d)
    (registries : Bool → DecompositionBlindRotation.Registry q d dc dw)
    (addresses : Bool → Fin (2^log) → MatrixFold.Cube dc × Fin dw) (difference : Cipher q (2^log))
    (source : Bool) (level : Fin levels) (coefficient : Poly q (2^log))
    (wrong : coefficient ≠ digit bits level (difference source)) :
    coefficient ≠ DecompositionBlindRotation.project (registries source) (addresses source)
      (DecompositionLinear.digit (Fin.castLE covered level)) ∨
    Failure bits registries addresses difference := by
  classical
  by_cases same : coefficient = DecompositionBlindRotation.project (registries source) (addresses source)
      (DecompositionLinear.digit (Fin.castLE covered level))
  · right
    refine ⟨source,?_⟩
    exact DecompositionBlindRotation.wrong_digit_coverage bits radixLarge radixSmall enough covered
      (registries source) (addresses source) (difference source) level (fun equal => wrong (same.trans equal))
  · exact Or.inl same

variable {b c r k n front suffix m queries height : ℕ}
  {Input Cfg Response Memory CommitMemory FirstMessage Message : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points (ZMod q) n b)] [SampleableType (Fin b → Fin b → ZMod q)]
variable (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
  (family : PackedPBSOriginalReferences.Family (2*levels))
  (base : Fin ((2*levels)+1) → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    b c r k front suffix m queries height)
  (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor (2*levels)) (PBSHadamard.Term (2*levels))
    FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)

variable (dummy : Digest)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
  (first : HadamardOutcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (n := n) (count := (2*levels))
    (front := front) (queries := queries) (height := height))
  (later : LoopOutcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k) (count := (2*levels))
    (front := front) (queries := queries) (height := height))
  (supported : (first,some later) ∈ support (PackedPBSHadamardNTT.witness length psi primitive family base hs dummy initial))


open NativeBlindRotation (Cipher Control digit externalProduct)
variable (dimensions : r+c = n+1) (rows : Bool → MatrixFold.Cube r)

omit [DecidableEq Input] [SampleableType Digest]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points (ZMod q) n b)] [SampleableType (Fin b → Fin b → ZMod q)] in
/-- Every actual coefficient mismatch is a digit-registry provenance failure,
a result-source mismatch, or a concrete canonical-decomposition constraint failure. -/
theorem coefficient_coverage (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (bits : ℕ) (radixLarge : 1 < 2^bits) (radixSmall : 2^bits < q)
    (enough : q-1 < (2^bits)^d) (covered : levels ≤ d)
    (registries : Bool → DecompositionBlindRotation.Registry q d dc dw)
    (addresses : Bool → Fin (2^log) → MatrixFold.Cube dc × Fin dw)
    (difference result : Cipher q (2^log))
    (wrong : ∃ entry ∈ later.1.results, ∃ half,
      PackedNTTBinding.row length (AuthenticatedNTT.sources (base entry.1 entry.2.1)
        dummy capacity radius entry.2.2.1 false) (rows half) ≠
      PackedHadamardRows.expectedCoefficient bits difference result entry.1 half) :
    (∃ source level incoming child, (Fin.castSucc (PBSHadamardBlindRotation.digitIndex (source,level)),(incoming,child)) ∈ later.1.results ∧
      ∃ half, PackedNTTBinding.row length (AuthenticatedNTT.sources
        (base (Fin.castSucc (PBSHadamardBlindRotation.digitIndex (source,level))) incoming)
        dummy capacity radius child.1 false) (rows half) ≠
      DecompositionBlindRotation.project (registries source) (addresses source)
        (DecompositionLinear.digit (Fin.castLE covered level))) ∨
    (∃ incoming child, (Fin.last (2*levels),(incoming,child)) ∈ later.1.results ∧
      ∃ half, PackedNTTBinding.row length (AuthenticatedNTT.sources (base (Fin.last (2*levels)) incoming)
        dummy capacity radius child.1 false) (rows half) ≠ result half) ∨
    Failure bits registries addresses difference := by
  obtain ⟨entry,member,half,different⟩ := wrong
  rcases entry with ⟨slot,incoming,child⟩
  induction slot using Fin.lastCases with
  | last =>
    exact Or.inr (Or.inl ⟨incoming,child,member,half,by simpa only [PackedHadamardRows.expected_result] using different⟩)
  | cast index =>
    obtain ⟨pair,equal⟩ := (PBSHadamardBlindRotation.digitEquiv levels).surjective index
    rcases pair with ⟨source,level⟩
    change PBSHadamardBlindRotation.digitIndex (source,level) = index at equal
    subst index
    have wrongDigit : PackedNTTBinding.row length (AuthenticatedNTT.sources
        (base (Fin.castSucc (PBSHadamardBlindRotation.digitIndex (source,level))) incoming)
        dummy capacity radius child.1 false) (rows half) ≠ digit bits level (difference source) := by
      simpa only [PackedHadamardRows.expected_digit] using different
    rcases digit_coverage bits radixLarge radixSmall enough covered registries addresses difference source level _ wrongDigit
        with binding | failed
    · exact Or.inl ⟨source,level,incoming,child,member,half,binding⟩
    · exact Or.inr (Or.inr failed)

include supported in
/-- Wrong external products expose actual registry constraints and provenance,
trusted key binding, or the already bounded original Hadamard/transform event. -/
theorem external_product_coverage (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (accepted : later.1.accepted = true)
    (bits : ℕ) (control : Control q (2^log) levels) (difference result : Cipher q (2^log))
    (radixLarge : 1 < 2^bits) (radixSmall : 2^bits < q)
    (enough : q-1 < (2^bits)^d) (covered : levels ≤ d)
    (registries : Bool → DecompositionBlindRotation.Registry q d dc dw)
    (addresses : Bool → Fin (2^log) → MatrixFold.Cube dc × Fin dw)
    (wrong : result ≠ externalProduct bits control difference) :
    ((∃ source level incoming child, (Fin.castSucc (PBSHadamardBlindRotation.digitIndex (source,level)),(incoming,child)) ∈ later.1.results ∧
      ∃ half, PackedNTTBinding.row length (AuthenticatedNTT.sources
        (base (Fin.castSucc (PBSHadamardBlindRotation.digitIndex (source,level))) incoming)
        dummy capacity radius child.1 false) (rows half) ≠
      DecompositionBlindRotation.project (registries source) (addresses source)
        (DecompositionLinear.digit (Fin.castLE covered level))) ∨
    (∃ incoming child, (Fin.last (2*levels),(incoming,child)) ∈ later.1.results ∧
      ∃ half, PackedNTTBinding.row length (AuthenticatedNTT.sources (base (Fin.last (2*levels)) incoming)
        dummy capacity radius child.1 false) (rows half) ≠ result half) ∨
    Failure bits registries addresses difference) ∨
    (∃ half source level, BlindRotationNTT.transform log psi (control source level half) ≠
      PBSHadamardBlindRotation.project (AuthenticatedZeroCheck.sources hs dummy capacity radius first.1)
        (PackedHadamardRows.address length dimensions (rows half))
        (.inl (PBSHadamardBlindRotation.digitIndex (source,level),true))) ∨
    (OriginalFactorExceptionUnion.OriginalRisk (PackedPBSHadamardNTT.hadamard family hs)
      dummy capacity radius first ∨
      PackedPBSLoopFunctionBound.WrongTransform length psi base hs dummy capacity radius (first,some later)) := by
  rcases PackedPBSExternalProductCoverage.external_product_coverage length psi primitive family base hs dummy initial
      first later supported dimensions rows capacity radius accepted bits control difference result wrong
      with coefficients | keys | risk
  · exact Or.inl (coefficient_coverage length base dummy later rows
      capacity radius bits radixLarge radixSmall enough covered registries addresses difference result coefficients)
  · exact Or.inr (Or.inl keys)
  · exact Or.inr (Or.inr risk)

end
end FormalProof4FHE.HasteBoots.PackedCoefficientDecomposition
