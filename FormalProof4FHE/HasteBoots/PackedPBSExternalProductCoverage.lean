module
public import FormalProof4FHE.HasteBoots.PackedPBSLoopFunctionBound
public import FormalProof4FHE.HasteBoots.PackedHadamardRows
public import FormalProof4FHE.HasteBoots.OwnedBlindRotationCoverage
@[expose] public section

/-! Accepted wrong external products expose original coefficient/key bindings
or events already controlled by the complete Hadamard-plus-NTT program. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSExternalProductCoverage
open OracleSpec OracleComp
open NativeRootMessage (Digest)
open PackedPBSHadamardNTT (HadamardOutcome LoopOutcome)
open CommittedJointMatrixOpening (snapshots)
noncomputable section
variable {q log levels b c r k n front suffix m queries height : ℕ} [Fact q.Prime]
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

include supported in
/-- Every trusted evaluation slot has an actual retained coefficient source.
A false binding is exposed, or the checked original transform is false. -/
theorem evaluation_coverage (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (accepted : later.1.accepted = true) (slot : Fin (2*levels+1)) (half : Bool)
    (target : NativeBlindRotation.Poly q (2^log))
    (wrong : BlindRotationNTT.transform log psi target ≠
      PackedNTTBinding.row length
        (QueryReindex.source dimensions (AuthenticatedZeroCheck.sources hs dummy capacity radius first.1
          (PackedPBSOriginalReferences.evaluationFactor slot))) (rows half)) :
    (∃ incoming child, (slot,(incoming,child)) ∈ later.1.results ∧
      PackedNTTBinding.row length (AuthenticatedNTT.sources (base slot incoming)
        dummy capacity radius child.1 false) (rows half) ≠ target) ∨
    PackedPBSLoopFunctionBound.WrongTransform length psi base hs dummy capacity radius (first,some later) := by
  obtain ⟨incoming,child,member,_,_⟩ := PackedPBSHadamardNTT.accepted_slots_bound
    length psi primitive family base hs dummy initial first later supported accepted slot
  by_cases same : PackedNTTBinding.row length (AuthenticatedNTT.sources (base slot incoming)
      dummy capacity radius child.1 false) (rows half) = target
  · right
    refine ⟨later,rfl,accepted,(slot,(incoming,child)),member,rows half,?_⟩
    change BlindRotationNTT.transform log psi
      (PackedNTTBinding.row length (AuthenticatedNTT.sources (base slot incoming)
        dummy capacity radius child.1 false) (rows half)) ≠ _
    rw [same]
    exact wrong
  · exact Or.inl ⟨incoming,child,member,same⟩

include supported in
/-- Original packed addresses remove all assumed NTT evaluation bindings.
Remaining coefficient provenance and trusted setup-key bindings are exposed,
not silently inferred from acceptance. -/
theorem external_product_coverage (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (accepted : later.1.accepted = true)
    (bits : ℕ) (control : Control q (2^log) levels) (difference result : Cipher q (2^log))
    (wrong : result ≠ externalProduct bits control difference) :
    (∃ entry ∈ later.1.results, ∃ half,
      PackedNTTBinding.row length (AuthenticatedNTT.sources (base entry.1 entry.2.1)
        dummy capacity radius entry.2.2.1 false) (rows half) ≠
      PackedHadamardRows.expectedCoefficient bits difference result entry.1 half) ∨
    (∃ half source level, BlindRotationNTT.transform log psi (control source level half) ≠
      PBSHadamardBlindRotation.project (AuthenticatedZeroCheck.sources hs dummy capacity radius first.1)
        (PackedHadamardRows.address length dimensions (rows half))
        (.inl (PBSHadamardBlindRotation.digitIndex (source,level),true))) ∨
    (OriginalFactorExceptionUnion.OriginalRisk (PackedPBSHadamardNTT.hadamard family hs)
      dummy capacity radius first ∨
      PackedPBSLoopFunctionBound.WrongTransform length psi base hs dummy capacity radius (first,some later)) := by
  have reached := PackedPBSHadamardNTT.reached_loop length psi primitive family base hs dummy initial first later supported
  have recorded := fun factor => ZeroCheckConditionalSoundness.fresh_recorded
    (PackedPBSHadamardNTT.hadamard family hs) dummy PBSHadamard.factors_complete initial first reached.2.1 factor
  rcases OwnedBlindRotationCoverage.accepted_wrong_external_coverage family.keys hs dummy capacity radius first
      (snapshots hs.tag first.1) (fun factor => ⟨rfl,recorded factor⟩)
      (fun half => PackedHadamardRows.address length dimensions (rows half)) psi primitive bits control difference result
      wrong reached.1 with digits | keys | output | had
  · obtain ⟨half,source,level,different⟩ := digits
    change BlindRotationNTT.transform log psi (digit bits level (difference source)) ≠
      PBSHadamardBlindRotation.project (AuthenticatedZeroCheck.sources hs dummy capacity radius first.1)
        (PackedHadamardRows.address length dimensions (rows half))
        (.inl (PBSHadamardBlindRotation.digitIndex (source,level),false)) at different
    have projected : BlindRotationNTT.transform log psi (digit bits level (difference source)) ≠
        PackedNTTBinding.row length
          (QueryReindex.source dimensions (AuthenticatedZeroCheck.sources hs dummy capacity radius first.1
            (PackedPBSOriginalReferences.evaluationFactor
              (Fin.castSucc (PBSHadamardBlindRotation.digitIndex (source,level)))))) (rows half) := by
      simpa only [PackedHadamardRows.evaluation_digit,←PackedHadamardRows.project_eq_row] using different
    rcases evaluation_coverage length psi primitive family base hs dummy initial first later supported dimensions rows
        capacity radius accepted (Fin.castSucc (PBSHadamardBlindRotation.digitIndex (source,level))) half
        (digit bits level (difference source)) projected with mismatch | risk
    · obtain ⟨incoming,child,member,different⟩ := mismatch
      refine Or.inl ⟨(_, (incoming,child)),member,half,?_⟩
      simpa only [PackedHadamardRows.expected_digit] using different
    · exact Or.inr (Or.inr (Or.inr risk))
  · exact Or.inr (Or.inl keys)
  · obtain ⟨half,different⟩ := output
    change BlindRotationNTT.transform log psi (result half) ≠
      PBSHadamardBlindRotation.project (AuthenticatedZeroCheck.sources hs dummy capacity radius first.1)
        (PackedHadamardRows.address length dimensions (rows half)) (.inr ()) at different
    have projected : BlindRotationNTT.transform log psi (result half) ≠
        PackedNTTBinding.row length
          (QueryReindex.source dimensions (AuthenticatedZeroCheck.sources hs dummy capacity radius first.1
            (PackedPBSOriginalReferences.evaluationFactor (Fin.last (2*levels))))) (rows half) := by
      simpa only [PackedHadamardRows.evaluation_result,←PackedHadamardRows.project_eq_row] using different
    rcases evaluation_coverage length psi primitive family base hs dummy initial first later supported dimensions rows
        capacity radius accepted (Fin.last (2*levels)) half (result half) projected with mismatch | risk
    · obtain ⟨incoming,child,member,different⟩ := mismatch
      refine Or.inl ⟨(_, (incoming,child)),member,half,?_⟩
      simpa only [PackedHadamardRows.expected_result] using different
    · exact Or.inr (Or.inr (Or.inr risk))
  · exact Or.inr (Or.inr (Or.inl had))

include supported in
/-- All round/half projections of one original family share the same bounded
Hadamard/transform event. No union over application projections is required. -/
theorem external_product_family_coverage {I : Type}
    (capacity : 2^suffix ≤ m*b) (radius : ℕ) (accepted : later.1.accepted = true)
    (rowFamily : I → Bool → MatrixFold.Cube r) (bits : I → ℕ)
    (control : I → Control q (2^log) levels) (difference result : I → Cipher q (2^log))
    (wrong : ∃ index, result index ≠ externalProduct (bits index) (control index) (difference index)) :
    (∃ index, ∃ entry ∈ later.1.results, ∃ half,
      PackedNTTBinding.row length (AuthenticatedNTT.sources (base entry.1 entry.2.1)
        dummy capacity radius entry.2.2.1 false) (rowFamily index half) ≠
      PackedHadamardRows.expectedCoefficient (bits index) (difference index) (result index) entry.1 half) ∨
    (∃ index half source level, BlindRotationNTT.transform log psi (control index source level half) ≠
      PBSHadamardBlindRotation.project (AuthenticatedZeroCheck.sources hs dummy capacity radius first.1)
        (PackedHadamardRows.address length dimensions (rowFamily index half))
        (.inl (PBSHadamardBlindRotation.digitIndex (source,level),true))) ∨
    (OriginalFactorExceptionUnion.OriginalRisk (PackedPBSHadamardNTT.hadamard family hs)
      dummy capacity radius first ∨
      PackedPBSLoopFunctionBound.WrongTransform length psi base hs dummy capacity radius (first,some later)) := by
  obtain ⟨index,different⟩ := wrong
  rcases external_product_coverage length psi primitive family base hs dummy initial first later supported
      dimensions (rowFamily index) capacity radius accepted (bits index) (control index) (difference index)
      (result index) different with coefficients | keys | risk
  · obtain ⟨entry,member,half,mismatch⟩ := coefficients
    exact Or.inl ⟨index,entry,member,half,mismatch⟩
  · obtain ⟨half,source,level,mismatch⟩ := keys
    exact Or.inr (Or.inl ⟨index,half,source,level,mismatch⟩)
  · exact Or.inr (Or.inr risk)

end
end FormalProof4FHE.HasteBoots.PackedPBSExternalProductCoverage
