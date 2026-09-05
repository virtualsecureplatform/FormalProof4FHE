import FormalProof4FHE.RLWE.BinaryNTTBGVConsolidated
import FormalProof4FHE.RLWE.BFVFoldFreeCircularSecurityFramework

/-!
# Unified Binary-NTT BGV: random masks and transition discrepancies

Checked additions from `sketch/unified_binary_ntt_bgv_proofs.tex`.
The fixed-mask CMAS implication remains open. Path and charge statements
below concern exact aligned transitions, not arbitrary FHE circuits.
-/

open OracleComp BigOperators

namespace FormalProof4FHE.RLWE.BinaryNTTSecurity.UnifiedBGV

noncomputable section

/-! ## Joint random-mask synthesis -/

/-- Two ordinary rows become two exposed masks and their summed body. -/
def randomMaskMap {Row R : Type} [CommRing R]
    (sigma : Row → R ≃+* R) :
    (Row → (R × R) × (R × R)) →+ (Row → R × R × R) where
  toFun rows r := ((rows r).1.1, sigma r (rows r).2.1,
    (rows r).1.2 + sigma r (rows r).2.2)
  map_zero' := by ext r <;> simp
  map_add' left right := by ext r <;> simp; abel

theorem randomMaskMap_surjective {Row R : Type} [CommRing R]
    (sigma : Row → R ≃+* R) : Function.Surjective (randomMaskMap sigma) := by
  intro target
  refine ⟨fun r => ((target r |>.1, (target r).2.2),
    ((sigma r).symm (target r).2.1, 0)), ?_⟩
  funext r
  simp [randomMaskMap]

theorem randomMaskMap_real {Row R : Type} [CommRing R]
    (sigma : Row → R ≃+* R) (a c e f : Row → R) (w : R) :
    randomMaskMap sigma (fun r => ((a r, a r * w + e r),
        (c r, c r * w + f r))) =
      fun r => (a r, sigma r (c r),
        a r * w + sigma r (c r) * sigma r w + (e r + sigma r (f r))) := by
  funext r
  simp [randomMaskMap]
  ring

/-- One joint uniform endpoint, with no independence assumption on NTT error
coordinates. The real error is the sum of two transformed source errors. -/
theorem randomMaskMap_uniform {Row R : Type} [Fintype Row]
    [CommRing R] [Fintype R] [DecidableEq R]
    [SampleableType (Row → (R × R) × (R × R))]
    [SampleableType (Row → R × R × R)]
    (sigma : Row → R ≃+* R) :
    evalDist (randomMaskMap sigma <$> ($ᵗ (Row → (R × R) × (R × R)))) =
    evalDist ($ᵗ (Row → R × R × R)) := by
  classical
  exact BFVFoldFreeCircularSecurityFramework.evalDist_map_surjective_addHom_uniform
    (randomMaskMap sigma) (randomMaskMap_surjective sigma)

/-! ## Charge conservation and path composition -/

/-- Aligned source and target witnesses let the existing ring-affine compiler
produce a transition between distinct operational keys. -/
theorem alignedTransition_phase {R : Type} [CommRing R]
    (operation : R ≃+* R) (sourcePivot targetPivot : Rˣ)
    (sourceOffset targetOffset sourceWitness targetWitness gadget mask error : R)
    (haligned : operation sourceWitness = targetWitness) :
    let form : CompactCoverCyclicCompiler.WitnessAffine R :=
      ⟨gadget * operation sourceOffset, gadget * operation (sourcePivot : R)⟩
    let row := CompactCoverCyclicCompiler.compilerRow targetPivot targetOffset
      form 0 (mask, mask * targetWitness + error)
    row.2 - row.1 * (targetOffset - (targetPivot : R) * targetWitness) =
      gadget * operation (sourceOffset - (sourcePivot : R) * sourceWitness) + error := by
  have h := CompactCoverCyclicCompiler.compiler_phase targetPivot targetOffset
    targetWitness error
    (⟨gadget * operation sourceOffset, gadget * operation (sourcePivot : R)⟩ :
      CompactCoverCyclicCompiler.WitnessAffine R) 0 mask
  simpa [CompactCoverCyclicCompiler.compilerRow,
    CompactCoverCyclicCompiler.targetSecret, CompactCoverCyclicCompiler.WitnessAffine.value,
    map_sub, map_mul, haligned, mul_sub, mul_assoc, add_comm] using h

def charge {G : Type} [Group G] (label automorphism : G) : G :=
  label⁻¹ * automorphism

def discrepancy {G : Type} [Group G] (source target operation : G) : G :=
  target⁻¹ * operation * source

theorem aligned_charge {G : Type} [Group G] (x operation gamma : G) :
    charge (operation * x) (operation * gamma) = charge x gamma := by
  simp [charge, mul_assoc]

theorem transition_charge {G : Type} [Group G] (x y operation gamma : G) :
    charge y (operation * gamma) =
      discrepancy x y operation * charge x gamma := by
  simp [charge, discrepancy, mul_assoc]

theorem discrepancy_comp {G : Type} [Group G] (x y z first second : G) :
    discrepancy y z second * discrepancy x y first =
      discrepancy x z (second * first) := by
  simp [discrepancy, mul_assoc]

theorem discrepancy_eq_one_iff {G : Type} [Group G] (x y operation : G) :
    discrepancy x y operation = 1 ↔ y = operation * x := by
  simp only [discrepancy, mul_assoc, inv_mul_eq_one]

/-- Chronological path operations and their successive destination labels. -/
def pathDiscrepancy {G : Type} [Group G] : G → List (G × G) → G
  | _, [] => 1
  | source, (target, operation) :: rest =>
      pathDiscrepancy target rest * discrepancy source target operation

def pathProduct {G : Type} [Group G] : List (G × G) → G
  | [] => 1
  | (_, operation) :: rest => pathProduct rest * operation

def pathEnd {G : Type} : G → List (G × G) → G
  | source, [] => source
  | _, (target, _) :: rest => pathEnd target rest

theorem pathDiscrepancy_telescope {G : Type} [Group G]
    (path : List (G × G)) (source : G) :
    pathDiscrepancy source path =
      (pathEnd source path)⁻¹ * pathProduct path * source := by
  induction path generalizing source with
  | nil => simp [pathDiscrepancy, pathEnd, pathProduct]
  | cons edge rest ih =>
    rcases edge with ⟨target, operation⟩
    simp [pathDiscrepancy, pathEnd, pathProduct, ih, discrepancy, mul_assoc]

/-! ## HolCMAS: distinguish relative and physical coordinates -/

/-- The physical automorphism mapping the target witness to the transformed
source witness. It is the conjugate of the normalized discrepancy. -/
def physicalDiscrepancy {G : Type} [Group G] (x y operation : G) : G :=
  operation * x * y⁻¹

theorem physicalDiscrepancy_conjugate {G : Type} [Group G]
    (x y operation : G) :
    physicalDiscrepancy x y operation =
      y * discrepancy x y operation * y⁻¹ := by
  simp [physicalDiscrepancy, discrepancy, mul_assoc]

theorem physicalDiscrepancy_witness {G R : Type} [Group G] [CommRing R]
    (action : G →* R ≃+* R) (x y operation : G) (w : R) :
    action (physicalDiscrepancy x y operation) (action y w) =
      action operation (action x w) := by
  change (action (physicalDiscrepancy x y operation) * action y) w =
    (action operation * action x) w
  rw [← action.map_mul, ← action.map_mul]
  congr 2
  simp [physicalDiscrepancy, mul_assoc]

theorem normalizedDiscrepancy_witness {G R : Type} [Group G] [CommRing R]
    (action : G →* R ≃+* R) (x y operation : G) (w : R) :
    action y⁻¹ (action operation (action x w)) =
      action (discrepancy x y operation) w := by
  change (action y⁻¹ * (action operation * action x)) w = _
  rw [← action.map_mul, ← action.map_mul]
  congr 2
  simp [discrepancy, mul_assoc]

/-- For cyclotomic (commutative) groups the physical and relative discrepancy
coincide; this is the extra premise needed by the manuscript's formula. -/
theorem physicalDiscrepancy_eq_of_comm {G : Type} [CommGroup G]
    (x y operation : G) :
    physicalDiscrepancy x y operation = discrepancy x y operation := by
  simp [physicalDiscrepancy, discrepancy, mul_comm, mul_assoc]

/-! ## Uniqueness of a free permutation operator expansion -/

def skewOperator {G Slot K : Type} [Fintype G] [CommRing K]
    (permutation : G → Slot → Slot) (coefficients : G → Slot → K)
    (input : Slot → K) (slot : Slot) : K :=
  ∑ g, coefficients g slot * input (permutation g slot)

/-- Distinct group elements address distinct input positions at each output
slot. Testing on a basis vector isolates the corresponding coefficient. -/
theorem skewOperator_basis {G Slot K : Type} [Fintype G] [DecidableEq G]
    [DecidableEq Slot] [CommRing K]
    (permutation : G → Slot → Slot)
    (hfree : ∀ slot, Function.Injective (fun g => permutation g slot))
    (coefficients : G → Slot → K) (selected : G) (slot : Slot) :
    skewOperator permutation coefficients
      (fun i => if i = permutation selected slot then 1 else 0) slot =
        coefficients selected slot := by
  unfold skewOperator
  have htest : ∀ g, permutation g slot = permutation selected slot ↔ g = selected :=
    fun g => ⟨fun h => hfree slot h, fun h => congrArg (fun a => permutation a slot) h⟩
  simp [htest]

theorem skewOperator_unique {G Slot K : Type} [Fintype G] [DecidableEq G]
    [DecidableEq Slot] [CommRing K]
    (permutation : G → Slot → Slot)
    (hfree : ∀ slot, Function.Injective (fun g => permutation g slot))
    (coefficients : G → Slot → K)
    (hzero : ∀ input slot, skewOperator permutation coefficients input slot = 0) :
    ∀ g slot, coefficients g slot = 0 := by
  intro g slot
  rw [← skewOperator_basis permutation hfree coefficients g slot]
  exact hzero _ _

/-- A term reachable from an initial diagonal sector has the inverse of that
sector's label as its charge. At identity output its automorphism is exactly
that inverse. The reachability premise is explicit. -/
theorem identityOutput_support {G : Type} [Group G]
    (initial : Set G) (gamma : G)
    (hreachable : ∃ x ∈ initial, charge 1 gamma = charge x 1) :
    gamma ∈ (fun x : G => x⁻¹) '' initial := by
  obtain ⟨x, hx, heq⟩ := hreachable
  have h : gamma = x⁻¹ := by simpa [charge] using heq
  exact ⟨x, hx, h.symm⟩

end
end FormalProof4FHE.RLWE.BinaryNTTSecurity.UnifiedBGV
