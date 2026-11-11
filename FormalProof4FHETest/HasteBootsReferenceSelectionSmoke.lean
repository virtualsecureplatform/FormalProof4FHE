module
import all FormalProof4FHE.HasteBoots.CandidateIdentityTables
import all FormalProof4FHETest.HasteBootsFactorFiberSmoke
import all FormalProof4FHETest.HasteBootsJobFamilySmoke
import all FormalProof4FHETest.HasteBootsScalarFinishAncestrySmoke

namespace FormalProof4FHE.HasteBoots.ReferenceSelectionSmoke
open MeasureTheory ProbabilityTheory
open InputIndexedOracle (World)
noncomputable section

local instance : MeasurableSpace (Fin 257) := ⊤
local instance : DiscreteMeasurableSpace (Fin 257) := ⟨by intro s; trivial⟩

def measure : Measure (Fin 257) := uniformOn Set.univ

theorem singleton_mass (value : Fin 257) : measure {value} = 1/257 := by
  rw [measure,show (Set.univ : Set (Fin 257)) = (↑(Finset.univ : Finset (Fin 257)) : Set (Fin 257)) by simp,
    show ({value} : Set (Fin 257)) = (↑({value} : Finset (Fin 257)) : Set (Fin 257)) by simp,uniformOn_apply_finset]
  simp

def Witness (world : Fin 257) : Type := PLift (world = 1)

/-- A good reference is attained only on a singleton of mass 1/257. The
bound keeps that probability and never divides by successful witness mass. -/
theorem rare_reference : measure {1} ≤ 1/257 := by
  have bound := AttainableReferenceBound.measure_le measure Set.univ {1} ∅ Witness (fun _ _ => True)
    (fun _ _ => {1}) (1/257) (by
      intro world _ occurred _
      exact ⟨⟨Set.mem_singleton_iff.mp occurred⟩⟩) (by intro _ _ _ _; trivial)
    (by intro _ _ _ _ world _ occurred; exact Or.inr occurred) (by
      intro _ _ _ _
      rw [Set.univ_inter,singleton_mass])
  simpa only [Set.univ_inter,Set.inter_empty,measure_empty,zero_add] using bound

/-- No reference can be fabricated in an empty witness class. -/
theorem empty_class : ¬∃ world ∈ (Set.univ : Set (Fin 257)), ∃ _ : Empty, True := by
  rintro ⟨_,_,candidate,_⟩
  exact Empty.elim candidate

/-- If all events are bad and no reference exists, the positive bad mass is
retained. It cannot be discarded by conditioning on a good-run event. -/
theorem bad_only : (Measure.dirac (0 : Fin 257)) {0} ≤ (Measure.dirac (0 : Fin 257)) {0} + 0 := by
  have bound := AttainableReferenceBound.measure_le (Measure.dirac (0 : Fin 257)) Set.univ {0} {0} (fun _ => Empty)
    (fun _ _ => True) (fun _ candidate => Empty.elim candidate) 0
    (by intro _ _ occurred safe; exact False.elim (safe occurred)) (by intro _ _ _ _; trivial)
    (by intro _ _ candidate; exact Empty.elim candidate) (by intro _ _ candidate; exact Empty.elim candidate)
  simpa only [Set.univ_inter] using bound

theorem bad_mass_positive : (Measure.dirac (0 : Fin 257)) {0} = 1 := by simp

open FactorFiberSmoke (program first changed same_prefix input)
open HasteBootsSamplerAncestrySmoke (worldZero)

theorem retained_history :
    (RefinedScalarSourceKernel.retained (OracleProgram.runPrefix first.position program) worldZero).run.2 =
      (OracleProgram.runPrefix first.position program worldZero).run.2 := rfl

theorem retained_fiber :
    (RefinedScalarSourceKernel.retained (OracleProgram.runPrefix first.position program) changed).run =
      (RefinedScalarSourceKernel.retained (OracleProgram.runPrefix first.position program) worldZero).run :=
  (RefinedScalarSourceKernel.retained_packet _ worldZero changed).mpr same_prefix

/-- Equal presentations keep the exact far-offset first request; no extra
query or successful-collector event is inserted by the adapter. -/
theorem first_reindexed :
    (PositionedFactorSamples.reindex first worldZero input rfl rfl).position = 3 ∧
      (PositionedFactorSamples.reindex first worldZero input rfl rfl).offset = 999 ∧
      (PositionedFactorSamples.reindex first worldZero input rfl rfl).count = 1 := ⟨rfl,rfl,rfl⟩

open HasteBootsScalarFinishAncestrySmoke (zero one)
open JobFamilySmoke (slots sourceFamily helper)

def point : Fin (NativeScalarQueryShape.laneBits 4+2) → NativeGoldExtensionArithmetic.Word := fun _ => zero
theorem shape : 3+1 = 2^NativeScalarQueryShape.laneBits (3+1) := by decide +kernel

def factors (selector : LookupOriginalSlots.Slots 3 JobFamilySmoke.firstRequest.toModel) :=
  ExtensionLookupIdentity.factors (fun i => NativeFieldWire.goldExtensionValue (point i)) (NativeFieldWire.goldExtensionValue one)
    (fun column => LookupSourceFlattening.flatten shape (sourceFamily selector column))
    (fun cell => PaddedExtension.decode (padding := 0) NativeExtensionFields.goldilocksBasis (helper cell)) 11

theorem partial_tables (candidate : LookupOriginalSlots.Slots 3 JobFamilySmoke.firstRequest.toModel) : HEq (factors slots) (factors candidate) :=
  LookupIdentityTableCongruence.partial_tables (lp := 1) (rp := 1) (lr := 2) (rr := 2) (lh := 0) (rh := 0) (lc := 3) (rc := 3) point point one one 11 11 shape shape (sourceFamily slots) (sourceFamily candidate) helper helper
    rfl rfl rfl rfl rfl rfl rfl (JobFamilySmoke.complete_sources candidate) HEq.rfl

/-- A nonzero padding fixture still uses the native degree-four partial
identity grammar; it has no independently supplied honest polynomial. -/
theorem partial_degree :
    (ScalarNativeSourceHealing.honest ExtensionLookupIdentity.partialArity
      (ExtensionLookupIdentity.partialCoefficient (NativeFieldWire.goldExtensionValue one)) ExtensionLookupIdentity.partialIndices
      (NativeScalarQueryShape.laneBits 4+2) (factors slots) []).natDegree ≤ 4 :=
  ScalarSourcePolynomial.degree _ _ _ 4 ExtensionLookupIdentity.partial_degree _ _ _

end
end FormalProof4FHE.HasteBoots.ReferenceSelectionSmoke
