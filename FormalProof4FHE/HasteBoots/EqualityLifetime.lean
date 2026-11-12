module
public import FormalProof4FHE.HasteBoots.EqualityPositionKernel
@[expose] public section

/-! Adaptive equality events over all original positions have one total
first-read charge. The whole-program reference bad ledger is retained once,
not repeated for every original input or job class. -/
namespace FormalProof4FHE.HasteBoots.EqualityLifetime
open InputIndexedOracle (Input World law)
open OracleProgram (Program)
open NativeRootMessage (Digest)
open MeasureTheory
noncomputable section

def Event {A : Type} (program : Program A) (dummy : Digest) (world : World) : Prop :=
  ∃ position input ordinal, EqualityClassKernel.Event program position input ordinal dummy world

def totalCharge {A : Type} (program : Program A) (world : World) : ENNReal :=
  ∑' position : ℕ, EqualityPositionKernel.charge program position world

theorem safe_bound {A : Type} (program : Program A) (dummy : Digest)  :
    law {world | Event program dummy world ∧ ¬GlobalReferenceBad.Bad program dummy world} ≤
      ∫⁻ world, totalCharge program world ∂law := by
  have union : {world | Event program dummy world ∧ ¬GlobalReferenceBad.Bad program dummy world} =
      ⋃ position : ℕ, {world | EqualityPositionKernel.Event program position dummy world} := by
    ext world
    simp only [Event,EqualityPositionKernel.Event,SafeEqualityClassKernel.Event,Set.mem_ofPred_eq,Set.mem_iUnion]
    constructor
    · rintro ⟨⟨position,input,ordinal,occurred⟩,safe⟩
      exact ⟨position,input,ordinal,occurred,safe⟩
    · rintro ⟨position,input,ordinal,occurred,safe⟩
      exact ⟨⟨position,input,ordinal,occurred⟩,safe⟩
  rw [union]
  have included := (measure_iUnion_le (fun position : ℕ => {world | EqualityPositionKernel.Event program position dummy world}) (μ := law)).trans
    (ENNReal.tsum_le_tsum (fun position => EqualityPositionKernel.bound program position dummy))
  unfold totalCharge
  rw [lintegral_tsum (fun position => (EqualityPositionKernel.charge_measurable program position).aemeasurable)]
  exact included

theorem bound {A : Type} (program : Program A) (dummy : Digest)  :
    law {world | Event program dummy world} ≤
      law {world | NativeRootFamilyLifetime.Bad dummy (OracleProgram.run program world).run.2} +
        GlobalReferenceBad.otherCharge program + ∫⁻ world, totalCharge program world ∂law := by
  have included : {world | Event program dummy world} ⊆
      {world | GlobalReferenceBad.Bad program dummy world} ∪
        {world | Event program dummy world ∧ ¬GlobalReferenceBad.Bad program dummy world} := by
    intro world occurred
    by_cases bad : GlobalReferenceBad.Bad program dummy world
    · exact Or.inl bad
    · exact Or.inr ⟨occurred,bad⟩
  exact (measure_mono included).trans ((measure_union_le _ _).trans
    (add_le_add (GlobalReferenceBad.bad_le program dummy) (safe_bound program dummy)))

end
end FormalProof4FHE.HasteBoots.EqualityLifetime
