module
public import FormalProof4FHE.HasteBoots.ScalarPositionKernel
@[expose] public section

/-! Adaptive scalar first-read positions compose after excluding the one
global bad ledger. Charges are selected by the actual original prefix and
input metadata; no query, retry, job-count or lifetime cutoff is imposed. -/
namespace FormalProof4FHE.HasteBoots.ScalarLifetimeComposition
open InputIndexedOracle (World law)
open OracleProgram (Program)
open NativeRootMessage (Digest)
open MeasureTheory
noncomputable section

def Event {A : Type} (program : Program A) (dummy : Digest) (radius : ℕ) (world : World) : Prop :=
  ∃ position input ordinal, AttainableIdentityEvent.Event program position input ordinal dummy radius world

def totalCharge {A : Type} (program : Program A) (world : World) : ENNReal :=
  ∑' position : ℕ, ScalarPositionKernel.charge program position world

theorem safe_bound {A : Type} (program : Program A) (dummy : Digest) (radius : ℕ) :
    law {world | Event program dummy radius world ∧ ¬GlobalReferenceBad.Bad program dummy world} ≤
      ∫⁻ world, totalCharge program world ∂law := by
  have union : {world | Event program dummy radius world ∧ ¬GlobalReferenceBad.Bad program dummy world} =
      ⋃ position : ℕ, {world | ScalarPositionKernel.Event program position dummy radius world} := by
    ext world
    simp only [Event,ScalarPositionKernel.Event,SafeIdentityKernel.Event,Set.mem_ofPred_eq,Set.mem_iUnion]
    constructor
    · rintro ⟨⟨position,input,ordinal,occurred⟩,safe⟩
      exact ⟨position,input,ordinal,occurred,safe⟩
    · rintro ⟨position,input,ordinal,occurred,safe⟩
      exact ⟨⟨position,input,ordinal,occurred⟩,safe⟩
  rw [union]
  have included := (measure_iUnion_le (fun position : ℕ => {world | ScalarPositionKernel.Event program position dummy radius world}) (μ := law)).trans
    (ENNReal.tsum_le_tsum (fun position => ScalarPositionKernel.bound program position dummy radius))
  unfold totalCharge
  rw [lintegral_tsum (fun position => (ScalarPositionKernel.charge_measurable program position).aemeasurable)]
  exact included

theorem bound {A : Type} (program : Program A) (dummy : Digest) (radius : ℕ) :
    law {world | Event program dummy radius world} ≤
      law {world | NativeRootFamilyLifetime.Bad dummy (OracleProgram.run program world).run.2} +
        GlobalReferenceBad.otherCharge program + ∫⁻ world, totalCharge program world ∂law := by
  have included : {world | Event program dummy radius world} ⊆
      {world | GlobalReferenceBad.Bad program dummy world} ∪
        {world | Event program dummy radius world ∧ ¬GlobalReferenceBad.Bad program dummy world} := by
    intro world occurred
    by_cases bad : GlobalReferenceBad.Bad program dummy world
    · exact Or.inl bad
    · exact Or.inr ⟨occurred,bad⟩
  exact (measure_mono included).trans ((measure_union_le _ _).trans
    (add_le_add (GlobalReferenceBad.bad_le program dummy) (safe_bound program dummy radius)))

end
end FormalProof4FHE.HasteBoots.ScalarLifetimeComposition
