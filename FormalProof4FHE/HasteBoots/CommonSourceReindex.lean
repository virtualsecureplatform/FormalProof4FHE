module
public import FormalProof4FHE.HasteBoots.CommonSource
@[expose] public section
namespace FormalProof4FHE.HasteBoots.CommonSourceReindex
variable {Position OldRow NewRow Symbol : Type} [Fintype Position]
  [DecidableEq Symbol] [DecidableEq (OldRow → Symbol)] [DecidableEq (NewRow → Symbol)]

def reindex (equiv : NewRow ≃ OldRow) (word : Position → OldRow → Symbol) : Position → NewRow → Symbol :=
  fun pos row => word pos (equiv row)

omit [Fintype Position] [DecidableEq Symbol] [DecidableEq (OldRow → Symbol)] [DecidableEq (NewRow → Symbol)] in
theorem rowsIn_iff (equiv : NewRow ≃ OldRow) (code : Set (Position → Symbol))
    (word : Position → OldRow → Symbol) :
    CommonSource.RowsIn code (reindex equiv word) ↔ CommonSource.RowsIn code word := by
  constructor
  · intro coded row
    simpa only [reindex,Equiv.apply_symm_apply] using coded (equiv.symm row)
  · intro coded row
    exact coded (equiv row)

omit [DecidableEq Symbol] in
theorem distance (equiv : NewRow ≃ OldRow) (left right : Position → OldRow → Symbol) :
    hammingDist (reindex equiv left) (reindex equiv right) = hammingDist left right := by
  apply le_antisymm
  · exact hammingDist_comp_le_hammingDist (fun _ (value : OldRow → Symbol) row => value (equiv row))
  · have bound := hammingDist_comp_le_hammingDist (x := reindex equiv left) (y := reindex equiv right)
      (fun _ (value : NewRow → Symbol) row => value (equiv.symm row))
    simpa only [reindex,Equiv.apply_symm_apply] using bound

variable [Zero Symbol]

theorem decode (equiv : NewRow ≃ OldRow) (code : Set (Position → Symbol)) (radius : ℕ)
    (margin : 2 * radius < Code.minDist code) (word : Position → OldRow → Symbol) :
    CommonSource.decode code radius (reindex equiv word) = reindex equiv (CommonSource.decode code radius word) := by
  by_cases near : ∃ source, CommonSource.RowsIn code source ∧ hammingDist word source ≤ radius
  · have chosen := CommonSource.decode_nearby code radius word near
    apply CommonSource.decode_eq_of_nearby code radius margin
    · exact (rowsIn_iff equiv code _).mpr chosen.1
    · rw [distance]
      exact chosen.2
  · have far : ¬∃ source, CommonSource.RowsIn code source ∧ hammingDist (reindex equiv word) source ≤ radius := by
      rintro ⟨source,coded,close⟩
      apply near
      refine ⟨reindex equiv.symm source,(rowsIn_iff equiv.symm code source).mpr coded,?_⟩
      have bound := distance equiv.symm (reindex equiv word) source
      have restored : reindex equiv.symm (reindex equiv word) = word := by
        funext pos row
        simp only [reindex,Equiv.apply_symm_apply]
      rw [restored] at bound
      exact bound.le.trans close
    rw [CommonSource.decode_fallback code radius _ far,CommonSource.decode_fallback code radius word near]
    rfl
end FormalProof4FHE.HasteBoots.CommonSourceReindex
