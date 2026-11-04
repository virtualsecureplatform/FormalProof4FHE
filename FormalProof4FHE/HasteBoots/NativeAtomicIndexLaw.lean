module

public import FormalProof4FHE.HasteBoots.NativeIndexRequest
public import FormalProof4FHE.HasteBoots.ColumnOpening
public import Mathlib.Logic.Equiv.Prod

@[expose] public section

/-! Finite-byte transport for the exact atomic decoder. A uniformly fresh
whole block gives a jointly uniform with-replacement draw vector. Freshness
of a real adaptive transcript request is not assumed by this finite law. -/
namespace FormalProof4FHE.HasteBoots.NativeAtomicIndexLaw

open OracleSpec OracleComp
open InputIndexedOracle (Byte)
open NativeIndexRequest (typedDraws)

noncomputable section

def blocks (count : ℕ) : (Fin (count*8) → Byte) ≃ (Fin count → Fin 8 → Byte) :=
  (Equiv.arrowCongr (finProdFinEquiv : Fin count × Fin 8 ≃ Fin (count*8)).symm (Equiv.refl Byte)).trans
    (Equiv.curry (Fin count) (Fin 8) Byte)

def splitBlock (bits count : ℕ) (fits : bits ≤ 64) :
    (Fin (count*8) → Byte) ≃ (Fin count → Fin (2^(64-bits))) × (Fin count → Fin (2^bits)) :=
  (blocks count).trans ((Equiv.piCongrRight (fun _ : Fin count => CanonicalByteMask.split bits 8 fits)).trans
    (Equiv.arrowProdEquivProdArrow (Fin count) (fun _ => Fin (2^(64-bits))) (fun _ => Fin (2^bits))))

theorem blocks_apply (count : ℕ) (raw : Fin (count*8) → Byte) (index : Fin count) (position : Fin 8) :
    blocks count raw index position = raw ⟨8*index.val+position.val,by have a := index.isLt; have b := position.isLt; omega⟩ := by
  change raw ⟨position.val+8*index.val,_⟩ = _
  congr 1
  apply Fin.ext
  change position.val+8*index.val = 8*index.val+position.val
  omega

theorem splitBlock_snd (bits count : ℕ) (fits : bits ≤ 64) (raw : Fin (count*8) → Byte) :
    (splitBlock bits count fits raw).2 = typedDraws bits count raw := by
  funext index
  change (CanonicalByteMask.split bits 8 fits (blocks count raw index)).2 = _
  rw [CanonicalByteMask.split_snd]
  unfold typedDraws
  congr 1
  funext position
  exact blocks_apply count raw index position

/-- This is a joint vector law. Independence is derived by the whole-block
bijection, including all discarded high bits at every original position. -/
theorem uniform_draws (bits count : ℕ) (fits : bits ≤ 64) (event : (Fin count → Fin (2^bits)) → Prop) :
    Pr{let raw ← $ᵗ (Fin (count*8) → Byte)}[event (typedDraws bits count raw)] =
      Pr{let draw ← $ᵗ (Fin count → Fin (2^bits))}[event draw] := by
  have splitLaw := SampleableType.prEvent_uniformSample_equiv (splitBlock bits count fits) (fun pair => event pair.2)
  have swapLaw := SampleableType.prEvent_uniformSample_equiv
    (Equiv.prodComm (Fin count → Fin (2^(64-bits))) (Fin count → Fin (2^bits))) (fun pair => event pair.1)
  have project := SampleableType.prEvent_uniformSample_fst (β := Fin count → Fin (2^(64-bits))) event
  calc _ = Pr{let raw ← $ᵗ (Fin (count*8) → Byte)}[event (splitBlock bits count fits raw).2] :=
          prEvent_congr _ _ _ (fun raw => by rw [splitBlock_snd])
       _ = _ := splitLaw.trans (swapLaw.trans project)

/-- The quota is the full original count, including repeated positions. -/
theorem agreement_probability {Symbol : Type} [DecidableEq Symbol] (bits count : ℕ) (fits : bits ≤ 64)
    (raw claimed : Fin (2^bits) → Symbol) :
    Pr{let bytes ← $ᵗ (Fin (count*8) → Byte)}[ColumnOpening.Agrees raw claimed (typedDraws bits count bytes)] =
      (((2^bits - hammingDist raw claimed : ℕ) : ENNReal) / (2^bits)) ^ count := by
  rw [uniform_draws bits count fits,ColumnOpening.probability_eq,Fintype.card_fin]
  simp only [Nat.cast_pow,Nat.cast_ofNat]

end
end FormalProof4FHE.HasteBoots.NativeAtomicIndexLaw
