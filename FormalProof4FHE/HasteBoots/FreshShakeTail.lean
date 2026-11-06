module
public import FormalProof4FHE.HasteBoots.NativeShakeReadLaw
@[expose] public section

/-! Freshness of an unread SHAKE tail in the actual cache. Arbitrary cache
entries outside that tail are retained; installed past bytes do not refresh. -/
namespace FormalProof4FHE.HasteBoots.FreshShakeTail
open InputIndexedOracle (Input Byte World)
open NativeShakeCache (Cache)
noncomputable section

def Fresh (cache : Cache) (input : Input) (offset : ℕ) : Prop :=
  ∀ position, offset ≤ position → cache (input,position) = none

theorem write_after (cache : Cache) (input values : Input) (offset position : ℕ)
    (afterRead : offset+values.length ≤ position) :
    NativeShakeHistory.writeBytes cache input offset values (input,position) = cache (input,position) := by
  induction values generalizing cache offset with
  | nil => rfl
  | cons value rest ih =>
    rw [NativeShakeHistory.writeBytes,ih _ (offset+1) (by simp only [List.length_cons] at afterRead; omega)]
    exact Function.update_of_ne (by intro same; have := congrArg Prod.snd same; simp only [List.length_cons] at afterRead; omega) _ _

theorem eager_values (cache : Cache) (input : Input) (offset count : ℕ)
    (fresh : Fresh cache input offset) (raw : Fin count → Byte) :
    (NativeShakeReadLaw.eager input offset raw cache).1 = List.ofFn raw := by
  rw [NativeShakeReadLaw.eager_bytes]
  congr 1
  funext index
  rw [fresh _ (by omega),Option.getD_none]

theorem eager_fresh (cache : Cache) (input : Input) (offset count : ℕ)
    (fresh : Fresh cache input offset) (raw : Fin count → Byte) :
    Fresh (NativeShakeReadLaw.eager input offset raw cache).2 input (offset+count) := by
  intro position afterRead
  rw [NativeShakeReadLaw.eager_records,eager_values cache input offset count fresh,
    write_after _ _ _ _ _ (by simpa only [List.length_ofFn] using afterRead)]
  exact fresh position (by omega)

theorem observed_fresh (log : List NativeTranscript.Observation) (world : World) (input : Input) (offset : ℕ)
    (unseen : ∀ position, offset ≤ position → (.inl (input,position) : InputIndexedOracle.Coordinate) ∉ ObservationReplay.footprint log) :
    Fresh (NativeShakeKernel.observed log world) input offset := by
  intro position beyond
  simp only [NativeShakeKernel.observed,unseen position beyond,ite_false]
end
end FormalProof4FHE.HasteBoots.FreshShakeTail
