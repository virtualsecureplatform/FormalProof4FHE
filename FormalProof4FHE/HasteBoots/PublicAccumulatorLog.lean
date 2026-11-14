module
public import FormalProof4FHE.HasteBoots.PublicAccumulatorEndpoint
@[expose] public section

/-! Public endpoint binding at the common ring size used by later stages,
without restricting the accumulator packing dimensions. -/
namespace FormalProof4FHE.HasteBoots.PublicAccumulatorLog
noncomputable section
variable {q oldLog newLog : ℕ}

/-- Reindex coefficient arrays along equality of their ring exponents. -/
def cast (same : oldLog = newLog) (cipher : NativeBlindRotation.Cipher q (2^oldLog)) :
    NativeBlindRotation.Cipher q (2^newLog) :=
  fun half index => cipher half (Fin.cast (congrArg (fun exponent => 2^exponent) same.symm) index)

theorem cast_refl (cipher : NativeBlindRotation.Cipher q (2^oldLog)) : cast rfl cipher = cipher := rfl

theorem cast_roundtrip (same : oldLog = newLog) (cipher : NativeBlindRotation.Cipher q (2^oldLog)) :
    cast same.symm (cast same cipher) = cipher := by
  subst newLog
  rfl

/-- Existing packed-length geometry determines the common ring exponent. -/
theorem exponent_eq {cells lanes log : ℕ} (length : 2^cells*(2^lanes) = 2^log) : cells+lanes = log :=
  Nat.pow_right_injective (by decide : 2 ≤ 2) (by simpa only [Nat.pow_add] using length)

variable {cells lanes rows log : ℕ} [Fact q.Prime]
  {Input Digest Cfg Response Memory CommitMemory : Type} {front suffix m queries height : ℕ}

/-- The existing public context is bound before any private-memory branch. -/
def factory (sameLog : cells+lanes = log) (rounds : PackedAccumulatorTrace.Rounds rows)
    (initial claimed : NativeBlindRotation.Cipher q (2^log))
    (behavior : Memory → AmbientAccumulator.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2^lanes) cells rows front suffix m queries height) :=
  PublicAccumulatorContext.factory rounds (cast sameLog.symm initial) (cast sameLog.symm claimed) behavior

/-- Every branch's actual endpoint reader recovers the logical public claim. -/
theorem factory_value (length : 2^cells*(2^lanes) = 2^log) (sameLog : cells+lanes = log)
    (rounds : PackedAccumulatorTrace.Rounds rows) (initial claimed : NativeBlindRotation.Cipher q (2^log))
    (behavior : Memory → AmbientAccumulator.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2^lanes) cells rows front suffix m queries height) (memory : Memory) :
    AccumulatorEndpoint.value length ((factory sameLog rounds initial claimed behavior) memory).context = claimed := by
  subst log
  exact PublicAccumulatorEndpoint.factory_value length rounds initial claimed behavior memory

end
end FormalProof4FHE.HasteBoots.PublicAccumulatorLog
