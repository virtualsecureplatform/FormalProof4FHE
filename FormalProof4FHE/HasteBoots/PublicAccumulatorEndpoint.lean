module
public import FormalProof4FHE.HasteBoots.PublicAccumulatorContext
public import FormalProof4FHE.HasteBoots.AccumulatorEndpoint
@[expose] public section

/-! The key-switch endpoint reader uses exactly the coefficient layout of the
public-bound accumulator context, including casts of the ring-size exponent. -/
namespace FormalProof4FHE.HasteBoots.PublicAccumulatorEndpoint
noncomputable section
variable {q cells lanes rows log : ℕ} [Fact q.Prime]

omit [Fact q.Prime] in
/-- Flattening for key switching equals decoding for blind rotation. -/
theorem value_eq_decode (length : 2^cells*(2^lanes) = 2^(cells+lanes))
    (context : PackedAccumulatorOracle.Context (ZMod q) (2^lanes) cells rows) :
    AccumulatorEndpoint.value length context = DecodedAccumulatorTrace.endpoint context.final := rfl

/-- The endpoint reader recovers the exact caller claim. -/
theorem value_public (length : 2^cells*(2^lanes) = 2^(cells+lanes))
    (rounds : PackedAccumulatorTrace.Rounds rows)
    (initial claimed : NativeBlindRotation.Cipher q (2^(cells+lanes))) :
    AccumulatorEndpoint.value length (PublicAccumulatorContext.context rounds initial claimed) = claimed := by
  rw [value_eq_decode]
  exact PublicAccumulatorContext.final_eq rounds initial claimed

/-- The extraction reader's exponent cast preserves every public coefficient. -/
theorem value_public_cast (length : 2^cells*(2^lanes) = 2^log)
    (sameLog : cells+lanes = log) (rounds : PackedAccumulatorTrace.Rounds rows)
    (initial claimed : NativeBlindRotation.Cipher q (2^(cells+lanes))) :
    (fun half index => AccumulatorEndpoint.value length
      (PublicAccumulatorContext.context rounds initial claimed) half
      (Fin.cast (congrArg (fun exponent => 2^exponent) sameLog) index)) = claimed := by
  subst log
  exact value_public length rounds initial claimed

variable {Input Digest Cfg Response Memory CommitMemory : Type}
  {front suffix m queries height : ℕ}

/-- No private-memory branch can change the key-switch endpoint. -/
theorem factory_value (length : 2^cells*(2^lanes) = 2^(cells+lanes))
    (rounds : PackedAccumulatorTrace.Rounds rows)
    (initial claimed : NativeBlindRotation.Cipher q (2^(cells+lanes)))
    (behavior : Memory → AmbientAccumulator.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2^lanes) cells rows front suffix m queries height) (memory : Memory) :
    AccumulatorEndpoint.value length
      ((PublicAccumulatorContext.factory rounds initial claimed behavior) memory).context = claimed :=
  value_public length rounds initial claimed

end
end FormalProof4FHE.HasteBoots.PublicAccumulatorEndpoint
