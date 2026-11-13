module
public import FormalProof4FHE.HasteBoots.AmbientAccumulator
public import FormalProof4FHE.HasteBoots.DecodedAccumulatorTrace
@[expose] public section

/-! Bind the accumulator verifier to the caller's public endpoints and native
round metadata before its behavior factory receives any challenges. -/
namespace FormalProof4FHE.HasteBoots.PublicAccumulatorContext
noncomputable section
variable {F Input Digest Cfg Response Memory CommitMemory : Type} [Field F]
  {b c r front suffix m queries height : ℕ}

/-- Context changes query locations and expected values, but never packet arity. -/
theorem queries_length (oldContext newContext : PackedAccumulatorOracle.Context F b c r)
    (query : PackedSumcheckSubclaim.Query F b ((1+r)+c)) (factor : Fin 7) :
    (PackedAccumulatorOracle.queries oldContext query factor).length =
      (PackedAccumulatorOracle.queries newContext query factor).length := by
  simp only [PackedAccumulatorOracle.queries]
  split_ifs <;> rfl

/-- Replace the trusted context and transport only the opening packet arity.
The ambient verifier will overwrite the behavior's roots, queries and values. -/
def bind (context : PackedAccumulatorOracle.Context F b c r)
    (behavior : AmbientAccumulator.Scheme F Input Digest Cfg Response Memory CommitMemory
      b c r front suffix m queries height) :
    AmbientAccumulator.Scheme F Input Digest Cfg Response Memory CommitMemory
      b c r front suffix m queries height :=
  {behavior with
    context := context
    build := fun emission packet factor =>
      queries_length behavior.context context packet.query factor ▸ behavior.build emission packet factor}

variable {q cells lanes rows : ℕ} [Fact q.Prime]

/-- Public endpoint values are packed in the native coefficient address order. -/
def context (rounds : PackedAccumulatorTrace.Rounds rows)
    (initial claimed : NativeBlindRotation.Cipher q (2^(cells+lanes))) :
    PackedAccumulatorOracle.Context (ZMod q) (2^lanes) cells rows where
  initial := PackedAccumulatorTrace.endpoint (RingHom.id (ZMod q)) initial
  final := PackedAccumulatorTrace.endpoint (RingHom.id (ZMod q)) claimed
  start := (FlatMatrixFold.index rows).symm (AccumulatorTrace.wrap rounds.shape)
  finish := (FlatMatrixFold.index rows).symm (AccumulatorTrace.last rounds.shape)

/-- Bind every private-memory branch to the same caller statement. -/
def factory (rounds : PackedAccumulatorTrace.Rounds rows)
    (initial claimed : NativeBlindRotation.Cipher q (2^(cells+lanes)))
    (behavior : Memory → AmbientAccumulator.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2^lanes) cells rows front suffix m queries height) :=
  fun memory => bind (context rounds initial claimed) (behavior memory)

/-- Decoding the trusted public initial endpoint recovers the caller's ciphertext. -/
theorem initial_eq (rounds : PackedAccumulatorTrace.Rounds rows)
    (initial claimed : NativeBlindRotation.Cipher q (2^(cells+lanes))) :
    DecodedAccumulatorTrace.endpoint (context rounds initial claimed).initial = initial :=
  DecodedAccumulatorTrace.endpoint_unpack initial

/-- Decoding the trusted public final endpoint recovers the caller's claim. -/
theorem final_eq (rounds : PackedAccumulatorTrace.Rounds rows)
    (initial claimed : NativeBlindRotation.Cipher q (2^(cells+lanes))) :
    DecodedAccumulatorTrace.endpoint (context rounds initial claimed).final = claimed :=
  DecodedAccumulatorTrace.endpoint_unpack claimed

end
end FormalProof4FHE.HasteBoots.PublicAccumulatorContext
