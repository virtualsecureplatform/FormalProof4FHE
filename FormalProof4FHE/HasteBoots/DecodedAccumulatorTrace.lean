module
public import FormalProof4FHE.HasteBoots.DecodedAccumulatorConstraints
@[expose] public section

/-! Construct the complete coefficient trace and endpoint ciphertexts from
original sources, preserving the native cyclic and active-round geometry. -/
namespace FormalProof4FHE.HasteBoots.DecodedAccumulatorTrace
noncomputable section
variable {q cells lanes rows : ℕ} [Fact q.Prime]

/-- Decode the actual public endpoint table, retaining both halves and lanes. -/
def endpoint (value : Bool → MatrixFold.Cube cells → Fin (2^lanes) → ZMod q) :
    NativeBlindRotation.Cipher q (2^(cells+lanes)) :=
  fun half index =>
    let coefficient := (PackedAccumulatorTrace.polynomial cells lanes).symm index
    value half coefficient.1 coefficient.2

/-- Repacking the constructed endpoint returns every original scalar. -/
theorem endpoint_pack (value : Bool → MatrixFold.Cube cells → Fin (2^lanes) → ZMod q) :
    PackedAccumulatorTrace.endpoint (RingHom.id (ZMod q)) (endpoint value) = value := by
  funext half cell lane
  simp only [PackedAccumulatorTrace.endpoint,endpoint,Equiv.symm_apply_apply,RingHom.id_apply]

/-- An original coefficient endpoint fixture is recovered exactly. -/
theorem endpoint_unpack (value : NativeBlindRotation.Cipher q (2^(cells+lanes))) :
    endpoint (PackedAccumulatorTrace.endpoint (RingHom.id (ZMod q)) value) = value := by
  funext half index
  simp only [endpoint,PackedAccumulatorTrace.endpoint,Prod.mk.eta,Equiv.apply_symm_apply,RingHom.id_apply]

/-- All original arithmetic arrays and endpoint tables are the exact pack of
the decoded trace. Only public start/finish index association is required. -/
theorem repack (sources : AccumulatorMatrixSoundness.Sources (ZMod q) (2^lanes) cells rows)
    (rounds : PackedAccumulatorTrace.Rounds rows)
    (start : sources.start = (FlatMatrixFold.index rows).symm (AccumulatorTrace.wrap rounds.shape))
    (finish : sources.finish = (FlatMatrixFold.index rows).symm (AccumulatorTrace.last rounds.shape)) :
    PackedAccumulatorTrace.sources (RingHom.id (ZMod q)) rounds (DecodedAccumulatorRows.tables sources)
      (endpoint sources.initial) (endpoint sources.final) sources.duplicateA sources.duplicateB = sources := by
  simp only [PackedAccumulatorTrace.sources,DecodedAccumulatorRows.tables,
    DecodedAccumulatorRows.pack_decode,endpoint_pack,←start,←finish]

/-- The actual residual family yields initial/final equality and full cyclic
continuity on the constructed trace, including both boundary corrections. -/
theorem linkage_of_holds
    (sources : AccumulatorMatrixSoundness.Sources (ZMod q) (2^lanes) cells rows)
    (rounds : PackedAccumulatorTrace.Rounds rows)
    (start : sources.start = (FlatMatrixFold.index rows).symm (AccumulatorTrace.wrap rounds.shape))
    (finish : sources.finish = (FlatMatrixFold.index rows).symm (AccumulatorTrace.last rounds.shape))
    (holds : AccumulatorEndpointSoundness.FullHolds sources) :
    AccumulatorTrace.Linkage rounds.shape (DecodedAccumulatorRows.tables sources)
      (endpoint sources.initial) (endpoint sources.final) := by
  have checked : AccumulatorEndpointSoundness.FullHolds
      (PackedAccumulatorTrace.sources (RingHom.id (ZMod q)) rounds (DecodedAccumulatorRows.tables sources)
        (endpoint sources.initial) (endpoint sources.final) sources.duplicateA sources.duplicateB) := by
    rw [repack sources rounds start finish]
    exact holds
  exact PackedAccumulatorTrace.linkage_of_holds (RingHom.id (ZMod q)) rounds (DecodedAccumulatorRows.tables sources)
    (endpoint sources.initial) (endpoint sources.final) sources.duplicateA sources.duplicateB checked

variable {levels : ℕ}

/-- The constructed original trace executes precisely the active rounds in
native order; padded rows remain in the constraints and are not executed. -/
theorem valid_trace_of_holds
    (sources : AccumulatorMatrixSoundness.Sources (ZMod q) (2^lanes) cells rows)
    (rounds : PackedAccumulatorTrace.Rounds rows)
    (start : sources.start = (FlatMatrixFold.index rows).symm (AccumulatorTrace.wrap rounds.shape))
    (finish : sources.finish = (FlatMatrixFold.index rows).symm (AccumulatorTrace.last rounds.shape))
    (holds : AccumulatorEndpointSoundness.FullHolds sources)
    (bits : ℕ) (controls : Fin rounds.count → NativeBlindRotation.Control q (2^(cells+lanes)) levels × ℕ)
    (rotation : ∀ round, DecodedAccumulatorRows.decode sources.product (AccumulatorTrace.active rounds.shape round) =
      fun half => NativeBlindRotation.rotate (controls round).2
        (DecodedAccumulatorRows.decode sources.input (AccumulatorTrace.active rounds.shape round) half))
    (external : ∀ round, DecodedAccumulatorRows.decode sources.external (AccumulatorTrace.active rounds.shape round) =
      NativeBlindRotation.externalProduct bits (controls round).1
        (DecodedAccumulatorRows.decode sources.difference (AccumulatorTrace.active rounds.shape round))) :
    NativeBlindRotation.ValidTrace bits (List.ofFn controls) (endpoint sources.initial)
      (List.ofFn (AccumulatorTrace.traceAt rounds.shape (DecodedAccumulatorRows.tables sources))) (endpoint sources.final) :=
  AccumulatorTrace.validTrace_tables rounds.shape (DecodedAccumulatorRows.tables sources) (endpoint sources.initial) (endpoint sources.final)
    (DecodedAccumulatorConstraints.arithmetic_of_holds sources holds.1) (linkage_of_holds sources rounds start finish holds)
    bits controls rotation external

/-- The decoded actual final endpoint is the result of the native run whenever
the original constraints and actual multiplication-stage semantics hold. -/
theorem output_eq_run_of_holds
    (sources : AccumulatorMatrixSoundness.Sources (ZMod q) (2^lanes) cells rows)
    (rounds : PackedAccumulatorTrace.Rounds rows)
    (start : sources.start = (FlatMatrixFold.index rows).symm (AccumulatorTrace.wrap rounds.shape))
    (finish : sources.finish = (FlatMatrixFold.index rows).symm (AccumulatorTrace.last rounds.shape))
    (holds : AccumulatorEndpointSoundness.FullHolds sources)
    (bits : ℕ) (controls : Fin rounds.count → NativeBlindRotation.Control q (2^(cells+lanes)) levels × ℕ)
    (rotation : ∀ round, DecodedAccumulatorRows.decode sources.product (AccumulatorTrace.active rounds.shape round) =
      fun half => NativeBlindRotation.rotate (controls round).2
        (DecodedAccumulatorRows.decode sources.input (AccumulatorTrace.active rounds.shape round) half))
    (external : ∀ round, DecodedAccumulatorRows.decode sources.external (AccumulatorTrace.active rounds.shape round) =
      NativeBlindRotation.externalProduct bits (controls round).1
        (DecodedAccumulatorRows.decode sources.difference (AccumulatorTrace.active rounds.shape round))) :
    endpoint sources.final = NativeBlindRotation.run bits (List.ofFn controls) (endpoint sources.initial) :=
  NativeBlindRotation.validTrace_output bits _ _ _ _
    (valid_trace_of_holds sources rounds start finish holds bits controls rotation external)

end
end FormalProof4FHE.HasteBoots.DecodedAccumulatorTrace
