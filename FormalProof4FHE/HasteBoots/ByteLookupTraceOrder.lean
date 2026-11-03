module

public import FormalProof4FHE.HasteBoots.CoefficientTraceOrder
public import FormalProof4FHE.HasteBoots.OptionalTraceOrder
public import FormalProof4FHE.HasteBoots.ByteLookupPairTyped

@[expose] public section

/-!
# Full completed raw-byte lookup observations increase with analysis depth

The order retains first-challenge bytes, all rejected reciprocal trials, and
all repeated pair records. Its events may inspect every retained observation.
It is therefore suitable for trace-sensitive helper and verifier continuations.
-/

open OracleSpec OracleComp
open scoped Classical

namespace FormalProof4FHE.HasteBoots.ByteLookupTraceOrder

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  {p degree width size : ℕ} [Module (ZMod p) K] [DecidableEq K]

omit [DecidableEq K] in
/-- The field candidate and its complete raw coefficient observation survive
an increase of the inner canonical-byte approximation. -/
theorem trial (basis : Module.Basis (Fin degree) (ZMod p) K) {first second : ℕ} (ordered : first ≤ second) :
    CompletedObservation.LE (ByteReciprocalSampler.step basis first) (ByteReciprocalSampler.step basis second)
      (fun result => ByteReciprocalSampler.candidate result ≠ none) := by
  apply CompletedObservation.complete_congr _ (CoefficientTraceOrder.extension basis 1 ordered)
  intro result
  cases tag : result.1 <;> simp [ByteReciprocalSampler.candidate, tag]

/-- Both inner and outer depths preserve completed reciprocal observations,
including all earlier completed rejected fields and their raw bytes. -/
theorem reciprocal (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → K)
    {inner outer inner' outer' : ℕ} (hi : inner ≤ inner') (ho : outer ≤ outer') :
    CompletedObservation.LE (ByteReciprocalSampler.program basis table inner outer)
      (ByteReciprocalSampler.program basis table inner' outer') OptionalTraceOrder.loopComplete :=
  CompletedObservation.trans
    (OptionalTraceOrder.loop_steps ByteReciprocalSampler.candidate (trial basis hi) (ByteReciprocalSampler.allow table) outer)
    (OptionalTraceOrder.loop_outer _ _ _ ho)

def pairComplete (result : ByteLookupPairSampler.Result p degree K) : Prop := result.value ≠ none

/-- Increasing all three depths preserves the actual complete pair record,
not merely its two projected field values. -/
theorem pair (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F)
    {hashDepth inner outer hashDepth' inner' outer' : ℕ}
    (hh : hashDepth ≤ hashDepth') (hi : inner ≤ inner') (ho : outer ≤ outer') :
    CompletedObservation.LE (ByteLookupPairSampler.program basis table hashDepth inner outer)
      (ByteLookupPairSampler.program basis table hashDepth' inner' outer') pairComplete := by
  unfold ByteLookupPairSampler.program
  apply CompletedObservation.bind (trial basis hh)
  · intro first done
    cases tag : ByteReciprocalSampler.candidate first with
    | none => exact (done tag).elim
    | some y =>
      simp only
      apply CompletedObservation.map (reciprocal basis (ByteLookupPairSampler.hashes table y) hi ho)
      intro last
      cases tag : last.value <;> simp [pairComplete, ByteLookupPairSampler.finish, OptionalTraceOrder.loopComplete, tag]
  · intro first suspended
    have tag : ByteReciprocalSampler.candidate first = none := by simpa only [not_not] using suspended
    simp [tag, pairComplete, prEvent_norm]

/-- Fresh repetition preserves all complete raw observations for any event on
the complete vector, including every rejected trial in each repetition. -/
theorem vector (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F)
    (repetitions : ℕ) {hashDepth inner outer hashDepth' inner' outer' : ℕ}
    (hh : hashDepth ≤ hashDepth') (hi : inner ≤ inner') (ho : outer ≤ outer') :
    CompletedObservation.LE (ByteLookupPairVector.program basis table hashDepth inner outer repetitions)
      (ByteLookupPairVector.program basis table hashDepth' inner' outer' repetitions) OptionalTraceOrder.vectorComplete :=
  OptionalTraceOrder.vector ByteLookupPairSampler.Result.value (pair basis table hh hi ho) repetitions

omit [Module (ZMod p) K] [DecidableEq K] in
/-- Proof-only typed vectors are uniquely determined by their full raw record. -/
theorem raw_injective {repetitions : ℕ} : Function.Injective (ByteLookupPairTyped.Sample.raw (p := p) (degree := degree) (K := K) (repetitions := repetitions)) := by
  intro first second equal
  have injective : Function.Injective (ByteLookupPairTyped.forget (K := K) (repetitions := repetitions)) := by
    intro left right same
    funext index
    have point := congrFun same index
    apply Prod.ext
    · exact congrArg (fun pair : K × K => pair.1) point
    · apply Subtype.ext
      exact congrArg (fun pair : K × K => pair.2) point
  have values : first.values = second.values :=
    Option.map_injective injective (first.consistent.trans (equal ▸ second.consistent.symm))
  cases first
  cases second
  cases equal
  cases values
  rfl

omit [Module (ZMod p) K] [DecidableEq K] in
/-- Completion agrees on the typed vector and the raw record. -/
theorem typed_complete {repetitions : ℕ} (observed : ByteLookupPairTyped.Sample p degree K repetitions) :
    OptionalTraceOrder.vectorComplete observed.raw ↔ observed.values ≠ none := by
  rw [OptionalTraceOrder.vectorComplete, ← observed.consistent]
  cases observed.values <;> simp

/-- The full typed observation order follows by injective erasure. No choice
of a replacement observation or resampling inverse is introduced. -/
theorem typed (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F)
    (repetitions : ℕ) {hashDepth inner outer hashDepth' inner' outer' : ℕ}
    (hh : hashDepth ≤ hashDepth') (hi : inner ≤ inner') (ho : outer ≤ outer') :
    CompletedObservation.LE (ByteLookupPairTyped.sample basis table hashDepth inner outer repetitions)
      (ByteLookupPairTyped.sample basis table hashDepth' inner' outer' repetitions) (fun result => result.values ≠ none) := by
  apply CompletedObservation.of_map_injective ByteLookupPairTyped.Sample.raw raw_injective _ OptionalTraceOrder.vectorComplete typed_complete
  rw [ByteLookupPairTyped.sample_raw, ByteLookupPairTyped.sample_raw]
  exact vector basis table repetitions hh hi ho

end

end FormalProof4FHE.HasteBoots.ByteLookupTraceOrder
