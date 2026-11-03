module

public import FormalProof4FHE.HasteBoots.ByteLookupPairVector
public import FormalProof4FHE.HasteBoots.LookupPairVector

@[expose] public section

/-!
# Proof-only typing of completed byte-backed challenge vectors

Support attachment supplies nonzero-offset proofs for the actual completed
values. It introduces no draw or fallback. Suspension and the full raw
observation remain in the output. Erasure is equality of query programs.
-/

open OracleSpec OracleComp MeasureTheory
open scoped Classical

namespace FormalProof4FHE.HasteBoots.ByteLookupPairTyped

noncomputable section

abbrev Raw (p degree : ℕ) (K : Type) (repetitions : ℕ) :=
  ObservedOptionalVector.Result (K × K) (ByteLookupPairSampler.Result p degree K) repetitions

def forget {K : Type} [Zero K] {repetitions : ℕ}
    (values : Fin repetitions → StagedRepeatedLookup.Pair K) : Fin repetitions → K × K :=
  fun index => ((values index).1, (values index).2.val)

structure Sample (p degree : ℕ) (K : Type) [Zero K] (repetitions : ℕ) where
  raw : Raw p degree K repetitions
  values : Option (Fin repetitions → StagedRepeatedLookup.Pair K)
  consistent : values.map forget = raw.values

def checked {K : Type} [Zero K] {repetitions : ℕ} (values : Option (Fin repetitions → K × K))
    (valid : values.elim True (fun values => ∀ index, (values index).2 ≠ 0)) :
    Option (Fin repetitions → StagedRepeatedLookup.Pair K) :=
  match values with
  | none => none
  | some values => some (fun index => ((values index).1, ⟨(values index).2, valid index⟩))

/-- Typing successful values preserves exactly the original optional vector. -/
theorem checked_forget {K : Type} [Zero K] {repetitions : ℕ} (values : Option (Fin repetitions → K × K))
    (valid : values.elim True (fun values => ∀ index, (values index).2 ≠ 0)) :
    (checked values valid).map forget = values := by
  cases values <;> rfl

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  {p degree width count size repetitions : ℕ} [Module (ZMod p) K] [DecidableEq K]

def ofSupported (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F)
    (hashDepth inner outer : ℕ) (raw : Raw p degree K repetitions)
    (supported : raw ∈ support (ByteLookupPairVector.program basis table hashDepth inner outer repetitions)) :
    Sample p degree K repetitions :=
  let valid : raw.values.elim True (fun values => ∀ index, (values index).2 ≠ 0) := by
    cases tag : raw.values with
    | none => trivial
    | some values => exact ByteLookupPairVector.returned_nonzero basis table hashDepth inner outer repetitions raw supported values tag
  ⟨raw, checked raw.values valid, checked_forget raw.values valid⟩

/-- Support proofs are attached to the existing byte program; no byte is
resampled and no partial trace is erased on suspension. -/
def sample (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F)
    (hashDepth inner outer repetitions : ℕ) : ProbComp (Sample p degree K repetitions) :=
  (fun observed => ofSupported basis table hashDepth inner outer observed.val
    ((canReturn_iff_mem_support _ _).mp observed.property)) <$>
    MonadAttach.attach (ByteLookupPairVector.program basis table hashDepth inner outer repetitions)

/-- Erasing support proofs and typed values recovers the original query tree. -/
theorem sample_raw (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F)
    (hashDepth inner outer repetitions : ℕ) :
    Sample.raw <$> sample basis table hashDepth inner outer repetitions =
      ByteLookupPairVector.program basis table hashDepth inner outer repetitions := by
  rw [sample, Functor.map_map]
  exact WeaklyLawfulMonadAttach.map_attach

omit [Module (ZMod p) K] [DecidableEq K] in
/-- Each typed observation carries its original suspended or completed values. -/
theorem value_event (observed : Sample p degree K repetitions) (event : (Fin repetitions → K × K) → Prop) :
    observed.values.elim False (fun values => event (forget values)) = observed.raw.values.elim False event := by
  rw [← observed.consistent]
  cases observed.values <;> rfl

/-- Exact optional value-program erasure, without postselection on completion. -/
theorem sample_values (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F)
    (hashDepth inner outer repetitions : ℕ) :
    (fun observed => observed.values.map forget) <$> sample basis table hashDepth inner outer repetitions =
      (fun raw => raw.values) <$> ByteLookupPairVector.program basis table hashDepth inner outer repetitions := by
  calc _ = (fun observed => observed.raw.values) <$> sample basis table hashDepth inner outer repetitions := by
            congr 1
            funext observed
            exact observed.consistent
       _ = _ := by rw [← Functor.map_map, sample_raw]

/-- Every successful-vector event retains the actual finite byte-program
law. This does not identify an entire native transcript with an ideal law. -/
theorem event_law (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F)
    (hashDepth inner outer repetitions : ℕ) (event : (Fin repetitions → K × K) → Prop) :
    Pr{let observed ← sample basis table hashDepth inner outer repetitions}[
      observed.values.elim False (fun values => event (forget values))] =
    Pr{let raw ← ByteLookupPairVector.program basis table hashDepth inner outer repetitions}[raw.values.elim False event] := by
  rw [← sample_raw basis table hashDepth inner outer repetitions, prEvent_map]
  exact prEvent_congr _ _ _ (fun observed => (value_event observed event).to_iff)

/-- The actual consumed-byte mean is unchanged by proof-only typing. -/
theorem expectedBytes (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F)
    (hashDepth inner outer repetitions : ℕ) :
    (∫⁻ value, value ∂𝒟[(fun observed => (ByteLookupPairVector.consumedBytes observed.raw : ENNReal)) <$>
      sample basis table hashDepth inner outer repetitions]) =
      ByteLookupPairVector.expectedBytes basis table hashDepth inner outer repetitions := by
  have observed := congrArg (fun computation : ProbComp (Raw p degree K repetitions) =>
    ∫⁻ value, value ∂𝒟[(fun raw => (ByteLookupPairVector.consumedBytes raw : ENNReal)) <$> computation])
    (sample_raw basis table hashDepth inner outer repetitions)
  simp only [Functor.map_map] at observed
  refine observed.trans ?_
  rfl

variable [Fintype K] [SampleableType K] [NeZero p]

/-- The typed successful-vector bound is derived from the underlying bytes. -/
theorem finite_bound {char : ℕ} [CharP K char] (valid : 1 < p)
    (basis : Module.Basis (Fin degree) (ZMod p) K)
    (sources : Fin count → Fin width → F) (table : Fin size → Fin width → F) (multiplicities : Fin size → K)
    (enough : size + 1 < Fintype.card K) (bad : ∃ index, ∀ entry, sources index ≠ table entry) (small : count < char)
    (hashDepth inner outer repetitions : ℕ) :
    Pr{let observed ← sample basis table hashDepth inner outer repetitions}[
      observed.values.elim False (LookupPairVector.AllPass sources table multiplicities)] ≤
      TupleLookupPair.error (Fintype.card K) width count size ^ repetitions := by
  have law := event_law basis table hashDepth inner outer repetitions
    (ObservedOptionalVector.All (TupleLookupPair.Passes sources table multiplicities))
  have events : (fun values : Fin repetitions → StagedRepeatedLookup.Pair K => ObservedOptionalVector.All (TupleLookupPair.Passes sources table multiplicities) (forget values)) =
      LookupPairVector.AllPass sources table multiplicities := by
    funext values
    rfl
  rw [events] at law
  exact law.trans_le (ByteLookupPairVector.finite_bound valid basis sources table multiplicities enough bad small hashDepth inner outer repetitions)

end

end FormalProof4FHE.HasteBoots.ByteLookupPairTyped
