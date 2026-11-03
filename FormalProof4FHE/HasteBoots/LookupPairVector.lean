module

public import FormalProof4FHE.HasteBoots.StagedRepeatedLookup
public import VCVio.OracleComp.CanReturn

@[expose] public section

/-!
# Typed private pair vectors with the proved ideal accepted-domain law

Attaching support proofs to the existing pair sampler changes no primitive
query. Every accepted offset is nonzero. The vector samples each pair afresh
in native order, and its all-pass probability retains the combined tuple-hash
and reciprocal-domain error to the actual repetition count. This is still the
ideal accepted-domain sampler, not native rejection-loop/FS/work refinement.
-/

open OracleSpec OracleComp
open scoped Classical

namespace FormalProof4FHE.HasteBoots.LookupPairVector

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq K] [Fintype K] [SampleableType K]
  {width count size : ℕ}

def forget (pair : StagedRepeatedLookup.Pair K) : K × K := (pair.1, pair.2.val)

/-- The original optional sampler succeeds with a valid nonzero offset on
every supported output when the public accepted domain is nonempty. -/
theorem sample_valid (table : Fin size → Fin width → F) (enough : size + 1 < Fintype.card K) :
    Pr{let pair ← TupleLookupPair.sample (K := K) table}[pair.2 ≠ 0] = 1 := by
  apply prEvent_bind_eq_of_forall_eq (OptionT.lift ($ᵗ K)) (by simp [prEvent_norm])
  intro y
  rw [prEvent_map, ReciprocalDetection.sample, ProbComp.prEvent_uniformSelectFinset]
  have filterEq : (ReciprocalDetection.allowed (fun i => TupleHash.hash y (table i))).filter (fun r => r ≠ 0) =
      ReciprocalDetection.allowed (fun i => TupleHash.hash y (table i)) := by
    apply Finset.filter_eq_self.mpr
    intro r member
    exact ((ReciprocalDetection.mem_allowed _ r).mp member).1
  rw [filterEq]
  have total := ReciprocalDetection.sample_total (fun i => TupleHash.hash y (table i)) enough
  rw [ReciprocalDetection.sample, ProbComp.prEvent_uniformSelectFinset] at total
  simpa only [Finset.filter_true] using total

theorem sample_supported (table : Fin size → Fin width → F) (enough : size + 1 < Fintype.card K)
    (value : Option (K × K)) (present : value ∈ support (TupleLookupPair.sample (K := K) table).run) :
    value.elim False (fun pair => pair.2 ≠ 0) := by
  have valid := sample_valid table enough
  rw [OptionT.prEvent_eq_run] at valid
  exact (prEvent_eq_one_iff _ _).mp valid value present

def checked (value : Option (K × K)) (valid : value.elim False (fun pair => pair.2 ≠ 0)) : StagedRepeatedLookup.Pair K :=
  match value with
  | none => False.elim valid
  | some pair => (pair.1, ⟨pair.2, valid⟩)

omit [DecidableEq K] [Fintype K] [SampleableType K] in
theorem checked_forget (value : Option (K × K)) (valid : value.elim False (fun pair => pair.2 ≠ 0)) :
    some (forget (checked value valid)) = value := by
  cases value with
  | none => exact valid.elim
  | some pair => rfl

/-- Support attachment is proof-only; it introduces no draw, query, fallback
or postselection. The original sampler's exact successful value is retained. -/
def sample (table : Fin size → Fin width → F) (enough : size + 1 < Fintype.card K) : ProbComp (StagedRepeatedLookup.Pair K) :=
  (fun observed => checked observed.val
    (sample_supported table enough observed.val ((canReturn_iff_mem_support _ _).mp observed.property))) <$>
    MonadAttach.attach (TupleLookupPair.sample (K := K) table).run

/-- Exact oracle-program erasure, stronger than a claimed equality of laws. -/
theorem sample_forget (table : Fin size → Fin width → F) (enough : size + 1 < Fintype.card K) :
    (fun pair => some (forget pair)) <$> sample (K := K) table enough = (TupleLookupPair.sample (K := K) table).run := by
  rw [sample, Functor.map_map]
  have equal : (fun observed : {value // MonadAttach.CanReturn (TupleLookupPair.sample (K := K) table).run value} =>
      some (forget (checked observed.val (sample_supported table enough observed.val
        ((canReturn_iff_mem_support _ _).mp observed.property))))) = Subtype.val := by
    funext observed
    exact checked_forget _ _
  rw [equal]
  exact WeaklyLawfulMonadAttach.map_attach

/-- Every event of the typed sample has the original pair distribution. -/
theorem sample_law (table : Fin size → Fin width → F) (enough : size + 1 < Fintype.card K) (event : K × K → Prop) :
    Pr{let pair ← sample (K := K) table enough}[event (forget pair)] =
      Pr{let pair ← TupleLookupPair.sample (K := K) table}[event pair] := by
  calc
    _ = Pr{let value ← (TupleLookupPair.sample (K := K) table).run}[value.elim False event] := by
      rw [← sample_forget table enough, prEvent_map]
      rfl
    _ = _ := (OptionT.prEvent_eq_run _ _).symm

def vector (table : Fin size → Fin width → F) (enough : size + 1 < Fintype.card K) :
    (repetitions : ℕ) → ProbComp (Fin repetitions → StagedRepeatedLookup.Pair K)
  | 0 => pure Fin.elim0
  | repetitions + 1 => do
    let pair ← sample (K := K) table enough
    let rest ← vector table enough repetitions
    pure (Fin.cons pair rest)

def AllPass {repetitions : ℕ} (sources : Fin count → Fin width → F) (table : Fin size → Fin width → F)
    (multiplicities : Fin size → K) (pairs : Fin repetitions → StagedRepeatedLookup.Pair K) : Prop :=
  ∀ index, TupleLookupPair.Passes sources table multiplicities (forget (pairs index))

omit [DecidableEq K] [Fintype K] [SampleableType K] in
theorem allPass_cons {repetitions : ℕ} (sources : Fin count → Fin width → F) (table : Fin size → Fin width → F)
    (multiplicities : Fin size → K) (pair : StagedRepeatedLookup.Pair K) (rest : Fin repetitions → StagedRepeatedLookup.Pair K) :
    AllPass sources table multiplicities (Fin.cons pair rest) ↔
      TupleLookupPair.Passes sources table multiplicities (forget pair) ∧ AllPass sources table multiplicities rest := by
  simp [AllPass, Fin.forall_fin_succ]

/-- Repetition independence is proved for the actual fresh-sampling program;
packing width does not replace or multiply the true repetition count. -/
theorem vector_probability (sources : Fin count → Fin width → F) (table : Fin size → Fin width → F)
    (multiplicities : Fin size → K) (enough : size + 1 < Fintype.card K) (repetitions : ℕ) :
    Pr{let pairs ← vector (K := K) table enough repetitions}[AllPass sources table multiplicities pairs] =
      Pr{let pair ← TupleLookupPair.sample (K := K) table}[TupleLookupPair.Passes sources table multiplicities pair] ^ repetitions := by
  induction repetitions with
  | zero => simp [vector, AllPass, prEvent_norm]
  | succ repetitions ih =>
    have independent := prEvent_bind_and_eq_mul (sample (K := K) table enough)
      (fun _ : StagedRepeatedLookup.Pair K => vector (K := K) table enough repetitions)
      (AllPass sources table multiplicities) (fun pair => TupleLookupPair.Passes sources table multiplicities (forget pair)) (fun _ => rfl)
    calc _ = Pr{let pair ← sample (K := K) table enough; let rest ← vector (K := K) table enough repetitions}[
          AllPass sources table multiplicities rest ∧ TupleLookupPair.Passes sources table multiplicities (forget pair)] := by
            simp only [vector, prEvent_norm, allPass_cons, and_comm]
         _ = Pr{let rest ← vector (K := K) table enough repetitions}[AllPass sources table multiplicities rest] *
           Pr{let pair ← sample (K := K) table enough}[TupleLookupPair.Passes sources table multiplicities (forget pair)] := independent
         _ = _ := by rw [ih, sample_law, pow_succ]

/-- Concrete ideal private-vector failure bound; both original losses remain. -/
theorem vector_bound {p : ℕ} [CharP K p]
    (sources : Fin count → Fin width → F) (table : Fin size → Fin width → F) (multiplicities : Fin size → K)
    (enough : size + 1 < Fintype.card K) (bad : ∃ i, ∀ j, sources i ≠ table j) (small : count < p) (repetitions : ℕ) :
    Pr{let pairs ← vector (K := K) table enough repetitions}[AllPass sources table multiplicities pairs] ≤
      TupleLookupPair.error (Fintype.card K) width count size ^ repetitions := by
  rw [vector_probability]
  gcongr
  exact TupleLookupPair.single_bound sources table multiplicities bad small

end

end FormalProof4FHE.HasteBoots.LookupPairVector
