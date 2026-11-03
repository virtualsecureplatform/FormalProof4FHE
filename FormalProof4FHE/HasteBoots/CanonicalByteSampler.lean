module

public import FormalProof4FHE.HasteBoots.CanonicalByteMask
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-!
# Canonical prime-field byte rejection: operational ideal law and byte cost

The native width is the bit length of p-1. Each attempt reads its ceiling byte
width, decodes little-endian, masks, and accepts exactly values below p. All
raw byte chunks, including rejected chunks, remain in the prefix trace.
Fresh ideal bytes are explicit; transcript/XOF and Rust refinement remain open.
-/

open OracleSpec OracleComp MeasureTheory
open scoped Classical BigOperators
open FormalProof4FHE.HasteBoots.CanonicalByteMask

namespace FormalProof4FHE.HasteBoots.CanonicalByteSampler

noncomputable section

def bits (p : ℕ) : ℕ := (p - 1).size

def byteCount (p : ℕ) : ℕ := (bits p + 7) / 8

theorem bits_positive (p : ℕ) (valid : 1 < p) : 0 < bits p :=
  Nat.size_pos.mpr (by omega)

theorem fits (p : ℕ) : bits p ≤ 8 * byteCount p := by
  unfold byteCount
  omega

theorem modulus_le (p : ℕ) (valid : 1 < p) : p ≤ 2 ^ bits p := by
  have bound := Nat.lt_size_self (p - 1)
  change p - 1 < 2 ^ bits p at bound
  omega

theorem range_lt_twice (p : ℕ) (valid : 1 < p) : 2 ^ bits p < 2 * p := by
  have positive := bits_positive p valid
  have lower : 2 ^ (bits p - 1) ≤ p - 1 := Nat.lt_size.mp (by change bits p - 1 < bits p; omega)
  have power : 2 ^ bits p = 2 * 2 ^ (bits p - 1) := by
    conv_lhs => rw [show bits p = (bits p - 1) + 1 by omega]
    rw [pow_succ']
  rw [power]
  omega

/-- Finite-range counting transport for a canonical value and any event. -/
def belowEvent (p q : ℕ) (bound : p ≤ q) (event : ℕ → Prop) :
    {value : Fin q // value.val < p ∧ event value.val} ≃ {value : Fin p // event value.val} where
  toFun value := ⟨⟨value.val.val, value.property.1⟩, value.property.2⟩
  invFun value := ⟨⟨value.val.val, lt_of_lt_of_le value.val.isLt bound⟩, value.val.isLt, value.property⟩
  left_inv value := by ext; rfl
  right_inv value := by ext; rfl

theorem truncated_card (p q : ℕ) (bound : p ≤ q) (event : ℕ → Prop) :
    (Finset.univ.filter (fun value : Fin q => value.val < p ∧ event value.val)).card =
      (Finset.univ.filter (fun value : Fin p => event value.val)).card := by
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (belowEvent p q bound event)

def accepted (p : ℕ) : Finset (Bytes (byteCount p)) :=
  Finset.univ.filter (fun raw => masked (bits p) raw < p)

/-- Each rejected byte chunk stays in order; `none` is analysis suspension. -/
def runPrefix (p : ℕ) : ℕ → ProbComp (RejectionSampling.Result (Bytes (byteCount p)))
  | 0 => pure (none, [])
  | fuel + 1 => do
    let raw ← $ᵗ (Bytes (byteCount p))
    if masked (bits p) raw < p then pure (some raw, [raw])
    else (fun result => (result.1, raw :: result.2)) <$> runPrefix p fuel

/-- Exact oracle-program equality derives the finite-domain proof interface
from the direct native below-modulus test, with no added draw or filtering. -/
theorem runPrefix_eq (p fuel : ℕ) : runPrefix p fuel = RejectionSampling.runPrefix (accepted p) fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    rw [runPrefix, RejectionSampling.runPrefix]
    congr 1
    funext raw
    simp only [accepted, Finset.mem_filter, Finset.mem_univ, true_and, ih]

/-- The hit event uses the actual native mask and below-modulus test. -/
theorem hit_law (p : ℕ) (event : ℕ → Prop) :
    RejectionSampling.hit (accepted p) (fun raw => event (masked (bits p) raw)) =
      Pr{let value ← $ᵗ (Fin (2 ^ bits p))}[value.val < p ∧ event value.val] := by
  unfold RejectionSampling.hit
  have same : ∀ raw, (raw ∈ accepted p ∧ event (masked (bits p) raw)) ↔
      (masked (bits p) raw < p ∧ event (masked (bits p) raw)) := by
    intro raw
    simp [accepted]
  exact (prEvent_congr _ _ _ same).trans (uniform_masked (bits p) (byteCount p) (fits p) (fun value => value < p ∧ event value))

theorem hit_fraction (p : ℕ) (valid : 1 < p) (event : ℕ → Prop) :
    RejectionSampling.hit (accepted p) (fun raw => event (masked (bits p) raw)) =
      ((Finset.univ.filter (fun value : Fin p => event value.val)).card : ENNReal) / (2 ^ bits p : ℕ) := by
  rw [hit_law, SampleableType.prEvent_uniformSample, truncated_card p _ (modulus_le p valid)]
  simp only [Fintype.card_fin]

def eventProbability (p : ℕ) (event : ℕ → Prop) : ENNReal :=
  ⨆ fuel, Pr{let result ← runPrefix p fuel}[result.1.elim False (fun raw => event (masked (bits p) raw))]

theorem eventProbability_eq (p : ℕ) (event : ℕ → Prop) :
    eventProbability p event =
      RejectionSampling.eventProbability (accepted p) (fun raw => event (masked (bits p) raw)) := by
  unfold eventProbability
  simp_rw [runPrefix_eq]
  rfl

/-- Exact limiting canonical value law, proved from the actual raw-byte
rejection prefixes rather than assuming masked/accepted values are uniform. -/
theorem uniform_value (p : ℕ) (valid : 1 < p) [NeZero p] (event : ℕ → Prop) :
    eventProbability p event = Pr{let value ← $ᵗ (Fin p)}[event value.val] := by
  rw [eventProbability_eq, RejectionSampling.eventProbability_eq_ratio, hit_fraction p valid]
  have denominator : RejectionSampling.hit (accepted p) (fun _ => True) = (p : ENNReal) / (2 ^ bits p : ℕ) := by
    simpa only [Finset.filter_true, Finset.card_univ, Fintype.card_fin] using hit_fraction p valid (fun _ => True)
  rw [denominator, SampleableType.prEvent_uniformSample]
  have nonzero : ((2 ^ bits p : ℕ) : ENNReal) ≠ 0 := by exact_mod_cast (by positivity : (2 ^ bits p : ℕ) ≠ 0)
  simp only [Fintype.card_fin, div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inr (ENNReal.inv_ne_top.mpr nonzero)) (Or.inl (by simp)), inv_inv]
  calc _ = ((Finset.univ.filter (fun value : Fin p => event value.val)).card : ENNReal) * (p : ENNReal)⁻¹ *
        (((2 ^ bits p : ℕ) : ENNReal) * ((2 ^ bits p : ℕ) : ENNReal)⁻¹) := by ac_rfl
       _ = _ := by rw [ENNReal.mul_inv_cancel nonzero (by simp), mul_one]

/-- Exact unbounded number of raw byte-chunk attempts. -/
theorem expected_attempts (p : ℕ) (valid : 1 < p) :
    RejectionSampling.totalExpectedAttempts (accepted p) = ((2 ^ bits p : ℕ) : ENNReal) / p := by
  rw [RejectionSampling.totalExpectedAttempts_eq, RejectionSampling.one_sub_reject]
  have hit : RejectionSampling.hit (accepted p) (fun _ => True) = (p : ENNReal) / (2 ^ bits p : ℕ) := by
    simpa only [Finset.filter_true, Finset.card_univ, Fintype.card_fin] using hit_fraction p valid (fun _ => True)
  rw [hit, div_eq_mul_inv]
  have nonzero : ((2 ^ bits p : ℕ) : ENNReal) ≠ 0 := by exact_mod_cast (by positivity : (2 ^ bits p : ℕ) ≠ 0)
  rw [ENNReal.mul_inv (Or.inr (ENNReal.inv_ne_top.mpr nonzero)) (Or.inl (by simp)), inv_inv]
  exact mul_comm _ _

theorem byteCount_positive (p : ℕ) (valid : 1 < p) : 0 < byteCount p := by
  have positive := bits_positive p valid
  have bound := fits p
  omega

/-- The configured u128 characteristic fits the fixed 16-byte scratch array. -/
theorem byteCount_le_sixteen (p : ℕ) (fitsWord : p < 2 ^ 128) : byteCount p ≤ 16 := by
  have sizeBound : bits p ≤ 128 := Nat.size_le.mpr (by omega)
  unfold byteCount
  omega

/-- The special full-width mask avoids the native out-of-width shift. -/
def nativeMask (p : ℕ) : ℕ := if bits p = 128 then 2 ^ 128 - 1 else 2 ^ bits p - 1

theorem nativeMask_eq (p : ℕ) : nativeMask p = 2 ^ bits p - 1 := by
  unfold nativeMask
  split_ifs with full
  · rw [full]
  · rfl

/-- Actual bytes read on success or suspension; raw discarded chunks remain
in the retained trace and each consumes the same configured byte width. -/
def consumedBytes (p : ℕ) (result : RejectionSampling.Result (Bytes (byteCount p))) : ℕ :=
  byteCount p * result.2.length

def expectedBytes (p fuel : ℕ) : ENNReal :=
  ∫⁻ value, value ∂𝒟[(fun result => (consumedBytes p result : ENNReal)) <$> runPrefix p fuel]

theorem expectedBytes_eq (p fuel : ℕ) :
    expectedBytes p fuel = (byteCount p : ENNReal) * RejectionSampling.expectedAttempts (accepted p) fuel := by
  rw [expectedBytes, runPrefix_eq, RejectionSampling.expectedAttempts]
  simp only [consumedBytes, Nat.cast_mul]
  let _ : MeasurableSpace (RejectionSampling.Result (Bytes (byteCount p))) := ⊤
  rw [lintegral_id_evalDist_map, lintegral_id_evalDist_map]
  exact lintegral_const_mul _ Measurable.of_discrete

def totalExpectedBytes (p : ℕ) : ENNReal := ⨆ fuel, expectedBytes p fuel

/-- Exact unbounded byte consumption of the raw-chunk rejection program. -/
theorem totalExpectedBytes_eq (p : ℕ) (valid : 1 < p) :
    totalExpectedBytes p = (byteCount p : ENNReal) * (((2 ^ bits p : ℕ) : ENNReal) / p) := by
  unfold totalExpectedBytes
  simp_rw [expectedBytes_eq]
  rw [← ENNReal.mul_iSup]
  exact congrArg ((byteCount p : ENNReal) * ·) (expected_attempts p valid)

theorem expected_attempts_lt_two (p : ℕ) (valid : 1 < p) :
    RejectionSampling.totalExpectedAttempts (accepted p) < 2 := by
  rw [expected_attempts p valid]
  have nonzero : (p : ENNReal) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  rw [ENNReal.div_lt_iff (Or.inl nonzero) (Or.inl (by simp))]
  exact_mod_cast range_lt_twice p valid

/-- Uniform public cost bound; it does not impose a maximum number of reads. -/
theorem totalExpectedBytes_lt_twice (p : ℕ) (valid : 1 < p) :
    totalExpectedBytes p < (byteCount p : ENNReal) * 2 := by
  rw [totalExpectedBytes_eq p valid, ← expected_attempts p valid]
  apply ENNReal.mul_lt_mul_right _ (by simp) (expected_attempts_lt_two p valid)
  exact_mod_cast (byteCount_positive p valid).ne'

/-- The all-zero raw chunk is accepted for each valid characteristic. -/
theorem accepted_nonempty (p : ℕ) (valid : 1 < p) : (accepted p).Nonempty := by
  refine ⟨fun _ => 0, ?_⟩
  have zeroWord : decode (fun _ : Fin (byteCount p) => (0 : Fin 256)) = 0 := by
    simp [decode_eq_sum]
  simp [accepted, masked, zeroWord, show 0 < p by omega]

theorem suspension_tends_to_zero (p : ℕ) (valid : 1 < p) :
    Filter.Tendsto (fun fuel => Pr{let result ← runPrefix p fuel}[result.1 = none]) Filter.atTop (nhds 0) :=
  by simpa only [runPrefix_eq] using RejectionSampling.suspension_tends_to_zero _ (accepted_nonempty p valid)

/-- The byte-cost limit is over all actual prefixes, not over an empirical
maximum or a fixed protocol budget. -/
theorem expectedBytes_tends_to_total (p : ℕ) :
    Filter.Tendsto (expectedBytes p) Filter.atTop (nhds (totalExpectedBytes p)) := by
  apply tendsto_atTop_iSup
  intro first second ordered
  rw [expectedBytes_eq, expectedBytes_eq]
  exact mul_le_mul_right (RejectionSampling.expectedAttempts_monotone (accepted p) ordered) _

/-- Prime-field residue transport; primality is needed only for the field
structure, not for uniformity of these canonical representatives. -/
theorem uniform_zmod (p : ℕ) (valid : 1 < p) [NeZero p] (event : ZMod p → Prop) :
    eventProbability p (fun value => event (value : ZMod p)) =
      Pr{let value ← $ᵗ (ZMod p)}[event value] := by
  have canonical : ∀ value : Fin p, (value.val : ZMod p) = (ZMod.finEquiv p) value := by
    intro value
    have val : ((ZMod.finEquiv p) value).val = value.val := by
      rcases p with _ | p
      · exact isEmptyElim value
      · rfl
    rw [← val, ZMod.natCast_zmod_val]
  rw [uniform_value p valid]
  refine (prEvent_congr _ _ (fun value => event ((ZMod.finEquiv p).toEquiv value)) ?_).trans
    (SampleableType.prEvent_uniformSample_equiv (ZMod.finEquiv p).toEquiv event)
  intro value
  change event (value.val : ZMod p) ↔ event ((ZMod.finEquiv p) value)
  rw [canonical]

/-- Convergence of the actual byte-retry value observations to the uniform
canonical law, with suspension excluded from successful observations. -/
theorem value_tends_to_uniform (p : ℕ) (valid : 1 < p) [NeZero p] (event : ℕ → Prop) :
    Filter.Tendsto (fun fuel => Pr{let result ← runPrefix p fuel}[
      result.1.elim False (fun raw => event (masked (bits p) raw))])
      Filter.atTop (nhds (Pr{let value ← $ᵗ (Fin p)}[event value.val])) := by
  rw [← uniform_value p valid, eventProbability_eq]
  simpa only [runPrefix_eq, RejectionSampling.eventProbability] using tendsto_atTop_iSup (RejectionSampling.success_monotone (accepted p)
    (fun raw => event (masked (bits p) raw)))

/-- Reference value of the native zero-initialized fixed scratch buffer,
including its full-width mask branch. -/
def nativeCandidate (p : ℕ) (fitsWord : p < 2 ^ 128) (raw : Bytes (byteCount p)) : ℕ :=
  decode (pad (byteCount_le_sixteen p fitsWord) raw) &&& nativeMask p

theorem nativeCandidate_eq (p : ℕ) (fitsWord : p < 2 ^ 128) (raw : Bytes (byteCount p)) :
    nativeCandidate p fitsWord raw = masked (bits p) raw := by
  rw [nativeCandidate, decode_pad, nativeMask_eq]
  rfl

/-- Each actually returned canonical word satisfies the native below-modulus
guard. Suspended prefixes cannot supply a typed field value. -/
theorem returned_canonical (p fuel : ℕ) (result : RejectionSampling.Result (Bytes (byteCount p)))
    (supported : result ∈ support (runPrefix p fuel)) (raw : Bytes (byteCount p))
    (returned : result.1 = some raw) : masked (bits p) raw < p := by
  rw [runPrefix_eq] at supported
  have member := RejectionSampling.returned_mem (accepted p) fuel result supported raw returned
  exact (Finset.mem_filter.mp member).2

end

end FormalProof4FHE.HasteBoots.CanonicalByteSampler
