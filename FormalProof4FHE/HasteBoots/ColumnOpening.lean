module

public import FormalProof4FHE.HasteBoots.ColumnSampling
public import FormalProof4FHE.HasteBoots.CommonSource
public import VCVio.OracleComp.Constructions.SampleableType.Measure

@[expose] public section

/-!
# Shared-column tests after responses have been fixed

The quota counts ordered draws with replacement. Several response checks may
use the SAME draw vector; no independence between these checks is required.
The adaptive bound permits responses to depend on the earlier challenge, but
samples columns only after those responses are fixed. Production XOF freshness
and authentication remain separate obligations.
-/

open ProbabilityTheory

namespace FormalProof4FHE.HasteBoots.ColumnOpening

variable {Position Symbol : Type} [Fintype Position] [DecidableEq Position]
  [DecidableEq Symbol]

/-- A response agrees with the available word at every ordered draw. -/
def Agrees (raw claimed : Position → Symbol) {queries : ℕ}
    (draw : Fin queries → Position) : Prop := ∀ i, raw (draw i) = claimed (draw i)

/-- The ordered quota determines the probability of missing delta bad columns. -/
noncomputable def missBound (Position : Type) [Fintype Position] (queries delta : ℕ) : ENNReal :=
  (((Fintype.card Position - delta : ℕ) : ENNReal) / Fintype.card Position) ^ queries

omit [Fintype Position] [DecidableEq Symbol] in
/-- Deduplicating the transmitted columns preserves the response-check event. -/
theorem agrees_dedup_iff (raw claimed : Position → Symbol) {queries : ℕ}
    (draw : Fin queries → Position) :
    (∀ pos ∈ (List.ofFn draw).dedup, raw pos = claimed pos) ↔ Agrees raw claimed draw := by
  simp only [List.mem_dedup, List.mem_ofFn, Agrees]
  constructor
  · intro checked i
    exact checked (draw i) ⟨i, rfl⟩
  · intro checked pos ⟨i, equal⟩
    rw [← equal]
    exact checked i

/-- Exact probability of avoiding all disagreements, including repeated draws. -/
theorem probability_eq (raw claimed : Position → Symbol) (queries : ℕ)
    [SampleableType (Fin queries → Position)] :
    Pr{let draw ← $ᵗ (Fin queries → Position)}[Agrees raw claimed draw] =
      (((Fintype.card Position - hammingDist raw claimed : ℕ) : ENNReal) /
        Fintype.card Position) ^ queries := by
  classical
  let good : Finset Position := Finset.univ.filter (fun pos => raw pos = claimed pos)
  have count : (Finset.univ.filter (Agrees raw claimed (queries := queries))).card =
      good.card ^ queries := by
    rw [← Fintype.card_subtype]
    calc _ = Fintype.card {draw : Fin queries → Position // ∀ i, draw i ∈ good} := by
          apply Fintype.card_congr
          exact Equiv.subtypeEquivRight (fun draw => by simp [Agrees, good])
         _ = good.card ^ queries := ColumnSampling.card_goodDraws good queries
  have goodCard : good.card = Fintype.card Position - hammingDist raw claimed := by
    have partition := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset Position)) (p := fun pos => raw pos = claimed pos)
    simp only [Finset.card_univ] at partition
    change good.card + hammingDist raw claimed = Fintype.card Position at partition
    omega
  rw [SampleableType.prEvent_uniformSample, count, goodCard, Fintype.card_fun]
  simp only [Fintype.card_fin, Nat.cast_pow, div_eq_mul_inv, ENNReal.inv_pow, mul_pow]

/-- Any established disagreement count gives a column-test bound. -/
theorem probability_le (raw claimed : Position → Symbol) (queries delta : ℕ)
    [SampleableType (Fin queries → Position)]
    (distance : delta ≤ hammingDist raw claimed) :
    Pr{let draw ← $ᵗ (Fin queries → Position)}[Agrees raw claimed draw] ≤
      (((Fintype.card Position - delta : ℕ) : ENNReal) /
        Fintype.card Position) ^ queries := by
  rw [probability_eq]
  apply pow_le_pow_left₀ zero_le
  exact ENNReal.div_le_div_right (by exact_mod_cast Nat.sub_le_sub_left distance _) _

/-- A false coded response to a nearby correct response must evade a fixed
distance-minus-radius set of columns. -/
theorem falseResponse_bound (C : Set (Position → Symbol)) (radius queries : ℕ)
    [SampleableType (Fin queries → Position)]
    (raw correct claimed : Position → Symbol) (correctC : correct ∈ C)
    (claimedC : claimed ∈ C) (different : correct ≠ claimed)
    (close : hammingDist raw correct ≤ radius) :
    Pr{let draw ← $ᵗ (Fin queries → Position)}[Agrees raw claimed draw] ≤
      (((Fintype.card Position - (Code.minDist C - radius) : ℕ) : ENNReal) /
        Fintype.card Position) ^ queries :=
  probability_le raw claimed queries _
    (CommonSource.falseResponse_distance C radius raw correct claimed
      correctC claimedC different close)

/-- Checking additional responses on the same columns cannot increase acceptance.
One disagreeing response suffices; there is no product of response probabilities. -/
theorem shared_bound {Test : Type} (raw claimed : Test → Position → Symbol)
    (queries delta : ℕ) [SampleableType (Fin queries → Position)]
    (witness : ∃ test, delta ≤ hammingDist (raw test) (claimed test)) :
    Pr{let draw ← $ᵗ (Fin queries → Position)}[
      ∀ test, Agrees (raw test) (claimed test) draw] ≤
      (((Fintype.card Position - delta : ℕ) : ENNReal) /
        Fintype.card Position) ^ queries := by
  obtain ⟨test, distance⟩ := witness
  exact (prEvent_mono _ _ _ (fun _ accepted => accepted test)).trans
    (probability_le (raw test) (claimed test) queries delta distance)

/-- Earlier challenges and arbitrary response choices may be correlated. Only
the later ordered column draws use a fresh uniform law. -/
theorem adaptive_shared_bound {Challenge Test : Type} (coins : ProbComp Challenge)
    (raw claimed : Challenge → Test → Position → Symbol)
    (bad : Challenge → Prop) (queries delta : ℕ)
    [SampleableType (Fin queries → Position)]
    (distance : ∀ challenge, ¬ bad challenge →
      ∃ test, delta ≤ hammingDist (raw challenge test) (claimed challenge test)) :
    Pr{let challenge ← coins; let draw ← $ᵗ (Fin queries → Position)}[
      ∀ test, Agrees (raw challenge test) (claimed challenge test) draw] ≤
      Pr{let challenge ← coins}[bad challenge] +
        (((Fintype.card Position - delta : ℕ) : ENNReal) /
          Fintype.card Position) ^ queries := by
  simpa only [prEvent_norm] using prEvent_bind_le_prEvent_add coins
    (fun challenge => do
      let draw ← $ᵗ (Fin queries → Position)
      pure (challenge, draw)) bad
    (fun pair => ∀ test, Agrees (raw pair.1 test) (claimed pair.1 test) pair.2)
    (fun challenge outside => by
      simpa only [prEvent_norm] using
        shared_bound (raw challenge) (claimed challenge) queries delta
          (distance challenge outside))

omit [DecidableEq Position] in
/-- Outside the proximity event, every coded claimed response disagrees on at
least radius+1 columns, even if it was chosen after the linear-test challenge. -/
theorem farResponse_distance (C : Set (Position → Symbol)) (radius : ℕ)
    (raw claimed : Position → Symbol) (member : claimed ∈ C)
    (far : (radius : ℕ∞) < Code.distFromCode raw C) :
    radius + 1 ≤ hammingDist raw claimed := by
  have lower := far.trans_le (Code.distFromCode_le_dist_to_mem raw claimed member)
  have strict : radius < hammingDist raw claimed := by exact_mod_cast lower
  omega

/-- A challenge-dependent coded response must either exploit the proximity event
or evade radius+1 bad columns using the later fresh draw vector. -/
theorem adaptive_far_bound {Challenge : Type} (coins : ProbComp Challenge)
    (C : Set (Position → Symbol)) (raw claimed : Challenge → Position → Symbol)
    (radius queries : ℕ) [SampleableType (Fin queries → Position)]
    (coded : ∀ challenge, claimed challenge ∈ C) :
    Pr{let challenge ← coins; let draw ← $ᵗ (Fin queries → Position)}[
      Agrees (raw challenge) (claimed challenge) draw] ≤
      Pr{let challenge ← coins}[Code.distFromCode (raw challenge) C ≤ radius] +
        (((Fintype.card Position - (radius + 1) : ℕ) : ENNReal) /
          Fintype.card Position) ^ queries := by
  have bound := adaptive_shared_bound coins
    (fun challenge (_ : Unit) => raw challenge)
    (fun challenge (_ : Unit) => claimed challenge)
    (fun challenge => Code.distFromCode (raw challenge) C ≤ radius)
    queries (radius + 1) (fun challenge outside =>
      ⟨(), farResponse_distance C radius _ _ (coded challenge) (lt_of_not_ge outside)⟩)
  simpa only [forall_const] using bound

end FormalProof4FHE.HasteBoots.ColumnOpening
