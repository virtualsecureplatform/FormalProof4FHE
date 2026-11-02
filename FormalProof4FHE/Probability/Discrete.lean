/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import VCVio.CryptoFoundations.HardnessAssumptions.NoisyLearning
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import VCVio.OracleComp.EvalDist.Sum
import FormalProof4FHE.Probability.PMFTotalVariation
import ToMathlib.MeasureTheory.Measure.Coupling.Maximal
import VCVio.EvalDist.MeasureTVDist.Event
import VCVio.EvalDist.Monad.UniformTable
import VCVio.EvalDist.EvalDistEq
import VCVio.EvalDist.ProbabilityBounds
import VCVio.EvalDist.MeasureTVDist.Bind
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.Constructions.UniformSelectMeasure

/-!
# Discrete probability interfaces

The finite cryptographic games use discrete observations. Their scalar probabilities and real
advantages are obtained from VCVio's measure semantics.
-/

open MeasureTheory OracleComp
open scoped ENNReal

namespace FormalProof4FHE

scoped instance (priority := 2000) instDiscreteObservation (α : Type) : MeasurableSpace α := ⊤

end FormalProof4FHE

open scoped FormalProof4FHE

namespace ProbComp

noncomputable def uniformPMF (n : ℕ) : PMF (Fin (n + 1)) :=
  PMF.ofFintype (α := Fin (n + 1)) (fun _ ↦ (n + 1 : ℝ≥0∞)⁻¹) (by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    exact ENNReal.mul_inv_cancel (by positivity) (by simp))

noncomputable def outputPMF {α : Type} (mx : ProbComp α) : PMF α :=
  simulateQ uniformPMF mx

@[simp] theorem outputPMF_pure {α : Type} (x : α) :
    outputPMF (pure x : ProbComp α) = pure x := rfl

@[simp] theorem outputPMF_bind {α β : Type} (mx : ProbComp α) (f : α → ProbComp β) :
    outputPMF (mx >>= f) = (outputPMF mx).bind (fun x ↦ outputPMF (f x)) :=
  simulateQ_bind _ _ _

@[simp] theorem outputPMF_query (n : ℕ) :
    outputPMF (unifSpec.query n : ProbComp (Fin (n + 1))) = uniformPMF n := by
  exact simulateQ_HasQuery_query uniformPMF n

theorem evalDist_eq_outputPMF_toMeasure {α : Type} (mx : ProbComp α) :
    𝒟[mx] = mx.outputPMF.toMeasure := by
  induction mx using OracleComp.inductionOn with
  | pure x =>
      change Measure.dirac x = (PMF.pure x).toMeasure
      exact (PMF.toMeasure_pure x).symm
  | query_bind t k ih =>
      rw [outputPMF_bind, evalDist_bind_of_discrete]
      ext s hs
      let : MeasurableSpace (Measure α) := Measure.instMeasurableSpace
      rw [Measure.bind_apply hs (by exact Measurable.of_discrete.aemeasurable),
        PMF.toMeasure_bind_apply _ _ _ hs, lintegral_countable']
      simp only [outputPMF_query, uniformPMF, PMF.ofFintype_apply, ← ih]
      simp [mul_comm, ProbabilityTheory.uniformOn_univ_apply_singleton]

end ProbComp

noncomputable instance : EvalDistSemantics PMF where
  denote := fun {_} _ p ↦ p.toMeasure
  apply_univ_le_one p := by simp

universe vDiscrete

noncomputable def probOutput {m : Type → Type vDiscrete} [Monad m] [EvalDistSemantics m]
    {α : Type} (mx : m α) (x : α) : ℝ≥0∞ :=
  Pr{let y ← mx}[y = x]

noncomputable def probEvent {m : Type → Type vDiscrete} [Monad m] [EvalDistSemantics m]
    {α : Type} (mx : m α) (p : α → Prop) : ℝ≥0∞ :=
  Pr{let x ← mx}[p x]

noncomputable abbrev probFailure {α : Type} (mx : ProbComp α) : ℝ≥0∞ := prFail mx

syntax "Pr[=" term "|" term "]" : term
syntax "Pr[⊥" "|" term "]" : term
syntax "Pr[" term "|" term "]" : term
macro_rules
  | `(Pr[= $x | $mx]) => `(probOutput $mx $x)
  | `(Pr[⊥ | $mx]) => `(probFailure $mx)
  | `(Pr[ $p | $mx]) => `(probEvent $mx $p)

@[simp] theorem probOutput_le_one {α : Type} {mx : ProbComp α} {x : α} :
    probOutput mx x ≤ 1 := prEvent_le_one _

theorem probOutput_ne_top {α : Type} {mx : ProbComp α} {x : α} :
    probOutput mx x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top probOutput_le_one

@[simp] theorem probEvent_le_one {α : Type} {mx : ProbComp α} {p : α → Prop} :
    probEvent mx p ≤ 1 := prEvent_le_one _

theorem probEvent_ne_top {α : Type} {mx : ProbComp α} {p : α → Prop} :
    probEvent mx p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top probEvent_le_one

@[simp] theorem probFailure_eq_zero {α : Type} (mx : ProbComp α) : probFailure mx = 0 := by
  simp [probFailure, prFail]

namespace ProbComp

noncomputable def boolDistAdvantage (mx my : ProbComp Bool) : ℝ :=
  |(probOutput mx true).toReal - (probOutput my true).toReal|

theorem boolDistAdvantage_eq_measure (mx my : ProbComp Bool) :
    mx.boolDistAdvantage my = (𝒟[mx].boolDist 𝒟[my]).toReal := by
  simp [boolDistAdvantage, Measure.toReal_boolDist, probOutput,
    prEvent_eq_evalDist_singleton]

theorem boolDistAdvantage_triangle (mx my mz : ProbComp Bool) :
    mx.boolDistAdvantage mz ≤ mx.boolDistAdvantage my + my.boolDistAdvantage mz :=
  abs_sub_le _ _ _

end ProbComp

noncomputable abbrev tvDist {α : Type} (mx my : ProbComp α) : ℝ := (𝒟[mx]).tvDist 𝒟[my]
noncomputable abbrev etvDist {α : Type} (mx my : ProbComp α) : ℝ≥0∞ := (𝒟[mx]).etvDist 𝒟[my]

theorem tvDist_nonneg {α : Type} (mx my : ProbComp α) : 0 ≤ tvDist mx my :=
  measureTVDist_nonneg mx my

@[simp] theorem tvDist_self {α : Type} (mx : ProbComp α) : tvDist mx mx = 0 :=
  measureTVDist_self mx

theorem tvDist_comm {α : Type} (mx my : ProbComp α) : tvDist mx my = tvDist my mx :=
  measureTVDist_comm mx my

theorem tvDist_triangle {α : Type} (mx my mz : ProbComp α) :
    tvDist mx mz ≤ tvDist mx my + tvDist my mz := measureTVDist_triangle mx my mz

theorem tvDist_le_one {α : Type} (mx my : ProbComp α) : tvDist mx my ≤ 1 :=
  measureTVDist_le_one mx my

namespace FormalProof4FHE

theorem evalDist_bind_congr' {α β : Type} (mx : ProbComp α) {ob₁ ob₂ : α → ProbComp β}
    (h : ∀ x, 𝒟[ob₁ x] = 𝒟[ob₂ x]) : 𝒟[mx >>= ob₁] = 𝒟[mx >>= ob₂] :=
  _root_.evalDist_bind_congr mx ob₁ ob₂ h

theorem evalDist_bind {α β : Type} (mx : ProbComp α) (f : α → ProbComp β) :
    𝒟[mx >>= f] = Measure.bind 𝒟[mx] (fun x ↦ 𝒟[f x]) :=
  evalDist_bind_of_discrete mx f

theorem evalDist_map {α β : Type} (mx : ProbComp α) (f : α → β) :
    𝒟[f <$> mx] = 𝒟[mx].map f := evalDist_map_of_discrete mx f

end FormalProof4FHE

theorem probOutput_def {α : Type} (mx : ProbComp α) (x : α) :
    probOutput mx x = 𝒟[mx] {x} := prEvent_eq_evalDist_singleton mx x

theorem probOutput_congr {α : Type} {mx my : ProbComp α} {x y : α}
    (hxy : x = y) (h : 𝒟[mx] = 𝒟[my]) : probOutput mx x = probOutput my y := by
  simp only [probOutput_def, hxy, h]

theorem evalDist_ext_iff {α : Type} {mx my : ProbComp α} :
    𝒟[mx] = 𝒟[my] ↔ ∀ x, probOutput mx x = probOutput my x := by
  constructor
  · intro h x
    exact probOutput_congr rfl h
  · intro h
    exact (OracleComp.evalDistEq_of_forall_prEvent_eq_output h).evalDist_eq

theorem evalDist_ext {α : Type} {mx my : ProbComp α}
    (h : ∀ x, probOutput mx x = probOutput my x) : 𝒟[mx] = 𝒟[my] :=
  evalDist_ext_iff.mpr h

@[simp] theorem probOutput_pure {α : Type} [DecidableEq α] (x y : α) :
    probOutput (pure y : ProbComp α) x = if x = y then 1 else 0 := by
  simp [probOutput, eq_comm]

@[simp] theorem probOutput_pure_self {α : Type} (x : α) :
    probOutput (pure x : ProbComp α) x = 1 := by simp [probOutput]

@[simp] theorem probOutput_uniformSample (α : Type) [Fintype α] [SampleableType α] (x : α) :
    probOutput ($ᵗ α) x = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  rw [probOutput_def, SampleableType.evalDist_uniformSample_singleton]

theorem probOutput_bind_eq_tsum {α β : Type}
    (mx : ProbComp α) (f : α → ProbComp β) (y : β) :
    probOutput (mx >>= f) y = ∑' x, probOutput mx x * probOutput (f x) y :=
  OracleComp.prEvent_bind_eq_tsum mx f (· = y)

theorem probOutput_bind_eq_sum_fintype {α β : Type} [Fintype α]
    (mx : ProbComp α) (f : α → ProbComp β) (y : β) :
    probOutput (mx >>= f) y = ∑ x, probOutput mx x * probOutput (f x) y := by
  rw [probOutput_bind_eq_tsum, tsum_fintype]

theorem probOutput_map_injective {α β : Type} (mx : ProbComp α) {f : α → β}
    (hf : Function.Injective f) (x : α) :
    probOutput (f <$> mx) (f x) = probOutput mx x := prEvent_map_injective mx hf x

theorem probOutput_map_equiv {α β : Type} (mx : ProbComp α) (e : α ≃ β) (y : β) :
    probOutput (e <$> mx) y = probOutput mx (e.symm y) := by
  simpa only [e.apply_symm_apply] using probOutput_map_injective mx e.injective (e.symm y)

theorem probOutput_map_eq_sum_fintype_ite {α β : Type} [Fintype α] [DecidableEq β]
    (mx : ProbComp α) (f : α → β) (y : β) :
    probOutput (f <$> mx) y = ∑ x, if y = f x then probOutput mx x else 0 := by
  rw [map_eq_bind_pure_comp, probOutput_bind_eq_sum_fintype]
  simp only [Function.comp_apply, probOutput_pure]
  simp [mul_ite]

theorem sum_probOutput_eq_one {α : Type} [Fintype α] {mx : ProbComp α}
    (_h : probFailure mx = 0) : ∑ x, probOutput mx x = 1 := by
  simp [probOutput_def]

theorem tsum_probOutput_of_liftM_PMF {α : Type} (mx : ProbComp α) :
    ∑' x, probOutput mx x = 1 :=
  OracleComp.tsum_prEvent_eq_one mx


namespace LearningWithErrors

noncomputable def realAdvantage {Sample Secret Output : Type} [Add Output]
    (problem : NoisyLearning.Problem Sample Secret Output) (adversary : NoisyLearning.Adversary problem) :
    ℝ := (NoisyLearning.advantage problem adversary).toReal

end LearningWithErrors

theorem probEvent_bind_eq_tsum {α β : Type} (mx : ProbComp α)
    (f : α → ProbComp β) (p : β → Prop) :
    probEvent (mx >>= f) p = ∑' x, probOutput mx x * probEvent (f x) p :=
  OracleComp.prEvent_bind_eq_tsum (spec := unifSpec) mx f p
theorem probEvent_eq_tsum_ite {α : Type} (mx : ProbComp α) (p : α → Prop) [DecidablePred p] :
    probEvent mx p = ∑' x, if p x then probOutput mx x else 0 :=
  OracleComp.prEvent_eq_tsum_ite (spec := unifSpec) mx p
theorem tsum_probOutput_bind_mul {α β : Type} (mx : ProbComp α) (g : α → ProbComp β)
    (f : β → ℝ≥0∞) :
    ∑' z, probOutput (mx >>= g) z * f z =
      ∑' x, probOutput mx x * ∑' z, probOutput (g x) z * f z :=
  OracleComp.tsum_prEvent_bind_mul (spec := unifSpec) mx g f
theorem tsum_probOutput_map_mul {α β : Type} (mx : ProbComp α) (g : α → β)
    (f : β → ℝ≥0∞) : ∑' z, probOutput (g <$> mx) z * f z =
      ∑' x, probOutput mx x * f (g x) :=
  OracleComp.tsum_prEvent_map_mul (spec := unifSpec) mx g f
theorem tsum_probOutput_pure_mul {α : Type} (x : α) (f : α → ℝ≥0∞) :
    ∑' z, probOutput (pure x : ProbComp α) z * f z = f x :=
  OracleComp.tsum_prEvent_pure_mul (spec := unifSpec) x f
theorem tsum_probOutput_le_one {α : Type} {mx : ProbComp α} :
    ∑' x, probOutput mx x ≤ 1 := OracleComp.tsum_prEvent_le_one mx

theorem tvDist_map_le {α β : Type} (f : α → β) (mx my : ProbComp α) :
    tvDist (f <$> mx) (f <$> my) ≤ tvDist mx my :=
  measureTVDist_map_le mx my f Measurable.of_discrete

theorem tvDist_bind_right_le {α β : Type} (f : α → ProbComp β) (mx my : ProbComp α) :
    tvDist (mx >>= f) (my >>= f) ≤ tvDist mx my :=
  OracleComp.measureTVDist_bind_right_le mx my f

theorem tvDist_bind_left_le {α β : Type} (mx : ProbComp α) (f g : α → ProbComp β) :
    tvDist (mx >>= f) (mx >>= g) ≤ ∑' a, (probOutput mx a).toReal * tvDist (f a) (g a) :=
  OracleComp.measureTVDist_bind_left_le_tsum mx f g

theorem tvDist_bind_left_le_const' {α β : Type} (mx : ProbComp α)
    (f g : α → ProbComp β) (c : ℝ) (h : ∀ a, tvDist (f a) (g a) ≤ c) :
    tvDist (mx >>= f) (mx >>= g) ≤ c := by
  obtain ⟨a, _⟩ := OracleComp.support_nonempty mx
  exact OracleComp.measureTVDist_bind_left_le_of_forall_le mx f g
    ((tvDist_nonneg _ _).trans (h a)) h

@[simp] theorem probOutput_bind_const {α β : Type} (mx : ProbComp α) (my : ProbComp β) (y : β) :
    probOutput (mx >>= fun _ ↦ my) y = probOutput my y := by
  rw [probOutput_def, probOutput_def, OracleComp.evalDist_bind_const]

theorem evalDist_map_bijective_uniform_cross (α : Type) {β : Type}
    [SampleableType α] [SampleableType β] (f : α → β) (hf : Function.Bijective f) :
    𝒟[f <$> ($ᵗ α)] = 𝒟[$ᵗ β] :=
  (SampleableType.map_uniformSample_evalDistEq_of_bijective hf).evalDist_eq

theorem probOutput_eq_zero_of_not_mem_support {α : Type} {mx : ProbComp α} {x : α}
    (hx : x ∉ support mx) : probOutput mx x = 0 :=
  prEvent_eq_zero_of_not_mem_support mx hx

theorem probOutput_eq_outputPMF {α : Type} (mx : ProbComp α) (x : α) :
    probOutput mx x = mx.outputPMF x := by
  rw [probOutput_def, ProbComp.evalDist_eq_outputPMF_toMeasure,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]

theorem etvDist_eq_half_tsum_probOutput_absDiff {α : Type} (mx my : ProbComp α) :
    etvDist mx my = (∑' x, ENNReal.absDiff (probOutput mx x) (probOutput my x)) / 2 := by
  classical
  let T : Finset α := ((OracleComp.support_finite mx).union
    (OracleComp.support_finite my)).toFinset
  have hm : ∀ oz : ProbComp α, support oz ⊆ (T : Set α) → 𝒟[oz] (↑T)ᶜ = 0 := by
    intro oz h
    have hp := (OracleComp.prEvent_eq_zero_iff oz (· ∈ (↑T : Set α)ᶜ)).2
      (fun x hx hn ↦ hn (h hx))
    simpa only [prEvent_eq_evalDist_of_discrete, Set.ofPred_mem_eq] using hp
  have hx : 𝒟[mx] (↑T)ᶜ = 0 := hm mx fun x h ↦ by simp [T, h]
  have hy : 𝒟[my] (↑T)ᶜ = 0 := hm my fun x h ↦ by simp [T, h]
  rw [tsum_eq_sum (s := T) (fun x h ↦ ?_)]
  · simp only [probOutput_def, ENNReal.absDiff, Finset.sum_add_distrib]
    rw [Measure.sum_tsub_comm hx hy, ← two_mul, mul_comm,
      ENNReal.mul_div_cancel_right (by norm_num) (by simp)]
    exact Measure.etvDist_eq_sum_tsub hx hy
  · have hx' : x ∉ support mx := fun hh ↦ h (by simp [T, hh])
    have hy' : x ∉ support my := fun hh ↦ h (by simp [T, hh])
    simp [probOutput_eq_zero_of_not_mem_support hx', probOutput_eq_zero_of_not_mem_support hy']

theorem tvDist_eq_outputPMF {α : Type} (mx my : ProbComp α) :
    tvDist mx my = PMF.tvDist mx.outputPMF my.outputPMF := by
  unfold tvDist Measure.tvDist PMF.tvDist
  congr 1
  rw [show (𝒟[mx]).etvDist 𝒟[my] = etvDist mx my from rfl,
    etvDist_eq_half_tsum_probOutput_absDiff, PMF.etvDist]
  simp only [probOutput_eq_outputPMF]

namespace ProbComp

noncomputable instance : MonadLift ProbComp PMF where
  monadLift := outputPMF

instance : LawfulMonadLiftT ProbComp PMF where
  monadLift_pure _ := rfl
  monadLift_bind := outputPMF_bind

@[simp] theorem outputPMF_map {α β : Type} (mx : ProbComp α) (f : α → β) :
    outputPMF (f <$> mx) = f <$> outputPMF mx := simulateQ_map _ _ _

end ProbComp

namespace ProbComp

theorem probOutput_uniformSelectListVector {α : Type} [DecidableEq α] {n : ℕ}
    (xs : List.Vector α (n + 1)) (x : α) :
    probOutput ($! xs) x = (xs.toList.count x : ℝ≥0∞) / (n + 1) := by
  have h : (fun a : α ↦ decide (a = x)) = (fun a ↦ a == x) := by
    funext a
    apply Bool.eq_iff_iff.mpr
    simp
  simpa only [probOutput, List.count, h] using prEvent_uniformSelectListVector xs (· = x)

end ProbComp

theorem probOutput_map {α β : Type} (mx : ProbComp α) (f : α → β) (y : β) :
    probOutput (f <$> mx) y = probEvent mx (fun x ↦ f x = y) := by
  exact prEvent_map mx f (· = y)

namespace FormalProof4FHE

theorem evalDist_map_eq_of_evalDist_eq {α β : Type} {mx my : ProbComp α}
    (h : 𝒟[mx] = 𝒟[my]) (f : α → β) : 𝒟[f <$> mx] = 𝒟[f <$> my] := by
  rw [evalDist_map, evalDist_map, h]

theorem evalDist_uniformSample_bind_update {D R : Type} [Finite D] [DecidableEq D]
    [Finite R] [Nonempty R] [SampleableType R] [SampleableType (D → R)] (t : D) :
    𝒟[do let u ← $ᵗ R; let g ← $ᵗ (D → R); pure (Function.update g t u)] =
      𝒟[$ᵗ (D → R)] := by
  simpa using evalDist_bind_bind_update_map ($ᵗ R) ($ᵗ (D → R))
    SampleableType.evalDist_uniformSample
    (@SampleableType.evalDist_uniformSample (D → R) _ MeasurableSpace.pi _)
    t id

end FormalProof4FHE

@[simp] theorem probOutput_pair_map {α β : Type} (mx : ProbComp α) (my : ProbComp β)
    (z : α × β) :
    probOutput (mx >>= fun x ↦ Prod.mk x <$> my) z =
      probOutput mx z.1 * probOutput my z.2 := by
  classical
  rcases z with ⟨a, b⟩
  rw [probOutput_eq_outputPMF, ProbComp.outputPMF_bind]
  simp only [PMF.bind_apply, ProbComp.outputPMF_map, PMF.monad_map_eq_map,
    PMF.map_apply, Prod.mk.injEq]
  simp only [ite_and]
  have inner (x : α) :
      (∑' y : β, if a = x then if b = y then my.outputPMF y else 0 else 0) =
        if a = x then my.outputPMF b else 0 := by
    by_cases h : a = x <;> simp [h]
  simp only [inner]
  simp [mul_ite, probOutput_eq_outputPMF]

@[simp] theorem probOutput_pair {α β : Type} (mx : ProbComp α) (my : ProbComp β)
    (z : α × β) :
    probOutput (do let x ← mx; let y ← my; pure (x, y)) z =
      probOutput mx z.1 * probOutput my z.2 := by
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using probOutput_pair_map mx my z

theorem probEvent_map {α β : Type} (mx : ProbComp α) (f : α → β) (p : β → Prop) :
    probEvent (f <$> mx) p = probEvent mx (fun x ↦ p (f x)) :=
  prEvent_map mx f p

theorem probOutput_bind_bind_swap {α β γ : Type} (mx : ProbComp α) (my : ProbComp β)
    (f : α → β → ProbComp γ) (z : γ) :
    probOutput (mx >>= fun a ↦ my >>= fun b ↦ f a b) z =
      probOutput (my >>= fun b ↦ mx >>= fun a ↦ f a b) z :=
  probOutput_congr rfl (OracleComp.evalDist_bind_bind_swap_of_uniform mx my f)

namespace ProbComp

theorem probOutput_true_le_add_ofReal_boolDistAdvantage (mx my : ProbComp Bool) :
    probOutput mx true ≤ probOutput my true + ENNReal.ofReal (mx.boolDistAdvantage my) := by
  apply (ENNReal.toReal_le_toReal probOutput_ne_top
    (ENNReal.add_ne_top.mpr ⟨probOutput_ne_top, ENNReal.ofReal_ne_top⟩)).mp
  rw [ENNReal.toReal_add probOutput_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by exact abs_nonneg _)]
  exact le_add_of_sub_left_le (le_abs_self _)

end ProbComp

theorem probEvent_eq_one_iff {α : Type} {mx : ProbComp α} {p : α → Prop} :
    probEvent mx p = 1 ↔ probFailure mx = 0 ∧ ∀ x ∈ support mx, p x := by
  simp only [probFailure_eq_zero, true_and]
  exact OracleComp.prEvent_eq_one_iff (spec := unifSpec) mx p

theorem probEvent_eq_zero_iff {α : Type} {mx : ProbComp α} {p : α → Prop} :
    probEvent mx p = 0 ↔ ∀ x ∈ support mx, ¬p x :=
  OracleComp.prEvent_eq_zero_iff (spec := unifSpec) mx p

theorem probOutput_bind_of_const {α β : Type} (mx : ProbComp α)
    {f : α → ProbComp β} {y : β} {r : ℝ≥0∞}
    (h : ∀ x ∈ support mx, probOutput (f x) y = r) :
    probOutput (mx >>= f) y = (1 - probFailure mx) * r := by
  rw [probOutput_bind_eq_tsum]
  simpa only [probOutput, probFailure_eq_zero, tsub_zero, one_mul] using
    OracleComp.tsum_prEvent_mul_of_const_on_support (spec := unifSpec) mx h

/-- A finite uniform oracle program has full successful-output mass. -/
class NeverFail {α : Type} (mx : ProbComp α) : Prop where
  probFailure_eq_zero : probFailure mx = 0

instance {α : Type} (mx : ProbComp α) : NeverFail mx := ⟨by simp⟩

namespace NeverFail

theorem of_probFailure_eq_zero {α : Type} (mx : ProbComp α) (h : probFailure mx = 0) :
    NeverFail mx := ⟨h⟩

theorem bind_of_forall {α β : Type} {mx : ProbComp α} {my : α → ProbComp β}
    [_hx : NeverFail mx] [_hy : ∀ x, NeverFail (my x)] : NeverFail (mx >>= my) :=
  inferInstance

end NeverFail

theorem probOutput_bind_congr' {α β : Type} (mx : ProbComp α)
    {f g : α → ProbComp β} (y : β) (h : ∀ x, probOutput (f x) y = probOutput (g x) y) :
    probOutput (mx >>= f) y = probOutput (mx >>= g) y := by
  simp only [probOutput_bind_eq_tsum, h]

theorem abs_probOutput_toReal_sub_le_tvDist (mx my : ProbComp Bool) :
    |(probOutput mx true).toReal - (probOutput my true).toReal| ≤ tvDist mx my :=
  abs_prEvent_toReal_sub_le_measureTVDist mx my (· = true) Measurable.of_discrete

namespace FormalProof4FHE

theorem evalDist_bind_bind_swap {α β γ : Type} (mx : ProbComp α) (my : ProbComp β)
    (f : α → β → ProbComp γ) :
    𝒟[mx >>= fun a ↦ my >>= fun b ↦ f a b] =
      𝒟[my >>= fun b ↦ mx >>= fun a ↦ f a b] :=
  OracleComp.evalDist_bind_bind_swap_of_uniform mx my f

theorem evalDist_bind_bijective_uniform_cross {α β γ : Type}
    [SampleableType α] [SampleableType β] (f : α → β) (hf : Function.Bijective f)
    (g : β → ProbComp γ) :
    𝒟[($ᵗ α) >>= fun x ↦ g (f x)] = 𝒟[($ᵗ β) >>= g] := by
  have h := ((SampleableType.map_uniformSample_evalDistEq_of_bijective hf).bind_left g).evalDist_eq
  simpa only [bind_map_left] using h

end FormalProof4FHE

theorem probOutput_bind_bijective_uniform_cross (α : Type) {β γ : Type}
    [SampleableType α] [SampleableType β] (f : α → β) (hf : Function.Bijective f)
    (g : β → ProbComp γ) (z : γ) :
    probOutput (($ᵗ α) >>= fun x ↦ g (f x)) z = probOutput (($ᵗ β) >>= g) z :=
  probOutput_congr rfl (FormalProof4FHE.evalDist_bind_bijective_uniform_cross f hf g)

theorem evalDist_add_right_uniform {α : Type} [AddGroup α] [SampleableType α] (shift : α) :
    𝒟[(fun x ↦ x + shift) <$> ($ᵗ α)] = 𝒟[$ᵗ α] :=
  evalDist_map_bijective_uniform_cross α _ (AddGroup.addRight_bijective shift)

namespace ProbComp

noncomputable def boolBiasAdvantage (mx : ProbComp Bool) : ℝ :=
  2 * |(probOutput mx true).toReal - 1 / 2|

theorem boolBiasAdvantage_eq_two_mul_abs_sub_half (mx : ProbComp Bool) :
    mx.boolBiasAdvantage = 2 * |(probOutput mx true).toReal - 1 / 2| := rfl

theorem boolBiasAdvantage_eq_measure (mx : ProbComp Bool) :
    mx.boolBiasAdvantage = 𝒟[mx].boolBias.toReal := by
  rw [Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure,
    ENNReal.toReal_mul, ENNReal.absDiff_toReal (measure_ne_top _ _) (by norm_num)]
  norm_num [boolBiasAdvantage, probOutput_def]

end ProbComp

theorem tsum_probOutput_eq_one' {α : Type} {mx : ProbComp α} (_h : probFailure mx = 0) :
    ∑' x, probOutput mx x = 1 := tsum_probOutput_of_liftM_PMF mx

theorem probEvent_uniformSample {α : Type} [Fintype α] [SampleableType α]
    (p : α → Prop) [DecidablePred p] :
    probEvent ($ᵗ α) p = (Finset.univ.filter p).card / (Fintype.card α : ℝ≥0∞) :=
  SampleableType.prEvent_uniformSample p

theorem probFailure_map {α β : Type} (mx : ProbComp α) (f : α → β) :
    probFailure (f <$> mx) = probFailure mx := by simp

theorem probOutput_fst_map_eq_sum {α β : Type} [Fintype β] (mx : ProbComp (α × β)) (x : α) :
    probOutput (Prod.fst <$> mx) x = ∑ y, probOutput mx (x, y) := by
  classical
  rw [probOutput_eq_outputPMF, ProbComp.outputPMF_map, PMF.monad_map_eq_map,
    PMF.map_apply, ENNReal.tsum_prod', ENNReal.tsum_comm]
  simp [probOutput_eq_outputPMF]

theorem mem_support_iff {α : Type} (mx : ProbComp α) (x : α) :
    x ∈ support mx ↔ probOutput mx x ≠ 0 :=
  OracleComp.mem_support_iff_prEvent_ne_zero mx x

@[simp] theorem probOutput_uniformFin (n : ℕ) (x : Fin (n + 1)) :
    probOutput ($[0..n]) x = (n + 1 : ℝ≥0∞)⁻¹ := by
  rw [probOutput_def, ProbComp.evalDist_uniformFin,
    ProbabilityTheory.uniformOn_univ_apply_singleton]
  simp

theorem probOutput_bind_uniformBool {α : Type} (f : Bool → ProbComp α) (x : α) :
    probOutput (($ᵗ Bool) >>= f) x = (probOutput (f true) x + probOutput (f false) x) / 2 := by
  rw [probOutput_bind_eq_tsum, tsum_fintype (L := .unconditional _), Fintype.sum_bool]
  simp only [probOutput_uniformSample, Fintype.card_bool, Nat.cast_ofNat, add_comm, div_eq_mul_inv]
  rw [← left_distrib, mul_comm]

theorem probOutput_false_eq_sub (mx : ProbComp Bool) :
    probOutput mx false = 1 - probFailure mx - probOutput mx true := by
  have h : probOutput mx false + probOutput mx true = 1 := by
    simpa only [probOutput_def, add_comm] using Measure.apply_true_add_apply_false_eq_one 𝒟[mx]
  rw [probFailure_eq_zero, tsub_zero, ← h, ENNReal.add_sub_cancel_right probOutput_ne_top]

@[simp] theorem probOutput_not_map (mx : ProbComp Bool) (b : Bool) :
    probOutput ((! ·) <$> mx) b = probOutput mx (!b) := by
  simpa only [Bool.not_not] using probOutput_map_injective mx Bool.not_injective (!b)

theorem probEvent_congr' {α : Type} {mx my : ProbComp α} {p q : α → Prop}
    (h1 : ∀ x ∈ support mx, p x ↔ q x) (h2 : 𝒟[mx] = 𝒟[my]) :
    probEvent mx p = probEvent my q :=
  (prEvent_congr_of_support mx p q h1).trans ((EvalDistEq.of_evalDist_eq h2).prEvent_eq q)

theorem probEvent_mono {α : Type} {mx : ProbComp α} {p q : α → Prop}
    (h : ∀ x ∈ support mx, p x → q x) : probEvent mx p ≤ probEvent mx q :=
  prEvent_mono_of_support mx p q h

theorem evalDist_uniformSample_map_comp_injective {A B R : Type} [Finite A] [Finite B]
    [Finite R] [Nonempty R] [SampleableType R] [SampleableType (A → R)]
    [SampleableType (B → R)] {e : A → B} (he : Function.Injective e) :
    𝒟[do let g ← $ᵗ (B → R); pure (g ∘ e)] = 𝒟[$ᵗ (A → R)] := by
  have h := evalDist_map_table_comp_injective ($ᵗ (A → R)) ($ᵗ (B → R))
    (@SampleableType.evalDist_uniformSample (A → R) _ MeasurableSpace.pi _)
    (@SampleableType.evalDist_uniformSample (B → R) _ MeasurableSpace.pi _) he
  have hd := EvalDistEq.of_evalDist_eq h
  simpa only [bind_pure_comp] using hd.evalDist_eq

theorem evalDist_map_fst_uniformSample_prod {α β : Type} [SampleableType α]
    [SampleableType β] [SampleableType (α × β)] :
    𝒟[Prod.fst <$> ($ᵗ (α × β))] = 𝒟[$ᵗ α] := by
  have h : Prod.fst <$> ($ᵗ (α × β)) =ᵈ ($ᵗ α) := fun p ↦ by
    rw [prEvent_map]
    exact (SampleableType.prEvent_uniformSample_inst_irrel
      (inferInstance : SampleableType (α × β)) (instSampleableTypeProd α β)
      (fun z ↦ p z.1)).trans (SampleableType.prEvent_uniformSample_fst (β := β) p)
  exact h.evalDist_eq

@[simp] theorem probOutput_prod_mk_map {α β : Type} [DecidableEq α] (mx : ProbComp β) (a : α) (z : α × β) :
    probOutput (Prod.mk a <$> mx) z = if z.1 = a then probOutput mx z.2 else 0 := by
  classical
  rcases z with ⟨x, y⟩
  rw [probOutput_eq_outputPMF, ProbComp.outputPMF_map, PMF.monad_map_eq_map, PMF.map_apply]
  simp only [Prod.mk.injEq]
  by_cases hx : x = a
  · simp [hx, probOutput_eq_outputPMF]
  · simp [hx]

theorem probEvent_eq_eq_probOutput {α : Type} (mx : ProbComp α) (x : α) :
    probEvent mx (· = x) = probOutput mx x := rfl

theorem probEvent_mono'' {α : Type} {mx : ProbComp α} {p q : α → Prop}
    (h : ∀ x, p x → q x) : probEvent mx p ≤ probEvent mx q :=
  probEvent_mono fun x _ ↦ h x

@[simp] theorem probEvent_true {α : Type} (mx : ProbComp α) :
    probEvent mx (fun _ ↦ True) = 1 := by simp [probEvent]

@[simp] theorem probEvent_false {α : Type} (mx : ProbComp α) :
    probEvent mx (fun _ ↦ False) = 0 := by simp [probEvent]

@[simp] theorem probOutput_map_const {α β : Type} [DecidableEq β] (mx : ProbComp α) (a b : β) :
    probOutput ((fun _ ↦ a) <$> mx) b = if b = a then 1 else 0 := by
  by_cases h : b = a <;> simp [probOutput, Functor.map_map, h, eq_comm]

theorem probOutput_true_eq_sub (mx : ProbComp Bool) :
    probOutput mx true = 1 - probFailure mx - probOutput mx false := by
  have h : probOutput mx true + probOutput mx false = 1 := by
    simpa only [probOutput_def] using Measure.apply_true_add_apply_false_eq_one 𝒟[mx]
  rw [probFailure_eq_zero, tsub_zero, ← h, ENNReal.add_sub_cancel_right probOutput_ne_top]

@[simp] theorem probEvent_not_eq_probOutput (mx : ProbComp Bool) :
    probEvent mx (· = false) = probOutput mx false := rfl

theorem probEvent_exists_finset_le_sum {ι α : Type} (s : Finset ι) (mx : ProbComp α)
    (p : ι → α → Prop) :
    probEvent mx (fun x ↦ ∃ i ∈ s, p i x) ≤ ∑ i ∈ s, probEvent mx (p i) :=
  prEvent_exists_finset_le s mx p

theorem probEvent_bind_pure_comp {α β : Type} (mx : ProbComp α) (f : α → β) (q : β → Prop) :
    probEvent (mx >>= pure ∘ f) q = probEvent mx (q ∘ f) := by
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using probEvent_map mx f q

theorem probEvent_bind_le_of_forall_le {α β : Type} {mx : ProbComp α}
    {f : α → ProbComp β} {q : β → Prop} {ε : ℝ≥0∞}
    (h : ∀ x ∈ support mx, probEvent (f x) q ≤ ε) : probEvent (mx >>= f) q ≤ ε :=
  prEvent_bind_le_of_forall_le_of_support mx f q h

theorem probOutput_bind_add_left_uniform (α : Type) [AddGroup α] [SampleableType α] {β : Type}
    (shift : α) (f : α → ProbComp β) (z : β) :
    probOutput (($ᵗ α) >>= fun y ↦ f (shift + y)) z = probOutput (($ᵗ α) >>= f) z :=
  probOutput_bind_bijective_uniform_cross α _ (AddGroup.addLeft_bijective shift) f z

namespace FormalProof4FHE

theorem evalDist_bind_const_neverFails {α β : Type} (mx : ProbComp α)
    (_h : probFailure mx = 0) (my : ProbComp β) :
    𝒟[mx >>= fun _ ↦ my] = 𝒟[my] := OracleComp.evalDist_bind_const mx my

theorem evalDist_bind_bijective_add_right_uniform {α β γ : Type}
    [SampleableType α] [SampleableType β] [AddGroup β]
    (f : α → β) (hf : Function.Bijective f) (shift : β) (cont : β → ProbComp γ) :
    𝒟[($ᵗ α) >>= fun x ↦ cont (f x + shift)] = 𝒟[($ᵗ β) >>= cont] :=
  evalDist_bind_bijective_uniform_cross (fun x ↦ f x + shift)
    ((AddGroup.addRight_bijective shift).comp hf) cont

end FormalProof4FHE

namespace FormalProof4FHE

theorem evalDist_bind_congr {α β : Type} {mx : ProbComp α} {f g : α → ProbComp β}
    (h : ∀ x ∈ support mx, 𝒟[f x] = 𝒟[g x]) : 𝒟[mx >>= f] = 𝒟[mx >>= g] :=
  OracleComp.evalDist_bind_congr_of_support mx f g h

end FormalProof4FHE

theorem probOutput_bind_add_right_uniform (α : Type) [AddGroup α] [SampleableType α] {β : Type}
    (shift : α) (f : α → ProbComp β) (z : β) :
    probOutput (($ᵗ α) >>= fun y ↦ f (y + shift)) z = probOutput (($ᵗ α) >>= f) z :=
  probOutput_bind_bijective_uniform_cross α _ (AddGroup.addRight_bijective shift) f z

theorem tvDist_bind_left_event_le {α β : Type} (mx : ProbComp α) (f g : α → ProbComp β)
    (bad : α → Prop) (h : ∀ x, ¬bad x → 𝒟[f x] = 𝒟[g x]) :
    tvDist (mx >>= f) (mx >>= g) ≤ (probEvent mx bad).toReal :=
  OracleComp.measureTVDist_bind_left_le_prEvent_of_evalDistEq mx f g bad
    (fun x hx ↦ EvalDistEq.of_evalDist_eq (h x hx))

@[simp] theorem probOutput_map_prod_mk {α β : Type} [DecidableEq β]
    (mx : ProbComp α) (b : β) (z : α × β) :
    probOutput ((fun a ↦ (a, b)) <$> mx) z = if z.2 = b then probOutput mx z.1 else 0 := by
  classical
  rcases z with ⟨x, y⟩
  rw [probOutput_eq_outputPMF, ProbComp.outputPMF_map, PMF.monad_map_eq_map, PMF.map_apply]
  simp only [Prod.mk.injEq]
  by_cases hy : y = b
  · simp [hy, probOutput_eq_outputPMF]
  · simp [hy]

namespace PMF

theorem probEvent_eq_tsum_mass {α : Type} (p : PMF α) (q : α → Prop) [DecidablePred q] :
    probEvent p q = ∑' x, if q x then p x else 0 := by
  classical
  unfold probEvent prEvent
  change (q <$> p).toMeasure {True} = _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.monad_map_eq_map, PMF.map_apply]
  apply tsum_congr
  intro x
  by_cases h : q x <;> simp [h]

@[simp] theorem probOutput_eq_apply {α : Type} (p : PMF α) (x : α) :
    probOutput p x = p x := by
  classical
  change probEvent p (· = x) = p x
  rw [probEvent_eq_tsum_mass]
  simp

theorem probEvent_eq_tsum_ite {α : Type} (p : PMF α) (q : α → Prop) [DecidablePred q] :
    probEvent p q = ∑' x, if q x then probOutput p x else 0 := by
  simpa only [probOutput_eq_apply] using probEvent_eq_tsum_mass p q

theorem probEvent_map {α β : Type} (p : PMF α) (f : α → β) (q : β → Prop) :
    probEvent (f <$> p) q = probEvent p (q ∘ f) := prEvent_map p f q

end PMF

theorem tvDist_bind_left_le_const
    {α β : Type} (mx : ProbComp α) (f g : α → ProbComp β) (c : ℝ)
    (hfg : ∀ a, a ∈ support mx → tvDist (f a) (g a) ≤ c) :
    tvDist (mx >>= f) (mx >>= g) ≤ c := by
  classical
  have hprob_ne_top : ∀ a : α, Pr[= a | mx] ≠ ⊤ := fun a =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (probOutput_le_one (mx := mx) (x := a))
  have hp_sum_ne_top : (∑' a : α, Pr[= a | mx]) ≠ ⊤ := by
    rw [tsum_probOutput_of_liftM_PMF]; exact ENNReal.one_ne_top
  have hp_summable : Summable (fun a : α => Pr[= a | mx].toReal) :=
    ENNReal.summable_toReal hp_sum_ne_top
  have hp_sum_toReal : (∑' a : α, Pr[= a | mx].toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq hprob_ne_top, tsum_probOutput_of_liftM_PMF, ENNReal.toReal_one]
  have hlhs_nonneg : ∀ a : α, 0 ≤ Pr[= a | mx].toReal * tvDist (f a) (g a) :=
    fun _ => mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _)
  have hlhs_le_p : ∀ a : α,
      Pr[= a | mx].toReal * tvDist (f a) (g a) ≤ Pr[= a | mx].toReal :=
    fun _ => mul_le_of_le_one_right ENNReal.toReal_nonneg (tvDist_le_one _ _)
  have hlhs_summable :
      Summable (fun a : α => Pr[= a | mx].toReal * tvDist (f a) (g a)) :=
    Summable.of_nonneg_of_le hlhs_nonneg hlhs_le_p hp_summable
  have hrhs_summable : Summable (fun a : α => Pr[= a | mx].toReal * c) :=
    Summable.mul_right _ hp_summable
  refine (tvDist_bind_left_le mx f g).trans ?_
  calc
    (∑' a : α, Pr[= a | mx].toReal * tvDist (f a) (g a))
        ≤ ∑' a : α, Pr[= a | mx].toReal * c :=
          Summable.tsum_le_tsum
            (fun a => by
              by_cases ha : a ∈ support mx
              · exact mul_le_mul_of_nonneg_left (hfg a ha) ENNReal.toReal_nonneg
              · rw [probOutput_eq_zero_of_not_mem_support ha]; simp)
            hlhs_summable hrhs_summable
    _ = (∑' a : α, Pr[= a | mx].toReal) * c := Summable.tsum_mul_right _ hp_summable
    _ = c := by rw [hp_sum_toReal, one_mul]

theorem evalDist_add_left_uniform {α : Type} [AddGroup α] [Fintype α] [SampleableType α]
    (a : α) : 𝒟[(a + ·) <$> ($ᵗ α)] = 𝒟[$ᵗ α] :=
  evalDist_map_bijective_uniform_cross α (a + ·) (Equiv.addLeft a).bijective

theorem probOutput_seq_map_prod_mk_eq_mul {α β : Type}
    (mx : ProbComp α) (my : ProbComp β) (z : α × β) :
    probOutput (Prod.mk <$> mx <*> my) z = probOutput mx z.1 * probOutput my z.2 := by
  rw [seq_eq_bind_map, bind_map_left]
  exact probOutput_pair_map mx my z

theorem tvDist_eq_zero_iff {α : Type} (mx my : ProbComp α) :
    tvDist mx my = 0 ↔ evalDist mx = evalDist my := measureTVDist_eq_zero_iff mx my

theorem mem_support_iff_of_evalDist_eq {α : Type} {mx my : ProbComp α}
    (h : evalDist mx = evalDist my) (x : α) : x ∈ support mx ↔ x ∈ support my := by
  rw [mem_support_iff, mem_support_iff, probOutput_congr rfl h]

theorem probOutput_eq_one_iff_forall {α : Type} (mx : ProbComp α) (x : α) :
    probOutput mx x = 1 ↔ probFailure mx = 0 ∧ ∀ y ∈ support mx, y = x :=
  probEvent_eq_one_iff

theorem probOutput_bind_mono {α β γ : Type} {mx : ProbComp α}
    {f : α → ProbComp β} {g : α → ProbComp γ} {x : β} {y : γ}
    (h : ∀ a ∈ support mx, probOutput (f a) x ≤ probOutput (g a) y) :
    probOutput (mx >>= f) x ≤ probOutput (mx >>= g) y :=
  prEvent_bind_mono_of_forall_le_of_support mx f g (· = x) (· = y) h

theorem probEvent_bind_of_const {α β : Type} (mx : ProbComp α)
    {my : α → ProbComp β} {p : β → Prop} {r : ℝ≥0∞}
    (h : ∀ a ∈ support mx, probEvent (my a) p = r) :
    probEvent (mx >>= my) p = (1 - probFailure mx) * r := by
  rw [probEvent_bind_eq_tsum]
  have hterm (a : α) : probOutput mx a * probEvent (my a) p = probOutput mx a * r := by
    by_cases ha : a ∈ support mx
    · rw [h a ha]
    · rw [probOutput_eq_zero_of_not_mem_support ha, zero_mul, zero_mul]
  simp only [hterm, ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF,
    probFailure_eq_zero, tsub_zero]

theorem probEvent_bind_le_probEvent {α β : Type} {mx : ProbComp α}
    {f : α → ProbComp β} {p : α → Prop} {q : β → Prop}
    (h : ∀ a ∈ support mx, ¬p a → probEvent (f a) q = 0) :
    probEvent (mx >>= f) q ≤ probEvent mx p :=
  prEvent_bind_le_prEvent_of_support mx f p q h

theorem probEvent_one_sub_le_of_compl_le {α : Type} {mx : ProbComp α}
    {p : α → Prop} {ε : ℝ≥0∞} (_hfail : probFailure mx = 0)
    (h : probEvent mx (fun x => ¬p x) ≤ ε) : 1 - ε ≤ probEvent mx p := by
  have hsum : probEvent mx p + probEvent mx (fun x => ¬p x) = 1 := by
    have htotal := prEvent_add_prEvent_not_eq_prEvent_true mx p
    change probEvent mx p + probEvent mx (fun x => ¬p x) =
      probEvent mx (fun _ => True) at htotal
    simpa only [probEvent_true] using htotal
  rw [ENNReal.eq_sub_of_add_eq probEvent_ne_top hsum]
  exact tsub_le_tsub_left h _

@[simp] theorem probEvent_pure {α : Type} (x : α) (p : α → Prop) [Decidable (p x)] :
    probEvent (pure x : ProbComp α) p = if p x then 1 else 0 := prEvent_pure x p

theorem probEvent_eq_zero {α : Type} {mx : ProbComp α} {p : α → Prop}
    (h : ∀ x ∈ support mx, ¬p x) : probEvent mx p = 0 := probEvent_eq_zero_iff.mpr h

theorem probOutput_bind_congr {α β : Type} {mx : ProbComp α}
    {f g : α → ProbComp β} {x : β}
    (h : ∀ a ∈ support mx, probOutput (f a) x = probOutput (g a) x) :
    probOutput (mx >>= f) x = probOutput (mx >>= g) x := by
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ support mx
  · rw [h a ha]
  · rw [probOutput_eq_zero_of_not_mem_support ha, zero_mul, zero_mul]

theorem probEvent_compl {α : Type} (mx : ProbComp α) (p : α → Prop) :
    probEvent mx p + probEvent mx (fun x => ¬p x) = 1 - probFailure mx := by
  have h := prEvent_add_prEvent_not_eq_prEvent_true mx p
  change probEvent mx p + probEvent mx (fun x => ¬p x) = probEvent mx (fun _ => True) at h
  simpa only [probEvent_true, probFailure_eq_zero, tsub_zero] using h

theorem probEvent_bind_le_probEvent_add {α β : Type} {mx : ProbComp α}
    {f : α → ProbComp β} {p : α → Prop} {q : β → Prop} {ε : ℝ≥0∞}
    (h : ∀ a ∈ support mx, ¬p a → probEvent (f a) q ≤ ε) :
    probEvent (mx >>= f) q ≤ probEvent mx p + ε :=
  prEvent_bind_le_prEvent_add_of_support mx f p q h

theorem probEvent_or_le {α : Type} (mx : ProbComp α) (p q : α → Prop) :
    probEvent mx (fun x => p x ∨ q x) ≤ probEvent mx p + probEvent mx q :=
  prEvent_or_le mx p q

theorem probEvent_eq_sum_fintype_ite {α : Type} [Fintype α] (mx : ProbComp α)
    (p : α → Prop) [DecidablePred p] :
    probEvent mx p = ∑ x, if p x then probOutput mx x else 0 := by
  rw [probEvent_eq_tsum_ite, tsum_fintype]
