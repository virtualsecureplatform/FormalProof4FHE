/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.SubspaceLWE.Adaptive
import FormalProof4FHE.LWE.Basic
import Mathlib.LinearAlgebra.Projection
import VCVio.OracleComp.QueryTracking.SeededOracle
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# Concrete LWE Simulator for Adaptive Subspace LWE

This file implements Pietrzak's affine-fiber simulator. It proves the exact real and
uniform response laws for every admissible full-rank query and supplies reusable eager-tape
lemmas for compiling a bounded online sample oracle into a batch LWE challenge.
-/

open Matrix OracleComp OracleSpec
open scoped ENNReal

namespace FormalProof4FHE.GeneralizedSubspaceLWE.Adaptive

noncomputable def equivProdKerOfSurjective {K E V : Type}
    [Field K] [AddCommGroup E] [Module K E] [AddCommGroup V] [Module K V]
    (f : E →ₗ[K] V) (hf : Function.Surjective f) :
    E ≃ₗ[K] V × LinearMap.ker f := by
  let p := (LinearMap.ker f).exists_isCompl.choose
  have hp : IsCompl (LinearMap.ker f) p :=
    (LinearMap.ker f).exists_isCompl.choose_spec
  let g : E →ₗ[K] LinearMap.ker f :=
    (LinearMap.ker f).projectionOnto p hp
  have hg : LinearMap.range g = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro y
    refine ⟨(y : E), ?_⟩
    exact (Submodule.projectionOnto_apply_left hp y)
  have hfg : IsCompl (LinearMap.ker f) (LinearMap.ker g) := by
    simpa [g] using hp
  exact LinearMap.equivProdOfSurjectiveOfIsCompl f g
    (LinearMap.range_eq_top.mpr hf) hg hfg

@[simp]
theorem equivProdKerOfSurjective_fst {K E V : Type}
    [Field K] [AddCommGroup E] [Module K E] [AddCommGroup V] [Module K V]
    (f : E →ₗ[K] V) (hf : Function.Surjective f) (x : E) :
    (equivProdKerOfSurjective f hf x).1 = f x := by
  simp [equivProdKerOfSurjective]

theorem vecMul_surjective_of_rank_eq_width {F : Type} [Field F]
    (rows cols : ℕ) (T : Matrix (Fin rows) (Fin cols) F)
    (hT : T.rank = cols) : Function.Surjective T.vecMulLinear := by
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  rw [range_vecMulLinear, ← Matrix.rank_eq_finrank_span_row, hT]
  simp

noncomputable def samplePreimage {K E V : Type}
    [Field K] [AddCommGroup E] [Module K E] [Fintype E]
    [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]
    (f : E →ₗ[K] V) (hf : Function.Surjective f) (target : V) : ProbComp E := by
  classical
  letI : Fintype (LinearMap.ker f) := Fintype.ofFinite _
  letI : SampleableType (LinearMap.ker f) :=
    SampleableType.ofFintype (LinearMap.ker f)
  exact do
    let kernelElement ← $ᵗ LinearMap.ker f
    return (equivProdKerOfSurjective f hf).symm (target, kernelElement)

theorem samplePreimage_mem {K E V : Type}
    [Field K] [AddCommGroup E] [Module K E] [Fintype E]
    [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]
    (f : E →ₗ[K] V) (hf : Function.Surjective f) (target : V)
    (x : E) (hx : x ∈ support (samplePreimage f hf target)) :
    f x = target := by
  classical
  letI : Fintype (LinearMap.ker f) := Fintype.ofFinite _
  letI : SampleableType (LinearMap.ker f) :=
    SampleableType.ofFintype (LinearMap.ker f)
  simp only [samplePreimage, support_bind, support_uniformSample, Set.mem_iUnion,
    support_pure, Set.mem_singleton_iff] at hx
  obtain ⟨kernelElement, _, rfl⟩ := hx
  have hfst := equivProdKerOfSurjective_fst f hf
    ((equivProdKerOfSurjective f hf).symm (target, kernelElement))
  simpa using hfst.symm

theorem evalDist_samplePreimage_uniformTarget {K E V : Type}
    [Field K] [AddCommGroup E] [Module K E] [Fintype E] [SampleableType E]
    [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V] [SampleableType V]
    (f : E →ₗ[K] V) (hf : Function.Surjective f) :
    𝒟[do
      let target ← $ᵗ V
      samplePreimage f hf target] = 𝒟[$ᵗ E] := by
  classical
  letI : Fintype (LinearMap.ker f) := Fintype.ofFinite _
  letI : SampleableType (LinearMap.ker f) :=
    SampleableType.ofFintype (LinearMap.ker f)
  let pairGame : ProbComp (V × LinearMap.ker f) := do
    let target ← $ᵗ V
    let kernelElement ← $ᵗ LinearMap.ker f
    return (target, kernelElement)
  have hpair : 𝒟[pairGame] = 𝒟[$ᵗ (V × LinearMap.ker f)] := by
    apply evalDist_ext
    intro pair
    simp [pairGame, probOutput_bind_eq_sum_fintype]
    rw [ENNReal.mul_inv] <;> simp
  rw [show (do
      let target ← $ᵗ V
      samplePreimage f hf target) =
      (equivProdKerOfSurjective f hf).symm <$> pairGame by
        simp [samplePreimage, pairGame, monad_norm]]
  calc
    𝒟[(equivProdKerOfSurjective f hf).symm <$> pairGame] =
        𝒟[(equivProdKerOfSurjective f hf).symm <$>
          ($ᵗ (V × LinearMap.ker f))] := by
      simp only [evalDist_map]
      rw [hpair]
    _ = 𝒟[$ᵗ E] := evalDist_map_bijective_uniform_cross
      (α := V × LinearMap.ker f) (β := E)
      (equivProdKerOfSurjective f hf).symm
      (equivProdKerOfSurjective f hf).symm.bijective

open FormalProof4FHE.GeneralizedSubspaceLWE

def simulatorTarget {F : Type} [Field F] {ambient dimension : ℕ}
    (query : Query F ambient)
    (hidden : Matrix (Fin ambient) (Fin dimension) F)
    (challenge : Fin dimension → F) : Fin dimension → F :=
  challenge - query.randomness.offset ᵥ* (query.secret.linear * hidden)

def simulatorCorrection {F : Type} [Field F] {ambient : ℕ}
    (query : Query F ambient) (blinding randomness : Fin ambient → F) : F :=
  dotProduct (query.randomness.apply randomness) (query.secret.apply blinding)

theorem simulator_algebra {F : Type} [Field F] {ambient dimension : ℕ}
    (query : Query F ambient)
    (hidden : Matrix (Fin ambient) (Fin dimension) F)
    (blinding randomness : Fin ambient → F)
    (secret challenge : Fin dimension → F) (error : F)
    (hpreimage : randomness ᵥ* (query.overlap * hidden) =
      simulatorTarget query hidden challenge) :
    noisyInnerProduct (hidden *ᵥ secret + blinding) randomness query error =
      dotProduct challenge secret + error +
        simulatorCorrection query blinding randomness := by
  unfold simulatorTarget at hpreimage
  unfold Query.overlap at hpreimage
  unfold noisyInnerProduct simulatorCorrection
  unfold AffineProjection.apply
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
  have hregroup :
      (query.secret.linear * hidden) *ᵥ secret +
          query.secret.linear *ᵥ blinding + query.secret.offset =
        (query.secret.linear * hidden) *ᵥ secret +
          (query.secret.linear *ᵥ blinding + query.secret.offset) := by
    abel
  rw [hregroup, dotProduct_add]
  rw [Matrix.dotProduct_mulVec]
  rw [Matrix.add_vecMul]
  rw [Matrix.vecMul_mulVec]
  rw [← Matrix.mul_assoc]
  rw [hpreimage]
  simp only [sub_add_cancel]
  ring

theorem subRight_bijective {A : Type} [AddGroup A] (constant : A) :
    Function.Bijective (fun value : A ↦ value - constant) := by
  refine ⟨fun first second heq => ?_, fun value => ⟨value + constant, by simp⟩⟩
  exact sub_left_injective heq

theorem evalDist_samplePreimage_sub_uniform {K E V : Type}
    [Field K] [AddCommGroup E] [Module K E] [Fintype E] [SampleableType E]
    [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V] [SampleableType V]
    (f : E →ₗ[K] V) (hf : Function.Surjective f) (constant : V) :
    𝒟[do
      let value ← $ᵗ V
      samplePreimage f hf (value - constant)] = 𝒟[$ᵗ E] := by
  let shift : V → V := fun value ↦ value - constant
  have hshift : 𝒟[shift <$> ($ᵗ V)] = 𝒟[$ᵗ V] :=
    evalDist_map_bijective_uniform_cross (α := V) (β := V)
      shift (subRight_bijective constant)
  rw [show (do
      let value ← $ᵗ V
      samplePreimage f hf (value - constant)) =
      (shift <$> ($ᵗ V)) >>= samplePreimage f hf by
        rw [map_eq_bind_pure_comp, bind_assoc]
        simp [shift]]
  rw [evalDist_bind, hshift, ← evalDist_bind]
  exact evalDist_samplePreimage_uniformTarget f hf

noncomputable def goodSimulator {F : Type} [Field F] [Fintype F]
    [DecidableEq F] [SampleableType F] {ambient dimension : ℕ}
    (query : Query F ambient)
    (hidden : Matrix (Fin ambient) (Fin dimension) F)
    (blinding : Fin ambient → F)
    (hfull : (query.overlap * hidden).rank = dimension)
    (valueSampler : (Fin dimension → F) → ProbComp F) :
    ProbComp (Response F ambient) := do
  let challenge ← $ᵗ (Fin dimension → F)
  let randomness ← samplePreimage (query.overlap * hidden).vecMulLinear
    (vecMul_surjective_of_rank_eq_width ambient dimension (query.overlap * hidden) hfull)
    (simulatorTarget query hidden challenge)
  let value ← valueSampler challenge
  return some (randomness, value + simulatorCorrection query blinding randomness)

theorem evalDist_goodSimulator_real {F : Type} [Field F] [Fintype F]
    [DecidableEq F] [SampleableType F] {ambient dimension : ℕ}
    (query : Query F ambient)
    (hidden : Matrix (Fin ambient) (Fin dimension) F)
    (blinding : Fin ambient → F)
    (hfull : (query.overlap * hidden).rank = dimension)
    (secret : Fin dimension → F) (errorSampler : ProbComp F) :
    𝒟[goodSimulator query hidden blinding hfull (fun challenge => do
        let error ← errorSampler
        return dotProduct challenge secret + error)] =
      𝒟[do
        let randomness ← $ᵗ (Fin ambient → F)
        let error ← errorSampler
        return some (randomness,
          noisyInnerProduct (hidden *ᵥ secret + blinding)
            randomness query error)] := by
  classical
  let transform := (query.overlap * hidden).vecMulLinear
  have hsurj : Function.Surjective transform :=
    vecMul_surjective_of_rank_eq_width ambient dimension (query.overlap * hidden) hfull
  let constant : Fin dimension → F :=
    query.randomness.offset ᵥ* (query.secret.linear * hidden)
  have hhead :
      𝒟[do
        let challenge ← $ᵗ (Fin dimension → F)
        samplePreimage transform hsurj (challenge - constant)] =
        𝒟[$ᵗ (Fin ambient → F)] :=
    evalDist_samplePreimage_sub_uniform transform hsurj constant
  simp only [goodSimulator, bind_assoc, pure_bind]
  change 𝒟[do
      let challenge ← $ᵗ (Fin dimension → F)
      let randomness ← samplePreimage transform hsurj (challenge - constant)
      let error ← errorSampler
      pure (some (randomness,
        (dotProduct challenge secret + error) +
          simulatorCorrection query blinding randomness))] = _
  have hrewrite : ∀ challenge : Fin dimension → F,
      ∀ randomness ∈ support (samplePreimage transform hsurj (challenge - constant)),
      ∀ error : F,
        (dotProduct challenge secret + error) +
            simulatorCorrection query blinding randomness =
          noisyInnerProduct (hidden *ᵥ secret + blinding)
            randomness query error := by
    intro challenge randomness hrandomness error
    have hpreimage := samplePreimage_mem transform hsurj (challenge - constant)
      randomness hrandomness
    exact (simulator_algebra query hidden blinding randomness secret challenge error
      (by simpa [transform, constant, simulatorTarget] using hpreimage)).symm
  -- Replace the simulator scalar by the algebraically equal honest scalar on every supported
  -- preimage, after which the challenge is no longer observable.
  calc
    𝒟[do
      let challenge ← $ᵗ (Fin dimension → F)
      let randomness ← samplePreimage transform hsurj (challenge - constant)
      let error ← errorSampler
      pure (some (randomness,
        (dotProduct challenge secret + error) +
          simulatorCorrection query blinding randomness))] =
        𝒟[do
          let challenge ← $ᵗ (Fin dimension → F)
          let randomness ← samplePreimage transform hsurj (challenge - constant)
          let error ← errorSampler
          pure (some (randomness,
            noisyInnerProduct (hidden *ᵥ secret + blinding)
              randomness query error))] := by
      refine evalDist_bind_congr' ($ᵗ (Fin dimension → F)) (fun challenge => ?_)
      refine evalDist_bind_congr
        (mx := samplePreimage transform hsurj (challenge - constant)) ?_
      intro randomness hrandomness
      refine evalDist_bind_congr' errorSampler (fun error => ?_)
      rw [hrewrite challenge randomness hrandomness error]
    _ = 𝒟[(do
          let challenge ← $ᵗ (Fin dimension → F)
          samplePreimage transform hsurj (challenge - constant)) >>= fun randomness => do
            let error ← errorSampler
            pure (some (randomness,
              noisyInnerProduct (hidden *ᵥ secret + blinding)
                randomness query error))] := by
      rw [bind_assoc]
    _ = 𝒟[do
        let randomness ← $ᵗ (Fin ambient → F)
        let error ← errorSampler
        return some (randomness,
          noisyInnerProduct (hidden *ᵥ secret + blinding)
            randomness query error)] := by
      rw [evalDist_bind, hhead, ← evalDist_bind]

theorem evalDist_goodSimulator_uniform {F : Type} [Field F] [Fintype F]
    [DecidableEq F] [SampleableType F] {ambient dimension : ℕ}
    (query : Query F ambient)
    (hidden : Matrix (Fin ambient) (Fin dimension) F)
    (blinding : Fin ambient → F)
    (hfull : (query.overlap * hidden).rank = dimension) :
    𝒟[goodSimulator query hidden blinding hfull (fun _ => $ᵗ F)] =
      𝒟[uniformResponse (R := F) ambient] := by
  classical
  let transform := (query.overlap * hidden).vecMulLinear
  have hsurj : Function.Surjective transform :=
    vecMul_surjective_of_rank_eq_width ambient dimension (query.overlap * hidden) hfull
  let constant : Fin dimension → F :=
    query.randomness.offset ᵥ* (query.secret.linear * hidden)
  have hhead :
      𝒟[do
        let challenge ← $ᵗ (Fin dimension → F)
        samplePreimage transform hsurj (challenge - constant)] =
        𝒟[$ᵗ (Fin ambient → F)] :=
    evalDist_samplePreimage_sub_uniform transform hsurj constant
  simp only [goodSimulator]
  change 𝒟[do
      let challenge ← $ᵗ (Fin dimension → F)
      let randomness ← samplePreimage transform hsurj (challenge - constant)
      let value ← $ᵗ F
      pure (some (randomness, value + simulatorCorrection query blinding randomness))] = _
  calc
    𝒟[do
      let challenge ← $ᵗ (Fin dimension → F)
      let randomness ← samplePreimage transform hsurj (challenge - constant)
      let value ← $ᵗ F
      pure (some (randomness, value + simulatorCorrection query blinding randomness))] =
        𝒟[(do
          let challenge ← $ᵗ (Fin dimension → F)
          samplePreimage transform hsurj (challenge - constant)) >>= fun randomness => do
            let value ← $ᵗ F
            pure (some (randomness,
              value + simulatorCorrection query blinding randomness))] := by
      rw [bind_assoc]
    _ = 𝒟[do
        let randomness ← $ᵗ (Fin ambient → F)
        let value ← $ᵗ F
        pure (some (randomness,
          value + simulatorCorrection query blinding randomness))] := by
      rw [evalDist_bind, hhead, ← evalDist_bind]
    _ = 𝒟[do
        let randomness ← $ᵗ (Fin ambient → F)
        let value ← $ᵗ F
        pure (some (randomness, value))] := by
      refine evalDist_bind_congr' ($ᵗ (Fin ambient → F)) (fun randomness => ?_)
      apply evalDist_ext
      intro output
      simpa using
        (probOutput_bind_add_right_uniform (α := F)
          (simulatorCorrection query blinding randomness)
          (fun value => (pure (some (randomness, value)) :
            ProbComp (Response F ambient))) output)
    _ = 𝒟[uniformResponse (R := F) ambient] := by
      rfl

/-! A distribution-independent eager-tape lemma.  VCVio's seeded-oracle theorem specializes
to uniform oracle semantics; the LWE tape also contains arbitrary error samples, so we use the
same argument for an arbitrary stateless `ProbComp` implementation. -/

theorem withPregen_run_bind_query_eq_pop {ι : Type} {spec : OracleSpec ι}
    [DecidableEq ι] (implementation : QueryImpl spec ProbComp)
    {α : Type} (index : spec.Domain) (continuation : spec.Range index → OracleComp spec α)
    (seed : QuerySeed spec) :
    (((implementation.withPregen index) >>= fun value =>
        simulateQ implementation.withPregen (continuation value)).run seed) =
      match seed.pop index with
      | none => do
          let value ← implementation index
          (simulateQ implementation.withPregen (continuation value)).run seed
      | some (value, seed') =>
          (simulateQ implementation.withPregen (continuation value)).run seed' := by
  cases hseed : seed index <;>
    simp [QueryImpl.withPregen_apply, StateT.run_bind, QuerySeed.pop, hseed]

theorem withPregen_run'_bind_query_eq_pop {ι : Type} {spec : OracleSpec ι}
    [DecidableEq ι] (implementation : QueryImpl spec ProbComp)
    {α : Type} (index : spec.Domain) (continuation : spec.Range index → OracleComp spec α)
    (seed : QuerySeed spec) :
    (((implementation.withPregen index) >>= fun value =>
        simulateQ implementation.withPregen (continuation value)).run' seed) =
      match seed.pop index with
      | none => do
          let value ← implementation index
          (simulateQ implementation.withPregen (continuation value)).run' seed
      | some (value, seed') =>
          (simulateQ implementation.withPregen (continuation value)).run' seed' := by
  change Prod.fst <$> ((implementation.withPregen index >>= fun value =>
    simulateQ implementation.withPregen (continuation value)).run seed) = _
  rw [withPregen_run_bind_query_eq_pop implementation index continuation seed]
  cases seed.pop index with
  | none => simp [map_bind]
  | some pair => rfl

private theorem tape_pop_addValue_self_nil {ι : Type} {spec : OracleSpec ι}
    [DecidableEq ι] {seed : QuerySeed spec} {index : ι} (hseed : seed index = [])
    (value : spec.Range index) :
    (seed.addValue index value).pop index = some (value, seed) := by
  have hlist : (seed.addValue index value) index = [value] := by
    simp [QuerySeed.addValue, QuerySeed.addValues, hseed]
  rw [QuerySeed.pop_eq_some_of_cons _ _ value [] hlist]
  suffices Function.update (seed.addValue index value) index
      ([] : List (spec.Range index)) = seed by
    rw [this]
    rfl
  funext other
  by_cases hother : other = index
  · subst hother
    simp [hseed]
  · rw [Function.update_of_ne hother]
    exact QuerySeed.addValues_of_ne seed [value] hother

private theorem tape_pop_addValue_self_cons {ι : Type} {spec : OracleSpec ι}
    [DecidableEq ι] {seed : QuerySeed spec} {index : ι} {head : spec.Range index}
    {tail : List (spec.Range index)} (hseed : seed index = head :: tail)
    (value : spec.Range index) :
    (seed.addValue index value).pop index =
      some (head, QuerySeed.addValue (Function.update seed index tail) index value) := by
  have hlist : (seed.addValue index value) index = head :: (tail ++ [value]) := by
    simp [QuerySeed.addValue, QuerySeed.addValues, hseed]
  rw [QuerySeed.pop_eq_some_of_cons _ _ head (tail ++ [value]) hlist]
  suffices Function.update (seed.addValue index value) index (tail ++ [value]) =
      QuerySeed.addValue (Function.update seed index tail) index value by
    rw [this]
    rfl
  funext other
  by_cases hother : other = index
  · subst hother
    simp [QuerySeed.addValue, QuerySeed.addValues]
  · simp [Function.update_of_ne hother, QuerySeed.addValue, QuerySeed.addValues]

private theorem tape_pop_addValue_of_ne_nil {ι : Type} {spec : OracleSpec ι}
    [DecidableEq ι] {seed : QuerySeed spec} {added index : ι} (hne : index ≠ added)
    (hseed : seed index = []) (value : spec.Range added) :
    (seed.addValue added value).pop index = none := by
  rw [QuerySeed.pop_eq_none_iff]
  exact (QuerySeed.addValues_of_ne seed [_] hne).trans hseed

private theorem tape_pop_addValue_of_ne_cons {ι : Type} {spec : OracleSpec ι}
    [DecidableEq ι] {seed : QuerySeed spec} {added index : ι}
    {head : spec.Range index} {tail : List (spec.Range index)}
    (hne : index ≠ added) (hseed : seed index = head :: tail)
    (value : spec.Range added) :
    (seed.addValue added value).pop index =
      some (head, QuerySeed.addValue (Function.update seed index tail) added value) := by
  have hlist : (seed.addValue added value) index = head :: tail :=
    (QuerySeed.addValues_of_ne seed [_] hne).trans hseed
  rw [QuerySeed.pop_eq_some_of_cons _ _ head tail hlist]
  suffices Function.update (seed.addValue added value) index tail =
      QuerySeed.addValue (Function.update seed index tail) added value by
    rw [this]
    rfl
  change Function.update (Function.update seed added (seed added ++ [value])) index tail =
    Function.update (Function.update seed index tail) added
      ((Function.update seed index tail) added ++ [value])
  conv_rhs =>
    rw [show (Function.update seed index tail) added = seed added from
      Function.update_of_ne (Ne.symm hne) tail seed]
  exact Function.update_comm (Ne.symm hne) (seed added ++ [value]) tail seed

theorem evalDist_sample_bind_withPregen_addValue {ι : Type} {spec : OracleSpec ι}
    [DecidableEq ι] (implementation : QueryImpl spec ProbComp)
    (seed : QuerySeed spec) (added : ι) {α : Type} (computation : OracleComp spec α) :
    𝒟[do
      let value ← implementation added
      (simulateQ implementation.withPregen computation).run' (seed.addValue added value)] =
      𝒟[(simulateQ implementation.withPregen computation).run' seed] := by
  revert seed
  induction computation using OracleComp.inductionOn with
  | pure output =>
      intro seed
      have hrun' : ∀ currentSeed,
          (simulateQ implementation.withPregen (pure output : OracleComp spec α)).run'
              currentSeed = (pure output : ProbComp α) := fun currentSeed => by simp
      apply evalDist_ext
      intro candidate
      simp_rw [hrun']
      rw [probOutput_bind_const]
      simp
  | query_bind index continuation ih =>
      intro seed
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        OracleQuery.input_query, id_map]
      apply evalDist_ext
      intro output
      simp_rw [withPregen_run'_bind_query_eq_pop implementation index continuation]
      by_cases hindex : index = added
      · cases hindex
        cases hseed : seed added with
        | nil =>
            simp_rw [tape_pop_addValue_self_nil hseed,
              (QuerySeed.pop_eq_none_iff seed added).mpr hseed]
        | cons head tail =>
            simp_rw [tape_pop_addValue_self_cons hseed,
              QuerySeed.pop_eq_some_of_cons seed added head tail hseed]
            exact congrFun (congrArg DFunLike.coe
              (ih head (Function.update seed added tail))) output
      · cases hseed : seed index with
        | nil =>
            simp_rw [tape_pop_addValue_of_ne_nil hindex hseed,
              (QuerySeed.pop_eq_none_iff seed index).mpr hseed]
            rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
            simp_rw [probOutput_bind_eq_tsum (implementation index) _ output]
            simp_rw [← ENNReal.tsum_mul_left]
            rw [ENNReal.tsum_comm]
            congr 1
            ext response
            calc
              (∑' value : spec.Range added,
                  Pr[= value | implementation added] *
                    (Pr[= response | implementation index] *
                      Pr[= output |
                        (simulateQ implementation.withPregen
                          (continuation response)).run' (seed.addValue added value)])) =
                  Pr[= response | implementation index] *
                    (∑' value : spec.Range added,
                      Pr[= value | implementation added] *
                        Pr[= output |
                          (simulateQ implementation.withPregen
                            (continuation response)).run' (seed.addValue added value)]) := by
                rw [← ENNReal.tsum_mul_left]
                apply tsum_congr
                intro value
                ac_rfl
              _ = Pr[= response | implementation index] *
                    Pr[= output |
                      (simulateQ implementation.withPregen
                        (continuation response)).run' seed] := by
                congr 1
                have hih := congrFun (congrArg DFunLike.coe (ih response seed)) output
                change Pr[= output | do
                    let value ← implementation added
                    (simulateQ implementation.withPregen
                      (continuation response)).run' (seed.addValue added value)] =
                  Pr[= output |
                    (simulateQ implementation.withPregen
                      (continuation response)).run' seed] at hih
                rw [probOutput_bind_eq_tsum] at hih
                exact hih
        | cons head tail =>
            simp_rw [tape_pop_addValue_of_ne_cons hindex hseed,
              QuerySeed.pop_eq_some_of_cons seed index head tail hseed]
            exact congrFun (congrArg DFunLike.coe
              (ih head (Function.update seed index tail))) output

theorem evalDist_replicate_bind_withPregen_addValues {ι : Type} {spec : OracleSpec ι}
    [DecidableEq ι] (implementation : QueryImpl spec ProbComp)
    (index : ι) {α : Type} (computation : OracleComp spec α) (count : ℕ) :
    ∀ seed : QuerySeed spec,
    𝒟[do
      let values ← OracleComp.replicate count (implementation index)
      (simulateQ implementation.withPregen computation).run' (seed.addValues values)] =
      𝒟[(simulateQ implementation.withPregen computation).run' seed] := by
  induction count with
  | zero =>
      intro seed
      simp [OracleComp.replicate_zero, QuerySeed.addValues_nil]
  | succ count ih =>
      intro seed
      simp only [OracleComp.replicate_succ_bind, bind_assoc, pure_bind]
      have hseed : ∀ (head : spec.Range index) (tail : List (spec.Range index)),
          seed.addValues (head :: tail) = (seed.addValues [head]).addValues tail :=
        fun head tail => QuerySeed.addValues_cons seed head tail
      calc
        𝒟[do
          let head ← implementation index
          let tail ← OracleComp.replicate count (implementation index)
          (simulateQ implementation.withPregen computation).run'
            (seed.addValues (head :: tail))] =
            𝒟[do
              let head ← implementation index
              let tail ← OracleComp.replicate count (implementation index)
              (simulateQ implementation.withPregen computation).run'
                ((seed.addValues [head]).addValues tail)] := by
          refine evalDist_bind_congr' (implementation index) (fun head => ?_)
          refine evalDist_bind_congr'
            (OracleComp.replicate count (implementation index)) (fun tail => ?_)
          rw [hseed head tail]
        _ = 𝒟[do
            let head ← implementation index
            (simulateQ implementation.withPregen computation).run'
              (seed.addValues [head])] := by
          rw [evalDist_bind]
          simp_rw [ih]
          rw [← evalDist_bind]
        _ = 𝒟[(simulateQ implementation.withPregen computation).run' seed] :=
          evalDist_sample_bind_withPregen_addValue implementation seed index computation

/-- Once a seed covers every charged query, its fallback implementation is unobservable. -/
theorem run_withPregen_eq_of_queryBound {ι : Type} {spec : OracleSpec ι}
    [DecidableEq ι] (first second : QueryImpl spec ProbComp)
    (charged : ι → Prop) [DecidablePred charged]
    (hsame : ∀ index, ¬charged index → first index = second index)
    {α : Type} (computation : OracleComp spec α) (budget : ℕ)
    (hbound : OracleComp.IsQueryBoundP computation charged budget)
    (seed : QuerySeed spec)
    (hcoverage : ∀ index, charged index → budget ≤ (seed index).length) :
    (simulateQ first.withPregen computation).run' seed =
      (simulateQ second.withPregen computation).run' seed := by
  induction computation using OracleComp.inductionOn generalizing budget seed with
  | pure output => simp
  | query_bind index continuation ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        OracleQuery.input_query, id_map]
      rw [withPregen_run'_bind_query_eq_pop first index continuation seed,
        withPregen_run'_bind_query_eq_pop second index continuation seed]
      by_cases hcharged : charged index
      · have hpositive : 0 < budget := by
          rcases hbound.1 with hnot | hpositive
          · exact absurd hcharged hnot
          · exact hpositive
        have hnonempty : seed index ≠ [] := by
          intro hempty
          have := hcoverage index hcharged
          simp [hempty] at this
          omega
        obtain ⟨head, tail, hseed⟩ := List.exists_cons_of_ne_nil hnonempty
        have hpop := QuerySeed.pop_eq_some_of_cons seed index head tail hseed
        rw [hpop]
        apply ih head (budget := budget - 1)
          (seed := Function.update seed index tail)
        · simpa [hcharged] using hbound.2 head
        · intro other hother
          by_cases heq : other = index
          · have hlength := hcoverage index hcharged
            rw [hseed] at hlength
            simp only [List.length_cons] at hlength
            subst other
            simp only [Function.update_self]
            omega
          · rw [Function.update_of_ne heq]
            exact le_trans (Nat.sub_le budget 1) (hcoverage other hother)
      · cases hseed : seed index with
        | nil =>
            have hpop : seed.pop index = none :=
              (QuerySeed.pop_eq_none_iff seed index).mpr hseed
            rw [hpop, hsame index hcharged]
            apply bind_congr
            intro response
            apply ih response (budget := budget) (seed := seed)
            · simpa [hcharged] using hbound.2 response
            · exact hcoverage
        | cons head tail =>
            have hpop := QuerySeed.pop_eq_some_of_cons seed index head tail hseed
            rw [hpop]
            apply ih head (budget := budget)
              (seed := Function.update seed index tail)
            · simpa [hcharged] using hbound.2 head
            · intro other hother
              have hne : other ≠ index := by
                intro heq
                subst heq
                exact hcharged hother
              rw [Function.update_of_ne hne]
              exact hcoverage other hother

abbrev LWESample (F : Type) (dimension : ℕ) := (Fin dimension → F) × F

def pairSamplerFromValue {F : Type} [SampleableType F] {dimension : ℕ}
    (valueSampler : (Fin dimension → F) → ProbComp F) :
    ProbComp (LWESample F dimension) := do
  let challenge ← $ᵗ (Fin dimension → F)
  let value ← valueSampler challenge
  return (challenge, value)

noncomputable def pairedGoodSimulator {F : Type} [Field F] [Fintype F]
    [DecidableEq F] [SampleableType F] {ambient dimension : ℕ}
    (query : Query F ambient)
    (hidden : Matrix (Fin ambient) (Fin dimension) F)
    (blinding : Fin ambient → F)
    (hfull : (query.overlap * hidden).rank = dimension)
    (sampleSampler : ProbComp (LWESample F dimension)) :
    ProbComp (Response F ambient) := do
  let sample ← sampleSampler
  let randomness ← samplePreimage (query.overlap * hidden).vecMulLinear
    (vecMul_surjective_of_rank_eq_width ambient dimension (query.overlap * hidden) hfull)
    (simulatorTarget query hidden sample.1)
  return some (randomness,
    sample.2 + simulatorCorrection query blinding randomness)

/-- Drawing the LWE value before the affine-fiber sample or after it gives the same
distribution, because both draws are independent once the public challenge is fixed. -/
theorem evalDist_pairedGoodSimulator_eq_goodSimulator {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ambient dimension : ℕ} (query : Query F ambient)
    (hidden : Matrix (Fin ambient) (Fin dimension) F)
    (blinding : Fin ambient → F)
    (hfull : (query.overlap * hidden).rank = dimension)
    (valueSampler : (Fin dimension → F) → ProbComp F) :
    𝒟[pairedGoodSimulator query hidden blinding hfull
        (pairSamplerFromValue valueSampler)] =
      𝒟[goodSimulator query hidden blinding hfull valueSampler] := by
  classical
  unfold pairedGoodSimulator pairSamplerFromValue goodSimulator
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_congr' ($ᵗ (Fin dimension → F)) (fun challenge => ?_)
  exact OracleComp.DeferredSampling.evalDist_bind_comm
    (valueSampler challenge)
    (samplePreimage (query.overlap * hidden).vecMulLinear
      (vecMul_surjective_of_rank_eq_width ambient dimension
        (query.overlap * hidden) hfull)
      (simulatorTarget query hidden challenge))
    (fun value randomness => pure (some (randomness,
      value + simulatorCorrection query blinding randomness)))

abbrev SourceInterface (F : Type) (dimension : ℕ) :=
  unifSpec + (Unit →ₒ LWESample F dimension)

/-- Online source semantics: public uniform queries are forwarded and the distinguished source
query draws one LWE sample. -/
def sourceImpl {F : Type} {dimension : ℕ}
    (sampleSampler : ProbComp (LWESample F dimension)) :
    QueryImpl (SourceInterface F dimension) ProbComp :=
  (QueryImpl.ofLift unifSpec ProbComp) +
    (fun (_ : Unit) => sampleSampler :
      QueryImpl (Unit →ₒ LWESample F dimension) ProbComp)

/-- The concrete LWE-to-SLWE query reduction.  On an admissible full-rank query it obtains one
source LWE sample and samples a uniform solution of Pietrzak's affine equation.  Rank loss is
reported as `none`; inadmissible queries agree exactly with the public SLWE guard. -/
noncomputable def simulatorReduction {F : Type} [Field F] [Fintype F]
    [DecidableEq F] [SampleableType F] {ambient dimension : ℕ}
    (threshold : ℕ) (hidden : Matrix (Fin ambient) (Fin dimension) F)
    (blinding : Fin ambient → F) :
    QueryImpl (OracleInterface F ambient)
      (OracleComp (SourceInterface F dimension)) := by
  classical
  intro oracleQuery
  rcases oracleQuery with uniformIndex | query
  · exact liftM ((SourceInterface F dimension).query (Sum.inl uniformIndex))
  · exact if hadmissible : query.IsAdmissible threshold then
      if hfull : (query.overlap * hidden).rank = dimension then do
        let sample ← liftM ((SourceInterface F dimension).query (Sum.inr ()))
        let randomness ← liftM (samplePreimage (query.overlap * hidden).vecMulLinear
          (vecMul_surjective_of_rank_eq_width ambient dimension
            (query.overlap * hidden) hfull)
          (simulatorTarget query hidden sample.1))
        return some (randomness,
          sample.2 + simulatorCorrection query blinding randomness)
      else
        return none
    else
      return none

/-- The online source implementation of one reduced query has the paired-simulator semantics. -/
theorem evalDist_sourceImpl_simulatorReduction_of_admissible_full {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ambient dimension : ℕ} (threshold : ℕ)
    (hidden : Matrix (Fin ambient) (Fin dimension) F)
    (blinding : Fin ambient → F) (query : Query F ambient)
    (hadmissible : query.IsAdmissible threshold)
    (hfull : (query.overlap * hidden).rank = dimension)
    (sampleSampler : ProbComp (LWESample F dimension)) :
    𝒟[simulateQ (sourceImpl sampleSampler)
        (simulatorReduction threshold hidden blinding (Sum.inr query))] =
      𝒟[pairedGoodSimulator query hidden blinding hfull sampleSampler] := by
  have hright :
      (sourceImpl sampleSampler) (Sum.inr ()) = sampleSampler := by
    rfl
  have hquery (t : unifSpec.Domain) :
      simulateQ (sourceImpl sampleSampler)
          (liftM (liftM (unifSpec.query t) : ProbComp (unifSpec.Range t)) :
            OracleComp (SourceInterface F dimension) (unifSpec.Range t)) =
        (liftM (unifSpec.query t) : ProbComp (unifSpec.Range t)) := by
    change simulateQ (sourceImpl sampleSampler)
        (liftM ((SourceInterface F dimension).query (Sum.inl t))) = _
    simp [sourceImpl]
    rfl
  have hleft {alpha : Type} (oa : ProbComp alpha) :
      simulateQ (sourceImpl sampleSampler)
          (liftM oa : OracleComp (SourceInterface F dimension) alpha) = oa := by
    induction oa using OracleComp.inductionOn with
    | pure x => simp
    | query_bind t k ih =>
        simp [hquery, ih]
  simp [simulatorReduction, hadmissible, hfull, pairedGoodSimulator,
    hright, hleft, monad_norm]
end FormalProof4FHE.GeneralizedSubspaceLWE.Adaptive
