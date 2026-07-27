/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.RankOneHNFLossinessRefined
import FormalProof4FHE.Probability.LeftoverHash
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Support-Aware Rank-One HNF Lossiness

This module formalizes the finite algebraic and probabilistic results from
`sketch/rank_one_hnf_lossiness_support_aware.tex`.

The main native results are the weighted spanning-tree bound for conditional guessing,
its sharp weighted-total-variation edge estimate and uniform-prior corollaries, descriptor
averaging and finite interval certificates, the exact local quadratic-codeword factorization,
guessing-probability data processing, and the exact likelihood of a coherently lifted finite
CRT/RNS channel.

Continuous Gaussian total variation, log-determinant entropy maximization, subgaussian row-energy
concentration, and Gaussian covariance decomposition require analytic probability infrastructure
which is not currently part of the finite `ProbComp` library.  Their precise conclusions are
represented by proof-carrying certificates.  No axiom is introduced.
-/

open OracleComp
open scoped ENNReal

namespace FormalProof4FHE.RLWE.RankOneHNFLossinessSupportAware

open RankOneHNFLossinessRefined
open RankOneHNFLossinessRLWENTRU

noncomputable section

/-! ## Elementary finite probability identities -/

/-- A finite `ProbComp` has total real point mass one. -/
theorem sum_probOutput_toReal_eq_one
    {Output : Type} [Fintype Output] (sampler : ProbComp Output) :
    (∑ output : Output, Pr[= output | sampler].toReal) = 1 := by
  have hsum : (∑ output : Output, Pr[= output | sampler]) = 1 := by
    exact sum_probOutput_eq_one (probFailure_eq_zero (mx := sampler))
  rw [← ENNReal.toReal_sum (s := Finset.univ)
    (f := fun output : Output ↦ Pr[= output | sampler])
    (fun _ _ ↦ probOutput_ne_top), hsum]
  simp

/-- The real maximum-likelihood expression for a finite joint law. -/
noncomputable def realFiniteGuessingMass
    {Secret Side : Type} [Fintype Secret] [Nonempty Secret] [Fintype Side]
    (joint : ProbComp (Secret × Side)) : ℝ :=
  ∑ side, Pr[= (maximizingSecret joint side, side) | joint].toReal

/-- The operational finite guessing probability, converted to `ℝ`, is exactly the sum of the
point masses selected by a maximum-likelihood estimator. -/
theorem conditionalGuessingProbability_toReal_eq_realFiniteGuessingMass
    {Secret Side : Type} [Fintype Secret] [Nonempty Secret] [Fintype Side]
    [DecidableEq Secret] [DecidableEq Side]
    (joint : ProbComp (Secret × Side)) :
    (conditionalGuessingProbability joint).toReal = realFiniteGuessingMass joint := by
  rw [conditionalGuessingProbability_eq_finiteGuessingMass]
  unfold finiteGuessingMass realFiniteGuessingMass
  have hsum :
      (∑ side, ⨆ secret, Pr[= (secret, side) | joint]) =
        ∑ side, Pr[= (maximizingSecret joint side, side) | joint] := by
    apply Finset.sum_congr rfl
    intro side _
    exact (maximizingSecret_eq_iSup joint side).symm
  rw [hsum, ENNReal.toReal_sum (fun _ _ ↦ probOutput_ne_top)]

/-! ## Telescoping along a finite spanning tree -/

/-- Symmetric absolute variation of a real vertex label across an unoriented edge. -/
def edgeVariation {Vertex : Type} (value : Vertex → ℝ) : Sym2 Vertex → ℝ :=
  Sym2.lift ⟨fun left right ↦ |value left - value right|, fun left right ↦ by
    change |value left - value right| = |value right - value left|
    exact abs_sub_comm _ _⟩

@[simp]
theorem edgeVariation_mk {Vertex : Type} (value : Vertex → ℝ) (left right : Vertex) :
    edgeVariation value s(left, right) = |value left - value right| := rfl

theorem edgeVariation_nonneg {Vertex : Type} (value : Vertex → ℝ) (edge : Sym2 Vertex) :
    0 ≤ edgeVariation value edge := by
  induction edge using Sym2.inductionOn with
  | _ left right => exact abs_nonneg _

/-- The endpoint value of a walk is bounded by its initial value plus the sum of all absolute
increments along the walk. -/
theorem walk_endpoint_le_start_add_edgeVariation
    {Vertex : Type} {graph : SimpleGraph Vertex} {start finish : Vertex}
    (value : Vertex → ℝ) (walk : graph.Walk start finish) :
    value finish ≤ value start + (walk.edges.map (edgeVariation value)).sum := by
  induction walk with
  | nil => simp
  | @cons left middle finish adjacency tail ih =>
      rw [SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons]
      have hstep : value middle ≤ value left + |value left - value middle| := by
        rw [abs_sub_comm]
        linarith [le_abs_self (value middle - value left)]
      calc
        value finish ≤ value middle + (tail.edges.map (edgeVariation value)).sum := ih
        _ ≤ (value left + |value left - value middle|) +
              (tail.edges.map (edgeVariation value)).sum := by linarith
        _ = value left +
              (edgeVariation value s(left, middle) +
                (tail.edges.map (edgeVariation value)).sum) := by
          simp only [edgeVariation_mk]
          ring

/-- In a connected finite graph, the variation along a simple root-to-vertex path is at most the
sum over every graph edge.  A tree is the sharp application because it has exactly `|V|-1`
edges. -/
theorem connected_value_le_root_add_edgeVariation
    {Vertex : Type} [Fintype Vertex] [DecidableEq Vertex]
    (graph : SimpleGraph Vertex) [Fintype graph.edgeSet]
    (connected : graph.Connected) (root vertex : Vertex) (value : Vertex → ℝ) :
    value vertex ≤ value root + ∑ edge ∈ graph.edgeFinset, edgeVariation value edge := by
  obtain ⟨walk, isPath⟩ := connected.exists_isPath root vertex
  have hwalk := walk_endpoint_le_start_add_edgeVariation value walk
  have hpathSum :
      (walk.edges.map (edgeVariation value)).sum =
        ∑ edge ∈ walk.edges.toFinset, edgeVariation value edge := by
    rw [← List.sum_toFinset (edgeVariation value) isPath.isTrail.edges_nodup]
  rw [hpathSum] at hwalk
  have hsubset : walk.edges.toFinset ⊆ graph.edgeFinset := by
    intro edge hedge
    rw [SimpleGraph.mem_edgeFinset]
    exact walk.edges_subset_edgeSet (by simpa using hedge)
  have hsum :
      (∑ edge ∈ walk.edges.toFinset, edgeVariation value edge) ≤
        ∑ edge ∈ graph.edgeFinset, edgeVariation value edge := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun edge _ _ ↦ edgeVariation_nonneg value edge)
  linarith

/-! ## Weighted spanning-tree guessing -/

/-- Real joint point mass `pi(s) P_s(y)` of a prior followed by a channel. -/
def weightedJointPointMass
    {Secret Output : Type} (prior : ProbComp Secret)
    (channel : Secret → ProbComp Output) (secret : Secret) (output : Output) : ℝ :=
  Pr[= secret | prior].toReal * Pr[= output | channel secret].toReal

/-- Weighted `L¹` distance across an unoriented secret edge. -/
def weightedEdgeL1
    {Secret Output : Type} [Fintype Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output) : Sym2 Secret → ℝ :=
  Sym2.lift ⟨
    fun left right ↦
      ∑ output,
        |weightedJointPointMass prior channel left output -
          weightedJointPointMass prior channel right output|,
    fun left right ↦ by
      apply Finset.sum_congr rfl
      intro output _
      rw [abs_sub_comm]⟩

@[simp]
theorem weightedEdgeL1_mk
    {Secret Output : Type} [Fintype Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (left right : Secret) :
    weightedEdgeL1 prior channel s(left, right) =
      ∑ output,
        |weightedJointPointMass prior channel left output -
          weightedJointPointMass prior channel right output| := rfl

theorem weightedEdgeL1_nonneg
    {Secret Output : Type} [Fintype Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (edge : Sym2 Secret) :
    0 ≤ weightedEdgeL1 prior channel edge := by
  induction edge using Sym2.inductionOn with
  | _ left right =>
      simp only [weightedEdgeL1_mk]
      exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

/-- Total variation across an unoriented channel edge. -/
def channelEdgeTV
    {Secret Output : Type} (channel : Secret → ProbComp Output) : Sym2 Secret → ℝ :=
  Sym2.lift ⟨fun left right ↦ tvDist (channel left) (channel right), fun left right ↦ by
    change tvDist (channel left) (channel right) = tvDist (channel right) (channel left)
    exact tvDist_comm _ _⟩

@[simp]
theorem channelEdgeTV_mk
    {Secret Output : Type} (channel : Secret → ProbComp Output) (left right : Secret) :
    channelEdgeTV channel s(left, right) = tvDist (channel left) (channel right) := rfl

/-- **Weighted spanning-tree guessing bound.**  The vertex type may be the subtype of secrets in
the posterior support.  The proof is the pointwise tree telescoping argument followed by a finite
sum over observations. -/
theorem weightedSpanningTreeGuessingBound
    {Secret Output : Type} [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (tree : SimpleGraph Secret) [Fintype tree.edgeSet]
    (isTree : tree.IsTree) (root : Secret) :
    (conditionalGuessingProbability
        (conditionalChannelJoint prior channel)).toReal ≤
      Pr[= root | prior].toReal +
        ∑ edge ∈ tree.edgeFinset, weightedEdgeL1 prior channel edge := by
  let joint := conditionalChannelJoint prior channel
  rw [conditionalGuessingProbability_toReal_eq_realFiniteGuessingMass]
  unfold realFiniteGuessingMass
  have hpoint : ∀ output,
      Pr[= (maximizingSecret joint output, output) | joint].toReal ≤
        weightedJointPointMass prior channel root output +
          ∑ edge ∈ tree.edgeFinset,
            edgeVariation
              (fun secret ↦ weightedJointPointMass prior channel secret output) edge := by
    intro output
    rw [probOutput_conditionalChannelJoint, ENNReal.toReal_mul]
    exact connected_value_le_root_add_edgeVariation tree isTree.connected root
      (maximizingSecret joint output)
      (fun secret ↦ weightedJointPointMass prior channel secret output)
  calc
    (∑ output, Pr[= (maximizingSecret joint output, output) | joint].toReal) ≤
        ∑ output,
          (weightedJointPointMass prior channel root output +
            ∑ edge ∈ tree.edgeFinset,
              edgeVariation
                (fun secret ↦ weightedJointPointMass prior channel secret output) edge) :=
      Finset.sum_le_sum fun output _ ↦ hpoint output
    _ = Pr[= root | prior].toReal +
          ∑ edge ∈ tree.edgeFinset, weightedEdgeL1 prior channel edge := by
      simp only [Finset.sum_add_distrib, weightedJointPointMass,
        ← Finset.mul_sum, sum_probOutput_toReal_eq_one, mul_one]
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro edge _
      induction edge using Sym2.inductionOn with
      | _ left right => rfl

/-! ### Weighted edge versus total variation -/

private theorem weightedEdgeL1_le_tv_of_le
    {Secret Output : Type} [Fintype Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (left right : Secret)
    (hmass : Pr[= right | prior].toReal ≤ Pr[= left | prior].toReal) :
    weightedEdgeL1 prior channel s(left, right) ≤
      |Pr[= left | prior].toReal - Pr[= right | prior].toReal| +
        2 * min Pr[= left | prior].toReal Pr[= right | prior].toReal *
          tvDist (channel left) (channel right) := by
  let a := Pr[= left | prior].toReal
  let b := Pr[= right | prior].toReal
  let p : Output → ℝ := fun output ↦ Pr[= output | channel left].toReal
  let q : Output → ℝ := fun output ↦ Pr[= output | channel right].toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hb : 0 ≤ b := ENNReal.toReal_nonneg
  have hpoint : ∀ output,
      |a * p output - b * q output| ≤
        (a - b) * p output + b * |p output - q output| := by
    intro output
    have hp : 0 ≤ p output := ENNReal.toReal_nonneg
    have hab : 0 ≤ a - b := sub_nonneg.mpr hmass
    calc
      |a * p output - b * q output| =
          |(a - b) * p output + b * (p output - q output)| := by ring_nf
      _ ≤ |(a - b) * p output| + |b * (p output - q output)| := abs_add_le _ _
      _ = (a - b) * p output + b * |p output - q output| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hab, abs_of_nonneg hp, abs_of_nonneg hb]
  simp only [weightedEdgeL1_mk, weightedJointPointMass]
  change (∑ output, |a * p output - b * q output|) ≤ _
  calc
    (∑ output, |a * p output - b * q output|) ≤
        ∑ output, ((a - b) * p output + b * |p output - q output|) :=
      Finset.sum_le_sum fun output _ ↦ hpoint output
    _ = (a - b) + b * ∑ output, |p output - q output| := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      change (a - b) * (∑ output, Pr[= output | channel left].toReal) + _ = _
      rw [sum_probOutput_toReal_eq_one]
      ring
    _ = |a - b| + 2 * min a b * tvDist (channel left) (channel right) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hmass), min_eq_right hmass,
        FormalProof4FHE.LeftoverHash.tvDist_eq_half_sum_abs]
      ring

/-- The weighted edge estimate
`||aP-bQ||₁ ≤ |a-b| + 2 min(a,b) TV(P,Q)` from the sketch. -/
theorem weightedEdgeL1_le_priorDiff_add_tv
    {Secret Output : Type} [Fintype Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (left right : Secret) :
    weightedEdgeL1 prior channel s(left, right) ≤
      |Pr[= left | prior].toReal - Pr[= right | prior].toReal| +
        2 * min Pr[= left | prior].toReal Pr[= right | prior].toReal *
          tvDist (channel left) (channel right) := by
  by_cases hmass : Pr[= right | prior].toReal ≤ Pr[= left | prior].toReal
  · exact weightedEdgeL1_le_tv_of_le prior channel left right hmass
  · have hreverse : Pr[= left | prior].toReal ≤ Pr[= right | prior].toReal :=
      le_of_not_ge hmass
    have h := weightedEdgeL1_le_tv_of_le prior channel right left hreverse
    simpa only [Sym2.eq_swap, abs_sub_comm, min_comm, tvDist_comm] using h

/-- Uniform-prior specialization of the weighted tree theorem. -/
theorem uniformSpanningTreeGuessingBound
    {Secret Output : Type} [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (tree : SimpleGraph Secret) [Fintype tree.edgeSet]
    (isTree : tree.IsTree) (root : Secret)
    (uniform : ∀ secret,
      Pr[= secret | prior].toReal = 1 / (Fintype.card Secret : ℝ)) :
    (conditionalGuessingProbability
        (conditionalChannelJoint prior channel)).toReal ≤
      1 / (Fintype.card Secret : ℝ) +
        (2 / (Fintype.card Secret : ℝ)) *
          ∑ edge ∈ tree.edgeFinset, channelEdgeTV channel edge := by
  calc
    (conditionalGuessingProbability
        (conditionalChannelJoint prior channel)).toReal ≤
        Pr[= root | prior].toReal +
          ∑ edge ∈ tree.edgeFinset, weightedEdgeL1 prior channel edge :=
      weightedSpanningTreeGuessingBound prior channel tree isTree root
    _ ≤ 1 / (Fintype.card Secret : ℝ) +
          ∑ edge ∈ tree.edgeFinset,
            ((2 / (Fintype.card Secret : ℝ)) * channelEdgeTV channel edge) := by
      rw [uniform root]
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro edge _
      induction edge using Sym2.inductionOn with
      | _ left right =>
        refine (weightedEdgeL1_le_priorDiff_add_tv prior channel left right).trans_eq ?_
        rw [uniform left, uniform right]
        simp only [channelEdgeTV_mk, sub_self, abs_zero, zero_add, min_self]
        ring
    _ = 1 / (Fintype.card Secret : ℝ) +
          (2 / (Fintype.card Secret : ℝ)) *
            ∑ edge ∈ tree.edgeFinset, channelEdgeTV channel edge := by
      rw [Finset.mul_sum]

/-- If every tree edge has distance at most `delta`, the `|Secret|-1` edges give the saturated
local bound `1/M + 2 (1-1/M) delta`. -/
theorem uniformSpanningTreeGuessingBound_of_edgeTV
    {Secret Output : Type} [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (tree : SimpleGraph Secret) [Fintype tree.edgeSet]
    (isTree : tree.IsTree) (root : Secret)
    (uniform : ∀ secret,
      Pr[= secret | prior].toReal = 1 / (Fintype.card Secret : ℝ))
    (delta : ℝ)
    (edgeTV : ∀ edge ∈ tree.edgeFinset, channelEdgeTV channel edge ≤ delta) :
    (conditionalGuessingProbability
        (conditionalChannelJoint prior channel)).toReal ≤
      1 / (Fintype.card Secret : ℝ) +
        2 * (1 - 1 / (Fintype.card Secret : ℝ)) * delta := by
  have hcardPos : (0 : ℝ) < Fintype.card Secret := by
    exact_mod_cast Fintype.card_pos
  have hedgeSum :
      (∑ edge ∈ tree.edgeFinset, channelEdgeTV channel edge) ≤
        (tree.edgeFinset.card : ℝ) * delta := by
    simpa only [nsmul_eq_mul, Nat.cast_ofNat, Nat.cast_mul] using
      (Finset.sum_le_card_nsmul tree.edgeFinset (channelEdgeTV channel) delta edgeTV)
  have htreeCardNat := isTree.card_edgeFinset
  have htreeCard :
      (tree.edgeFinset.card : ℝ) = (Fintype.card Secret : ℝ) - 1 := by
    have hcast :
        (tree.edgeFinset.card : ℝ) + 1 = (Fintype.card Secret : ℝ) := by
      exact_mod_cast htreeCardNat
    linarith
  calc
    (conditionalGuessingProbability
        (conditionalChannelJoint prior channel)).toReal ≤
      1 / (Fintype.card Secret : ℝ) +
        (2 / (Fintype.card Secret : ℝ)) *
          ∑ edge ∈ tree.edgeFinset, channelEdgeTV channel edge :=
      uniformSpanningTreeGuessingBound prior channel tree isTree root uniform
    _ ≤ 1 / (Fintype.card Secret : ℝ) +
        (2 / (Fintype.card Secret : ℝ)) *
          ((tree.edgeFinset.card : ℝ) * delta) := by
      gcongr
    _ = 1 / (Fintype.card Secret : ℝ) +
        2 * (1 - 1 / (Fintype.card Secret : ℝ)) * delta := by
      rw [htreeCard]
      field_simp [ne_of_gt hcardPos]

/-! ## Descriptor averaging and local support graphs -/

/-- Exact real form of descriptor averaging: conditioned finite guessing masses average with the
actual descriptor distribution. -/
theorem contextualGuessingProbability_toReal_eq_average
    {Context Secret Output : Type}
    [Fintype Context] [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Context] [DecidableEq Secret] [DecidableEq Output]
    (contextSampler : ProbComp Context)
    (prior : Context → ProbComp Secret)
    (channel : Context → Secret → ProbComp Output) :
    (conditionalGuessingProbability
      (contextualChannelJoint contextSampler prior channel)).toReal =
      ∑ context,
        Pr[= context | contextSampler].toReal *
          (conditionalGuessingProbability
            (conditionalChannelJoint (prior context) (channel context))).toReal := by
  rw [conditionalGuessingProbability_eq_finiteGuessingMass,
    finiteGuessingMass_contextualChannelJoint]
  have hfinite : ∀ context,
      finiteGuessingMass
        (conditionalChannelJoint (prior context) (channel context)) ≠ ⊤ := by
    intro context
    rw [← conditionalGuessingProbability_eq_finiteGuessingMass]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top
      (conditionalGuessingProbability_le_one _)
  rw [ENNReal.toReal_sum (fun context _ ↦
    ENNReal.mul_ne_top probOutput_ne_top (hfinite context))]
  apply Finset.sum_congr rfl
  intro context _
  rw [ENNReal.toReal_mul, ← conditionalGuessingProbability_eq_finiteGuessingMass]

/-- Integrate arbitrary real pointwise guessing bounds over the actual descriptor law. -/
theorem descriptorAveragedGuessingBound
    {Descriptor Secret Output : Type}
    [Fintype Descriptor] [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Descriptor] [DecidableEq Secret] [DecidableEq Output]
    (descriptorSampler : ProbComp Descriptor)
    (prior : Descriptor → ProbComp Secret)
    (channel : Descriptor → Secret → ProbComp Output)
    (bound : Descriptor → ℝ)
    (pointwise : ∀ descriptor,
      (conditionalGuessingProbability
        (conditionalChannelJoint (prior descriptor) (channel descriptor))).toReal ≤
          bound descriptor) :
    (conditionalGuessingProbability
      (contextualChannelJoint descriptorSampler prior channel)).toReal ≤
      ∑ descriptor, Pr[= descriptor | descriptorSampler].toReal * bound descriptor := by
  rw [contextualGuessingProbability_toReal_eq_average]
  apply Finset.sum_le_sum
  intro descriptor _
  exact mul_le_mul_of_nonneg_left (pointwise descriptor) ENNReal.toReal_nonneg

/-- A connected local graph contains a spanning tree made only of local edges, so the uniform
tree theorem applies with the same edge-distance bound. -/
theorem uniformConnectedLocalGuessingBound
    {Secret Output : Type} [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (localGraph : SimpleGraph Secret) [Fintype localGraph.edgeSet]
    (connected : localGraph.Connected)
    (uniform : ∀ secret,
      Pr[= secret | prior].toReal = 1 / (Fintype.card Secret : ℝ))
    (delta : ℝ)
    (localTV : ∀ edge ∈ localGraph.edgeFinset,
      channelEdgeTV channel edge ≤ delta) :
    (conditionalGuessingProbability
      (conditionalChannelJoint prior channel)).toReal ≤
      1 / (Fintype.card Secret : ℝ) +
        2 * (1 - 1 / (Fintype.card Secret : ℝ)) * delta := by
  obtain ⟨tree, tree_le, isTree⟩ := connected.exists_isTree_le
  letI : Fintype tree.edgeSet := Fintype.ofFinite tree.edgeSet
  let root : Secret := Classical.choice inferInstance
  apply uniformSpanningTreeGuessingBound_of_edgeTV prior channel tree isTree root uniform delta
  intro edge hedge
  exact localTV edge (SimpleGraph.edgeFinset_mono tree_le hedge)

/-- **Local-edge ternary certificate, descriptor-averaged form.**  Any concrete full-ternary or
fixed-weight graph need only provide connectivity and local edge TV estimates. -/
theorem descriptorAveragedLocalGuessingBound
    {Descriptor Secret Output : Type}
    [Fintype Descriptor] [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Descriptor] [DecidableEq Secret] [DecidableEq Output]
    (descriptorSampler : ProbComp Descriptor)
    (prior : ProbComp Secret)
    (channel : Descriptor → Secret → ProbComp Output)
    (localGraph : SimpleGraph Secret) [Fintype localGraph.edgeSet]
    (connected : localGraph.Connected)
    (uniform : ∀ secret,
      Pr[= secret | prior].toReal = 1 / (Fintype.card Secret : ℝ))
    (delta : Descriptor → ℝ)
    (localTV : ∀ descriptor edge, edge ∈ localGraph.edgeFinset →
      channelEdgeTV (channel descriptor) edge ≤ delta descriptor) :
    (conditionalGuessingProbability
      (contextualChannelJoint descriptorSampler (fun _ ↦ prior) channel)).toReal ≤
      1 / (Fintype.card Secret : ℝ) +
        2 * (1 - 1 / (Fintype.card Secret : ℝ)) *
          ∑ descriptor,
            Pr[= descriptor | descriptorSampler].toReal * delta descriptor := by
  let scale : ℝ := 2 * (1 - 1 / (Fintype.card Secret : ℝ))
  have hpoint : ∀ descriptor,
      (conditionalGuessingProbability
        (conditionalChannelJoint prior (channel descriptor))).toReal ≤
        1 / (Fintype.card Secret : ℝ) + scale * delta descriptor := by
    intro descriptor
    exact uniformConnectedLocalGuessingBound prior (channel descriptor) localGraph connected
      uniform (delta descriptor) (localTV descriptor)
  calc
    (conditionalGuessingProbability
      (contextualChannelJoint descriptorSampler (fun _ ↦ prior) channel)).toReal ≤
        ∑ descriptor, Pr[= descriptor | descriptorSampler].toReal *
          (1 / (Fintype.card Secret : ℝ) + scale * delta descriptor) :=
      descriptorAveragedGuessingBound descriptorSampler (fun _ ↦ prior) channel _ hpoint
    _ = 1 / (Fintype.card Secret : ℝ) + scale *
          ∑ descriptor,
            Pr[= descriptor | descriptorSampler].toReal * delta descriptor := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
        sum_probOutput_toReal_eq_one, one_mul]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro descriptor _
      ring
    _ = 1 / (Fintype.card Secret : ℝ) +
        2 * (1 - 1 / (Fintype.card Secret : ℝ)) *
          ∑ descriptor,
            Pr[= descriptor | descriptorSampler].toReal * delta descriptor := rfl

/-! ### Concrete finite ternary support cardinalities -/

/-- Full coefficientwise ternary support.  `Fin 3` is a finite encoding of `{-1,0,1}`. -/
abbrev FullTernarySecret (dimension : ℕ) := Fin dimension → Fin 3

@[simp]
theorem card_fullTernarySecret (dimension : ℕ) :
    Fintype.card (FullTernarySecret dimension) = 3 ^ dimension := by
  simp [FullTernarySecret]

/-- Exact-Hamming-weight ternary secrets, represented by a support of size `weight` and one sign
bit at every support position. -/
abbrev FixedWeightTernarySecret (dimension weight : ℕ) :=
  Σ support : ↥((Finset.univ : Finset (Fin dimension)).powersetCard weight),
    support.1 → Fin 2

@[simp]
theorem card_fixedWeightTernarySecret (dimension weight : ℕ) :
    Fintype.card (FixedWeightTernarySecret dimension weight) =
      2 ^ weight * dimension.choose weight := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  calc
    (∑ support :
        ↥((Finset.univ : Finset (Fin dimension)).powersetCard weight),
        2 ^ support.1.card) =
        ∑ _support :
          ↥((Finset.univ : Finset (Fin dimension)).powersetCard weight),
          2 ^ weight := by
      apply Finset.sum_congr rfl
      intro support _
      rw [(Finset.mem_powersetCard.mp support.property).2]
    _ = ((Finset.univ : Finset (Fin dimension)).powersetCard weight).card *
          2 ^ weight := by simp
    _ = 2 ^ weight * dimension.choose weight := by
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      ring

/-! ## Exact local quadratic codeword algebra -/

/-- One row of the quadratic codeword `mu(s)=z*s+fg*s^2`. -/
def quadraticCodewordRow {R : Type} [CommRing R] (z fg secret : R) : R :=
  z * secret + fg * secret ^ 2

/-- Exact local factorization
`mu(t)-mu(s)=(t-s)(z+fg(t+s))`. -/
theorem quadraticCodewordRow_sub_factor
    {R : Type} [CommRing R] (z fg left right : R) :
    quadraticCodewordRow z fg right - quadraticCodewordRow z fg left =
      (right - left) * (z + fg * (right + left)) := by
  simp only [quadraticCodewordRow]
  ring

/-- Row-indexed version of the exact local quadratic-edge factorization. -/
theorem quadraticCodeword_sub_factor
    {R Row : Type} [CommRing R]
    (z fg : Row → R) (left right : R) :
    (fun row ↦ quadraticCodewordRow (z row) (fg row) right -
      quadraticCodewordRow (z row) (fg row) left) =
    fun row ↦ (right - left) * (z row + fg row * (right + left)) := by
  funext row
  exact quadraticCodewordRow_sub_factor (z row) (fg row) left right

/-- The exact finite/discrete local distance.  It deliberately uses the implemented translated
noise channels; no continuous-Gaussian approximation is made. -/
def exactQuadraticShiftDistance
    {Secret Output : Type} [Add Output]
    (noise : ProbComp Output) (mean : Secret → Output) (left right : Secret) : ℝ :=
  tvDist (additiveChannel noise mean left) (additiveChannel noise mean right)

theorem channelEdgeTV_additiveChannel
    {Secret Output : Type} [Add Output]
    (noise : ProbComp Output) (mean : Secret → Output) (left right : Secret) :
    channelEdgeTV (additiveChannel noise mean) s(left, right) =
      exactQuadraticShiftDistance noise mean left right := rfl

/-! ## Finite interval certificates -/

/-- Elementary finite partition inequality underlying the interval certificate.  The `bad` set
and the fibers of `cell` on its complement form an exact partition, so there is no measurability
or disjointness side condition left implicit. -/
theorem finiteIntervalExpectationBound
    {Context Cell : Type} [Fintype Context] [Fintype Cell]
    [DecidableEq Context] [DecidableEq Cell]
    (weight pointwise : Context → ℝ) (bad : Context → Prop) [DecidablePred bad]
    (cell : Context → Cell) (beta : ℝ) (cellMassUpper cellBound : Cell → ℝ)
    (weight_nonneg : ∀ context, 0 ≤ weight context)
    (pointwise_le_one : ∀ context, pointwise context ≤ 1)
    (cellBound_nonneg : ∀ index, 0 ≤ cellBound index)
    (badMass : (∑ context ∈ Finset.univ.filter bad, weight context) ≤ beta)
    (cellMass : ∀ index,
      (∑ context ∈ Finset.univ.filter (fun context ↦ ¬bad context ∧ cell context = index),
        weight context) ≤ cellMassUpper index)
    (goodPointwise : ∀ context, ¬bad context →
      pointwise context ≤ cellBound (cell context)) :
    (∑ context, weight context * pointwise context) ≤
      beta + ∑ index, cellMassUpper index * cellBound index := by
  let badSet : Finset Context := Finset.univ.filter bad
  let goodSet : Finset Context := Finset.univ.filter fun context ↦ ¬bad context
  have hsplit (summand : Context → ℝ) :
      (∑ context, summand context) =
        (∑ context ∈ badSet, summand context) +
          ∑ context ∈ goodSet, summand context := by
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ bad summand).symm
  have hbadPart :
      (∑ context ∈ badSet, weight context * pointwise context) ≤
        ∑ context ∈ badSet, weight context := by
    apply Finset.sum_le_sum
    intro context _
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left (pointwise_le_one context) (weight_nonneg context))
  have hgoodPart :
      (∑ context ∈ goodSet, weight context * pointwise context) ≤
        ∑ context ∈ goodSet, weight context * cellBound (cell context) := by
    apply Finset.sum_le_sum
    intro context hcontext
    exact mul_le_mul_of_nonneg_left
      (goodPointwise context (by simpa [goodSet] using hcontext))
      (weight_nonneg context)
  have hreindex :
      (∑ context ∈ goodSet, weight context * cellBound (cell context)) =
        ∑ index,
          (∑ context ∈ goodSet.filter (fun context ↦ cell context = index),
            weight context) * cellBound index := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (s := goodSet) (t := Finset.univ) (g := cell)
      (fun _ _ ↦ Finset.mem_univ _) (fun context ↦
        weight context * cellBound (cell context))]
    apply Finset.sum_congr rfl
    intro index _
    calc
      (∑ context ∈ goodSet.filter (fun context ↦ cell context = index),
          weight context * cellBound (cell context)) =
          ∑ context ∈ goodSet.filter (fun context ↦ cell context = index),
            weight context * cellBound index := by
        apply Finset.sum_congr rfl
        intro context hcontext
        have hcell : cell context = index := (Finset.mem_filter.mp hcontext).2
        rw [hcell]
      _ = (∑ context ∈ goodSet.filter (fun context ↦ cell context = index),
            weight context) * cellBound index := by
        rw [Finset.sum_mul]
  have hcellPart :
      (∑ index,
          (∑ context ∈ goodSet.filter (fun context ↦ cell context = index),
            weight context) * cellBound index) ≤
        ∑ index, cellMassUpper index * cellBound index := by
    apply Finset.sum_le_sum
    intro index _
    apply mul_le_mul_of_nonneg_right _ (cellBound_nonneg index)
    have hsame :
        goodSet.filter (fun context ↦ cell context = index) =
          Finset.univ.filter (fun context ↦ ¬bad context ∧ cell context = index) := by
      ext context
      simp [goodSet]
    rw [hsame]
    exact cellMass index
  calc
    (∑ context, weight context * pointwise context) =
        (∑ context ∈ badSet, weight context * pointwise context) +
          ∑ context ∈ goodSet, weight context * pointwise context :=
      hsplit _
    _ ≤ (∑ context ∈ badSet, weight context) +
          ∑ context ∈ goodSet, weight context * cellBound (cell context) :=
      add_le_add hbadPart hgoodPart
    _ = (∑ context ∈ badSet, weight context) +
          ∑ index,
            (∑ context ∈ goodSet.filter (fun context ↦ cell context = index),
              weight context) * cellBound index := by rw [hreindex]
    _ ≤ beta + ∑ index, cellMassUpper index * cellBound index := by
      exact add_le_add (by simpa [badSet] using badMass) hcellPart

/-- **Finite interval certificate for conditional guessing.**  It integrates checked cell-mass
upper bounds and checked pointwise guessing bounds, charging at most one on the bad set. -/
theorem finiteIntervalGuessingCertificate
    {Context Cell Secret Output : Type}
    [Fintype Context] [Fintype Cell] [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Context] [DecidableEq Cell] [DecidableEq Secret] [DecidableEq Output]
    (contextSampler : ProbComp Context)
    (prior : Context → ProbComp Secret)
    (channel : Context → Secret → ProbComp Output)
    (bad : Context → Prop) [DecidablePred bad] (cell : Context → Cell)
    (beta : ℝ) (cellMassUpper cellBound : Cell → ℝ)
    (cellBound_nonneg : ∀ index, 0 ≤ cellBound index)
    (badMass :
      (∑ context ∈ Finset.univ.filter bad,
        Pr[= context | contextSampler].toReal) ≤ beta)
    (cellMass : ∀ index,
      (∑ context ∈ Finset.univ.filter
        (fun context ↦ ¬bad context ∧ cell context = index),
        Pr[= context | contextSampler].toReal) ≤ cellMassUpper index)
    (pointwise : ∀ context, ¬bad context →
      (conditionalGuessingProbability
        (conditionalChannelJoint (prior context) (channel context))).toReal ≤
          cellBound (cell context)) :
    (conditionalGuessingProbability
      (contextualChannelJoint contextSampler prior channel)).toReal ≤
      beta + ∑ index, cellMassUpper index * cellBound index := by
  rw [contextualGuessingProbability_toReal_eq_average]
  apply finiteIntervalExpectationBound
    (weight := fun context ↦ Pr[= context | contextSampler].toReal)
    (pointwise := fun context ↦
      (conditionalGuessingProbability
        (conditionalChannelJoint (prior context) (channel context))).toReal)
    (bad := bad) (cell := cell) (beta := beta)
    (cellMassUpper := cellMassUpper) (cellBound := cellBound)
  · exact fun _ ↦ ENNReal.toReal_nonneg
  · intro context
    exact ENNReal.toReal_mono ENNReal.one_ne_top
      (conditionalGuessingProbability_le_one _)
  · exact cellBound_nonneg
  · exact badMass
  · exact cellMass
  · exact pointwise

/-! ## Guessing data processing and anisotropic decomposition -/

/-- Apply a randomized post-processing kernel to the public side of a joint secret/side law. -/
def postprocessJoint
    {Secret Source Target : Type} (joint : ProbComp (Secret × Source))
    (kernel : Source → ProbComp Target) : ProbComp (Secret × Target) := do
  let value ← joint
  let target ← kernel value.2
  return (value.1, target)

theorem probOutput_postprocessJoint
    {Secret Source Target : Type}
    [Fintype Secret] [Fintype Source] [Fintype Target]
    [DecidableEq Secret] [DecidableEq Source] [DecidableEq Target]
    (joint : ProbComp (Secret × Source)) (kernel : Source → ProbComp Target)
    (secret : Secret) (target : Target) :
    Pr[= (secret, target) | postprocessJoint joint kernel] =
      ∑ source,
        Pr[= (secret, source) | joint] * Pr[= target | kernel source] := by
  classical
  simp [postprocessJoint, probOutput_bind_eq_sum_fintype, Fintype.sum_prod_type]

/-- **Randomized data processing for conditional guessing.**  A public channel that is
independent of the secret cannot improve the optimal guessing probability. -/
theorem conditionalGuessingProbability_postprocessJoint_le
    {Secret Source Target : Type}
    [Fintype Secret] [Nonempty Secret] [Fintype Source] [Fintype Target]
    [DecidableEq Secret] [DecidableEq Source] [DecidableEq Target]
    (joint : ProbComp (Secret × Source)) (kernel : Source → ProbComp Target) :
    conditionalGuessingProbability (postprocessJoint joint kernel) ≤
      conditionalGuessingProbability joint := by
  rw [conditionalGuessingProbability_eq_finiteGuessingMass,
    conditionalGuessingProbability_eq_finiteGuessingMass]
  unfold finiteGuessingMass
  calc
    (∑ target, ⨆ secret,
        Pr[= (secret, target) | postprocessJoint joint kernel]) ≤
        ∑ target, ∑ source,
          (⨆ secret, Pr[= (secret, source) | joint]) *
            Pr[= target | kernel source] := by
      apply Finset.sum_le_sum
      intro target _
      apply iSup_le
      intro secret
      rw [probOutput_postprocessJoint]
      apply Finset.sum_le_sum
      intro source _
      exact mul_le_mul_left
        (le_iSup (fun candidate ↦ Pr[= (candidate, source) | joint]) secret) _
    _ = ∑ source,
        (⨆ secret, Pr[= (secret, source) | joint]) *
          ∑ target, Pr[= target | kernel source] := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro source _
      rw [Finset.mul_sum]
    _ = ∑ source, ⨆ secret, Pr[= (secret, source) | joint] := by
      apply Finset.sum_congr rfl
      intro source _
      rw [sum_probOutput_eq_one (probFailure_eq_zero (mx := kernel source)), mul_one]

/-- A proof-carrying finite interface for covariance-dominated Gaussian decomposition.  The PSD
field records the matrix condition `Sigma_E - A Sigma_G A* >= 0`; `decomposition` is the analytic
Gaussian existence/equality-in-law obligation. -/
structure CovarianceDominatedGaussianCertificate
    (Secret Source Target SourceCoordinate TargetCoordinate : Type)
    [Fintype SourceCoordinate] [Fintype TargetCoordinate]
    [DecidableEq SourceCoordinate] [DecidableEq TargetCoordinate] where
  linearMap : Matrix TargetCoordinate SourceCoordinate ℝ
  noiseCovariance : Matrix TargetCoordinate TargetCoordinate ℝ
  blurCovariance : Matrix SourceCoordinate SourceCoordinate ℝ
  covarianceDomination :
    (noiseCovariance - linearMap * blurCovariance * linearMap.transpose).PosSemidef
  blurredJoint : ProbComp (Secret × Source)
  observedJoint : ProbComp (Secret × Target)
  residualKernel : Source → ProbComp Target
  decomposition :
    evalDist observedJoint = evalDist (postprocessJoint blurredJoint residualKernel)

/-- **Covariance-dominated Gaussian lossiness**, once the analytic decomposition certificate is
supplied.  The inequality itself is the native randomized data-processing theorem above. -/
theorem covarianceDominatedGaussianLossiness
    {Secret Source Target SourceCoordinate TargetCoordinate : Type}
    [Fintype Secret] [Nonempty Secret] [Fintype Source] [Fintype Target]
    [DecidableEq Secret] [DecidableEq Source] [DecidableEq Target]
    [Fintype SourceCoordinate] [Fintype TargetCoordinate]
    [DecidableEq SourceCoordinate] [DecidableEq TargetCoordinate]
    (certificate : CovarianceDominatedGaussianCertificate
      Secret Source Target SourceCoordinate TargetCoordinate) :
    conditionalGuessingProbability certificate.observedJoint ≤
      conditionalGuessingProbability certificate.blurredJoint := by
  rw [conditionalGuessingProbability_congr certificate.decomposition]
  exact conditionalGuessingProbability_postprocessJoint_le
    certificate.blurredJoint certificate.residualKernel

/-! ## Exact coherent CRT/RNS likelihood -/

/-- A distinguished-limb codec: decoding the large-limb residue recovers the unique coherent
error whenever the residue lies in the image.  The arithmetic theorem
`boundedCoherentLift_unique` supplies `encodeStar` injectivity when `q_star > 2B`. -/
structure CoherentLiftCodec (Secret Error Star : Type) where
  encodeStar : Secret → Error → Star
  decodeStar : Secret → Star → Option Error
  decode_encode : ∀ secret error,
    decodeStar secret (encodeStar secret error) = some error
  encode_decode : ∀ secret star error,
    decodeStar secret star = some error → encodeStar secret error = star

theorem CoherentLiftCodec.encodeStar_injective
    {Secret Error Star : Type} (codec : CoherentLiftCodec Secret Error Star)
    (secret : Secret) : Function.Injective (codec.encodeStar secret) := by
  intro left right heq
  have hleft := codec.decode_encode secret left
  have hright := codec.decode_encode secret right
  rw [heq, hright] at hleft
  exact Option.some.inj hleft.symm

/-- Any family of injective distinguished-limb encoders has a (possibly noncomputable) exact
decoder and hence a coherent-lift codec. -/
noncomputable def CoherentLiftCodec.ofInjective
    {Secret Error Star : Type} [Nonempty Error]
    (encode : Secret → Error → Star)
    (injective : ∀ secret, Function.Injective (encode secret)) :
    CoherentLiftCodec Secret Error Star := by
  classical
  exact
    { encodeStar := encode
      decodeStar := fun secret star ↦
        dite (∃ error, encode secret error = star)
          (fun h ↦ some (Classical.choose h)) (fun _ ↦ none)
          (h := Classical.propDecidable _)
      decode_encode := by
        intro secret error
        split
        · rename_i himage
          simp only [Option.some.injEq]
          apply injective secret
          exact Classical.choose_spec himage
        · rename_i hnot
          exact (hnot (show ∃ candidate, encode secret candidate = encode secret error from
            Exists.intro error rfl)).elim
      encode_decode := by
        intro secret star error hdecode
        split at hdecode
        · rename_i himage
          simp only [Option.some.injEq] at hdecode
          subst error
          exact Classical.choose_spec himage
        · contradiction }

/-- The complete coherent observation: one distinguished large limb and all remaining limbs. -/
abbrev CoherentObservation (Star Rest : Type) := Star × Rest

/-- Reduce one common error into the distinguished limb and all remaining limbs.  There is one
error sample, not one independent sample per RNS limb. -/
def coherentLiftChannel
    {Secret Error Star Rest : Type}
    (errorSampler : ProbComp Error) (codec : CoherentLiftCodec Secret Error Star)
    (encodeRest : Secret → Error → Rest) (secret : Secret) :
    ProbComp (CoherentObservation Star Rest) :=
  (fun error ↦ (codec.encodeStar secret error, encodeRest secret error)) <$> errorSampler

/-- Candidate likelihood obtained by center-lifting the distinguished residue and checking every
remaining-limb consistency constraint. -/
def coherentLiftLikelihood
    {Secret Error Star Rest : Type} [DecidableEq Rest]
    (errorSampler : ProbComp Error) (codec : CoherentLiftCodec Secret Error Star)
    (encodeRest : Secret → Error → Rest) (secret : Secret)
    (observation : CoherentObservation Star Rest) : ENNReal :=
  match codec.decodeStar secret observation.1 with
  | none => 0
  | some error =>
      if observation.2 = encodeRest secret error then Pr[= error | errorSampler] else 0

private theorem coherentObservationEncoder_injective
    {Secret Error Star Rest : Type}
    (codec : CoherentLiftCodec Secret Error Star)
    (encodeRest : Secret → Error → Rest) (secret : Secret) :
    Function.Injective
      (fun error ↦ (codec.encodeStar secret error, encodeRest secret error)) := by
  intro left right heq
  apply codec.encodeStar_injective secret
  exact congrArg Prod.fst heq

/-- **Exact coherent-lift likelihood.**  A large-limb candidate lift contributes its actual error
mass exactly when every remaining limb is consistent, and contributes zero otherwise. -/
theorem probOutput_coherentLiftChannel
    {Secret Error Star Rest : Type} [Fintype Error]
    [DecidableEq Error] [DecidableEq Star] [DecidableEq Rest]
    (errorSampler : ProbComp Error) (codec : CoherentLiftCodec Secret Error Star)
    (encodeRest : Secret → Error → Rest) (secret : Secret)
    (observation : CoherentObservation Star Rest) :
    Pr[= observation | coherentLiftChannel errorSampler codec encodeRest secret] =
      coherentLiftLikelihood errorSampler codec encodeRest secret observation := by
  let encoder : Error → CoherentObservation Star Rest :=
    fun error ↦ (codec.encodeStar secret error, encodeRest secret error)
  have hinjective : Function.Injective encoder :=
    coherentObservationEncoder_injective codec encodeRest secret
  change Pr[= observation | encoder <$> errorSampler] = _
  unfold coherentLiftLikelihood
  cases hdecode : codec.decodeStar secret observation.1 with
  | some error =>
    change Pr[= observation | encoder <$> errorSampler] =
      if observation.2 = encodeRest secret error then Pr[= error | errorSampler] else 0
    by_cases hrest : observation.2 = encodeRest secret error
    · have hstar : codec.encodeStar secret error = observation.1 :=
        codec.encode_decode secret observation.1 error hdecode
      have hobs : observation = encoder error := by
        apply Prod.ext
        · exact hstar.symm
        · exact hrest
      rw [if_pos hrest, hobs]
      exact probOutput_map_injective errorSampler hinjective error
    · rw [if_neg hrest, probOutput_map_eq_sum_fintype_ite]
      apply Finset.sum_eq_zero
      intro candidate _
      rw [if_neg]
      intro hobs
      have hcand : candidate = error := by
        apply codec.encodeStar_injective secret
        have hfirst := congrArg Prod.fst hobs
        exact hfirst.symm.trans (codec.encode_decode secret observation.1 error hdecode).symm
      subst candidate
      exact hrest (congrArg Prod.snd hobs)
  | none =>
    change Pr[= observation | encoder <$> errorSampler] = 0
    rw [probOutput_map_eq_sum_fintype_ite]
    apply Finset.sum_eq_zero
    intro error _
    rw [if_neg]
    intro hobs
    have hstar : codec.encodeStar secret error = observation.1 :=
      (congrArg Prod.fst hobs).symm
    have hencoded := codec.decode_encode secret error
    rw [hstar, hdecode] at hencoded
    contradiction

/-- Insert the explicit bounded-support indicator from the paper.  Outside the certified error
set the sampler has zero mass, so the indicator does not change the exact likelihood. -/
theorem probOutput_coherentLiftChannel_supported
    {Secret Error Star Rest : Type} [Fintype Error]
    [DecidableEq Error] [DecidableEq Star] [DecidableEq Rest]
    (errorSampler : ProbComp Error) (codec : CoherentLiftCodec Secret Error Star)
    (encodeRest : Secret → Error → Rest) (allowed : Error → Prop)
    [DecidablePred allowed]
    (supported : ∀ error, ¬allowed error → Pr[= error | errorSampler] = 0)
    (secret : Secret) (observation : CoherentObservation Star Rest) :
    Pr[= observation | coherentLiftChannel errorSampler codec encodeRest secret] =
      match codec.decodeStar secret observation.1 with
      | none => 0
      | some error =>
          if allowed error ∧ observation.2 = encodeRest secret error
          then Pr[= error | errorSampler] else 0 := by
  rw [probOutput_coherentLiftChannel]
  unfold coherentLiftLikelihood
  cases hdecode : codec.decodeStar secret observation.1 with
  | some error =>
    change (if observation.2 = encodeRest secret error
      then Pr[= error | errorSampler] else 0) =
      if allowed error ∧ observation.2 = encodeRest secret error
      then Pr[= error | errorSampler] else 0
    by_cases hallowed : allowed error
    · simp [hallowed]
    · rw [supported error hallowed]
      simp
  | none => rfl

/-- The exact complete-channel maximal-leakage mass is the sum of the largest coherent candidate
likelihood at each complete observation. -/
theorem channelMaximalLeakageMass_coherentLiftChannel
    {Secret Error Star Rest : Type}
    [Fintype Secret] [Fintype Error] [Fintype Star] [Fintype Rest]
    [DecidableEq Error] [DecidableEq Star] [DecidableEq Rest]
    (errorSampler : ProbComp Error) (codec : CoherentLiftCodec Secret Error Star)
    (encodeRest : Secret → Error → Rest) :
    channelMaximalLeakageMass
      (coherentLiftChannel errorSampler codec encodeRest) =
      ∑ observation, ⨆ secret,
        coherentLiftLikelihood errorSampler codec encodeRest secret observation := by
  unfold channelMaximalLeakageMass
  apply Finset.sum_congr rfl
  intro observation _
  congr 1
  funext secret
  exact probOutput_coherentLiftChannel errorSampler codec encodeRest secret observation

/-! ### The `q_star > 2B` arithmetic interface -/

/-- Coherent integer error vectors with a checked centered coordinate bound. -/
def BoundedCoherentError (Coordinate : Type) (bound : ℤ) :=
  {error : Coordinate → ℤ // ∀ coordinate, |error coordinate| ≤ bound}

/-- Reduction modulo a limb larger than twice the bound is injective on bounded coherent error
vectors.  This is the concrete arithmetic fact used to construct `CoherentLiftCodec`. -/
theorem boundedResidueEncoder_injective
    {Coordinate : Type} (modulus bound : ℤ)
    (hbound : 0 ≤ bound) (hmodulus : 2 * bound < modulus) :
    Function.Injective
      (fun error : BoundedCoherentError Coordinate bound ↦
        fun coordinate ↦ error.1 coordinate % modulus) := by
  intro left right heq
  apply Subtype.ext
  apply boundedCoherentLift_unique modulus bound left.1 right.1 hbound hmodulus
    left.2 right.2
  intro coordinate
  exact congrFun heq coordinate

/-- Candidate-codeword translation does not affect distinguished-limb injectivity. -/
theorem boundedShiftedResidueEncoder_injective
    {Secret Coordinate : Type} (modulus bound : ℤ)
    (mean : Secret → Coordinate → ℤ)
    (hbound : 0 ≤ bound) (hmodulus : 2 * bound < modulus)
    (secret : Secret) :
    Function.Injective
      (fun error : BoundedCoherentError Coordinate bound ↦
        fun coordinate ↦ (mean secret coordinate + error.1 coordinate) % modulus) := by
  intro left right heq
  apply Subtype.ext
  apply boundedCoherentLift_unique modulus bound left.1 right.1 hbound hmodulus
    left.2 right.2
  intro coordinate
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
  have hshift := congrFun heq coordinate
  have hzero := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hshift
  simpa only [add_sub_add_left_eq_sub] using hzero

/-- Noncomputable exact center-lift codec obtained from `q_star > 2B`. -/
noncomputable def boundedShiftedResidueCodec
    {Secret Coordinate : Type} (modulus bound : ℤ)
    (mean : Secret → Coordinate → ℤ)
    (hbound : 0 ≤ bound) (hmodulus : 2 * bound < modulus) :
    CoherentLiftCodec Secret (BoundedCoherentError Coordinate bound) (Coordinate → ℤ) := by
  letI : Nonempty (BoundedCoherentError Coordinate bound) :=
    ⟨⟨0, fun _ ↦ by simpa using hbound⟩⟩
  exact CoherentLiftCodec.ofInjective
    (fun secret error coordinate ↦
      (mean secret coordinate + error.1 coordinate) % modulus)
    (boundedShiftedResidueEncoder_injective modulus bound mean hbound hmodulus)

/-! ### CRT recombination invariance -/

/-- Total variation is exactly invariant under a public bijection. -/
theorem tvDist_map_equiv
    {Source Target : Type} (equiv : Source ≃ Target)
    (left right : ProbComp Source) :
    tvDist (equiv <$> left) (equiv <$> right) = tvDist left right := by
  apply le_antisymm
  · exact tvDist_map_le (m := ProbComp) equiv left right
  · have hreverse := tvDist_map_le (m := ProbComp) equiv.symm
      (equiv <$> left) (equiv <$> right)
    simpa only [Functor.map_map, Equiv.symm_apply_apply, id_map'] using hreverse

/-- Recombining all CRT limbs by an equivalence preserves conditional guessing exactly. -/
theorem conditionalGuessingProbability_crtRecombination
    {Secret CRT Recombined : Type} [DecidableEq Secret]
    (crt : CRT ≃ Recombined) (joint : ProbComp (Secret × CRT)) :
    conditionalGuessingProbability (mapJointSide crt joint) =
      conditionalGuessingProbability joint :=
  conditionalGuessingProbability_mapJointSide crt joint

/-- Every pairwise complete-channel distance is unchanged by CRT recombination. -/
theorem tvDist_crtRecombination
    {Secret CRT Recombined : Type} (crt : CRT ≃ Recombined)
    (channel : Secret → ProbComp CRT) (left right : Secret) :
    tvDist (crt <$> channel left) (crt <$> channel right) =
      tvDist (channel left) (channel right) :=
  tvDist_map_equiv crt _ _

/-- **CRT invariance and joint tree bound.**  Apply the tree theorem once to the complete coherent
CRT observation, then transport the result through the CRT recombination bijection. -/
theorem crtRecombinedWeightedTreeGuessingBound
    {Secret CRT Recombined : Type}
    [Fintype Secret] [Nonempty Secret] [Fintype CRT]
    [DecidableEq Secret] [DecidableEq CRT]
    (crt : CRT ≃ Recombined)
    (prior : ProbComp Secret) (channel : Secret → ProbComp CRT)
    (tree : SimpleGraph Secret) [Fintype tree.edgeSet]
    (isTree : tree.IsTree) (root : Secret) :
    (conditionalGuessingProbability
      (mapJointSide crt (conditionalChannelJoint prior channel))).toReal ≤
      Pr[= root | prior].toReal +
        ∑ edge ∈ tree.edgeFinset, weightedEdgeL1 prior channel edge := by
  rw [conditionalGuessingProbability_mapJointSide]
  exact weightedSpanningTreeGuessingBound prior channel tree isTree root

/-! ## Exact ternary covariance interfaces -/

/-- Closed form for the square covariance of independent symmetric ternary coefficients with
nonzero probability `p`. -/
def iidTernarySquareCovariance
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (dimension : ℕ) (p : ℝ) (evenProjection : Matrix Coordinate Coordinate ℝ) :
    Matrix Coordinate Coordinate ℝ :=
  (2 * (dimension : ℝ) * p ^ 2) • (1 : Matrix Coordinate Coordinate ℝ) +
    (2 * (p - 3 * p ^ 2)) • evenProjection

/-- Closed form for exact Hamming weight, where `p=w/n` and
`p₂=w(w-1)/(n(n-1))`. -/
def fixedWeightTernarySquareCovariance
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (dimension : ℕ) (p p₂ : ℝ) (evenProjection : Matrix Coordinate Coordinate ℝ) :
    Matrix Coordinate Coordinate ℝ :=
  (2 * (dimension : ℝ) * p₂) • (1 : Matrix Coordinate Coordinate ℝ) +
    (2 * (p - 3 * p₂)) • evenProjection

/-- Algebraic certificate for the four negacyclic multiplication-tensor identities used in the
ternary moment calculation. -/
structure NegacyclicTensorCertificate
    (Coordinate : Type) [Fintype Coordinate] [DecidableEq Coordinate] where
  dimension : ℕ
  tensor : Matrix Coordinate (Coordinate × Coordinate) ℝ
  swap : Matrix (Coordinate × Coordinate) (Coordinate × Coordinate) ℝ
  diagonalProjection : Matrix (Coordinate × Coordinate) (Coordinate × Coordinate) ℝ
  evenProjection : Matrix Coordinate Coordinate ℝ
  identityVector : Matrix (Coordinate × Coordinate) Unit ℝ
  tensor_mul_transpose :
    tensor * tensor.transpose =
      (dimension : ℝ) • (1 : Matrix Coordinate Coordinate ℝ)
  tensor_mul_swap : tensor * swap = tensor
  tensor_mul_identityVector : tensor * identityVector = 0
  tensor_diagonal_tensor_transpose :
    tensor * diagonalProjection * tensor.transpose = 2 • evenProjection

/-- Tensor covariance for independent symmetric ternary coordinates. -/
def iidTernaryTensorCovariance
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (p : ℝ)
    (swap diagonalProjection :
      Matrix (Coordinate × Coordinate) (Coordinate × Coordinate) ℝ) :=
  p ^ 2 • (1 + swap) + (p - 3 * p ^ 2) • diagonalProjection

/-- Tensor covariance for the exact-weight symmetric ternary law. -/
def fixedWeightTernaryTensorCovariance
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (p p₂ : ℝ)
    (swap diagonalProjection :
      Matrix (Coordinate × Coordinate) (Coordinate × Coordinate) ℝ)
    (identityVector : Matrix (Coordinate × Coordinate) Unit ℝ) :=
  p₂ • (1 + swap) +
    (p₂ - p ^ 2) • (identityVector * identityVector.transpose) +
    (p - 3 * p₂) • diagonalProjection

/-- Native matrix derivation of the IID square-covariance formula from the tensor identities and
the elementary fourth-moment tensor covariance. -/
theorem iidTernaryTensor_pushforward
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (certificate : NegacyclicTensorCertificate Coordinate) (p : ℝ) :
    certificate.tensor *
        iidTernaryTensorCovariance p certificate.swap certificate.diagonalProjection *
        certificate.tensor.transpose =
      iidTernarySquareCovariance certificate.dimension p certificate.evenProjection := by
  simp only [iidTernaryTensorCovariance, iidTernarySquareCovariance,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, certificate.tensor_mul_swap,
    certificate.tensor_mul_transpose, certificate.tensor_diagonal_tensor_transpose]
  module

/-- Native exact-weight square-covariance derivation.  The extra rank-one diagonal-mean term is
killed by `C vec(I)=0`. -/
theorem fixedWeightTernaryTensor_pushforward
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (certificate : NegacyclicTensorCertificate Coordinate) (p p₂ : ℝ) :
    certificate.tensor *
        fixedWeightTernaryTensorCovariance p p₂ certificate.swap
          certificate.diagonalProjection certificate.identityVector *
        certificate.tensor.transpose =
      fixedWeightTernarySquareCovariance certificate.dimension p p₂
        certificate.evenProjection := by
  simp only [fixedWeightTernaryTensorCovariance, fixedWeightTernarySquareCovariance,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, certificate.tensor_mul_swap,
    certificate.tensor_mul_transpose, certificate.tensor_diagonal_tensor_transpose,
    ← Matrix.mul_assoc, certificate.tensor_mul_identityVector, Matrix.zero_mul]
  module

/-- Full covariance expansion of a linear/quadratic codeword before using the vanishing mixed
third moments. -/
def linearQuadraticCodebookCovariance
    {Coordinate Output : Type} [Fintype Coordinate] [Fintype Output]
    (linear quadratic : Matrix Output Coordinate ℝ)
    (secretCovariance crossSecretSquare crossSquareSecret squareCovariance :
      Matrix Coordinate Coordinate ℝ) : Matrix Output Output ℝ :=
  linear * secretCovariance * linear.transpose +
    linear * crossSecretSquare * quadratic.transpose +
    quadratic * crossSquareSecret * linear.transpose +
    quadratic * squareCovariance * quadratic.transpose

/-- Vanishing linear--quadratic cross covariance removes both mixed blocks exactly. -/
theorem linearQuadraticCodebookCovariance_of_cross_eq_zero
    {Coordinate Output : Type} [Fintype Coordinate] [Fintype Output]
    (linear quadratic : Matrix Output Coordinate ℝ)
    (secretCovariance squareCovariance : Matrix Coordinate Coordinate ℝ) :
    linearQuadraticCodebookCovariance linear quadratic secretCovariance 0 0 squareCovariance =
      linear * secretCovariance * linear.transpose +
        quadratic * squareCovariance * quadratic.transpose := by
  simp [linearQuadraticCodebookCovariance]

/-- Proof-carrying statement of the exact ternary moment calculation.  All objects are finite
matrices; producing this certificate for a concrete sampler is the remaining finite combinatorial
moment calculation, while downstream covariance and information proofs use its checked fields. -/
structure ExactTernaryMomentCertificate
    (Coordinate : Type) [Fintype Coordinate] [DecidableEq Coordinate] where
  p : ℝ
  secretMean : Coordinate → ℝ
  squareMean : Coordinate → ℝ
  secretCovariance : Matrix Coordinate Coordinate ℝ
  crossSecretSquare : Matrix Coordinate Coordinate ℝ
  crossSquareSecret : Matrix Coordinate Coordinate ℝ
  squareCovariance : Matrix Coordinate Coordinate ℝ
  expectedSquareCovariance : Matrix Coordinate Coordinate ℝ
  secretMean_eq_zero : secretMean = 0
  secretCovariance_eq : secretCovariance = p • (1 : Matrix Coordinate Coordinate ℝ)
  crossSecretSquare_eq_zero : crossSecretSquare = 0
  crossSquareSecret_eq_zero : crossSquareSecret = 0
  squareCovariance_eq : squareCovariance = expectedSquareCovariance

/-- The exact codebook covariance `p Z Z* + G Sigma_Q G*`, with no mixed term. -/
theorem ExactTernaryMomentCertificate.codebookCovariance_eq
    {Coordinate Output : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    [Fintype Output]
    (certificate : ExactTernaryMomentCertificate Coordinate)
    (linear quadratic : Matrix Output Coordinate ℝ) :
    linearQuadraticCodebookCovariance linear quadratic
        certificate.secretCovariance certificate.crossSecretSquare
        certificate.crossSquareSecret certificate.squareCovariance =
      certificate.p • (linear * linear.transpose) +
        quadratic * certificate.expectedSquareCovariance * quadratic.transpose := by
  rw [certificate.secretCovariance_eq, certificate.crossSecretSquare_eq_zero,
    certificate.crossSquareSecret_eq_zero, certificate.squareCovariance_eq,
    linearQuadraticCodebookCovariance_of_cross_eq_zero]
  rw [Matrix.mul_smul, Matrix.smul_mul]
  simp

/-! ## Gaussian edge and leakage-averaged information certificates -/

/-- Analytic boundary for the equal-covariance continuous-Gaussian TV identity. -/
structure ContinuousGaussianEdgeDistanceCertificate
    (Secret : Type) where
  mahalanobisDistance : Secret → Secret → ℝ
  edgeDistance : Secret → Secret → ℝ
  standardNormalCDF : ℝ → ℝ
  exact_edge_distance : ∀ left right,
    edgeDistance left right =
      2 * standardNormalCDF (mahalanobisDistance left right / 2) - 1

/-- Certified exact Gaussian edge formula. -/
theorem ContinuousGaussianEdgeDistanceCertificate.edgeDistance_eq
    {Secret : Type} (certificate : ContinuousGaussianEdgeDistanceCertificate Secret)
    (left right : Secret) :
    certificate.edgeDistance left right =
      2 * certificate.standardNormalCDF
        (certificate.mahalanobisDistance left right / 2) - 1 :=
  certificate.exact_edge_distance left right

/-- The log-determinant expression `1/2 log₂ det(I + Sigma_N⁻¹ Sigma_mu)`.  For positive definite
noise covariance this is determinant-equivalent to the symmetric inverse-square-root form. -/
noncomputable def gaussianLogDetInformationBound
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (noiseCovariance codebookCovariance : Matrix Coordinate Coordinate ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.logb 2
    (Matrix.det (1 + noiseCovariance⁻¹ * codebookCovariance))

/-- Proof-carrying interface for the analytic Gaussian entropy-maximization and conditional
log-determinant steps.  Descriptor averaging and Fano arithmetic below are native. -/
structure LeakageAveragedGaussianInformationCertificate
    (Descriptor Coordinate : Type)
    [Fintype Descriptor] [DecidableEq Descriptor]
    [Fintype Coordinate] [DecidableEq Coordinate] where
  descriptorSampler : ProbComp Descriptor
  noiseCovariance : Descriptor → Matrix Coordinate Coordinate ℝ
  codebookCovariance : Descriptor → Matrix Coordinate Coordinate ℝ
  pointwiseInformation : Descriptor → ℝ
  information : ℝ
  secretEntropy : ℝ
  conditionalEntropy : ℝ
  success : ℝ
  logSupport : ℝ
  logSupport_pos : 0 < logSupport
  success_le_one : success ≤ 1
  pointwise_le_logDet : ∀ descriptor,
    pointwiseInformation descriptor ≤
      gaussianLogDetInformationBound (noiseCovariance descriptor)
        (codebookCovariance descriptor)
  information_le_average : information ≤
    ∑ descriptor,
      Pr[= descriptor | descriptorSampler].toReal * pointwiseInformation descriptor
  entropy_chain : conditionalEntropy = secretEntropy - information
  fano : conditionalEntropy ≤ 1 + (1 - success) * logSupport

/-- The analytic pointwise bounds imply the actual descriptor-averaged information bound. -/
theorem LeakageAveragedGaussianInformationCertificate.information_le_logDetAverage
    {Descriptor Coordinate : Type}
    [Fintype Descriptor] [DecidableEq Descriptor]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (certificate : LeakageAveragedGaussianInformationCertificate Descriptor Coordinate) :
    certificate.information ≤
      ∑ descriptor,
        Pr[= descriptor | certificate.descriptorSampler].toReal *
          gaussianLogDetInformationBound
            (certificate.noiseCovariance descriptor)
            (certificate.codebookCovariance descriptor) := by
  refine certificate.information_le_average.trans ?_
  apply Finset.sum_le_sum
  intro descriptor _
  exact mul_le_mul_of_nonneg_left (certificate.pointwise_le_logDet descriptor)
    ENNReal.toReal_nonneg

/-- Convert the leakage-averaged Gaussian certificate to the already-native finite Fano data. -/
noncomputable def LeakageAveragedGaussianInformationCertificate.toFanoData
    {Descriptor Coordinate : Type}
    [Fintype Descriptor] [DecidableEq Descriptor]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (certificate : LeakageAveragedGaussianInformationCertificate Descriptor Coordinate) :
    FiniteSupportFanoData where
  secretEntropy := certificate.secretEntropy
  information := certificate.information
  informationBound :=
    ∑ descriptor,
      Pr[= descriptor | certificate.descriptorSampler].toReal *
        gaussianLogDetInformationBound
          (certificate.noiseCovariance descriptor)
          (certificate.codebookCovariance descriptor)
  conditionalEntropy := certificate.conditionalEntropy
  success := certificate.success
  logSupport := certificate.logSupport
  logSupport_pos := certificate.logSupport_pos
  success_le_one := certificate.success_le_one
  information_le := certificate.information_le_logDetAverage
  entropy_chain := certificate.entropy_chain
  fano := certificate.fano

/-- **Leakage-averaged Gaussian information/Fano bound.** -/
theorem leakageAveragedGaussianFanoBound
    {Descriptor Coordinate : Type}
    [Fintype Descriptor] [DecidableEq Descriptor]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (certificate : LeakageAveragedGaussianInformationCertificate Descriptor Coordinate) :
    certificate.success ≤ min 1
      (1 - (certificate.secretEntropy -
        (∑ descriptor,
          Pr[= descriptor | certificate.descriptorSampler].toReal *
            gaussianLogDetInformationBound
              (certificate.noiseCovariance descriptor)
              (certificate.codebookCovariance descriptor)) - 1) /
        certificate.logSupport) :=
  finiteSupportFanoBound certificate.toFanoData

/-! ## Complete row-energy concentration boundary -/

/-- The complete canonical row energy `R_k=sum_j |sigma_k(w_j)|²`. -/
def completeCanonicalRowEnergy
    {Embedding Row Element : Type} [Fintype Row]
    (embedding : Embedding → Element → ℝ) (ratio : Row → Element)
    (coordinate : Embedding) : ℝ :=
  ∑ row, |embedding coordinate (ratio row)| ^ 2

/-- The exact singular-value identity now names the complete row energy explicitly. -/
theorem canonicalRatioBlockSingularValueSquared_eq_completeRowEnergy
    {Embedding Row Element : Type} [Fintype Embedding] [Fintype Row]
    (embedding : Embedding → Element → ℝ) (ratio : Row → Element) :
    canonicalRatioBlockSingularValueSquared embedding ratio =
      ⨆ coordinate, completeCanonicalRowEnergy embedding ratio coordinate := rfl

/-- Analytic boundary for Bernstein concentration of every complete row energy.  The finite
descriptor, good-event, and failure-probability statements are explicit and checkable. -/
structure CompleteRowEnergyConcentrationCertificate
    (Descriptor Embedding : Type)
    [Fintype Descriptor] [DecidableEq Descriptor]
    [Fintype Embedding] where
  descriptorSampler : ProbComp Descriptor
  rowEnergy : Descriptor → Embedding → ℝ
  upperBound : Descriptor → Embedding → ℝ
  good : Descriptor → Bool
  failure : ℝ
  failure_nonneg : 0 ≤ failure
  failure_probability_le :
    Pr[= false | good <$> descriptorSampler] ≤ ENNReal.ofReal failure
  rowEnergy_le : ∀ descriptor, good descriptor = true → ∀ coordinate,
    rowEnergy descriptor coordinate ≤ upperBound descriptor coordinate

/-- Certified simultaneous complete-row-energy bound. -/
theorem CompleteRowEnergyConcentrationCertificate.bound
    {Descriptor Embedding : Type}
    [Fintype Descriptor] [DecidableEq Descriptor] [Fintype Embedding]
    (certificate : CompleteRowEnergyConcentrationCertificate Descriptor Embedding)
    (descriptor : Descriptor) (hgood : certificate.good descriptor = true)
    (coordinate : Embedding) :
    certificate.rowEnergy descriptor coordinate ≤
      certificate.upperBound descriptor coordinate :=
  certificate.rowEnergy_le descriptor hgood coordinate

end

end FormalProof4FHE.RLWE.RankOneHNFLossinessSupportAware
