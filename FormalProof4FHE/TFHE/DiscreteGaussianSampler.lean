/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.FinitePMFCompiler
import FormalProof4FHE.Probability.ModularGaussian
import FormalProof4FHE.TFHE.SamplerReplacement

/-!
# Certified Discrete-Gaussian Samplers for TFHE

The exact modular discrete Gaussian is a mathematical `PMF`; native TFHE games require finite,
executable `ProbComp` samplers.  This module instantiates the generic finite ticket-table compiler
at the exact torus-scaled modular discrete Gaussian and carries its checked approximation error
through scalar and coefficientwise-ring translation bounds as well as the complete adaptive-TFHE
replacement bounds.

No ideal PMF is declared executable.  A `ScalarCertificate` contains a nonempty finite ticket
table and a proof of its TV error against `ModularGaussian.torusDistribution`.  Two independently
implemented tables certified against the same ideal distribution are therefore close by the sum
of their certificate errors.  Sampling `degree` coefficients independently lifts this to ring
errors with the standard `degree` hybrid factor.  Translating one executable table by a fixed
residual costs the corresponding ideal modular-Gaussian shift distance plus twice the certificate
error; this also lifts coefficientwise and feeds the native conditional-smudging layer.
-/

open OracleComp
open scoped ENNReal

namespace FormalProof4FHE.TFHE.DiscreteGaussianSampler

/-- A checked finite implementation of the exact torus-scaled modular discrete Gaussian. -/
abbrev ScalarCertificate (q : ℕ) [NeZero q]
    (alpha : ℝ) (halpha : 0 < alpha) :=
  FinitePMFCompiler.TicketTable.Certificate
    (ModularGaussian.torusDistribution q alpha halpha)

/-! ## Explicit uniform residue table -/

/-- A completely explicit ticket table containing every residue modulo `q` exactly once.  This
is useful as an executable approximation to a modular Gaussian whose width makes the ideal law
negligibly close to uniform. -/
def uniformResidueTable (q : ℕ) [NeZero q] :
    FinitePMFCompiler.TicketTable (ZMod q) where
  sizePred := q - 1
  tickets := ⟨List.ofFn (fun index : Fin q ↦ ZMod.finEquiv q index), by
    rw [List.length_ofFn]
    exact (Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne q))).symm⟩

@[simp]
theorem uniformResidueTable_ticketCount (q : ℕ) [NeZero q] :
    (uniformResidueTable q).ticketCount = q := by
  simp [uniformResidueTable, FinitePMFCompiler.TicketTable.ticketCount,
    Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne q))]

@[simp]
theorem uniformResidueTable_ticketValue (q : ℕ) [NeZero q]
    (ticket : Fin (uniformResidueTable q).ticketCount) :
    (uniformResidueTable q).ticketValue ticket =
      ZMod.finEquiv q (Fin.cast (uniformResidueTable_ticketCount q) ticket) := by
  change (List.ofFn (fun index : Fin q ↦ ZMod.finEquiv q index))[ticket.val]'_ = _
  rw [List.getElem_ofFn]
  rfl

/-- Sampling the explicit residue table is exactly uniform modulo `q`. -/
theorem uniformResidueTable_sampler_evalDist (q : ℕ) [NeZero q] :
    evalDist (uniformResidueTable q).sampler = evalDist ($ᵗ (ZMod q)) := by
  rw [FinitePMFCompiler.TicketTable.sampler_eq_ticketValue_map_uniform]
  apply evalDist_map_bijective_uniform_cross
  rw [show (uniformResidueTable q).ticketValue =
      fun ticket ↦ ZMod.finEquiv q
        (Fin.cast (uniformResidueTable_ticketCount q) ticket) by
    funext ticket
    exact uniformResidueTable_ticketValue q ticket]
  have hcast : Function.Bijective
      (Fin.cast (uniformResidueTable_ticketCount q)) := by
    constructor
    · exact Fin.cast_injective _
    · intro value
      refine ⟨Fin.cast (uniformResidueTable_ticketCount q).symm value, ?_⟩
      simp
  exact (ZMod.finEquiv q).bijective.comp hcast

/-- The PMF denoted by the explicit residue table is the exact uniform PMF. -/
theorem uniformResidueTable_outputPMF (q : ℕ) [NeZero q] :
    (uniformResidueTable q).outputPMF = PMF.uniformOfFintype (ZMod q) := by
  have hdist := uniformResidueTable_sampler_evalDist q
  have htable :
      (liftM (uniformResidueTable q).sampler : SPMF (ZMod q)) =
        liftM (uniformResidueTable q).outputPMF := by
    unfold FinitePMFCompiler.TicketTable.outputPMF
    rfl
  have hlift :
      (liftM (uniformResidueTable q).outputPMF : SPMF (ZMod q)) =
        liftM (PMF.uniformOfFintype (ZMod q)) := by
    rw [← htable]
    simpa only [evalDist_def, evalDist_uniformSample] using hdist
  ext residue
  have hprob := congrArg
    (fun distribution : SPMF (ZMod q) ↦ distribution residue) hlift
  simpa only [SPMF.liftM_apply] using hprob

/-- The explicit uniform table, certified against a torus-scaled modular Gaussian.  The
certificate error is the universal Gaussian-to-uniform translation bound; the sampler itself is
fully explicit and exactly uniform. -/
noncomputable def uniformResidueCertificate
    (q : ℕ) [NeZero q] (alpha : ℝ) (halpha : 0 < alpha) :
    ScalarCertificate q alpha halpha where
  table := uniformResidueTable q
  bound := ENNReal.ofReal (ModularGaussian.torusUniformBound q alpha halpha)
  bound_ne_top := ENNReal.ofReal_ne_top
  valid := by
    rw [← FinitePMFCompiler.TicketTable.etvDist_outputPMF_eq_certificateError,
      uniformResidueTable_outputPMF]
    have htv :
        PMF.tvDist (PMF.uniformOfFintype (ZMod q))
            (ModularGaussian.torusDistribution q alpha halpha) ≤
          ModularGaussian.torusUniformBound q alpha halpha := by
      rw [PMF.tvDist_comm]
      exact ModularGaussian.tvDist_torusDistribution_uniform_le q alpha halpha
    calc
      (PMF.uniformOfFintype (ZMod q)).etvDist
          (ModularGaussian.torusDistribution q alpha halpha) =
          ENNReal.ofReal
            (PMF.tvDist (PMF.uniformOfFintype (ZMod q))
              (ModularGaussian.torusDistribution q alpha halpha)) := by
        rw [PMF.tvDist]
        exact (ENNReal.ofReal_toReal (PMF.etvDist_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (ModularGaussian.torusUniformBound q alpha halpha) :=
        ENNReal.ofReal_le_ofReal htv

@[simp]
theorem uniformResidueCertificate_table
    (q : ℕ) [NeZero q] (alpha : ℝ) (halpha : 0 < alpha) :
    (uniformResidueCertificate q alpha halpha).table = uniformResidueTable q := rfl

@[simp]
theorem uniformResidueCertificate_bound
    (q : ℕ) [NeZero q] (alpha : ℝ) (halpha : 0 < alpha) :
    (uniformResidueCertificate q alpha halpha).bound =
      ENNReal.ofReal (ModularGaussian.torusUniformBound q alpha halpha) := rfl

/-- Specialize the generic finite pointwise checker to the exact modular discrete Gaussian.
Repeated residues in `table` encode the rational approximation weights. -/
noncomputable def certificateOfPointwise
    (q : ℕ) [NeZero q] (alpha : ℝ) (halpha : 0 < alpha)
    (table : FinitePMFCompiler.TicketTable (ZMod q))
    (pointwiseBound : ℝ≥0∞) (hpointwiseFinite : pointwiseBound ≠ ⊤)
    (hpointwise : ∀ residue : ZMod q,
      ENNReal.absDiff
        ((table.tickets.toList.count residue : ℝ≥0∞) /
          (table.ticketCount : ℝ≥0∞))
        (ModularGaussian.torusDistribution q alpha halpha residue) ≤
          pointwiseBound) :
    ScalarCertificate q alpha halpha :=
  FinitePMFCompiler.TicketTable.Certificate.ofPointwise
    table pointwiseBound hpointwiseFinite hpointwise

/-- The executable scalar sampler carried by a Gaussian certificate. -/
def scalarSampler {q : ℕ} [NeZero q] {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : ScalarCertificate q alpha halpha) : ProbComp (ZMod q) :=
  certificate.table.sampler

/-- The certificate's PMF denotation is within its checked bound of the exact modular discrete
Gaussian. -/
theorem pmf_tvDist_scalarTarget_le
    {q : ℕ} [NeZero q] {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : ScalarCertificate q alpha halpha) :
    PMF.tvDist certificate.table.outputPMF
        (ModularGaussian.torusDistribution q alpha halpha) ≤
      certificate.bound.toReal :=
  certificate.tvDist_le

/-- A fixed translation of the executable ticket sampler costs at most the corresponding ideal
modular-Gaussian translation plus two copies of the checked compilation error.  One copy moves
the executable distribution to the ideal before translation, and the other moves it back. -/
theorem addShiftDistance_scalarSampler_le
    {q : ℕ} [NeZero q] {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : ScalarCertificate q alpha halpha) (shift : ZMod q) :
    FormalProof4FHE.FiniteProduct.addShiftDistance
        (scalarSampler certificate) shift ≤
      2 * certificate.bound.toReal +
        ModularGaussian.shiftDistance
          (ModularGaussian.torusDistribution q alpha halpha) shift := by
  let executable := certificate.table.outputPMF
  let ideal := ModularGaussian.torusDistribution q alpha halpha
  let shiftedExecutable := ModularGaussian.translate shift executable
  let shiftedIdeal := ModularGaussian.translate shift ideal
  have hcompile : PMF.tvDist executable ideal ≤ certificate.bound.toReal := by
    exact certificate.tvDist_le
  have hshiftCompile : PMF.tvDist shiftedExecutable shiftedIdeal ≤
      certificate.bound.toReal := by
    exact (PMF.tvDist_map_le (fun value : ZMod q ↦ shift + value)
      executable ideal).trans hcompile
  have hcompileReverse : PMF.tvDist ideal executable ≤ certificate.bound.toReal := by
    rw [PMF.tvDist_comm]
    exact hcompile
  have hexecutable :=
    FinitePMFCompiler.TicketTable.tvDist_map_sampler_le_outputPMF
      certificate.table (fun value : ZMod q ↦ shift + value)
  calc
    FormalProof4FHE.FiniteProduct.addShiftDistance
        (scalarSampler certificate) shift ≤
        PMF.tvDist shiftedExecutable executable := by
      simpa only [FormalProof4FHE.FiniteProduct.addShiftDistance, scalarSampler,
        shiftedExecutable, ModularGaussian.translate, executable] using hexecutable
    _ ≤ PMF.tvDist shiftedExecutable shiftedIdeal +
          (PMF.tvDist shiftedIdeal ideal + PMF.tvDist ideal executable) :=
      (PMF.tvDist_triangle shiftedExecutable shiftedIdeal executable).trans
        (add_le_add le_rfl (PMF.tvDist_triangle shiftedIdeal ideal executable))
    _ ≤ certificate.bound.toReal +
          (ModularGaussian.shiftDistance ideal shift + certificate.bound.toReal) :=
      add_le_add hshiftCompile (add_le_add le_rfl hcompileReverse)
    _ = 2 * certificate.bound.toReal +
          ModularGaussian.shiftDistance
            (ModularGaussian.torusDistribution q alpha halpha) shift := by
      dsimp only [ideal]
      ring

/-- Sum of the two one-sided certificate errors against a shared ideal target. -/
noncomputable def pairBound
    {q : ℕ} [NeZero q] {alpha : ℝ} {halpha : 0 < alpha}
    (left right : ScalarCertificate q alpha halpha) : ℝ :=
  left.bound.toReal + right.bound.toReal

theorem pairBound_nonneg
    {q : ℕ} [NeZero q] {alpha : ℝ} {halpha : 0 < alpha}
    (left right : ScalarCertificate q alpha halpha) :
    0 ≤ pairBound left right := by
  exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- Two executable scalar implementations certified against the same exact Gaussian differ by
at most the sum of their checked approximation errors. -/
theorem tvDist_scalarSampler_le
    {q : ℕ} [NeZero q] {alpha : ℝ} {halpha : 0 < alpha}
    (left right : ScalarCertificate q alpha halpha) :
    tvDist (scalarSampler left) (scalarSampler right) ≤ pairBound left right := by
  exact FinitePMFCompiler.TicketTable.tvDist_samplers_le_of_common_target left right

/-- Exact coefficientwise ideal ring-error specification.  This remains a mathematical PMF and
is not used as executable code. -/
noncomputable def idealRingDistribution
    (q degree : ℕ) [NeZero q] (alpha : ℝ) (halpha : 0 < alpha) :
    PMF (RLWE.Rq q degree) :=
  LatticeCrypto.Poly.ofPi <$>
    ModularGaussian.iid degree
      (ModularGaussian.torusDistribution q alpha halpha)

/-- Rebuild the vector-backed native ring carrier from its coefficient function.  Naming this
typed map keeps later ticket-space normal forms in the native `Rq` carrier. -/
def ringErrorFromCoefficients {q degree : ℕ}
    (values : Fin degree → ZMod q) : RLWE.Rq q degree :=
  LatticeCrypto.Poly.ofPi values

/-- Executable ring-error sampler obtained from independent certified scalar tickets. -/
def ringSampler
    {q : ℕ} [NeZero q] (degree : ℕ) {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : ScalarCertificate q alpha halpha) :
    ProbComp (RLWE.Rq q degree) :=
  LatticeCrypto.Poly.ofPi <$>
    ProbComp.sampleIID degree (scalarSampler certificate)

theorem ringSampler_eq_ringErrorFromCoefficients
    {q : ℕ} [NeZero q] (degree : ℕ) {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : ScalarCertificate q alpha halpha) :
    ringSampler degree certificate =
      ringErrorFromCoefficients <$>
        ProbComp.sampleIID degree (scalarSampler certificate) := by
  rfl

/-- The ring sampler carried by the explicit uniform-residue Gaussian certificate is exactly
uniform on the complete native coefficient ring. -/
theorem ringSampler_uniformResidueCertificate_evalDist_eq_uniform
    (q degree : ℕ) [NeZero q] (alpha : ℝ) (halpha : 0 < alpha) :
    evalDist
        (ringSampler degree (uniformResidueCertificate q alpha halpha)) =
      evalDist ($ᵗ (RLWE.Rq q degree)) := by
  let assemble : (Fin degree → ZMod q) → RLWE.Rq q degree :=
    LatticeCrypto.Poly.ofPi
  have hscalar :
      evalDist
          (scalarSampler (uniformResidueCertificate q alpha halpha)) =
        evalDist ($ᵗ (ZMod q)) := by
    simpa only [scalarSampler, uniformResidueCertificate_table] using
      uniformResidueTable_sampler_evalDist q
  have hcoefficients :=
    FormalProof4FHE.FiniteProduct.evalDist_fin_mOfFn_congr degree
      (fun _ ↦ scalarSampler (uniformResidueCertificate q alpha halpha))
      (fun _ ↦ ($ᵗ (ZMod q))) (fun _ ↦ hscalar)
  have hiidUniform :=
    FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
      (alpha := ZMod q) degree
  have hassemble : Function.Bijective assemble := by
    apply Function.bijective_iff_has_inverse.mpr
    exact ⟨LatticeCrypto.Poly.toPi, LatticeCrypto.Poly.toPi_ofPi,
      LatticeCrypto.Poly.ofPi_toPi⟩
  calc
    evalDist
        (ringSampler degree (uniformResidueCertificate q alpha halpha)) =
        evalDist (assemble <$>
          ProbComp.sampleIID degree
            (scalarSampler (uniformResidueCertificate q alpha halpha))) := rfl
    _ = evalDist (assemble <$>
          ProbComp.sampleIID degree ($ᵗ (ZMod q))) :=
      evalDist_map_eq_of_evalDist_eq hcoefficients assemble
    _ = evalDist (assemble <$> ($ᵗ (Fin degree → ZMod q))) :=
      evalDist_map_eq_of_evalDist_eq hiidUniform assemble
    _ = evalDist ($ᵗ (RLWE.Rq q degree)) :=
      evalDist_map_bijective_uniform_cross
        (α := Fin degree → ZMod q) (β := RLWE.Rq q degree)
        assemble hassemble

/-- Uniform ticket indices used by all coefficients of one executable ring error. -/
abbrev RingTicketCoins
    {q : ℕ} [NeZero q] (degree : ℕ) {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : ScalarCertificate q alpha halpha) :=
  Fin degree → Fin certificate.table.ticketCount

/-- Deterministically decode a complete coefficient-ticket vector into one ring error. -/
def ringErrorFromTickets
    {q : ℕ} [NeZero q] (degree : ℕ) {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : ScalarCertificate q alpha halpha)
    (tickets : RingTicketCoins degree certificate) : RLWE.Rq q degree :=
  ringErrorFromCoefficients fun coefficient ↦
    certificate.table.ticketValue (tickets coefficient)

/-- The executable ring sampler is exactly the deterministic image of a uniform finite ticket
vector. -/
theorem ringSampler_evalDist_eq_uniformTickets
    {q : ℕ} [NeZero q] (degree : ℕ) {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : ScalarCertificate q alpha halpha) :
    evalDist (ringSampler degree certificate) =
      evalDist (ringErrorFromTickets degree certificate <$>
        ($ᵗ (RingTicketCoins degree certificate))) := by
  let Ticket := Fin certificate.table.ticketCount
  let decode : Fin degree → Ticket → ZMod q := fun _ ticket ↦
    certificate.table.ticketValue ticket
  have hPointwise :
      Fin.mOfFn degree (fun _ ↦ scalarSampler certificate) =
        (fun tickets coefficient ↦ decode coefficient (tickets coefficient)) <$>
          Fin.mOfFn degree (fun _ ↦ ($ᵗ Ticket : ProbComp Ticket)) := by
    rw [FormalProof4FHE.FiniteProduct.map_fin_mOfFn]
    unfold scalarSampler decode Ticket
    rw [certificate.table.sampler_eq_ticketValue_map_uniform]
  have hUniform := FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
    (alpha := Ticket) degree
  rw [ringSampler_eq_ringErrorFromCoefficients]
  unfold ProbComp.sampleIID
  rw [hPointwise]
  have hMapped := evalDist_map_eq_of_evalDist_eq hUniform
    (ringErrorFromTickets degree certificate)
  rw [Functor.map_map]
  have hDecode :
      (fun tickets ↦ ringErrorFromCoefficients
          (fun coefficient ↦ decode coefficient (tickets coefficient))) =
        ringErrorFromTickets degree certificate := by
    funext tickets
    rfl
  rw [hDecode]
  exact hMapped

/-- Uniform scalar-ticket indices for every coefficient of every ring error in a finite
vector. -/
abbrev RingErrorVectorTicketCoins
    {q : ℕ} [NeZero q] (count degree : ℕ) {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : ScalarCertificate q alpha halpha) :=
  Fin count → RingTicketCoins degree certificate

/-- Decode all coefficient tickets in a finite vector of ring errors. -/
def ringErrorVectorFromTickets
    {q : ℕ} [NeZero q] (count degree : ℕ) {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : ScalarCertificate q alpha halpha)
    (tickets : RingErrorVectorTicketCoins count degree certificate) :
    Fin count → RLWE.Rq q degree :=
  fun row ↦ ringErrorFromTickets degree certificate (tickets row)

/-- Independent executable ring errors are exactly a deterministic image of the uniform nested
ticket space. -/
theorem sampleIID_ringSampler_evalDist_eq_uniformTickets
    {q : ℕ} [NeZero q] (count degree : ℕ) {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : ScalarCertificate q alpha halpha) :
    evalDist (ProbComp.sampleIID count (ringSampler degree certificate)) =
      evalDist (ringErrorVectorFromTickets count degree certificate <$>
        ($ᵗ (RingErrorVectorTicketCoins count degree certificate))) := by
  let One := RingTicketCoins degree certificate
  let decode := ringErrorFromTickets degree certificate
  have hCoordinate :
      evalDist (ringSampler degree certificate) =
        evalDist (decode <$> ($ᵗ One)) := by
    simpa only [decode, One] using
      (ringSampler_evalDist_eq_uniformTickets degree certificate)
  have hProduct :
      evalDist (Fin.mOfFn count fun _ ↦ ringSampler degree certificate) =
        evalDist (Fin.mOfFn count fun _ ↦ decode <$> ($ᵗ One)) := by
    apply FormalProof4FHE.FiniteProduct.evalDist_fin_mOfFn_congr
    intro row
    exact hCoordinate
  have hPointwise := FormalProof4FHE.FiniteProduct.map_fin_mOfFn count
    (fun _ ↦ ($ᵗ One : ProbComp One)) (fun _ ↦ decode)
  have hUniform := FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
    (alpha := One) count
  have hMapped := evalDist_map_eq_of_evalDist_eq hUniform
    (ringErrorVectorFromTickets count degree certificate)
  unfold ProbComp.sampleIID
  calc
    _ = evalDist (Fin.mOfFn count fun _ ↦ decode <$> ($ᵗ One)) := hProduct
    _ = evalDist
        (ringErrorVectorFromTickets count degree certificate <$>
          Fin.mOfFn count (fun _ ↦ ($ᵗ One : ProbComp One))) := by
      rw [← hPointwise]
      rfl
    _ = _ := hMapped

/-- Coefficientwise addition commutes with rebuilding a vector-backed negacyclic polynomial. -/
theorem add_ofPi_eq_ofPi_add
    {q degree : ℕ} (shift : RLWE.Rq q degree) (values : Fin degree → ZMod q) :
    let rebuilt : RLWE.Rq q degree := LatticeCrypto.Poly.ofPi values
    let shifted : RLWE.Rq q degree := LatticeCrypto.Poly.ofPi
      (fun coefficient ↦ LatticeCrypto.Poly.toPi shift coefficient + values coefficient)
    shift + rebuilt = shifted := by
  dsimp only
  apply LatticeCrypto.Poly.ext_get_eq
  intro coefficient
  simpa [RLWE.negacyclicRing, LatticeCrypto.Poly.toPi,
      LatticeCrypto.Poly.ofPi, LatticeCrypto.vectorNegacyclicRing_backend,
      LatticeCrypto.vectorBackend, Vector.get] using
    (LatticeCrypto.NegacyclicRing.coeff_add (RLWE.negacyclicRing q degree)
      shift (LatticeCrypto.Poly.ofPi values) coefficient)

/-- Translating a coefficientwise ring sampler costs at most the sum of the executable scalar
translation costs of the residual polynomial's coefficients. -/
theorem addShiftDistance_ringSampler_le_sum_scalar
    {q : ℕ} [NeZero q] (degree : ℕ) {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : ScalarCertificate q alpha halpha) (shift : RLWE.Rq q degree) :
    FormalProof4FHE.FiniteProduct.addShiftDistance
        (ringSampler degree certificate) shift ≤
      ∑ coefficient, FormalProof4FHE.FiniteProduct.addShiftDistance
        (scalarSampler certificate) (LatticeCrypto.Poly.toPi shift coefficient) := by
  let scalar := scalarSampler certificate
  let coefficients := LatticeCrypto.Poly.toPi shift
  let vectors := ProbComp.sampleIID degree scalar
  have hshifted :
      (fun value : RLWE.Rq q degree ↦ shift + value) <$>
          ringSampler degree certificate =
        LatticeCrypto.Poly.ofPi <$>
          ((fun values ↦ coefficients + values) <$> vectors) := by
    unfold ringSampler
    simp only [Functor.map_map, scalar, vectors, coefficients]
    congr 1
    funext values
    exact add_ofPi_eq_ofPi_add shift values
  calc
    FormalProof4FHE.FiniteProduct.addShiftDistance
        (ringSampler degree certificate) shift =
        tvDist
          (LatticeCrypto.Poly.ofPi <$>
            ((fun values ↦ coefficients + values) <$> vectors))
          (LatticeCrypto.Poly.ofPi <$> vectors) := by
      rw [FormalProof4FHE.FiniteProduct.addShiftDistance, hshifted]
      rfl
    _ ≤ tvDist ((fun values ↦ coefficients + values) <$> vectors) vectors :=
      tvDist_map_le (m := ProbComp) LatticeCrypto.Poly.ofPi _ _
    _ ≤ ∑ coefficient, FormalProof4FHE.FiniteProduct.addShiftDistance
          scalar (coefficients coefficient) := by
      exact FormalProof4FHE.FiniteProduct.tvDist_add_fin_mOfFn_le_sum
        degree scalar coefficients
    _ = ∑ coefficient, FormalProof4FHE.FiniteProduct.addShiftDistance
          (scalarSampler certificate) (LatticeCrypto.Poly.toPi shift coefficient) := by
      rfl

/-- Fully certified coefficientwise discrete-Gaussian bound for translating one native ring
error.  Every coefficient pays its ideal modular-Gaussian shift cost and twice the finite ticket
compiler error. -/
theorem addShiftDistance_ringSampler_le_sum_ideal
    {q : ℕ} [NeZero q] (degree : ℕ) {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : ScalarCertificate q alpha halpha) (shift : RLWE.Rq q degree) :
    FormalProof4FHE.FiniteProduct.addShiftDistance
        (ringSampler degree certificate) shift ≤
      ∑ coefficient,
        (2 * certificate.bound.toReal +
          ModularGaussian.shiftDistance
            (ModularGaussian.torusDistribution q alpha halpha)
            (LatticeCrypto.Poly.toPi shift coefficient)) := by
  exact (addShiftDistance_ringSampler_le_sum_scalar degree certificate shift).trans
    (Finset.sum_le_sum fun coefficient _ ↦
      addShiftDistance_scalarSampler_le certificate
        (LatticeCrypto.Poly.toPi shift coefficient))

/-- Coefficientwise compilation lifts the scalar common-target bound with a `degree` hybrid
factor. -/
theorem tvDist_ringSampler_le
    {q : ℕ} [NeZero q] (degree : ℕ) {alpha : ℝ} {halpha : 0 < alpha}
    (left right : ScalarCertificate q alpha halpha) :
    tvDist (ringSampler degree left) (ringSampler degree right) ≤
      (degree : ℝ) * pairBound left right := by
  calc
    tvDist (ringSampler degree left) (ringSampler degree right) ≤
        tvDist
          (ProbComp.sampleIID degree (scalarSampler left))
          (ProbComp.sampleIID degree (scalarSampler right)) :=
      tvDist_map_le (m := ProbComp) LatticeCrypto.Poly.ofPi _ _
    _ ≤ (degree : ℝ) *
        tvDist (scalarSampler left) (scalarSampler right) :=
      SamplerReplacement.tvDist_sampleIID_le degree _ _
    _ ≤ (degree : ℝ) * pairBound left right :=
      mul_le_mul_of_nonneg_left (tvDist_scalarSampler_le left right)
        (Nat.cast_nonneg degree)

/-- Fully explicit BRK/KSK/adaptive-input accounting for certified discrete-Gaussian tables.

The three certificate pairs may use distinct Gaussian widths.  Ring certificates are compiled
coefficientwise, hence the additional `degree` factor in the bootstrapping-key term. -/
theorem adaptiveReplacementCost_le_certificates
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ) [NeZero q]
    {ringAlpha keySwitchAlpha inputAlpha : ℝ}
    {hringAlpha : 0 < ringAlpha}
    {hkeySwitchAlpha : 0 < keySwitchAlpha}
    {hinputAlpha : 0 < inputAlpha}
    (ringLeft ringRight : ScalarCertificate q ringAlpha hringAlpha)
    (keySwitchLeft keySwitchRight :
      ScalarCertificate q keySwitchAlpha hkeySwitchAlpha)
    (inputLeft inputRight : ScalarCertificate q inputAlpha hinputAlpha) :
    SamplerReplacement.adaptiveReplacementCost q degree ringRank tgswLevels lweDimension
        keySwitchLevels queryCount
        (ringSampler degree ringLeft) (ringSampler degree ringRight)
        (scalarSampler keySwitchLeft) (scalarSampler keySwitchRight)
        (scalarSampler inputLeft) (scalarSampler inputRight) ≤
      ((SamplerReplacement.bootstrappingErrorCount ringRank tgswLevels lweDimension : ℝ) *
          ((degree : ℝ) * pairBound ringLeft ringRight) +
        (SamplerReplacement.keySwitchErrorCount ringRank degree keySwitchLevels : ℝ) *
          pairBound keySwitchLeft keySwitchRight) +
        (queryCount : ℝ) * pairBound inputLeft inputRight := by
  exact SamplerReplacement.adaptiveReplacementCost_le
    q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount
    (ringSampler degree ringLeft) (ringSampler degree ringRight)
    (scalarSampler keySwitchLeft) (scalarSampler keySwitchRight)
    (scalarSampler inputLeft) (scalarSampler inputRight)
    ((degree : ℝ) * pairBound ringLeft ringRight)
    (pairBound keySwitchLeft keySwitchRight)
    (pairBound inputLeft inputRight)
    (tvDist_ringSampler_le degree ringLeft ringRight)
    (tvDist_scalarSampler_le keySwitchLeft keySwitchRight)
    (tvDist_scalarSampler_le inputLeft inputRight)

end FormalProof4FHE.TFHE.DiscreteGaussianSampler
