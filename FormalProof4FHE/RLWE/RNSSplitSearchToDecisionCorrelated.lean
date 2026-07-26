/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.QuadraticKDMBinaryTernary
import Mathlib.Data.ZMod.Basic

/-!
# RNS/NTT Search-to-Decision with Coherent Errors and Leakage

This module formalizes the finite algebraic and probability-theoretic content of
`rns_split_search_to_decision_correlated.tex`.

The RNS carrier is heterogeneous: limb `i` has its own field `K i`, and a ring element is a
dependent table `(i : Limb) -> Slot -> K i`.  Thus the development does not identify distinct
RNS primes with one common field.  It proves:

* projection of a coherent full-RNS HNF block to any limb/NTT coordinate;
* the correct-candidate identity and the wrong-candidate permutation after conditioning on an
  arbitrary state containing every other limb, every other slot, the complete coherent error,
  and arbitrary leakage;
* exact probability transport through an arbitrary sampler of that conditioned state;
* secret-shift rerandomization for non-target coordinates;
* deterministic recovery of the complete RNS secret from one recovered limb and a coherent
  liftable HNF anchor;
* injectivity, and hence liftability, of coefficientwise binary and centered-ternary anchors in
  every `ZMod q_i` limb when `q_i > 2`;
* the two-level limb/slot hybrid endpoints and the telescoping adjacent-gap lemma;
* diagonal slot automorphisms and their coordinate action; and
* the exact masked-quadratic compiler over the heterogeneous RNS product.

The TeX theorem also contains an asymptotic running-time assertion based on candidate
enumeration, acceptance-probability estimation, and amplification.  The current finite-game
library has no cost semantics for oracle calls.  Accordingly the final computational theorem
uses the checked `SplitSearchToDecisionCertificate` interface already used by the quadratic-KDM
development.  The local facts needed to construct that certificate are proved here; its
estimation loss and query bound remain explicit certificate fields rather than hidden axioms.
-/

open OracleComp

namespace FormalProof4FHE.RLWE.RNSSplitSearchToDecisionCorrelated

noncomputable section

/-! ## Heterogeneous split RNS carrier -/

/-- The complete split RNS/NTT carrier.  Different limbs may use genuinely different fields. -/
abbrev RNS (Limb Slot : Type) (K : Limb → Type) :=
  (limb : Limb) → Slot → K limb

/-- One complete NTT limb. -/
abbrev LimbValue (Slot : Type) (K : Type) := Slot → K

/-- RNS-limb projection. -/
def projectLimb {Limb Slot : Type} {K : Limb → Type}
    (value : RNS Limb Slot K) (limb : Limb) : LimbValue Slot (K limb) :=
  value limb

/-- RNS/NTT coordinate projection. -/
def projectCoordinate {Limb Slot : Type} {K : Limb → Type}
    (value : RNS Limb Slot K) (limb : Limb) (slot : Slot) : K limb :=
  value limb slot

/-- An explicit split-ring decomposition.  In a concrete cyclotomic instantiation `sourceRing`
is `R / Q R`, while the target is the full product of split prime-field powers. -/
structure Decomposition (SourceRing Limb Slot : Type) (K : Limb → Type)
    [CommRing SourceRing] [∀ limb, CommRing (K limb)] where
  equiv : SourceRing ≃+* RNS Limb Slot K

/-! ## Coherent HNF blocks -/

/-- All errors and public leakage sampled jointly.  No product structure or independence is
imposed inside this object. -/
structure ErrorState (R Row Leakage : Type) where
  anchorError : R
  rowError : Row → R
  leakage : Leakage

/-- A public HNF block `(Lambda,b0,{(c_j,d_j)}_j)`. -/
structure Block (R Row Leakage : Type) where
  leakage : Leakage
  anchor : R
  coefficient : Row → R
  body : Row → R

@[ext]
theorem Block.ext
    {R Row Leakage : Type} {left right : Block R Row Leakage}
    (hLeakage : left.leakage = right.leakage)
    (hAnchor : left.anchor = right.anchor)
    (hCoefficient : left.coefficient = right.coefficient)
    (hBody : left.body = right.body) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Assemble a real coherent HNF block for fixed hidden values. -/
def realBlock {R Row Leakage : Type} [CommRing R]
    (secret : R) (state : ErrorState R Row Leakage) (coefficient : Row → R) :
    Block R Row Leakage where
  leakage := state.leakage
  anchor := secret + state.anchorError
  coefficient := coefficient
  body := fun row ↦ coefficient row * secret + state.rowError row

/-- Assemble the random endpoint for fixed leakage and uniform payload values. -/
def randomBlock {R Row Leakage : Type}
    (leakage : Leakage) (anchor : R) (coefficient body : Row → R) :
    Block R Row Leakage where
  leakage := leakage
  anchor := anchor
  coefficient := coefficient
  body := body

/-- Project a full split-RNS block to one field coordinate, retaining its leakage separately. -/
def projectBlockCoordinate
    {Limb Slot Row Leakage : Type} {K : Limb → Type}
    (limb : Limb) (slot : Slot) (block : Block (RNS Limb Slot K) Row Leakage) :
    Leakage × QuadraticKDM.CoordinateView (K limb) Row :=
  (block.leakage,
    (block.anchor limb slot,
      (fun row ↦ block.coefficient row limb slot,
        fun row ↦ block.body row limb slot)))

/-- Projection of a coherent full-RNS real block is exactly the one-field HNF coordinate used by
the candidate test.  All cross-limb correlation remains in the unprojected `state`. -/
theorem projectBlockCoordinate_realBlock
    {Limb Slot Row Leakage : Type} {K : Limb → Type}
    [∀ limb, CommRing (K limb)]
    (limb : Limb) (slot : Slot) (secret : RNS Limb Slot K)
    (state : ErrorState (RNS Limb Slot K) Row Leakage)
    (coefficient : Row → RNS Limb Slot K) :
    projectBlockCoordinate limb slot (realBlock secret state coefficient) =
      (state.leakage,
        QuadraticKDM.coordinateReal (secret limb slot)
          (state.anchorError limb slot) (fun row ↦ state.rowError row limb slot)
          (fun row ↦ coefficient row limb slot)) := by
  rfl

/-! ## Candidate test with arbitrary coherent side information -/

/-- Attach arbitrary fixed side information to the wrong-candidate coordinate map. -/
def wrongCandidateWithSideInfo
    {K Row SideInfo : Type} [CommRing K]
    (secret candidate anchorError : K) (rowError : Row → K) (sideInfo : SideInfo)
    (coins : QuadraticKDM.CoordinateView K Row) :
    SideInfo × QuadraticKDM.CoordinateView K Row :=
  (sideInfo,
    QuadraticKDM.wrongCandidateMap secret candidate anchorError rowError coins)

/-- Conditioned on arbitrary side information, a wrong candidate produces an exactly uniform
coordinate.  `SideInfo` can contain all other limbs and slots and the complete coherent error and
leakage state. -/
theorem wrongCandidateWithSideInfo_evalDist_eq_uniform
    {K Row SideInfo : Type} [Field K]
    [Fintype K] [DecidableEq K] [Fintype Row] [DecidableEq Row]
    [SampleableType K]
    (secret candidate anchorError : K) (rowError : Row → K) (sideInfo : SideInfo)
    (hWrong : candidate ≠ secret) :
    evalDist (wrongCandidateWithSideInfo secret candidate anchorError rowError sideInfo <$>
        ($ᵗ (QuadraticKDM.CoordinateView K Row))) =
      evalDist ((fun view ↦ (sideInfo, view)) <$>
        ($ᵗ (QuadraticKDM.CoordinateView K Row))) := by
  have hCoordinate := QuadraticKDM.wrongCandidate_evalDist_eq_uniform
    secret candidate anchorError rowError hWrong
  let finish := fun view : QuadraticKDM.CoordinateView K Row ↦
    (pure (sideInfo, view) : ProbComp (SideInfo × QuadraticKDM.CoordinateView K Row))
  calc
    evalDist (wrongCandidateWithSideInfo secret candidate anchorError rowError sideInfo <$>
        ($ᵗ (QuadraticKDM.CoordinateView K Row))) =
      evalDist ((QuadraticKDM.wrongCandidateMap secret candidate anchorError rowError <$>
          ($ᵗ (QuadraticKDM.CoordinateView K Row))) >>= finish) := by
        simp [wrongCandidateWithSideInfo, finish, map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist (($ᵗ (QuadraticKDM.CoordinateView K Row)) >>= finish) := by
      rw [evalDist_bind, hCoordinate, ← evalDist_bind]
    _ = evalDist ((fun view ↦ (sideInfo, view)) <$>
        ($ᵗ (QuadraticKDM.CoordinateView K Row))) := by
      simp [finish, map_eq_bind_pure_comp]

/-- The conditioned theorem remains exact after sampling an arbitrary joint state.  In
particular, no independence between its error coordinates or leakage components is used. -/
theorem wrongCandidate_jointState_evalDist_eq_uniform
    {K Row State : Type} [Field K]
    [Fintype K] [DecidableEq K] [Fintype Row] [DecidableEq Row]
    [SampleableType K]
    (stateSampler : ProbComp State)
    (secret candidate anchorError : State → K) (rowError : State → Row → K)
    (hWrong : ∀ state, candidate state ≠ secret state) :
    evalDist (stateSampler >>= fun state ↦
        wrongCandidateWithSideInfo (secret state) (candidate state) (anchorError state)
            (rowError state) state <$>
          ($ᵗ (QuadraticKDM.CoordinateView K Row))) =
      evalDist (stateSampler >>= fun state ↦
        (fun view ↦ (state, view)) <$>
          ($ᵗ (QuadraticKDM.CoordinateView K Row))) := by
  refine evalDist_bind_congr' stateSampler fun state ↦ ?_
  exact wrongCandidateWithSideInfo_evalDist_eq_uniform
    (secret state) (candidate state) (anchorError state) (rowError state) state (hWrong state)

/-- Attach arbitrary fixed side information to the correct-candidate experiment. -/
theorem correctCandidateWithSideInfo_evalDist_eq_freshReal
    {K Row SideInfo : Type} [Field K]
    [Fintype K] [DecidableEq K] [Fintype Row] [DecidableEq Row]
    [SampleableType K]
    (secret anchorError : K) (rowError coefficient : Row → K) (sideInfo : SideInfo) :
    evalDist (($ᵗ (K × (Row → K))) >>= fun coins ↦
        pure (sideInfo,
          QuadraticKDM.candidateTransform secret coins.1 coins.2
            (QuadraticKDM.coordinateReal secret anchorError rowError coefficient))) =
      evalDist (($ᵗ (K × (Row → K))) >>= fun fresh ↦
        pure (sideInfo,
          QuadraticKDM.coordinateReal fresh.1 anchorError rowError fresh.2)) := by
  have hCoordinate := QuadraticKDM.correctCandidate_evalDist_eq_freshReal
    secret anchorError rowError coefficient
  let finish := fun view : QuadraticKDM.CoordinateView K Row ↦
    (pure (sideInfo, view) : ProbComp (SideInfo × QuadraticKDM.CoordinateView K Row))
  calc
    evalDist (($ᵗ (K × (Row → K))) >>= fun coins ↦
        pure (sideInfo,
          QuadraticKDM.candidateTransform secret coins.1 coins.2
            (QuadraticKDM.coordinateReal secret anchorError rowError coefficient))) =
      evalDist ((($ᵗ (K × (Row → K))) >>= fun coins ↦
        pure (QuadraticKDM.candidateTransform secret coins.1 coins.2
          (QuadraticKDM.coordinateReal secret anchorError rowError coefficient))) >>= finish) := by
        simp [finish]
    _ = evalDist ((($ᵗ (K × (Row → K))) >>= fun fresh ↦
        pure (QuadraticKDM.coordinateReal fresh.1 anchorError rowError fresh.2)) >>= finish) := by
      rw [evalDist_bind, hCoordinate, ← evalDist_bind]
    _ = evalDist (($ᵗ (K × (Row → K))) >>= fun fresh ↦
        pure (sideInfo,
          QuadraticKDM.coordinateReal fresh.1 anchorError rowError fresh.2)) := by
      simp [finish]

/-- The correct-candidate identity also lifts through an arbitrary coherent state sampler. -/
theorem correctCandidate_jointState_evalDist_eq_freshReal
    {K Row State : Type} [Field K]
    [Fintype K] [DecidableEq K] [Fintype Row] [DecidableEq Row]
    [SampleableType K]
    (stateSampler : ProbComp State)
    (secret anchorError : State → K)
    (rowError coefficient : State → Row → K) :
    evalDist (stateSampler >>= fun state ↦
        ($ᵗ (K × (Row → K))) >>= fun coins ↦
          pure (state,
            QuadraticKDM.candidateTransform (secret state) coins.1 coins.2
              (QuadraticKDM.coordinateReal (secret state) (anchorError state)
                (rowError state) (coefficient state)))) =
      evalDist (stateSampler >>= fun state ↦
        ($ᵗ (K × (Row → K))) >>= fun fresh ↦
          pure (state,
            QuadraticKDM.coordinateReal fresh.1 (anchorError state)
              (rowError state) fresh.2)) := by
  refine evalDist_bind_congr' stateSampler fun state ↦ ?_
  exact correctCandidateWithSideInfo_evalDist_eq_freshReal
    (secret state) (anchorError state) (rowError state) (coefficient state) state

/-! ## Secret shifts for non-target coordinates -/

/-- Shift the hidden secret represented by one HNF coordinate while retaining its exact error. -/
def secretShiftCoordinate {K Row : Type} [CommRing K]
    (shift : K) (source : QuadraticKDM.CoordinateView K Row) :
    QuadraticKDM.CoordinateView K Row :=
  (source.1 + shift,
    (source.2.1, fun row ↦ source.2.2 row + source.2.1 row * shift))

/-- The public secret shift changes `x` to `x+r` and leaves every error coordinate unchanged. -/
theorem secretShiftCoordinate_real
    {K Row : Type} [CommRing K]
    (secret shift anchorError : K) (rowError coefficient : Row → K) :
    secretShiftCoordinate shift
        (QuadraticKDM.coordinateReal secret anchorError rowError coefficient) =
      QuadraticKDM.coordinateReal (secret + shift) anchorError rowError coefficient := by
  apply Prod.ext
  · dsimp [secretShiftCoordinate, QuadraticKDM.coordinateReal]
    ring
  · apply Prod.ext
    · rfl
    · funext row
      dsimp [secretShiftCoordinate, QuadraticKDM.coordinateReal]
      ring

/-- Explicit inverse of the public secret shift. -/
def secretShiftCoordinateInv {K Row : Type} [CommRing K]
    (shift : K) (source : QuadraticKDM.CoordinateView K Row) :
    QuadraticKDM.CoordinateView K Row :=
  (source.1 - shift,
    (source.2.1, fun row ↦ source.2.2 row - source.2.1 row * shift))

@[simp]
theorem secretShiftCoordinateInv_secretShiftCoordinate
    {K Row : Type} [CommRing K]
    (shift : K) (source : QuadraticKDM.CoordinateView K Row) :
    secretShiftCoordinateInv shift (secretShiftCoordinate shift source) = source := by
  rcases source with ⟨anchor, coefficient, body⟩
  apply Prod.ext
  · simp [secretShiftCoordinateInv, secretShiftCoordinate]
  · apply Prod.ext
    · rfl
    · funext row
      simp [secretShiftCoordinateInv, secretShiftCoordinate]

@[simp]
theorem secretShiftCoordinate_secretShiftCoordinateInv
    {K Row : Type} [CommRing K]
    (shift : K) (source : QuadraticKDM.CoordinateView K Row) :
    secretShiftCoordinate shift (secretShiftCoordinateInv shift source) = source := by
  rcases source with ⟨anchor, coefficient, body⟩
  apply Prod.ext
  · simp [secretShiftCoordinateInv, secretShiftCoordinate]
  · apply Prod.ext
    · rfl
    · funext row
      simp [secretShiftCoordinateInv, secretShiftCoordinate]

/-- For fixed shift, the public coordinate shift is a permutation. -/
theorem secretShiftCoordinate_bijective
    {K Row : Type} [CommRing K] (shift : K) :
    Function.Bijective (secretShiftCoordinate (Row := Row) shift) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨secretShiftCoordinateInv shift,
      secretShiftCoordinateInv_secretShiftCoordinate shift,
      secretShiftCoordinate_secretShiftCoordinateInv shift⟩

/-- Translation by a fixed secret is a permutation of a field. -/
theorem addFixed_bijective {K : Type} [AddCommGroup K] (secret : K) :
    Function.Bijective (fun shift : K ↦ secret + shift) := by
  let inverse : K → K := fun fresh ↦ fresh - secret
  refine Function.bijective_iff_has_inverse.mpr ⟨inverse, ?_, ?_⟩
  · intro shift
    simp [inverse]
  · intro fresh
    simp [inverse]

/-- A uniform shift replaces a fixed coordinate secret by a fresh uniform secret, without
resampling or decorrelating its errors. -/
theorem uniformSecretShift_evalDist_eq_freshReal
    {K Row : Type} [Field K]
    [Fintype K] [DecidableEq K] [SampleableType K]
    (secret anchorError : K) (rowError coefficient : Row → K) :
    evalDist (($ᵗ K) >>= fun shift ↦
        pure (secretShiftCoordinate shift
          (QuadraticKDM.coordinateReal secret anchorError rowError coefficient))) =
      evalDist (($ᵗ K) >>= fun freshSecret ↦
        pure (QuadraticKDM.coordinateReal freshSecret anchorError rowError coefficient)) := by
  have hShift :
    evalDist ((fun shift : K ↦ secret + shift) <$> ($ᵗ K)) = evalDist ($ᵗ K) :=
    evalDist_map_bijective_uniform_cross
      (α := K) (β := K)
      (fun shift : K ↦ secret + shift) (addFixed_bijective secret)
  calc
    evalDist (($ᵗ K) >>= fun shift ↦
        pure (secretShiftCoordinate shift
          (QuadraticKDM.coordinateReal secret anchorError rowError coefficient))) =
      evalDist (($ᵗ K) >>= fun shift ↦
        pure (QuadraticKDM.coordinateReal (secret + shift)
          anchorError rowError coefficient)) := by
      refine evalDist_bind_congr' ($ᵗ K) fun shift ↦ ?_
      rw [secretShiftCoordinate_real]
    _ = evalDist (((fun shift : K ↦ secret + shift) <$> ($ᵗ K)) >>= fun freshSecret ↦
        pure (QuadraticKDM.coordinateReal freshSecret anchorError rowError coefficient)) := by
      simp [map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist (($ᵗ K) >>= fun freshSecret ↦
        pure (QuadraticKDM.coordinateReal freshSecret anchorError rowError coefficient)) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hShift _

/-! ## Coherent liftable anchors -/

/-- A common small object reduced into every RNS limb, together with a partial lift from each
limb.  `Good` is the no-wrap/tail event. -/
structure LiftableAnchor (Small Limb Slot : Type) (K : Limb → Type)
    [∀ limb, AddCommGroup (K limb)] where
  reduce : Small → RNS Limb Slot K
  lift : (limb : Limb) → LimbValue Slot (K limb) → Option Small
  Good : Small → Prop
  lift_reduce : ∀ limb small, Good small → lift limb (reduce small limb) = some small

/-- Probability of the anchor lift-failure event under a concrete small-anchor sampler. -/
noncomputable def liftFailureProbability
    {Small Limb Slot : Type} {K : Limb → Type}
    [∀ limb, AddCommGroup (K limb)]
    (anchor : LiftableAnchor Small Limb Slot K) (smallSampler : ProbComp Small) : ℝ :=
  (Pr[(fun small ↦ ¬ anchor.Good small) | smallSampler]).toReal

/-- Paper-level `(S,tau)` liftability as an explicit finite probability bound. -/
def LiftFailureBound
    {Small Limb Slot : Type} {K : Limb → Type}
    [∀ limb, AddCommGroup (K limb)]
    (anchor : LiftableAnchor Small Limb Slot K) (smallSampler : ProbComp Small)
    (tau : ℝ) : Prop :=
  liftFailureProbability anchor smallSampler ≤ tau

/-- Recover a complete RNS secret from its public HNF anchor and one recovered limb. -/
def recoverFromLimb
    {Small Limb Slot : Type} {K : Limb → Type}
    [∀ limb, AddCommGroup (K limb)]
    (anchor : LiftableAnchor Small Limb Slot K) (limb : Limb)
    (publicAnchor : RNS Limb Slot K) (recoveredLimb : LimbValue Slot (K limb)) :
    Option (RNS Limb Slot K) := do
  let small ← anchor.lift limb (recoveredLimb - publicAnchor limb)
  return publicAnchor + anchor.reduce small

/-- **One recovered limb determines the full HNF secret.**  This is the deterministic good-event
statement; a concrete anchor law separately bounds the probability of `not (Good small)`. -/
theorem recoverFromLimb_eq_some
    {Small Limb Slot : Type} {K : Limb → Type}
    [∀ limb, CommRing (K limb)]
    (anchor : LiftableAnchor Small Limb Slot K) (limb : Limb)
    (secret : RNS Limb Slot K) (small : Small) (hGood : anchor.Good small) :
    recoverFromLimb anchor limb (secret - anchor.reduce small) (secret limb) =
      some secret := by
  have hDifference :
      secret limb - (secret - anchor.reduce small) limb = anchor.reduce small limb := by
    funext slot
    simp
  simp [recoverFromLimb, anchor.lift_reduce limb small hGood]

/-- Recovery stated directly for a real HNF block whose anchor error is the reduction of one
common negated small polynomial. -/
theorem recoverFromLimb_realBlock
    {Small Limb Slot Row Leakage : Type} {K : Limb → Type}
    [∀ limb, CommRing (K limb)]
    (anchor : LiftableAnchor Small Limb Slot K) (limb : Limb)
    (secret : RNS Limb Slot K) (small : Small) (hGood : anchor.Good small)
    (state : ErrorState (RNS Limb Slot K) Row Leakage)
    (coefficient : Row → RNS Limb Slot K)
    (hAnchorError : state.anchorError = -anchor.reduce small) :
    recoverFromLimb anchor limb (realBlock secret state coefficient).anchor (secret limb) =
      some secret := by
  rw [show (realBlock secret state coefficient).anchor = secret - anchor.reduce small by
    change secret + state.anchorError = secret - anchor.reduce small
    rw [hAnchorError, sub_eq_add_neg]]
  exact recoverFromLimb_eq_some anchor limb secret small hGood

/-! ### Generic finite lifting from limbwise injectivity -/

/-- A canonical partial inverse.  It returns `none` exactly outside the image. -/
noncomputable def partialInverse {Domain Codomain : Type} (encode : Domain → Codomain)
    (value : Codomain) : Option Domain := by
  letI : Decidable (∃ input, encode input = value) := Classical.propDecidable _
  exact if h : ∃ input, encode input = value then some (Classical.choose h) else none

/-- On the image of an injective encoding, `partialInverse` recovers the unique input. -/
theorem partialInverse_apply_of_injective
    {Domain Codomain : Type} (encode : Domain → Codomain)
    (hInjective : Function.Injective encode) (input : Domain) :
    partialInverse encode (encode input) = some input := by
  have hExists : ∃ candidate, encode candidate = encode input := ⟨input, rfl⟩
  simp only [partialInverse, dif_pos hExists, Option.some.injEq]
  apply hInjective
  exact Classical.choose_spec hExists

/-- Limbwise injectivity of one common encoding constructs a coherent liftable anchor. -/
def LiftableAnchor.ofInjective
    {Small Limb Slot : Type} {K : Limb → Type}
    [∀ limb, AddCommGroup (K limb)]
    (reduce : Small → RNS Limb Slot K)
    (hInjective : ∀ limb, Function.Injective (fun small ↦ reduce small limb)) :
    LiftableAnchor Small Limb Slot K where
  reduce := reduce
  lift := fun limb ↦ partialInverse (fun small ↦ reduce small limb)
  Good := fun _ ↦ True
  lift_reduce := by
    intro limb small _hGood
    exact partialInverse_apply_of_injective _ (hInjective limb) small

/-! ### Binary and centered-ternary anchors over `ZMod q_i` -/

/-- Coefficientwise digits, with `L=2` for binary and `L=3` for centered ternary. -/
abbrev DigitAnchor (L : ℕ) (Coefficient : Type) := Coefficient → Fin L

/-- Embed a digit vector in `ZMod q`, subtracting a public centering offset. -/
def digitResidue (q L offset : ℕ) {Coefficient : Type}
    (secret : DigitAnchor L Coefficient) : Coefficient → ZMod q :=
  fun coefficient ↦ ((secret coefficient).val : ZMod q) - (offset : ZMod q)

/-- Bounded natural digits embed injectively modulo `q` whenever `L <= q`. -/
theorem digitResidue_injective
    {q L offset : ℕ} {Coefficient : Type} (hLq : L ≤ q) :
    Function.Injective (digitResidue (Coefficient := Coefficient) q L offset) := by
  intro left right hEqual
  funext coefficient
  apply Fin.ext
  have hCoordinate := congrFun hEqual coefficient
  have hCast : ((left coefficient).val : ZMod q) = ((right coefficient).val : ZMod q) := by
    simpa [digitResidue] using congrArg (fun value : ZMod q ↦ value + (offset : ZMod q)) hCoordinate
  have hModulo :=
    (ZMod.natCast_eq_natCast_iff' (left coefficient).val (right coefficient).val q).mp hCast
  have hLeft : (left coefficient).val < q := (left coefficient).isLt.trans_le hLq
  have hRight : (right coefficient).val < q := (right coefficient).isLt.trans_le hLq
  simpa [Nat.mod_eq_of_lt hLeft, Nat.mod_eq_of_lt hRight] using hModulo

/-- Explicit inverse-NTT/NTT coordinate equivalences for every limb.  The domain is the
coefficient representation used to define binary or ternary smallness; the codomain is the split
NTT-slot representation used by the candidate hybrid. -/
structure NTTCoordinates (Limb Coefficient Slot : Type) (modulus : Limb → ℕ) where
  equiv : (limb : Limb) →
    (Coefficient → ZMod (modulus limb)) ≃ (Slot → ZMod (modulus limb))

/-- Reduce one coefficient digit vector coherently into every RNS prime and then apply that
limb's NTT coordinate equivalence. -/
def digitAnchorReduction
    {Limb Coefficient Slot : Type} (modulus : Limb → ℕ)
    (ntt : NTTCoordinates Limb Coefficient Slot modulus) (L offset : ℕ)
    (secret : DigitAnchor L Coefficient) :
    RNS Limb Slot (fun limb ↦ ZMod (modulus limb)) :=
  fun limb ↦ ntt.equiv limb (digitResidue (modulus limb) L offset secret)

/-- Every limb projection of the coherent digit reduction is injective when the alphabet fits in
that limb modulus. -/
theorem digitAnchorReduction_limb_injective
    {Limb Coefficient Slot : Type} (modulus : Limb → ℕ)
    (ntt : NTTCoordinates Limb Coefficient Slot modulus) (L offset : ℕ)
    (hFits : ∀ limb, L ≤ modulus limb) (limb : Limb) :
    Function.Injective
      (fun secret : DigitAnchor L Coefficient ↦
        digitAnchorReduction modulus ntt L offset secret limb) :=
  (ntt.equiv limb).injective.comp (digitResidue_injective (hFits limb))

/-- Generic liftable coherent digit anchor. -/
def digitLiftableAnchor
    {Limb Coefficient Slot : Type} (modulus : Limb → ℕ)
    (ntt : NTTCoordinates Limb Coefficient Slot modulus) (L offset : ℕ)
    (hFits : ∀ limb, L ≤ modulus limb) :
    LiftableAnchor (DigitAnchor L Coefficient) Limb Slot (fun limb ↦ ZMod (modulus limb)) :=
  LiftableAnchor.ofInjective (digitAnchorReduction modulus ntt L offset)
    (digitAnchorReduction_limb_injective modulus ntt L offset hFits)

/-- Binary anchors are deterministically liftable from every limb for `q_i > 2`. -/
def binaryLiftableAnchor
    {Limb Coefficient Slot : Type} (modulus : Limb → ℕ)
    (ntt : NTTCoordinates Limb Coefficient Slot modulus)
    (hModulus : ∀ limb, 2 < modulus limb) :
    LiftableAnchor (DigitAnchor 2 Coefficient) Limb Slot
      (fun limb ↦ ZMod (modulus limb)) :=
  digitLiftableAnchor modulus ntt 2 0 (fun limb ↦ by
    have h := hModulus limb
    omega)

/-- Centered ternary digits `{-1,0,1}` are represented as `digit-1` and are deterministically
liftable from every limb for `q_i > 2`. -/
def ternaryLiftableAnchor
    {Limb Coefficient Slot : Type} (modulus : Limb → ℕ)
    (ntt : NTTCoordinates Limb Coefficient Slot modulus)
    (hModulus : ∀ limb, 2 < modulus limb) :
    LiftableAnchor (DigitAnchor 3 Coefficient) Limb Slot
      (fun limb ↦ ZMod (modulus limb)) :=
  digitLiftableAnchor modulus ntt 3 1 (fun limb ↦ by
    have h := hModulus limb
    omega)

/-! ## Two-level limb/NTT hybrid -/

/-- Lexicographic limb-major position `(i,nu) |-> nu + N*i`. -/
def coordinatePosition {limbCount slotCount : ℕ}
    (limb : Fin limbCount) (slot : Fin slotCount) : Fin (limbCount * slotCount) :=
  finProdFinEquiv (limb, slot)

@[simp]
theorem coordinatePosition_val {limbCount slotCount : ℕ}
    (limb : Fin limbCount) (slot : Fin slotCount) :
    (coordinatePosition limb slot).val = slot.val + slotCount * limb.val := by
  rfl

/-- Replace the first `replaced` RNS/NTT coordinates of `real` by the corresponding coordinates
of `random`.  The order is limb-major and then slot-major. -/
def hybridRNS
    {limbCount slotCount : ℕ} {K : Fin limbCount → Type}
    (replaced : ℕ) (real random : RNS (Fin limbCount) (Fin slotCount) K) :
    RNS (Fin limbCount) (Fin slotCount) K :=
  fun limb slot ↦
    if (coordinatePosition limb slot).val < replaced then random limb slot else real limb slot

/-- The zero-coordinate hybrid is the real value. -/
@[simp]
theorem hybridRNS_zero
    {limbCount slotCount : ℕ} {K : Fin limbCount → Type}
    (real random : RNS (Fin limbCount) (Fin slotCount) K) :
    hybridRNS 0 real random = real := by
  funext limb slot
  simp [hybridRNS]

/-- After all `s*N` coordinates have been replaced, the hybrid is the random value. -/
@[simp]
theorem hybridRNS_all
    {limbCount slotCount : ℕ} {K : Fin limbCount → Type}
    (real random : RNS (Fin limbCount) (Fin slotCount) K) :
    hybridRNS (limbCount * slotCount) real random = random := by
  funext limb slot
  simp only [hybridRNS]
  rw [if_pos (coordinatePosition limb slot).isLt]

/-- Immediately before position `k`, that coordinate retains its real value. -/
theorem hybridRNS_at_position
    {limbCount slotCount : ℕ} {K : Fin limbCount → Type}
    (real random : RNS (Fin limbCount) (Fin slotCount) K)
    (position : Fin (limbCount * slotCount)) :
    hybridRNS position.val real random (finProdFinEquiv.symm position).1
        (finProdFinEquiv.symm position).2 =
      real (finProdFinEquiv.symm position).1 (finProdFinEquiv.symm position).2 := by
  have hPosition :
      coordinatePosition (finProdFinEquiv.symm position).1
          (finProdFinEquiv.symm position).2 = position :=
    finProdFinEquiv.apply_symm_apply position
  simp only [hybridRNS]
  rw [congrArg Fin.val hPosition]
  simp

/-- Immediately after position `k`, that coordinate has its random value. -/
theorem hybridRNS_at_position_succ
    {limbCount slotCount : ℕ} {K : Fin limbCount → Type}
    (real random : RNS (Fin limbCount) (Fin slotCount) K)
    (position : Fin (limbCount * slotCount)) :
    hybridRNS (position.val + 1) real random (finProdFinEquiv.symm position).1
        (finProdFinEquiv.symm position).2 =
      random (finProdFinEquiv.symm position).1 (finProdFinEquiv.symm position).2 := by
  have hPosition :
      coordinatePosition (finProdFinEquiv.symm position).1
          (finProdFinEquiv.symm position).2 = position :=
    finProdFinEquiv.apply_symm_apply position
  simp only [hybridRNS]
  rw [congrArg Fin.val hPosition]
  simp

/-- Every coordinate other than `k` is identical in the two adjacent hybrids. -/
theorem hybridRNS_succ_apply_of_ne
    {limbCount slotCount : ℕ} {K : Fin limbCount → Type}
    (real random : RNS (Fin limbCount) (Fin slotCount) K)
    (position : Fin (limbCount * slotCount)) (limb : Fin limbCount) (slot : Fin slotCount)
    (hNe : coordinatePosition limb slot ≠ position) :
    hybridRNS (position.val + 1) real random limb slot =
      hybridRNS position.val real random limb slot := by
  have hValNe : (coordinatePosition limb slot).val ≠ position.val := by
    intro hEqual
    exact hNe (Fin.ext hEqual)
  simp only [hybridRNS]
  by_cases hBefore : (coordinatePosition limb slot).val < position.val
  · rw [if_pos (hBefore.trans_le (Nat.le_succ _)), if_pos hBefore]
  · have hAfter : position.val < (coordinatePosition limb slot).val := by omega
    rw [if_neg (by omega), if_neg (by omega)]

/-- Hybridize only the right-hand sides of a public HNF block.  Leakage and all public
coefficients are retained exactly. -/
def hybridBlock
    {limbCount slotCount : ℕ} {K : Fin limbCount → Type} {Row Leakage : Type}
    (replaced : ℕ) (real : Block (RNS (Fin limbCount) (Fin slotCount) K) Row Leakage)
    (randomAnchor : RNS (Fin limbCount) (Fin slotCount) K)
    (randomBody : Row → RNS (Fin limbCount) (Fin slotCount) K) :
    Block (RNS (Fin limbCount) (Fin slotCount) K) Row Leakage where
  leakage := real.leakage
  anchor := hybridRNS replaced real.anchor randomAnchor
  coefficient := real.coefficient
  body := fun row ↦ hybridRNS replaced (real.body row) (randomBody row)

/-- `H_(1,0)` is the real block. -/
@[simp]
theorem hybridBlock_zero
    {limbCount slotCount : ℕ} {K : Fin limbCount → Type} {Row Leakage : Type}
    (real : Block (RNS (Fin limbCount) (Fin slotCount) K) Row Leakage)
    (randomAnchor : RNS (Fin limbCount) (Fin slotCount) K)
    (randomBody : Row → RNS (Fin limbCount) (Fin slotCount) K) :
    hybridBlock 0 real randomAnchor randomBody = real := by
  apply Block.ext <;> simp [hybridBlock]

/-- `H_(s,N)` is the random-right-hand-side block, with the original uniform public
coefficients retained. -/
@[simp]
theorem hybridBlock_all
    {limbCount slotCount : ℕ} {K : Fin limbCount → Type} {Row Leakage : Type}
    (real : Block (RNS (Fin limbCount) (Fin slotCount) K) Row Leakage)
    (randomAnchor : RNS (Fin limbCount) (Fin slotCount) K)
    (randomBody : Row → RNS (Fin limbCount) (Fin slotCount) K) :
    hybridBlock (limbCount * slotCount) real randomAnchor randomBody =
      randomBlock real.leakage randomAnchor real.coefficient randomBody := by
  apply Block.ext <;> simp [hybridBlock, randomBlock]

/-! ### Telescoping hybrid gap -/

/-- The endpoint gap is at most the sum of all adjacent hybrid gaps. -/
theorem abs_sub_le_sum_adjacent (values : ℕ → ℝ) (count : ℕ) :
    |values 0 - values count| ≤
      ∑ index ∈ Finset.range count, |values index - values (index + 1)| := by
  rw [← Finset.sum_range_sub' values count]
  exact Finset.abs_sum_le_sum_abs
    (fun index ↦ values index - values (index + 1)) (Finset.range count)

/-- If there is at least one transition, one adjacent hybrid has at least the average endpoint
gap.  Instantiating `count=s*N` gives the `epsilon/(sN)` transition in the TeX proof. -/
theorem exists_adjacent_gap_ge_average
    (values : ℕ → ℝ) (count : ℕ) (hCount : 0 < count) :
    ∃ index : Fin count,
      |values 0 - values count| / (count : ℝ) ≤
        |values index.val - values (index.val + 1)| := by
  let endpointGap := |values 0 - values count|
  have hConstantSum :
      (∑ _index ∈ Finset.range count, endpointGap / (count : ℝ)) = endpointGap := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have hSum :
      (∑ _index ∈ Finset.range count, endpointGap / (count : ℝ)) ≤
        ∑ index ∈ Finset.range count, |values index - values (index + 1)| := by
    rw [hConstantSum]
    exact abs_sub_le_sum_adjacent values count
  obtain ⟨index, hIndex, hGap⟩ :=
    Finset.exists_le_of_sum_le
      (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hCount)) hSum
  exact ⟨⟨index, Finset.mem_range.mp hIndex⟩, hGap⟩

/-- Two-level RNS/NTT specialization of the average-gap theorem. -/
theorem exists_rns_ntt_adjacent_gap
    (values : ℕ → ℝ) (limbCount slotCount : ℕ)
    (hLimbCount : 0 < limbCount) (hSlotCount : 0 < slotCount) :
    ∃ position : Fin (limbCount * slotCount),
      |values 0 - values (limbCount * slotCount)| /
          ((limbCount * slotCount : ℕ) : ℝ) ≤
        |values position.val - values (position.val + 1)| := by
  exact exists_adjacent_gap_ge_average values (limbCount * slotCount)
    (Nat.mul_pos hLimbCount hSlotCount)

/-! ## Diagonal automorphism equivariance -/

/-- Apply one slot permutation simultaneously in every RNS limb.  This is a ring equivalence;
there is deliberately no operation that transforms just one limb. -/
def diagonalSlotEquiv
    {Limb Slot : Type} {K : Limb → Type} [∀ limb, Semiring (K limb)]
    (permutation : Equiv.Perm Slot) :
    RNS Limb Slot K ≃+* RNS Limb Slot K where
  toFun := fun value limb slot ↦ value limb (permutation.symm slot)
  invFun := fun value limb slot ↦ value limb (permutation slot)
  left_inv := by
    intro value
    funext limb slot
    simp
  right_inv := by
    intro value
    funext limb slot
    simp
  map_mul' := by
    intro left right
    rfl
  map_add' := by
    intro left right
    rfl

/-- Coordinate action of the diagonal slot automorphism. -/
@[simp]
theorem diagonalSlotEquiv_apply_permutation
    {Limb Slot : Type} {K : Limb → Type} [∀ limb, Semiring (K limb)]
    (permutation : Equiv.Perm Slot) (value : RNS Limb Slot K)
    (limb : Limb) (slot : Slot) :
    diagonalSlotEquiv permutation value limb (permutation slot) = value limb slot := by
  simp [diagonalSlotEquiv]

/-- A family of diagonal automorphisms, its induced leakage action, and slot transitivity. -/
structure AutomorphismAction (GroupIndex Slot Leakage : Type) where
  slotPermutation : GroupIndex → Equiv.Perm Slot
  leakagePermutation : GroupIndex → Equiv.Perm Leakage
  transitive : ∀ source target : Slot,
    ∃ element, slotPermutation element source = target

/-- Apply an automorphism diagonally to the complete coherent error/leakage state. -/
def actErrorState
    {GroupIndex Limb Slot Row Leakage : Type} {K : Limb → Type}
    [∀ limb, Semiring (K limb)]
    (action : AutomorphismAction GroupIndex Slot Leakage) (element : GroupIndex)
    (state : ErrorState (RNS Limb Slot K) Row Leakage) :
    ErrorState (RNS Limb Slot K) Row Leakage where
  anchorError := diagonalSlotEquiv (action.slotPermutation element) state.anchorError
  rowError := fun row ↦ diagonalSlotEquiv (action.slotPermutation element) (state.rowError row)
  leakage := action.leakagePermutation element state.leakage

/-- Apply the same diagonal automorphism to a complete public block and its leakage. -/
def actBlock
    {GroupIndex Limb Slot Row Leakage : Type} {K : Limb → Type}
    [∀ limb, Semiring (K limb)]
    (action : AutomorphismAction GroupIndex Slot Leakage) (element : GroupIndex)
    (block : Block (RNS Limb Slot K) Row Leakage) :
    Block (RNS Limb Slot K) Row Leakage where
  leakage := action.leakagePermutation element block.leakage
  anchor := diagonalSlotEquiv (action.slotPermutation element) block.anchor
  coefficient := fun row ↦
    diagonalSlotEquiv (action.slotPermutation element) (block.coefficient row)
  body := fun row ↦ diagonalSlotEquiv (action.slotPermutation element) (block.body row)

/-- The diagonal public action commutes exactly with real HNF block assembly. -/
theorem actBlock_realBlock
    {GroupIndex Limb Slot Row Leakage : Type} {K : Limb → Type}
    [∀ limb, CommRing (K limb)]
    (action : AutomorphismAction GroupIndex Slot Leakage) (element : GroupIndex)
    (secret : RNS Limb Slot K) (state : ErrorState (RNS Limb Slot K) Row Leakage)
    (coefficient : Row → RNS Limb Slot K) :
    actBlock action element (realBlock secret state coefficient) =
      realBlock
        (diagonalSlotEquiv (action.slotPermutation element) secret)
        (actErrorState action element state)
        (fun row ↦ diagonalSlotEquiv (action.slotPermutation element) (coefficient row)) := by
  apply Block.ext
  · rfl
  · simp [actBlock, realBlock, actErrorState]
  · rfl
  · funext row
    simp [actBlock, realBlock, actErrorState]

/-! ### Affine-complement action for binary anchors -/

/-- A diagonal automorphism family together with an additive secret correction.  For binary
coefficient secrets the correction is the usual complement polynomial on the coordinates whose
coefficient action is negated. -/
structure AffineAutomorphismAction
    (GroupIndex Limb Slot Leakage : Type) (K : Limb → Type)
    [∀ limb, Semiring (K limb)] extends AutomorphismAction GroupIndex Slot Leakage where
  shift : GroupIndex → RNS Limb Slot K

/-- Error/leakage action compatible with changing the auxiliary secret from `X` to
`sigma(X)+tau`.  The HNF anchor error changes from `e0` to `sigma(e0)-tau`; terminal errors are
only transformed by `sigma`. -/
def affineActErrorState
    {GroupIndex Limb Slot Row Leakage : Type} {K : Limb → Type}
    [∀ limb, CommRing (K limb)]
    (action : AffineAutomorphismAction GroupIndex Limb Slot Leakage K)
    (element : GroupIndex) (state : ErrorState (RNS Limb Slot K) Row Leakage) :
    ErrorState (RNS Limb Slot K) Row Leakage where
  anchorError :=
    diagonalSlotEquiv (action.slotPermutation element) state.anchorError - action.shift element
  rowError := fun row ↦ diagonalSlotEquiv (action.slotPermutation element) (state.rowError row)
  leakage := action.leakagePermutation element state.leakage

/-- Public affine source action.  Its body correction is the exact term needed for the shifted
auxiliary secret `sigma(X)+tau`. -/
def affineActBlock
    {GroupIndex Limb Slot Row Leakage : Type} {K : Limb → Type}
    [∀ limb, CommRing (K limb)]
    (action : AffineAutomorphismAction GroupIndex Limb Slot Leakage K)
    (element : GroupIndex) (block : Block (RNS Limb Slot K) Row Leakage) :
    Block (RNS Limb Slot K) Row Leakage where
  leakage := action.leakagePermutation element block.leakage
  anchor := diagonalSlotEquiv (action.slotPermutation element) block.anchor
  coefficient := fun row ↦
    diagonalSlotEquiv (action.slotPermutation element) (block.coefficient row)
  body := fun row ↦
    diagonalSlotEquiv (action.slotPermutation element) (block.body row) +
      diagonalSlotEquiv (action.slotPermutation element) (block.coefficient row) *
        action.shift element

/-- **Binary affine-complement HNF identity.**  The complete public block action commutes with
real assembly under the shifted auxiliary secret and the corrected coherent anchor error. -/
theorem affineActBlock_realBlock
    {GroupIndex Limb Slot Row Leakage : Type} {K : Limb → Type}
    [∀ limb, CommRing (K limb)]
    (action : AffineAutomorphismAction GroupIndex Limb Slot Leakage K)
    (element : GroupIndex) (secret : RNS Limb Slot K)
    (state : ErrorState (RNS Limb Slot K) Row Leakage)
    (coefficient : Row → RNS Limb Slot K) :
    affineActBlock action element (realBlock secret state coefficient) =
      realBlock
        (diagonalSlotEquiv (action.slotPermutation element) secret + action.shift element)
        (affineActErrorState action element state)
        (fun row ↦ diagonalSlotEquiv (action.slotPermutation element) (coefficient row)) := by
  apply Block.ext
  · rfl
  · simp [affineActBlock, realBlock, affineActErrorState]
  · rfl
  · funext row
    simp only [affineActBlock, realBlock, affineActErrorState, RingEquiv.map_add,
      RingEquiv.map_mul]
    ring

/-- Exact joint-law equivariance for the affine-complement action. -/
def ErrorLawAffineEquivariant
    {GroupIndex Limb Slot Row Leakage : Type} {K : Limb → Type}
    [∀ limb, CommRing (K limb)]
    (action : AffineAutomorphismAction GroupIndex Limb Slot Leakage K)
    (stateSampler : ProbComp (ErrorState (RNS Limb Slot K) Row Leakage)) : Prop :=
  ∀ element,
    evalDist (affineActErrorState action element <$> stateSampler) = evalDist stateSampler

/-- Exact distributional equivariance of the complete joint error/leakage law.  This single law
preserves arbitrary cross-limb correlations. -/
def ErrorLawEquivariant
    {GroupIndex Limb Slot Row Leakage : Type} {K : Limb → Type}
    [∀ limb, Semiring (K limb)]
    (action : AutomorphismAction GroupIndex Slot Leakage)
    (stateSampler : ProbComp (ErrorState (RNS Limb Slot K) Row Leakage)) : Prop :=
  ∀ element,
    evalDist (actErrorState action element <$> stateSampler) = evalDist stateSampler

/-- Transitivity transports any chosen slot to the target slot while acting on the complete RNS
element. -/
theorem exists_diagonal_transport
    {GroupIndex Limb Slot Leakage : Type} {K : Limb → Type}
    [∀ limb, Semiring (K limb)]
    (action : AutomorphismAction GroupIndex Slot Leakage)
    (source target : Slot) (value : RNS Limb Slot K) (limb : Limb) :
    ∃ element,
      diagonalSlotEquiv (action.slotPermutation element) value limb target = value limb source := by
  obtain ⟨element, hElement⟩ := action.transitive source target
  refine ⟨element, ?_⟩
  rw [← hElement]
  exact diagonalSlotEquiv_apply_permutation
    (action.slotPermutation element) value limb source

/-! ## Full coherent source problem and computational theorem -/

/-- Real coherent HNF sampler for a fixed auxiliary secret.  Because `stateSampler` does not
take the secret or the public coefficients as an argument, the required independence is enforced
by construction while all components inside `ErrorState` may remain correlated. -/
def coherentRealSampler
    {R Row Leakage : Type} [CommRing R] [SampleableType (Row → R)]
    (stateSampler : ProbComp (ErrorState R Row Leakage)) (secret : R) :
    ProbComp (Block R Row Leakage) := do
  let state ← stateSampler
  let coefficient ← $ᵗ (Row → R)
  return realBlock secret state coefficient

/-- Random endpoint retaining the genuine leakage marginal and replacing the anchor and all
right-hand sides by independent uniforms. -/
def coherentRandomSampler
    {R Row Leakage : Type}
    [SampleableType R] [SampleableType (QuadraticKDM.TargetTranscript R Row)]
    (stateSampler : ProbComp (ErrorState R Row Leakage)) :
    ProbComp (Block R Row Leakage) := do
  let state ← stateSampler
  let anchor ← $ᵗ R
  let pair ← $ᵗ (QuadraticKDM.TargetTranscript R Row)
  return randomBlock state.leakage anchor pair.1 pair.2

/-- The full coherent source-decision problem. -/
def coherentProblem
    {R Row Leakage : Type} [CommRing R]
    [SampleableType R] [SampleableType (Row → R)]
    [SampleableType (QuadraticKDM.TargetTranscript R Row)]
    (stateSampler : ProbComp (ErrorState R Row Leakage)) :
    FormalProof4FHE.LWE.AuxiliaryInput.Problem R (Block R Row Leakage) Unit where
  sampleSecret := $ᵗ R
  sampleReal := coherentRealSampler stateSampler
  sampleZero := coherentRealSampler stateSampler
  sampleUniform := coherentRandomSampler stateSampler
  sampleAuxiliary := fun _ ↦ pure ()

/-- RNS search-to-decision certificate.  Its `loss` records candidate-estimation error, anchor
lift failure, and any other finite reduction loss.  The local algebra required by its target
coordinate tests is proved above. -/
abbrev SearchToDecisionCertificate
    {Secret DecisionChallenge DecisionAuxiliary SearchChallenge SearchAuxiliary : Type}
    (decisionProblem : FormalProof4FHE.LWE.AuxiliaryInput.Problem
      Secret DecisionChallenge DecisionAuxiliary)
    (searchProblem : FormalProof4FHE.LWE.AuxiliaryInput.Search.Problem
      Secret SearchChallenge SearchAuxiliary) :=
  QuadraticKDM.SplitSearchToDecisionCertificate decisionProblem searchProblem

/-- **RNS-limb/NTT search-to-decision theorem, finite quantitative form.**  A checked
candidate-enumeration/amplification certificate transfers complete-secret search hardness to the
coherent source decision problem, with its explicit loss added once. -/
theorem coherentAdvantage_le_search_add_loss
    {R Row Leakage SearchChallenge SearchAuxiliary : Type} [CommRing R]
    [SampleableType R] [SampleableType (Row → R)]
    [SampleableType (QuadraticKDM.TargetTranscript R Row)]
    (stateSampler : ProbComp (ErrorState R Row Leakage))
    (searchProblem : FormalProof4FHE.LWE.AuxiliaryInput.Search.Problem
      R SearchChallenge SearchAuxiliary)
    (certificate : SearchToDecisionCertificate (coherentProblem stateSampler) searchProblem)
    (distinguisher :
      FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
        (Block R Row Leakage) Unit)
    (searchBound lossBound : ℝ)
    (hSearch :
      (FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability searchProblem
        (certificate.toSolver distinguisher)).toReal ≤ searchBound)
    (hLoss : certificate.loss distinguisher ≤ lossBound) :
    FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
        (coherentProblem stateSampler) distinguisher ≤ searchBound + lossBound := by
  exact QuadraticKDM.sourceAdvantage_le_search_add_loss
    (coherentProblem stateSampler) searchProblem certificate distinguisher
    searchBound lossBound hSearch hLoss

/-- Uniform search hardness and a uniform certificate-loss bound imply public decision hardness
for every allowed distinguisher. -/
theorem coherentPublicHardAgainst
    {R Row Leakage SearchChallenge SearchAuxiliary : Type} [CommRing R]
    [SampleableType R] [SampleableType (Row → R)]
    [SampleableType (QuadraticKDM.TargetTranscript R Row)]
    (stateSampler : ProbComp (ErrorState R Row Leakage))
    (searchProblem : FormalProof4FHE.LWE.AuxiliaryInput.Search.Problem
      R SearchChallenge SearchAuxiliary)
    (certificate : SearchToDecisionCertificate (coherentProblem stateSampler) searchProblem)
    (allowed :
      FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
        (Block R Row Leakage) Unit → Prop)
    (searchBound lossBound : ℝ)
    (hSearch : ∀ distinguisher, allowed distinguisher →
      (FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability searchProblem
        (certificate.toSolver distinguisher)).toReal ≤ searchBound)
    (hLoss : ∀ distinguisher, allowed distinguisher →
      certificate.loss distinguisher ≤ lossBound) :
    FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.PublicHardAgainst
      (coherentProblem stateSampler) allowed (searchBound + lossBound) := by
  intro distinguisher hAllowed
  exact coherentAdvantage_le_search_add_loss stateSampler searchProblem certificate distinguisher
    searchBound lossBound (hSearch distinguisher hAllowed) (hLoss distinguisher hAllowed)

/-! ## Masked quadratic HNF source and compiler -/

/-- One coherent source error/leakage state for
`b0=X-S`, `d_j=c_j*X+g_j*Z^2+E_j`, and `T=S-Z`. -/
def quadraticErrorState
    {R Row : Type} [CommRing R]
    (weight : Row → R) (secret proofMask : R) (finalError : Row → R) :
    ErrorState R Row R where
  anchorError := -secret
  rowError := fun row ↦ weight row * proofMask ^ 2 + finalError row
  leakage := secret - proofMask

/-- Public compiler
`A_j=c_j-2g_jT`, `B_j=d_j-c_jb0-g_jT^2`. -/
def compileQuadratic
    {R Row : Type} [CommRing R] (weight : Row → R) (source : Block R Row R) :
    QuadraticKDM.TargetTranscript R Row :=
  (fun row ↦ source.coefficient row - 2 * weight row * source.leakage,
    fun row ↦ source.body row - source.coefficient row * source.anchor -
      weight row * source.leakage ^ 2)

/-- **Exact quadratic compiler identity.**  The source error `g_j Z^2+E_j` compiles to the
implementation-width final error `E_j`, not to a flooded or gadget-scaled error. -/
theorem compileQuadratic_realBlock
    {R Row : Type} [CommRing R]
    (weight : Row → R) (auxiliarySecret secret proofMask : R)
    (finalError coefficient : Row → R) :
    compileQuadratic weight
        (realBlock auxiliarySecret
          (quadraticErrorState weight secret proofMask finalError) coefficient) =
      QuadraticKDMBinaryTernary.kdmTranscript weight secret finalError
        (fun row ↦ coefficient row - 2 * weight row * (secret - proofMask)) := by
  apply Prod.ext
  · rfl
  · funext row
    simp only [compileQuadratic, realBlock, quadraticErrorState,
      QuadraticKDMBinaryTernary.kdmTranscript]
    ring

/-- The same compiler identity specialized to the heterogeneous RNS product. -/
theorem compileQuadratic_rns
    {Limb Slot Row : Type} {K : Limb → Type} [∀ limb, CommRing (K limb)]
    (weight : Row → RNS Limb Slot K)
    (auxiliarySecret secret proofMask : RNS Limb Slot K)
    (finalError coefficient : Row → RNS Limb Slot K) :
    compileQuadratic weight
        (realBlock auxiliarySecret
          (quadraticErrorState weight secret proofMask finalError) coefficient) =
      QuadraticKDMBinaryTernary.kdmTranscript weight secret finalError
        (fun row ↦ coefficient row - 2 * weight row * (secret - proofMask)) :=
  compileQuadratic_realBlock weight auxiliarySecret secret proofMask finalError coefficient

/-- Fixed affine compiler map in the random source branch. -/
def randomQuadraticCompilerMap
    {R Row : Type} [CommRing R] (weight : Row → R) (hint anchor : R)
    (pair : QuadraticKDM.TargetTranscript R Row) : QuadraticKDM.TargetTranscript R Row :=
  compileQuadratic weight (randomBlock hint anchor pair.1 pair.2)

/-- Explicit inverse of the random-branch compiler. -/
def randomQuadraticCompilerMapInv
    {R Row : Type} [CommRing R] (weight : Row → R) (hint anchor : R)
    (output : QuadraticKDM.TargetTranscript R Row) : QuadraticKDM.TargetTranscript R Row :=
  (fun row ↦ output.1 row + 2 * weight row * hint,
    fun row ↦ output.2 row + (output.1 row + 2 * weight row * hint) * anchor +
      weight row * hint ^ 2)

@[simp]
theorem randomQuadraticCompilerMapInv_randomQuadraticCompilerMap
    {R Row : Type} [CommRing R] (weight : Row → R) (hint anchor : R)
    (pair : QuadraticKDM.TargetTranscript R Row) :
    randomQuadraticCompilerMapInv weight hint anchor
        (randomQuadraticCompilerMap weight hint anchor pair) = pair := by
  apply Prod.ext
  · funext row
    simp [randomQuadraticCompilerMapInv, randomQuadraticCompilerMap,
      compileQuadratic, randomBlock]
  · funext row
    simp [randomQuadraticCompilerMapInv, randomQuadraticCompilerMap,
      compileQuadratic, randomBlock]
    ring

@[simp]
theorem randomQuadraticCompilerMap_randomQuadraticCompilerMapInv
    {R Row : Type} [CommRing R] (weight : Row → R) (hint anchor : R)
    (output : QuadraticKDM.TargetTranscript R Row) :
    randomQuadraticCompilerMap weight hint anchor
        (randomQuadraticCompilerMapInv weight hint anchor output) = output := by
  apply Prod.ext
  · funext row
    simp [randomQuadraticCompilerMapInv, randomQuadraticCompilerMap,
      compileQuadratic, randomBlock]
  · funext row
    simp [randomQuadraticCompilerMapInv, randomQuadraticCompilerMap,
      compileQuadratic, randomBlock]
    ring

/-- Conditioned on `(T,b0)`, the random source compiler is an affine permutation. -/
theorem randomQuadraticCompilerMap_bijective
    {R Row : Type} [CommRing R] (weight : Row → R) (hint anchor : R) :
    Function.Bijective (randomQuadraticCompilerMap weight hint anchor) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨randomQuadraticCompilerMapInv weight hint anchor,
      randomQuadraticCompilerMapInv_randomQuadraticCompilerMap weight hint anchor,
      randomQuadraticCompilerMap_randomQuadraticCompilerMapInv weight hint anchor⟩

/-- Hence the random source branch compiles to exact joint uniformity. -/
theorem randomQuadraticCompiler_evalDist_eq_uniform
    {R Row : Type} [CommRing R]
    [Fintype R] [DecidableEq R] [Fintype Row] [DecidableEq Row]
    [SampleableType R]
    (weight : Row → R) (hint anchor : R) :
    evalDist (randomQuadraticCompilerMap weight hint anchor <$>
        ($ᵗ (QuadraticKDM.TargetTranscript R Row))) =
      evalDist ($ᵗ (QuadraticKDM.TargetTranscript R Row)) :=
  evalDist_map_bijective_uniform_cross
    (α := QuadraticKDM.TargetTranscript R Row)
    (β := QuadraticKDM.TargetTranscript R Row)
    (randomQuadraticCompilerMap weight hint anchor)
    (randomQuadraticCompilerMap_bijective weight hint anchor)

/-! ### Exact source/target probability transport -/

/-- Hidden values in one masked quadratic source state. -/
structure QuadraticLatent (R Row : Type) where
  secret : R
  proofMask : R
  finalError : Row → R

/-- Map a joint latent sampler to its complete coherent source error/leakage sampler. -/
def quadraticStateSampler
    {R Row : Type} [CommRing R] (weight : Row → R)
    (latentSampler : ProbComp (QuadraticLatent R Row)) :
    ProbComp (ErrorState R Row R) :=
  (fun latent ↦ quadraticErrorState weight latent.secret latent.proofMask latent.finalError) <$>
    latentSampler

/-- Translation from source coefficients `c_j` to target masks `A_j`. -/
def quadraticCoefficientShift
    {R Row : Type} [CommRing R] (weight : Row → R) (secret proofMask : R)
    (coefficient : Row → R) : Row → R :=
  fun row ↦ coefficient row - 2 * weight row * (secret - proofMask)

/-- The real-branch coefficient translation is a permutation. -/
theorem quadraticCoefficientShift_bijective
    {R Row : Type} [CommRing R] (weight : Row → R) (secret proofMask : R) :
    Function.Bijective (quadraticCoefficientShift weight secret proofMask) := by
  let inverse : (Row → R) → (Row → R) := fun mask row ↦
    mask row + 2 * weight row * (secret - proofMask)
  refine Function.bijective_iff_has_inverse.mpr ⟨inverse, ?_, ?_⟩
  · intro coefficient
    funext row
    simp [inverse, quadraticCoefficientShift]
  · intro mask
    funext row
    simp [inverse, quadraticCoefficientShift]

/-- Canonical target KDM sampler induced by the same joint latent law. -/
def quadraticKDMSampler
    {R Row : Type} [CommRing R] [SampleableType (Row → R)]
    (weight : Row → R) (latentSampler : ProbComp (QuadraticLatent R Row)) :
    ProbComp (QuadraticKDM.TargetTranscript R Row) := do
  let latent ← latentSampler
  let mask ← $ᵗ (Row → R)
  return QuadraticKDMBinaryTernary.kdmTranscript
    weight latent.secret latent.finalError mask

/-- Canonical zero-message rows with the same exact secret/final-error law. -/
def quadraticZeroSampler
    {R Row : Type} [CommRing R] [SampleableType (Row → R)]
    (latentSampler : ProbComp (QuadraticLatent R Row)) :
    ProbComp (QuadraticKDM.TargetTranscript R Row) := do
  let latent ← latentSampler
  let mask ← $ᵗ (Row → R)
  return QuadraticKDMBinaryTernary.zeroTranscript latent.secret latent.finalError mask

/-- Canonical uniform endpoint for all target rows. -/
def quadraticUniformSampler
    {R Row : Type} [SampleableType (QuadraticKDM.TargetTranscript R Row)] :
    ProbComp (QuadraticKDM.TargetTranscript R Row) :=
  $ᵗ (QuadraticKDM.TargetTranscript R Row)

/-- For fixed hidden values, compiling uniform source coefficients gives the canonical target KDM
distribution exactly. -/
theorem fixedRealQuadraticCompile_evalDist_eq_kdm
    {R Row : Type} [CommRing R]
    [Fintype R] [DecidableEq R] [Fintype Row] [DecidableEq Row]
    [SampleableType R]
    (weight : Row → R) (auxiliarySecret secret proofMask : R)
    (finalError : Row → R) :
    evalDist (($ᵗ (Row → R)) >>= fun coefficient ↦
        pure (compileQuadratic weight
          (realBlock auxiliarySecret
            (quadraticErrorState weight secret proofMask finalError) coefficient))) =
      evalDist (($ᵗ (Row → R)) >>= fun mask ↦
        pure (QuadraticKDMBinaryTernary.kdmTranscript weight secret finalError mask)) := by
  have hShift :
      evalDist (quadraticCoefficientShift weight secret proofMask <$> ($ᵗ (Row → R))) =
        evalDist ($ᵗ (Row → R)) :=
    evalDist_map_bijective_uniform_cross
      (α := Row → R) (β := Row → R)
      (quadraticCoefficientShift weight secret proofMask)
      (quadraticCoefficientShift_bijective weight secret proofMask)
  calc
    evalDist (($ᵗ (Row → R)) >>= fun coefficient ↦
        pure (compileQuadratic weight
          (realBlock auxiliarySecret
            (quadraticErrorState weight secret proofMask finalError) coefficient))) =
      evalDist ((quadraticCoefficientShift weight secret proofMask <$>
          ($ᵗ (Row → R))) >>= fun mask ↦
        pure (QuadraticKDMBinaryTernary.kdmTranscript weight secret finalError mask)) := by
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      refine evalDist_bind_congr' ($ᵗ (Row → R)) fun coefficient ↦ ?_
      rw [compileQuadratic_realBlock]
      rfl
    _ = evalDist (($ᵗ (Row → R)) >>= fun mask ↦
        pure (QuadraticKDMBinaryTernary.kdmTranscript weight secret finalError mask)) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hShift _

/-- Compiling the complete real coherent sampler gives the exact KDM sampler. -/
theorem compiledCoherentReal_evalDist_eq_kdm
    {R Row : Type} [CommRing R]
    [Fintype R] [DecidableEq R] [Fintype Row] [DecidableEq Row]
    [SampleableType R]
    (weight : Row → R) (latentSampler : ProbComp (QuadraticLatent R Row))
    (auxiliarySecret : R) :
    evalDist (coherentRealSampler (quadraticStateSampler weight latentSampler) auxiliarySecret >>=
        fun source ↦ pure (compileQuadratic weight source)) =
      evalDist (quadraticKDMSampler weight latentSampler) := by
  unfold coherentRealSampler quadraticStateSampler quadraticKDMSampler
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  refine evalDist_bind_congr' latentSampler fun latent ↦ ?_
  exact fixedRealQuadraticCompile_evalDist_eq_kdm weight auxiliarySecret
    latent.secret latent.proofMask latent.finalError

/-- Compiling the complete random coherent sampler gives exact uniformity, provided the genuine
latent sampler has no failure mass. -/
theorem compiledCoherentRandom_evalDist_eq_uniform
    {R Row : Type} [CommRing R]
    [Fintype R] [DecidableEq R] [Fintype Row] [DecidableEq Row]
    [SampleableType R]
    (weight : Row → R) (latentSampler : ProbComp (QuadraticLatent R Row))
    (hLatent : Pr[⊥ | latentSampler] = 0) :
    evalDist (coherentRandomSampler (quadraticStateSampler weight latentSampler) >>=
        fun source ↦ pure (compileQuadratic weight source)) =
      evalDist (quadraticUniformSampler (R := R) (Row := Row)) := by
  let Uniform := quadraticUniformSampler (R := R) (Row := Row)
  calc
    evalDist (coherentRandomSampler (quadraticStateSampler weight latentSampler) >>=
        fun source ↦ pure (compileQuadratic weight source)) =
      evalDist (latentSampler >>= fun latent ↦
        ($ᵗ R) >>= fun _anchor ↦ Uniform) := by
      unfold coherentRandomSampler quadraticStateSampler
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      refine evalDist_bind_congr' latentSampler fun latent ↦ ?_
      refine evalDist_bind_congr' ($ᵗ R) fun anchor ↦ ?_
      change evalDist (($ᵗ (QuadraticKDM.TargetTranscript R Row)) >>= fun pair ↦
          pure (randomQuadraticCompilerMap weight
            (latent.secret - latent.proofMask) anchor pair)) =
        evalDist ($ᵗ (QuadraticKDM.TargetTranscript R Row))
      simpa only [map_eq_bind_pure_comp, Function.comp_def] using
        randomQuadraticCompiler_evalDist_eq_uniform weight
          (latent.secret - latent.proofMask) anchor
    _ = evalDist (latentSampler >>= fun _latent ↦ Uniform) := by
      refine evalDist_bind_congr' latentSampler fun _latent ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        ($ᵗ R) (by simp) _
    _ = evalDist Uniform :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        latentSampler hLatent _

/-! ### Exact game correspondence and quadratic KDM corollary -/

/-- Coherent source problem induced by the masked quadratic latent law. -/
def quadraticSourceProblem
    {R Row : Type} [CommRing R]
    [SampleableType R] [SampleableType (Row → R)]
    [SampleableType (QuadraticKDM.TargetTranscript R Row)]
    (weight : Row → R) (latentSampler : ProbComp (QuadraticLatent R Row)) :
    FormalProof4FHE.LWE.AuxiliaryInput.Problem R (Block R Row R) Unit :=
  coherentProblem (quadraticStateSampler weight latentSampler)

/-- Public reduction induced by the exact quadratic compiler. -/
def quadraticSourceReduction
    {R Row : Type} [CommRing R] (weight : Row → R)
    (distinguisher : QuadraticKDM.Distinguisher R Row) :
    FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Block R Row R) Unit :=
  fun source _ ↦ distinguisher (compileQuadratic weight source)

/-- The reduced coherent-source real game is exactly the target quadratic KDM game. -/
theorem quadraticSourceReduction_realGame_evalDist
    {R Row : Type} [CommRing R]
    [Fintype R] [DecidableEq R] [Fintype Row] [DecidableEq Row]
    [SampleableType R]
    (weight : Row → R) (latentSampler : ProbComp (QuadraticLatent R Row))
    (distinguisher : QuadraticKDM.Distinguisher R Row) :
    evalDist (FormalProof4FHE.LWE.AuxiliaryInput.realGame
        (quadraticSourceProblem weight latentSampler)
        (FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicContinuation
          (quadraticSourceReduction weight distinguisher))) =
      evalDist (quadraticKDMSampler weight latentSampler >>= distinguisher) := by
  unfold FormalProof4FHE.LWE.AuxiliaryInput.realGame
    FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicContinuation
    quadraticSourceProblem coherentProblem quadraticSourceReduction
  simp only [pure_bind]
  calc
    evalDist (($ᵗ R) >>= fun auxiliarySecret ↦
        coherentRealSampler (quadraticStateSampler weight latentSampler) auxiliarySecret >>=
          fun source ↦ distinguisher (compileQuadratic weight source)) =
      evalDist (($ᵗ R) >>= fun _auxiliarySecret ↦
        quadraticKDMSampler weight latentSampler >>= distinguisher) := by
      refine evalDist_bind_congr' ($ᵗ R) fun auxiliarySecret ↦ ?_
      simpa only [bind_assoc, pure_bind] using
        (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
          (compiledCoherentReal_evalDist_eq_kdm weight latentSampler auxiliarySecret)
          distinguisher)
    _ = evalDist (quadraticKDMSampler weight latentSampler >>= distinguisher) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        ($ᵗ R) (by simp) _

/-- The reduced coherent-source random game is exactly the uniform target game. -/
theorem quadraticSourceReduction_randomGame_evalDist
    {R Row : Type} [CommRing R]
    [Fintype R] [DecidableEq R] [Fintype Row] [DecidableEq Row]
    [SampleableType R]
    (weight : Row → R) (latentSampler : ProbComp (QuadraticLatent R Row))
    (distinguisher : QuadraticKDM.Distinguisher R Row)
    (hLatent : Pr[⊥ | latentSampler] = 0) :
    evalDist (FormalProof4FHE.LWE.AuxiliaryInput.uniformGame
        (quadraticSourceProblem weight latentSampler)
        (FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicContinuation
          (quadraticSourceReduction weight distinguisher))) =
      evalDist (quadraticUniformSampler >>= distinguisher) := by
  unfold FormalProof4FHE.LWE.AuxiliaryInput.uniformGame
    FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicContinuation
    quadraticSourceProblem coherentProblem quadraticSourceReduction
  simp only [pure_bind]
  calc
    evalDist (($ᵗ R) >>= fun _auxiliarySecret ↦
        coherentRandomSampler (quadraticStateSampler weight latentSampler) >>= fun source ↦
          distinguisher (compileQuadratic weight source)) =
      evalDist (($ᵗ R) >>= fun _auxiliarySecret ↦
        quadraticUniformSampler >>= distinguisher) := by
      refine evalDist_bind_congr' ($ᵗ R) fun _auxiliarySecret ↦ ?_
      simpa only [bind_assoc, pure_bind] using
        (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
          (compiledCoherentRandom_evalDist_eq_uniform weight latentSampler hLatent)
          distinguisher)
    _ = evalDist (quadraticUniformSampler >>= distinguisher) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        ($ᵗ R) (by simp) _

/-- Quadratic KDM-versus-zero advantage. -/
noncomputable def quadraticKDMAdvantage
    {R Row : Type} [CommRing R] [SampleableType (Row → R)]
    (weight : Row → R) (latentSampler : ProbComp (QuadraticLatent R Row))
    (distinguisher : QuadraticKDM.Distinguisher R Row) : ℝ :=
  (quadraticKDMSampler weight latentSampler >>= distinguisher).boolDistAdvantage
    (quadraticZeroSampler latentSampler >>= distinguisher)

/-- Quadratic KDM-versus-uniform advantage. -/
noncomputable def quadraticKDMUniformAdvantage
    {R Row : Type} [CommRing R]
    [SampleableType (Row → R)] [SampleableType (QuadraticKDM.TargetTranscript R Row)]
    (weight : Row → R) (latentSampler : ProbComp (QuadraticLatent R Row))
    (distinguisher : QuadraticKDM.Distinguisher R Row) : ℝ :=
  (quadraticKDMSampler weight latentSampler >>= distinguisher).boolDistAdvantage
    (quadraticUniformSampler >>= distinguisher)

/-- Zero-message-versus-uniform advantage. -/
noncomputable def quadraticZeroUniformAdvantage
    {R Row : Type} [CommRing R]
    [SampleableType (Row → R)] [SampleableType (QuadraticKDM.TargetTranscript R Row)]
    (latentSampler : ProbComp (QuadraticLatent R Row))
    (distinguisher : QuadraticKDM.Distinguisher R Row) : ℝ :=
  (quadraticZeroSampler latentSampler >>= distinguisher).boolDistAdvantage
    (quadraticUniformSampler >>= distinguisher)

/-- Target KDM-versus-uniform advantage is exactly the coherent-source public decision
advantage. -/
theorem quadraticKDMUniformAdvantage_eq_sourceAdvantage
    {R Row : Type} [CommRing R]
    [Fintype R] [DecidableEq R] [Fintype Row] [DecidableEq Row]
    [SampleableType R]
    (weight : Row → R) (latentSampler : ProbComp (QuadraticLatent R Row))
    (distinguisher : QuadraticKDM.Distinguisher R Row)
    (hLatent : Pr[⊥ | latentSampler] = 0) :
    quadraticKDMUniformAdvantage weight latentSampler distinguisher =
      FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
        (quadraticSourceProblem weight latentSampler)
        (quadraticSourceReduction weight distinguisher) := by
  unfold quadraticKDMUniformAdvantage
    FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
    FormalProof4FHE.LWE.AuxiliaryInput.circularLweAdvantage
    ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (quadraticSourceReduction_realGame_evalDist weight latentSampler distinguisher) true,
    evalDist_ext_iff.mp
      (quadraticSourceReduction_randomGame_evalDist
        weight latentSampler distinguisher hLatent) true]

/-- Triangle decomposition through the common uniform endpoint. -/
theorem quadraticKDMAdvantage_le_kdmUniform_add_zeroUniform
    {R Row : Type} [CommRing R]
    [SampleableType (Row → R)] [SampleableType (QuadraticKDM.TargetTranscript R Row)]
    (weight : Row → R) (latentSampler : ProbComp (QuadraticLatent R Row))
    (distinguisher : QuadraticKDM.Distinguisher R Row) :
    quadraticKDMAdvantage weight latentSampler distinguisher ≤
      quadraticKDMUniformAdvantage weight latentSampler distinguisher +
        quadraticZeroUniformAdvantage latentSampler distinguisher := by
  have h := ProbComp.boolDistAdvantage_triangle
    (quadraticKDMSampler weight latentSampler >>= distinguisher)
    (quadraticUniformSampler >>= distinguisher)
    (quadraticZeroSampler latentSampler >>= distinguisher)
  unfold quadraticKDMAdvantage quadraticKDMUniformAdvantage
    quadraticZeroUniformAdvantage
  rw [show (quadraticUniformSampler >>= distinguisher).boolDistAdvantage
      (quadraticZeroSampler latentSampler >>= distinguisher) =
      (quadraticZeroSampler latentSampler >>= distinguisher).boolDistAdvantage
        (quadraticUniformSampler >>= distinguisher) by
    unfold ProbComp.boolDistAdvantage
    rw [abs_sub_comm]] at h
  exact h

/-- **RNS source-decision corollary for quadratic KDM.**  Complete-secret coherent-HNF search
hardness, the checked RNS search-to-decision certificate, and ordinary zero-message RLWE security
bound quadratic KDM security. -/
theorem quadraticKDMAdvantage_le_search_add_loss_add_zero
    {R Row SearchChallenge SearchAuxiliary : Type} [CommRing R]
    [Fintype R] [DecidableEq R] [Fintype Row] [DecidableEq Row]
    [SampleableType R]
    (weight : Row → R) (latentSampler : ProbComp (QuadraticLatent R Row))
    (distinguisher : QuadraticKDM.Distinguisher R Row)
    (searchProblem : FormalProof4FHE.LWE.AuxiliaryInput.Search.Problem
      R SearchChallenge SearchAuxiliary)
    (certificate : SearchToDecisionCertificate
      (quadraticSourceProblem weight latentSampler) searchProblem)
    (searchBound lossBound zeroBound : ℝ)
    (hLatent : Pr[⊥ | latentSampler] = 0)
    (hSearch :
      (FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability searchProblem
        (certificate.toSolver (quadraticSourceReduction weight distinguisher))).toReal ≤
          searchBound)
    (hLoss : certificate.loss (quadraticSourceReduction weight distinguisher) ≤ lossBound)
    (hZero : quadraticZeroUniformAdvantage latentSampler distinguisher ≤ zeroBound) :
    quadraticKDMAdvantage weight latentSampler distinguisher ≤
      (searchBound + lossBound) + zeroBound := by
  calc
    quadraticKDMAdvantage weight latentSampler distinguisher ≤
        quadraticKDMUniformAdvantage weight latentSampler distinguisher +
          quadraticZeroUniformAdvantage latentSampler distinguisher :=
      quadraticKDMAdvantage_le_kdmUniform_add_zeroUniform
        weight latentSampler distinguisher
    _ = FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
          (quadraticSourceProblem weight latentSampler)
          (quadraticSourceReduction weight distinguisher) +
        quadraticZeroUniformAdvantage latentSampler distinguisher := by
      rw [quadraticKDMUniformAdvantage_eq_sourceAdvantage
        weight latentSampler distinguisher hLatent]
    _ ≤ (searchBound + lossBound) + zeroBound :=
      add_le_add
        (QuadraticKDM.sourceAdvantage_le_search_add_loss
          (quadraticSourceProblem weight latentSampler) searchProblem certificate
          (quadraticSourceReduction weight distinguisher)
          searchBound lossBound hSearch hLoss)
        hZero

/-- Heterogeneous-field specialization of the complete quadratic KDM theorem. -/
theorem rns_quadraticKDMAdvantage_le_search_add_loss_add_zero
    {Limb Slot Row SearchChallenge SearchAuxiliary : Type} {K : Limb → Type}
    [∀ limb, Field (K limb)]
    [Fintype (RNS Limb Slot K)] [DecidableEq (RNS Limb Slot K)]
    [Fintype Row] [DecidableEq Row] [SampleableType (RNS Limb Slot K)]
    (weight : Row → RNS Limb Slot K)
    (latentSampler : ProbComp (QuadraticLatent (RNS Limb Slot K) Row))
    (distinguisher : QuadraticKDM.Distinguisher (RNS Limb Slot K) Row)
    (searchProblem : FormalProof4FHE.LWE.AuxiliaryInput.Search.Problem
      (RNS Limb Slot K) SearchChallenge SearchAuxiliary)
    (certificate : SearchToDecisionCertificate
      (quadraticSourceProblem weight latentSampler) searchProblem)
    (searchBound lossBound zeroBound : ℝ)
    (hLatent : Pr[⊥ | latentSampler] = 0)
    (hSearch :
      (FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability searchProblem
        (certificate.toSolver (quadraticSourceReduction weight distinguisher))).toReal ≤
          searchBound)
    (hLoss : certificate.loss (quadraticSourceReduction weight distinguisher) ≤ lossBound)
    (hZero : quadraticZeroUniformAdvantage latentSampler distinguisher ≤ zeroBound) :
    quadraticKDMAdvantage weight latentSampler distinguisher ≤
      (searchBound + lossBound) + zeroBound := by
  exact quadraticKDMAdvantage_le_search_add_loss_add_zero
    weight latentSampler distinguisher searchProblem certificate
    searchBound lossBound zeroBound hLatent hSearch hLoss hZero

/-! ### Deterministic good events for binary and ternary anchors -/

/-- The binary liftable-anchor good event is unconditional. -/
theorem binaryLiftableAnchor_good
    {Limb Coefficient Slot : Type} (modulus : Limb → ℕ)
    (ntt : NTTCoordinates Limb Coefficient Slot modulus)
    (hModulus : ∀ limb, 2 < modulus limb) (secret : DigitAnchor 2 Coefficient) :
    (binaryLiftableAnchor modulus ntt hModulus).Good secret := by
  trivial

/-- The centered-ternary liftable-anchor good event is unconditional. -/
theorem ternaryLiftableAnchor_good
    {Limb Coefficient Slot : Type} (modulus : Limb → ℕ)
    (ntt : NTTCoordinates Limb Coefficient Slot modulus)
    (hModulus : ∀ limb, 2 < modulus limb) (secret : DigitAnchor 3 Coefficient) :
    (ternaryLiftableAnchor modulus ntt hModulus).Good secret := by
  trivial

end

end FormalProof4FHE.RLWE.RNSSplitSearchToDecisionCorrelated
