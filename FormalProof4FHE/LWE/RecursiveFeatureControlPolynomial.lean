/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.RecursiveFeatureControlHybrid

/-!
# The quadratic part of the actual original-bit control table

Constant-feature, linear-feature, and repeated-index quadratic-feature control
messages are quadratic on binary secrets. The fixed polynomial below retains
all of these messages exactly and replaces only the products of three distinct
secret bits by zero. It instantiates the ordinary-LWE hop of ControlHybrid.
The security of that remaining complete-view cubic replacement is unproved.
-/

open Matrix

namespace FormalProof4FHE.LWE.RecursiveFeatureControlPolynomial

open RecursiveMultiplication RecursiveFeatureGSW RecursiveFeatureBootstrap
open RecursiveFeatureSecurityView RecursiveFeatureControlHybrid

def linearPolynomial {R : Type} [CommRing R] {n : ℕ} (weight : R) (index : Fin n) :
    RecursiveQuadratic.Polynomial R n 1 where
  quadratic := fun _ ↦ 0
  linear := fun _ row ↦ if row = index then weight else 0
  constant := fun _ ↦ 0

def pairPolynomial {R : Type} [CommRing R] {n : ℕ} (weight : R) (first second : Fin n) :
    RecursiveQuadratic.Polynomial R n 1 where
  quadratic := fun _ row column ↦ if row = first then if column = second then weight else 0 else 0
  linear := fun _ ↦ 0
  constant := fun _ ↦ 0

def zeroPolynomial {R : Type} [CommRing R] (n : ℕ) : RecursiveQuadratic.Polynomial R n 1 where
  quadratic := fun _ ↦ 0
  linear := fun _ ↦ 0
  constant := fun _ ↦ 0

theorem message_linearPolynomial {R : Type} [CommRing R] {n : ℕ}
    (weight : R) (index : Fin n) (secret : Fin n → R) :
    RecursiveQuadratic.message (linearPolynomial weight index) secret 0 = weight * secret index := by
  simp [RecursiveQuadratic.message, linearPolynomial, dotProduct, ite_mul]

theorem message_pairPolynomial {R : Type} [CommRing R] {n : ℕ}
    (weight : R) (first second : Fin n) (secret : Fin n → R) :
    RecursiveQuadratic.message (pairPolynomial weight first second) secret 0 = weight * secret first * secret second := by
  simp [RecursiveQuadratic.message, pairPolynomial, vecMul, dotProduct, mul_ite, ite_mul]
  ring

def genuineCubic {n : ℕ} (index : Fin n) : Feature n → Bool
  | some (.inr (first, second)) => decide (index ≠ first ∧ index ≠ second ∧ first ≠ second)
  | _ => false

def piecePolynomial {q n : ℕ} [NeZero q] (params : Parameters q)
    (index : Fin n) (coordinate : Feature n) (level : Fin params.levels) :
    RecursiveQuadratic.Polynomial (ZMod q) n 1 :=
  let weight := TFHE.Gadget.Base.gadget params level
  match coordinate with
  | none => linearPolynomial weight index
  | some (.inl row) => pairPolynomial weight index row
  | some (.inr (first, second)) =>
      if index = first then pairPolynomial weight index second
      else if index = second then pairPolynomial weight index first
      else if first = second then pairPolynomial weight index first
      else zeroPolynomial n

theorem message_piecePolynomial {q n : ℕ} [NeZero q] (params : Parameters q)
    (bits : Fin n → Bool) (index : Fin n) (coordinate : Feature n) (level : Fin params.levels) :
    RecursiveQuadratic.message (piecePolynomial params index coordinate level) (GSWSelfKey.binaryEmbed bits) 0 =
      if genuineCubic index coordinate then 0 else controlMessage params (GSWSelfKey.binaryEmbed bits) index coordinate level := by
  cases coordinate with
  | none =>
      simp [piecePolynomial, genuineCubic, message_linearPolynomial, controlMessage, gadgetBatch_phase, feature, mul_comm]
  | some coordinate => cases coordinate with
    | inl row =>
        simp only [piecePolynomial, genuineCubic, Bool.false_eq_true, ↓reduceIte, message_pairPolynomial,
          controlMessage, gadgetBatch_phase, feature]
        ring
    | inr pair =>
        rcases pair with ⟨first, second⟩
        by_cases hfirst : index = first
        · subst first
          cases hbit : bits index <;>
            simp [piecePolynomial, genuineCubic, message_pairPolynomial, controlMessage_quadratic, GSWSelfKey.binaryEmbed, hbit]
        · by_cases hsecond : index = second
          · subst second
            cases hbit : bits index <;>
              simp [piecePolynomial, genuineCubic, hfirst, message_pairPolynomial, controlMessage_quadratic,
                GSWSelfKey.binaryEmbed, hbit]
          · by_cases hpair : first = second
            · subst second
              cases hbit : bits first <;>
                simp [piecePolynomial, genuineCubic, hfirst, message_pairPolynomial, controlMessage_quadratic,
                  GSWSelfKey.binaryEmbed, hbit]
            · simp [piecePolynomial, genuineCubic, hfirst, hsecond, hpair,
                RecursiveQuadratic.message, zeroPolynomial]

def coordinates {q : ℕ} (params : Parameters q) (n : ℕ)
    (index : Fin (controlCount params n)) : Fin n × Feature n × Fin params.levels :=
  let split := finProdFinEquiv.symm index
  let column := finProdFinEquiv.symm split.2
  (split.1, (featureEquiv n).symm column.1, column.2)

def controlPolynomial {q n : ℕ} [NeZero q] (params : Parameters q) : ControlPolynomial params n where
  quadratic index :=
    (piecePolynomial params (coordinates params n index).1
      (coordinates params n index).2.1 (coordinates params n index).2.2).quadratic 0
  linear index :=
    (piecePolynomial params (coordinates params n index).1
      (coordinates params n index).2.1 (coordinates params n index).2.2).linear 0
  constant index :=
    (piecePolynomial params (coordinates params n index).1
      (coordinates params n index).2.1 (coordinates params n index).2.2).constant 0

theorem controlPolynomial_message_at {q n : ℕ} [NeZero q] (params : Parameters q)
    (bits : Fin n → Bool) (index : Fin n) (coordinate : Feature n) (level : Fin params.levels) :
    RecursiveQuadratic.message (controlPolynomial params) (GSWSelfKey.binaryEmbed bits)
      (finProdFinEquiv (index, finProdFinEquiv (featureEquiv n coordinate, level))) =
      if genuineCubic index coordinate then 0 else controlMessage params (GSWSelfKey.binaryEmbed bits) index coordinate level := by
  have hcoords : coordinates params n
      (finProdFinEquiv (index, finProdFinEquiv (featureEquiv n coordinate, level))) = (index, coordinate, level) := by
    simp [coordinates]
  change RecursiveQuadratic.message
    (piecePolynomial params (coordinates params n _).1 (coordinates params n _).2.1 (coordinates params n _).2.2)
      (GSWSelfKey.binaryEmbed bits) 0 = _
  rw [hcoords]
  exact message_piecePolynomial params bits index coordinate level

/-- Every retained column is the exact same fresh scalar ciphertext, with the same masks and errors. -/
theorem stored_control_non_cubic_eq {q n p : ℕ} [NeZero q] (params : Parameters q)
    (draws : Draws params n p) (index : Fin n) (coordinate : Feature n) (level : Fin params.levels)
    (hnotCubic : genuineCubic index coordinate = false) :
    originalView params (viewWithPolynomial params (controlPolynomial params) draws).2 index
        (finProdFinEquiv (featureEquiv n coordinate, level)) =
      originalView params (controls params draws) index
        (finProdFinEquiv (featureEquiv n coordinate, level)) := by
  change originalView params (storeOriginal params _) index _ = _
  rw [originalView_storeOriginal, controls_view]
  simp only [freshOriginal]
  rw [controlPolynomial_message_at]
  simp only [hnotCubic, Bool.false_eq_true, ↓reduceIte, controlMessage, GSWSelfKey.binaryEmbed, GSWGadget.bitMessage]

open OracleComp AsymmEncAlg RecursiveQuadraticParameters RecursiveFeaturePublicKeyParameters

noncomputable def familyObserver (parameter : ℕ)
    (adversary : IND_CPA_Adv (RecursiveFeatureSecurityParameters.family parameter)) :=
  fromINDCPA (params parameter) (level parameter) ($ᵗ (Fin (dimension parameter) → Bool))
    (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter)) adversary

/-- This is the remaining real-to-quadratic hop, with the real IND-CPA observer. -/
noncomputable def familyControlReplacementAdvantage (parameter : ℕ)
    (adversary : IND_CPA_Adv (RecursiveFeatureSecurityParameters.family parameter)) : ℝ :=
  controlReplacementAdvantage (params parameter) (controlPolynomial (params parameter))
    ($ᵗ (Fin (dimension parameter) → Bool))
    (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter))
    (familyObserver parameter adversary)

/-- The quadratic comparison has an ordinary-LWE reduction; security of the cubic hop
is not assumed or proved by this bound. -/
theorem family_oneTime_abs_signedAdvantage_le (parameter : ℕ)
    (adversary : IND_CPA_Adv (RecursiveFeatureSecurityParameters.family parameter)) :
    |IND_CPA_OneTime_signedAdvantageReal (RecursiveFeatureSecurityParameters.family parameter) adversary| ≤
      familyControlReplacementAdvantage parameter adversary +
        quadraticOrdinaryLoss parameter (params parameter) (controlPolynomial (params parameter))
          (familyObserver parameter adversary) +
        implementationLoss (RecursiveFeatureSecurityParameters.scalarErrorCount parameter) parameter +
        maskingBound parameter := by
  simpa only [RecursiveFeatureSecurityParameters.family, familyControlReplacementAdvantage,
    familyObserver, RecursiveFeatureSecurityParameters.scalarErrorCount, maskingBound, maskingPerColumnBound,
    RecursiveFeatureSecurityView.Dimension, RecursiveFeaturePublicKey.Dimension, featureRows, params,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    using actual_oneTime_abs_signedAdvantage_le parameter (params parameter) (level parameter)
      (controlPolynomial (params parameter)) adversary

theorem family_implementationLoss_negligible :
    negligible (fun parameter ↦ ENNReal.ofReal
      (implementationLoss (RecursiveFeatureSecurityParameters.scalarErrorCount parameter) parameter)) := by
  simpa only [RecursiveFeatureSecurityParameters.scalarErrorCountPolynomial_eval]
    using implementationLoss_negligible RecursiveFeatureSecurityParameters.scalarErrorCountPolynomial

end FormalProof4FHE.LWE.RecursiveFeatureControlPolynomial
