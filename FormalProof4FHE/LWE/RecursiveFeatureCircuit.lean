/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.RecursiveFeatureBootstrapParameters
import FormalProof4FHE.LWE.GSWCircuit

/-!
# Stored shared-circuit evaluation with one recursive-feature key

The actual NAND DAG evaluator reuses stored inputs and intermediate wires. Every
gate applies the same original-bit controls and preserves the same feature-secret
noise invariant. Ciphertext dimensions do not depend on circuit size or depth.
The parameter margins are discharged by the companion eventual-budget theorem.
This correctness result does not discharge cubic original-bit control security.
-/

namespace FormalProof4FHE.LWE.RecursiveFeatureCircuit

open RecursiveMultiplication RecursiveFeatureGSW RecursiveFeatureBootstrap

def operation {factor p n : ℕ} [NeZero factor] [NeZero p]
    (params : Parameters (factor * p)) (original : StoredOriginal params n)
    (level : Fin params.levels) (oneCode : ZMod p)
    (first second : GSWAccumulator.StoredCiphertext params (rows n)) :
    GSWAccumulator.StoredCiphertext params (rows n) :=
  refreshedNandStored params (originalView params original)
    (ofMatrix params (GSWAccumulator.ciphertextView params first))
    (ofMatrix params (GSWAccumulator.ciphertextView params second)) level oneCode

def evaluateWires {factor p n inputs wires : ℕ} [NeZero factor] [NeZero p]
    (params : Parameters (factor * p)) (original : StoredOriginal params n)
    (level : Fin params.levels) (oneCode : ZMod p)
    (initial : Vector (GSWAccumulator.StoredCiphertext params (rows n)) inputs)
    (program : GSWCircuit.Program inputs wires) :
    Vector (GSWAccumulator.StoredCiphertext params (rows n)) wires :=
  GSWCircuit.runStored (operation params original level oneCode) initial program

theorem evaluateCounted_eq {factor p n inputs wires : ℕ} [NeZero factor] [NeZero p]
    (params : Parameters (factor * p)) (original : StoredOriginal params n)
    (level : Fin params.levels) (oneCode : ZMod p)
    (initial : Vector (GSWAccumulator.StoredCiphertext params (rows n)) inputs)
    (program : GSWCircuit.Program inputs wires) :
    GSWCircuit.runCounted (operation params original level oneCode) initial program =
      (evaluateWires params original level oneCode initial program, GSWCircuit.gateCount program) :=
  GSWCircuit.runCounted_eq _ _ _

open RecursiveFeatureBootstrapParameters

theorem noiseBound_evaluateWires (parameter : ℕ)
    (hbudget : lookupModulus parameter * postNandBound parameter < RecursiveQuadraticParameters.modulus parameter)
    {inputs wires : ℕ} (bits : Fin (dimension parameter) → Bool)
    (original : StoredOriginal (params parameter (capacity_of_budget parameter hbudget)) (dimension parameter))
    (initial : Vector (GSWAccumulator.StoredCiphertext
      (params parameter (capacity_of_budget parameter hbudget)) (rows (dimension parameter))) inputs)
    (messages : Vector Bool inputs) (program : GSWCircuit.Program inputs wires)
    (hcontrols : ∀ index, NoiseBound (params parameter (capacity_of_budget parameter hbudget))
      (GSWSelfKey.binaryEmbed bits) (originalView _ original index)
      (GSWGadget.bitMessage (bits index)) (keyBound parameter))
    (hinputs : ∀ index, NoiseBound (params parameter (capacity_of_budget parameter hbudget))
      (GSWSelfKey.binaryEmbed bits)
      (ofMatrix _ (GSWAccumulator.ciphertextView _ (initial.get index)))
      (GSWGadget.bitMessage (messages.get index)) (outputBound parameter)) :
    ∀ index, NoiseBound (params parameter (capacity_of_budget parameter hbudget)) (GSWSelfKey.binaryEmbed bits)
      (ofMatrix _ (GSWAccumulator.ciphertextView _
        ((evaluateWires (params parameter (capacity_of_budget parameter hbudget)) original
          (level parameter (capacity_of_budget parameter hbudget)) (oneCode parameter) initial program).get index)))
      (GSWGadget.bitMessage ((GSWCircuit.runBits messages program).get index)) (outputBound parameter) := by
  apply GSWCircuit.runStored_rel
    (operation (params parameter (capacity_of_budget parameter hbudget)) original
      (level parameter (capacity_of_budget parameter hbudget)) (oneCode parameter))
    (fun ciphertext bit ↦ NoiseBound (params parameter (capacity_of_budget parameter hbudget))
      (GSWSelfKey.binaryEmbed bits) (ofMatrix _ (GSWAccumulator.ciphertextView _ ciphertext))
      (GSWGadget.bitMessage bit) (outputBound parameter)) initial messages program _ hinputs
  intro first second firstBit secondBit hfirst hsecond
  exact RecursiveFeatureBootstrapParameters.noiseBound_refreshedNand parameter hbudget bits
    (originalView _ original) _ _ firstBit secondBit hcontrols hfirst hsecond

/-- Every selected output of an arbitrary shared circuit decrypts under the original secret. -/
theorem decode_evaluate (parameter : ℕ)
    (hbudget : lookupModulus parameter * postNandBound parameter < RecursiveQuadraticParameters.modulus parameter)
    {inputs wires : ℕ} (bits : Fin (dimension parameter) → Bool)
    (original : StoredOriginal (params parameter (capacity_of_budget parameter hbudget)) (dimension parameter))
    (initial : Vector (GSWAccumulator.StoredCiphertext
      (params parameter (capacity_of_budget parameter hbudget)) (rows (dimension parameter))) inputs)
    (messages : Vector Bool inputs) (program : GSWCircuit.Program inputs wires) (output : Fin wires)
    (hcontrols : ∀ index, NoiseBound (params parameter (capacity_of_budget parameter hbudget))
      (GSWSelfKey.binaryEmbed bits) (originalView _ original index)
      (GSWGadget.bitMessage (bits index)) (keyBound parameter))
    (hinputs : ∀ index, NoiseBound (params parameter (capacity_of_budget parameter hbudget))
      (GSWSelfKey.binaryEmbed bits)
      (ofMatrix _ (GSWAccumulator.ciphertextView _ (initial.get index)))
      (GSWGadget.bitMessage (messages.get index)) (outputBound parameter)) :
    decode (params parameter (capacity_of_budget parameter hbudget)) (GSWSelfKey.binaryEmbed bits)
      (ofMatrix _ (GSWAccumulator.ciphertextView _
        ((evaluateWires (params parameter (capacity_of_budget parameter hbudget)) original
          (level parameter (capacity_of_budget parameter hbudget)) (oneCode parameter) initial program).get output)))
      (level parameter (capacity_of_budget parameter hbudget)) = (GSWCircuit.runBits messages program).get output := by
  apply decode_eq_bit _ _ _ _ (outputBound parameter) (level parameter (capacity_of_budget parameter hbudget))
    (noiseBound_evaluateWires parameter hbudget bits original initial messages program hcontrols hinputs output)
  rw [gadget_distance]
  exact output_margin parameter hbudget

end FormalProof4FHE.LWE.RecursiveFeatureCircuit
