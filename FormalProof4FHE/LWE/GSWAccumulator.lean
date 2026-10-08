/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.GSWGadget

/-!
# Same-key LWE-to-GSW programmable cyclic accumulator

Use a vector of GSW ciphertexts instead of a ring accumulator. An encrypted secret bit selects
between the current vector and its public cyclic shift. Every step adds one bounded control
error times the public digit factor, even if the control ciphertext is reused or the errors
are correlated. Summing the final indicator coordinates selected by a public Boolean lookup
produces a GSW encryption of that lookup applied to the LWE phase.

The actual public evaluator takes only controls, mask coefficients, and the body. Secret bits
occur solely in correctness statements. `freshBootKey` encrypts each bit under the same binary
secret that decrypts the output. There is no second secret or operational key schedule.

This proves a concrete small-modulus LWE-to-GSW correctness component. `GSWModulusSwitch` and
`GSWBootstrap` supply public scaled reduction from a large-modulus GSW column;
`GSWBootstrapParameters` proves compatible bounds closed under NAND and refresh. Security of the
complete same-key control view still requires the unresolved ordinary-LWE reduction; it is not
asserted here.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.LWE.GSWAccumulator

open GSWGadget

abbrev Accumulator {Q : ℕ} (params : Parameters Q) (rows modulus : ℕ) :=
  ZMod modulus → Ciphertext params rows

/-- Public zero-error indicator at the known body value. -/
def initial {Q p : ℕ} [NeZero Q] [NeZero p] {rows : ℕ} (params : Parameters Q)
    (body : ZMod p) : Accumulator params rows p :=
  fun index ↦ if index = body then gadget params rows else 0

/-- Concrete backing data for a rectangular ciphertext. -/
abbrev StoredCiphertext {Q : ℕ} (params : Parameters Q) (rows : ℕ) :=
  Vector (Vector (ZMod Q) (rows * params.levels)) rows

/-- Eagerly construct data, rather than a function which reconstructs data on each read. -/
def storeCiphertext {Q : ℕ} {rows : ℕ} (params : Parameters Q)
    (ciphertext : Ciphertext params rows) : StoredCiphertext params rows :=
  Vector.ofFn fun row : Fin rows ↦
    Vector.ofFn fun column : Fin (rows * params.levels) ↦ ciphertext row column

/-- Mathematical matrix interface of already stored ciphertext data. -/
def ciphertextView {Q : ℕ} {rows : ℕ} (params : Parameters Q)
    (ciphertext : StoredCiphertext params rows) : Ciphertext params rows :=
  fun row column ↦ (ciphertext.get row).get column

@[simp]
theorem ciphertextView_storeCiphertext {Q : ℕ} {rows : ℕ} (params : Parameters Q)
    (ciphertext : Ciphertext params rows) :
    ciphertextView params (storeCiphertext params ciphertext) = ciphertext := by
  ext row column
  simp [ciphertextView, storeCiphertext, Vector.get]

/-- Concrete backing data for one full cyclic stage. -/
abbrev StoredAccumulator {Q : ℕ} (params : Parameters Q) (rows modulus : ℕ) :=
  Vector (StoredCiphertext params rows) modulus

/-- Materialize every cyclic coordinate and every matrix entry. -/
def storeAccumulator {Q p : ℕ} [NeZero p] {rows : ℕ} (params : Parameters Q)
    (accumulator : Accumulator params rows p) : StoredAccumulator params rows p :=
  Vector.ofFn fun index : Fin p ↦ storeCiphertext params (accumulator (index.val : ZMod p))

/-- Function view backed by the passed data, with no earlier-stage computation on a read. -/
def accumulatorView {Q p : ℕ} [NeZero p] {rows : ℕ} (params : Parameters Q)
    (accumulator : StoredAccumulator params rows p) : Accumulator params rows p :=
  fun index ↦ ciphertextView params (accumulator.get ⟨index.val, index.val_lt⟩)

@[simp]
theorem accumulatorView_storeAccumulator {Q p : ℕ} [NeZero p] {rows : ℕ}
    (params : Parameters Q) (accumulator : Accumulator params rows p) :
    accumulatorView params (storeAccumulator params accumulator) = accumulator := by
  funext index
  simp [accumulatorView, storeAccumulator, Vector.get]

/-- Public cyclic update. No secret bit is an argument to this operation. -/
def step {Q p : ℕ} [NeZero Q] [NeZero p] {rows : ℕ} (params : Parameters Q)
    (control : Ciphertext params rows) (weight : ZMod p)
    (accumulator : Accumulator params rows p) : Accumulator params rows p :=
  fun index ↦ cmux params control (accumulator (index + weight)) (accumulator index)

/-- Executable stored sequence of encrypted conditional rotations. Each recursive call
returns finite data before the next stage reads its entries. -/
def runStored {Q p : ℕ} [NeZero Q] [NeZero p] {rows dimension : ℕ} (params : Parameters Q)
    (controls : Fin dimension → Ciphertext params rows) (weights : Fin dimension → ZMod p)
    (body : ZMod p) : List (Fin dimension) → StoredAccumulator params rows p
  | [] => storeAccumulator params (initial params body)
  | index :: tail =>
      let previous := runStored params controls weights body tail
      storeAccumulator params (step params (controls index) (weights index)
        (accumulatorView params previous))

/-- Mathematical view of the stored public evaluator. -/
def run {Q p : ℕ} [NeZero Q] [NeZero p] {rows dimension : ℕ} (params : Parameters Q)
    (controls : Fin dimension → Ciphertext params rows) (weights : Fin dimension → ZMod p)
    (body : ZMod p) (indices : List (Fin dimension)) : Accumulator params rows p :=
  accumulatorView params (runStored params controls weights body indices)

@[simp]
theorem run_nil {Q p : ℕ} [NeZero Q] [NeZero p] {rows dimension : ℕ} (params : Parameters Q)
    (controls : Fin dimension → Ciphertext params rows) (weights : Fin dimension → ZMod p)
    (body : ZMod p) : run params controls weights body [] = initial params body := by
  simp [run, runStored]

@[simp]
theorem run_cons {Q p : ℕ} [NeZero Q] [NeZero p] {rows dimension : ℕ} (params : Parameters Q)
    (controls : Fin dimension → Ciphertext params rows) (weights : Fin dimension → ZMod p)
    (body : ZMod p) (index : Fin dimension) (tail : List (Fin dimension)) :
    run params controls weights body (index :: tail) =
      step params (controls index) (weights index) (run params controls weights body tail) := by
  simp [run, runStored]

/-- Proof-only location of the ideal indicator. -/
def target {p dimension : ℕ} (bits : Fin dimension → Bool) (weights : Fin dimension → ZMod p)
    (body : ZMod p) : List (Fin dimension) → ZMod p
  | [] => body
  | index :: tail => target bits weights body tail - if bits index then weights index else 0

/-- Every initial indicator ciphertext has zero noise. -/
theorem noiseBound_initial {Q p : ℕ} [NeZero Q] [NeZero p] {rows : ℕ}
    (params : Parameters Q) (secret : Fin rows → ZMod Q) (body index : ZMod p) :
    NoiseBound params secret (initial params body index) (bitMessage (decide (index = body))) 0 := by
  intro column
  by_cases hindex : index = body <;>
    simp [initial, bitMessage, hindex, GSWOperations.noise,
      LatticeCrypto.centeredRepr_eq_valMinAbs]

/-- Each encrypted rotation costs one control digit product and keeps the branch error bound.
All controls and accumulator entries are measured under the same secret. -/
theorem noiseBound_run {Q p : ℕ} [NeZero Q] [NeZero p] {rows dimension : ℕ}
    (params : Parameters Q) (secret : Fin rows → ZMod Q)
    (bits : Fin dimension → Bool) (controls : Fin dimension → Ciphertext params rows)
    (weights : Fin dimension → ZMod p) (body : ZMod p) (indices : List (Fin dimension))
    (bound : ℕ)
    (hcontrols : ∀ index ∈ indices, NoiseBound params secret (controls index)
      (bitMessage (bits index)) bound) :
    ∀ position, NoiseBound params secret (run params controls weights body indices position)
      (bitMessage (decide (position = target bits weights body indices)))
      (indices.length * growth params rows * bound) := by
  induction indices with
  | nil =>
    intro position column
    by_cases hposition : position = body <;>
      simp [run_nil, target, initial, bitMessage, hposition, GSWOperations.noise,
        LatticeCrypto.centeredRepr_eq_valMinAbs]
  | cons index tail ih =>
    intro position
    have hhead := hcontrols index (List.mem_cons_self ..)
    have htail := ih (fun item hitem ↦ hcontrols item (List.mem_cons_of_mem _ hitem))
    have hmessage :
        (if bits index then bitMessage (R := ZMod Q)
            (decide (position + weights index = target bits weights body tail))
          else bitMessage (decide (position = target bits weights body tail))) =
        bitMessage (decide (position = target bits weights body (index :: tail))) := by
      cases hbit : bits index <;> simp [target, hbit, eq_sub_iff_add_eq]
    have hstep := noiseBound_cmux params secret (controls index)
      (run params controls weights body tail (position + weights index))
      (run params controls weights body tail position) (bits index)
      (bitMessage (decide (position + weights index = target bits weights body tail)))
      (bitMessage (decide (position = target bits weights body tail))) bound
      (tail.length * growth params rows * bound) hhead (htail _) (htail _)
    rw [hmessage] at hstep
    simpa only [run_cons, step, List.length_cons, Nat.add_mul, Nat.one_mul,
      Nat.mul_assoc, Nat.add_comm] using hstep

/-- Public programmable lookup of the final encrypted indicator. -/
def lookup {Q p : ℕ} [NeZero Q] [NeZero p] {rows : ℕ} (params : Parameters Q)
    (function : ZMod p → Bool) (accumulator : Accumulator params rows p) :
    Ciphertext params rows :=
  ∑ index : ZMod p, if function index then accumulator index else 0

/-- Sum of the selected ideal indicator entries is precisely the lookup bit. -/
theorem sum_indicator {Q p : ℕ} [NeZero Q] [NeZero p]
    (function : ZMod p → Bool) (location : ZMod p) :
    (∑ index : ZMod p, if function index then
      bitMessage (R := ZMod Q) (decide (index = location)) else 0) = bitMessage (function location) := by
  classical
  have hterm : ∀ index : ZMod p,
      (if function index then bitMessage (R := ZMod Q) (decide (index = location)) else 0) =
        if index = location then bitMessage (function location) else 0 := by
    intro index
    by_cases hindex : index = location
    · subst index
      cases function location <;> simp [bitMessage]
    · simp [bitMessage, hindex]
  simp_rw [hterm]
  simp

/-- Finite sums retain the exact message-relative error sum. -/
theorem noise_sum {Q : ℕ} [NeZero Q] {rows : ℕ} (params : Parameters Q)
    (secret : Fin rows → ZMod Q) {Index : Type} [Fintype Index]
    (ciphertexts : Index → Ciphertext params rows) (messages : Index → ZMod Q) :
    GSWOperations.noise secret (gadget params rows) (∑ index, ciphertexts index)
      (∑ index, messages index) =
      ∑ index, GSWOperations.noise secret (gadget params rows) (ciphertexts index) (messages index) := by
  simp only [GSWOperations.noise, vecMul_sum, Finset.sum_smul, Finset.sum_sub_distrib]

/-- The selected-coordinate sum costs at most the lookup modulus times the accumulator bound. -/
theorem noiseBound_lookup {Q p : ℕ} [NeZero Q] [NeZero p] {rows : ℕ}
    (params : Parameters Q) (secret : Fin rows → ZMod Q) (function : ZMod p → Bool)
    (accumulator : Accumulator params rows p) (location : ZMod p) (bound : ℕ)
    (haccumulator : ∀ index, NoiseBound params secret (accumulator index)
      (bitMessage (decide (index = location))) bound) :
    NoiseBound params secret (lookup params function accumulator) (bitMessage (function location))
      (p * bound) := by
  intro column
  rw [← sum_indicator (Q := Q) function location]
  unfold lookup
  rw [noise_sum]
  simp only [Finset.sum_apply]
  change (LatticeCrypto.centeredRepr (∑ index : ZMod p,
    GSWOperations.noise secret (gadget params rows)
      (if function index then accumulator index else 0)
      (if function index then bitMessage (decide (index = location)) else 0) column)).natAbs ≤ _
  calc
    _ ≤ ∑ index : ZMod p, (LatticeCrypto.centeredRepr
        (GSWOperations.noise secret (gadget params rows)
          (if function index then accumulator index else 0)
          (if function index then bitMessage (decide (index = location)) else 0) column)).natAbs :=
      TFHE.NoiseBounds.centeredRepr_finset_sum_natAbs_le _ Finset.univ
    _ ≤ ∑ _index : ZMod p, bound := by
      apply Finset.sum_le_sum
      intro index _
      cases function index with
      | false => simp [GSWOperations.noise, LatticeCrypto.centeredRepr_eq_valMinAbs]
      | true => simpa using haccumulator index column
    _ = p * bound := by simp

/-- The semantic location is the public body minus the selected secret coefficients. -/
theorem target_eq_sum {p dimension : ℕ} (bits : Fin dimension → Bool)
    (weights : Fin dimension → ZMod p) (body : ZMod p) (indices : List (Fin dimension)) :
    target bits weights body indices =
      body - (indices.map fun index ↦ if bits index then weights index else 0).sum := by
  induction indices with
  | nil => simp [target]
  | cons index tail ih =>
    simp only [target, List.map_cons, List.sum_cons, ih]
    ring

/-- Exactly the LWE phase, with the same binary bits embedded at the lookup modulus. -/
theorem target_all_eq_phase {p dimension : ℕ} (bits : Fin dimension → Bool)
    (weights : Fin dimension → ZMod p) (body : ZMod p) :
    target bits weights body (List.ofFn fun index : Fin dimension ↦ index) =
      body - dotProduct (GSWSelfKey.binaryEmbed bits) weights := by
  rw [target_eq_sum, List.map_ofFn, List.sum_ofFn]
  congr 1
  apply Finset.sum_congr rfl
  intro index _
  cases hbit : bits index <;> simp [GSWSelfKey.binaryEmbed, hbit]

/-- Actual public small-modulus LWE-to-GSW refresh returns stored ciphertext data. -/
def refreshStored {Q p : ℕ} [NeZero Q] [NeZero p] {rows dimension : ℕ} (params : Parameters Q)
    (controls : Fin dimension → Ciphertext params rows) (weights : Fin dimension → ZMod p)
    (body : ZMod p) (function : ZMod p → Bool) : StoredCiphertext params rows :=
  let accumulator := runStored params controls weights body (List.ofFn fun index : Fin dimension ↦ index)
  storeCiphertext params (lookup params function (accumulatorView params accumulator))

/-- Matrix view of the actual stored output, used by phase and correctness theorems. -/
def refresh {Q p : ℕ} [NeZero Q] [NeZero p] {rows dimension : ℕ} (params : Parameters Q)
    (controls : Fin dimension → Ciphertext params rows) (weights : Fin dimension → ZMod p)
    (body : ZMod p) (function : ZMod p → Bool) : Ciphertext params rows :=
  ciphertextView params (refreshStored params controls weights body function)

/-- Concrete output bound independent of the input ciphertext noise and coefficient sizes. -/
theorem noiseBound_refresh {Q p : ℕ} [NeZero Q] [NeZero p] {rows dimension : ℕ}
    (params : Parameters Q) (secret : Fin rows → ZMod Q) (bits : Fin dimension → Bool)
    (controls : Fin dimension → Ciphertext params rows) (weights : Fin dimension → ZMod p)
    (body : ZMod p) (function : ZMod p → Bool) (bound : ℕ)
    (hcontrols : ∀ index, NoiseBound params secret (controls index) (bitMessage (bits index)) bound) :
    NoiseBound params secret (refresh params controls weights body function)
      (bitMessage (function (body - dotProduct (GSWSelfKey.binaryEmbed bits) weights)))
      (p * dimension * growth params rows * bound) := by
  have hrun := noiseBound_run params secret bits controls weights body
    (List.ofFn fun index : Fin dimension ↦ index) bound (fun index _ ↦ hcontrols index)
  rw [target_all_eq_phase] at hrun
  simpa only [refresh, refreshStored, ciphertextView_storeCiphertext, run,
    List.length_ofFn, Nat.mul_assoc] using
    noiseBound_lookup params secret function _ _ _ hrun

/-- An actual one-key control generator: encrypt each secret bit under that same binary secret. -/
def freshBootKey {Q : ℕ} [NeZero Q] {dimension : ℕ} (params : Parameters Q)
    (bits : Fin dimension → Bool)
    (challenges : Fin dimension →
      Matrix (Fin dimension) (Fin ((dimension + 1) * params.levels)) (ZMod Q))
    (errors : Fin dimension → Fin ((dimension + 1) * params.levels) → ZMod Q) :
    Fin dimension → Ciphertext params (dimension + 1) :=
  fun index ↦ GSWOperations.ciphertextMatrix (GSWSelfKey.freshTranscript (layout params dimension)
    (GSWSelfKey.binaryEmbed bits) (fun _ ↦ bitMessage (bits index)) (challenges index) (errors index))

/-- End-to-end deterministic correctness of the small-modulus lookup component using the
actual same-key fresh controls. No second secret or unimplemented ciphertext evaluator occurs. -/
theorem decrypt_refresh_freshBootKey {Q p : ℕ} [NeZero Q] [NeZero p] {dimension : ℕ}
    (params : Parameters Q) (bits : Fin dimension → Bool)
    (challenges : Fin dimension →
      Matrix (Fin dimension) (Fin ((dimension + 1) * params.levels)) (ZMod Q))
    (errors : Fin dimension → Fin ((dimension + 1) * params.levels) → ZMod Q)
    (weights : Fin dimension → ZMod p) (body : ZMod p) (function : ZMod p → Bool)
    (bound : ℕ) (level : Fin params.levels)
    (herrors : ∀ index column, (LatticeCrypto.centeredRepr (errors index column)).natAbs ≤ bound)
    (hmargin : 2 * (p * dimension * growth params (dimension + 1) * bound) <
      TFHE.BootstrappingCorrectness.centeredDistance 0 (TFHE.Gadget.Base.gadget params level)) :
    decrypt params (GSWSelfKey.binaryEmbed bits)
      (refresh params (freshBootKey params bits challenges errors) weights body function) level =
      function (body - dotProduct (GSWSelfKey.binaryEmbed bits) weights) := by
  apply decrypt_eq_bit params (GSWSelfKey.binaryEmbed bits) _ _ _ level _ hmargin
  apply noiseBound_refresh params _ bits
  intro index
  exact noiseBound_fresh params (GSWSelfKey.binaryEmbed bits) (bits index)
    (challenges index) (errors index) bound (herrors index)

end FormalProof4FHE.LWE.GSWAccumulator
